import V185TrunkScan23Chunk0481

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_2851281 : List Nat := [1, 2, 2, 1, 2, 1, 1, 4, 1, 1, 7]
def baseStart_2851281 : Nat := 118140960795 + 2851281 * 2 ^ 59
def prefixEnd_2851281 : Nat := 4983230072969 + 3 ^ 40 * 2851281 * 2
def baseEnd_2851281 : Nat := 1464077634032364083674703

theorem tailTrace_2851281 : CollatzResearch.WordTrace tailWord_2851281 prefixEnd_2851281 1464077634032364083674703 := by
  unfold tailWord_2851281
  simp only [CollatzResearch.WordTrace]
  refine ⟨103994761583303371871041697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69329841055535581247361131 103994761583303371871041697)
  ·
    refine ⟨77996071187477528903281273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 103994761583303371871041697 77996071187477528903281273)
    ·
      refine ⟨58497053390608146677460955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 77996071187477528903281273 58497053390608146677460955)
      ·
        refine ⟨87745580085912220016191433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58497053390608146677460955 87745580085912220016191433)
        ·
          refine ⟨65809185064434165012143575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 87745580085912220016191433 65809185064434165012143575)
          ·
            refine ⟨98713777596651247518215363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65809185064434165012143575 98713777596651247518215363)
            ·
              refine ⟨148070666394976871277323045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 98713777596651247518215363 148070666394976871277323045)
              ·
                refine ⟨27763249949058163364498071, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 148070666394976871277323045 27763249949058163364498071)
                ·
                  refine ⟨41644874923587245046747107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27763249949058163364498071 41644874923587245046747107)
                  ·
                    refine ⟨62467312385380867570120661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 41644874923587245046747107 62467312385380867570120661)
                    ·
                      refine ⟨1464077634032364083674703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 62467312385380867570120661 1464077634032364083674703)
                      ·
                        rfl

theorem cell23_2851281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 4, 1, 1, 7].length) (baseStart_2851281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2851281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2851281 prefixEnd_2851281 := by exact prefixLift 2851281
  have htrace : WordTrace (prefixWord ++ tailWord_2851281) baseStart_2851281 baseEnd_2851281 := by
    simpa [prefixWord, tailWord_2851281, baseEnd_2851281] using wordTrace_append hprefix tailTrace_2851281
  have hstable : (prefixWord ++ tailWord_2851281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2851281).length < 2 ^ (prefixWord ++ tailWord_2851281).sum := by decide
  have hdescent : baseEnd_2851281 < baseStart_2851281 := by decide
  rcases family_descends (prefixWord ++ tailWord_2851281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2851308 : List Nat := [2, 2, 1, 1, 2, 1, 4, 1, 4, 1, 4]
def baseStart_2851308 : Nat := 118140960795 + 2851308 * 2 ^ 59
def prefixEnd_2851308 : Nat := 4983230072969 + 3 ^ 40 * 2851308 * 2
def baseEnd_2851308 : Nat := 1464091498010035478037079

theorem tailTrace_2851308 : CollatzResearch.WordTrace tailWord_2851308 prefixEnd_2851308 1464091498010035478037079 := by
  unfold tailWord_2851308
  simp only [CollatzResearch.WordTrace]
  refine ⟨51997873177102777741137289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69330497569470370321516385 51997873177102777741137289)
  ·
    refine ⟨38998404882827083305852967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51997873177102777741137289 38998404882827083305852967)
    ·
      refine ⟨58497607324240624958779451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38998404882827083305852967 58497607324240624958779451)
      ·
        refine ⟨87746410986360937438169177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58497607324240624958779451 87746410986360937438169177)
        ·
          refine ⟨65809808239770703078626883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 87746410986360937438169177 65809808239770703078626883)
          ·
            refine ⟨98714712359656054617940325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65809808239770703078626883 98714712359656054617940325)
            ·
              refine ⟨18509008567435510240863811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 98714712359656054617940325 18509008567435510240863811)
              ·
                refine ⟨27763512851153265361295717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18509008567435510240863811 27763512851153265361295717)
                ·
                  refine ⟨5205658659591237255242947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27763512851153265361295717 5205658659591237255242947)
                  ·
                    refine ⟨7808487989386855882864421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5205658659591237255242947 7808487989386855882864421)
                    ·
                      refine ⟨1464091498010035478037079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7808487989386855882864421 1464091498010035478037079)
                      ·
                        rfl

theorem cell23_2851308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 1, 4].length) (baseStart_2851308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2851308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2851308 prefixEnd_2851308 := by exact prefixLift 2851308
  have htrace : WordTrace (prefixWord ++ tailWord_2851308) baseStart_2851308 baseEnd_2851308 := by
    simpa [prefixWord, tailWord_2851308, baseEnd_2851308] using wordTrace_append hprefix tailTrace_2851308
  have hstable : (prefixWord ++ tailWord_2851308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2851308).length < 2 ^ (prefixWord ++ tailWord_2851308).sum := by decide
  have hdescent : baseEnd_2851308 < baseStart_2851308 := by decide
  rcases family_descends (prefixWord ++ tailWord_2851308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2851325 : List Nat := [1, 4, 1, 1, 1, 3, 1, 3, 2, 4, 2]
def baseStart_2851325 : Nat := 118140960795 + 2851325 * 2 ^ 59
def prefixEnd_2851325 : Nat := 4983230072969 + 3 ^ 40 * 2851325 * 2
def baseEnd_2851325 : Nat := 1464100227181161911524501

theorem tailTrace_2851325 : CollatzResearch.WordTrace tailWord_2851325 prefixEnd_2851325 1464100227181161911524501 := by
  unfold tailWord_2851325
  simp only [CollatzResearch.WordTrace]
  refine ⟨103996366395143967385643429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69330910930095978257095619 103996366395143967385643429)
  ·
    refine ⟨19499318699089493884808143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 103996366395143967385643429 19499318699089493884808143)
    ·
      refine ⟨29248978048634240827212215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19499318699089493884808143 29248978048634240827212215)
      ·
        refine ⟨43873467072951361240818323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29248978048634240827212215 43873467072951361240818323)
        ·
          refine ⟨65810200609427041861227485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43873467072951361240818323 65810200609427041861227485)
          ·
            refine ⟨24678825228535140697960307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 65810200609427041861227485 24678825228535140697960307)
            ·
              refine ⟨37018237842802711046940461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24678825228535140697960307 37018237842802711046940461)
              ·
                refine ⟨13881839191051016642602673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37018237842802711046940461 13881839191051016642602673)
                ·
                  refine ⟨10411379393288262481952005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13881839191051016642602673 10411379393288262481952005)
                  ·
                    refine ⟨1952133636241549215366001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10411379393288262481952005 1952133636241549215366001)
                    ·
                      refine ⟨1464100227181161911524501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1952133636241549215366001 1464100227181161911524501)
                      ·
                        rfl

theorem cell23_2851325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 1, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 1, 3, 2, 4, 2].length) (baseStart_2851325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2851325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2851325 prefixEnd_2851325 := by exact prefixLift 2851325
  have htrace : WordTrace (prefixWord ++ tailWord_2851325) baseStart_2851325 baseEnd_2851325 := by
    simpa [prefixWord, tailWord_2851325, baseEnd_2851325] using wordTrace_append hprefix tailTrace_2851325
  have hstable : (prefixWord ++ tailWord_2851325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2851325).length < 2 ^ (prefixWord ++ tailWord_2851325).sum := by decide
  have hdescent : baseEnd_2851325 < baseStart_2851325 := by decide
  rcases family_descends (prefixWord ++ tailWord_2851325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2851338 : List Nat := [3, 1, 2, 2, 2, 1, 1, 1, 2, 4, 4]
def baseStart_2851338 : Nat := 118140960795 + 2851338 * 2 ^ 59
def prefixEnd_2851338 : Nat := 4983230072969 + 3 ^ 40 * 2851338 * 2
def baseEnd_2851338 : Nat := 1464106902429670360661941

theorem tailTrace_2851338 : CollatzResearch.WordTrace tailWord_2851338 prefixEnd_2851338 1464106902429670360661941 := by
  unfold tailWord_2851338
  simp only [CollatzResearch.WordTrace]
  refine ⟨25999210136024217651466667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69331227029397913737244445 25999210136024217651466667)
  ·
    refine ⟨38998815204036326477200001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25999210136024217651466667 38998815204036326477200001)
    ·
      refine ⟨29249111403027244857900001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38998815204036326477200001 29249111403027244857900001)
      ·
        refine ⟨21936833552270433643425001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29249111403027244857900001 21936833552270433643425001)
        ·
          refine ⟨16452625164202825232568751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21936833552270433643425001 16452625164202825232568751)
          ·
            refine ⟨24678937746304237848853127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16452625164202825232568751 24678937746304237848853127)
            ·
              refine ⟨37018406619456356773279691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24678937746304237848853127 37018406619456356773279691)
              ·
                refine ⟨55527609929184535159919537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37018406619456356773279691 55527609929184535159919537)
                ·
                  refine ⟨41645707446888401369939653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 55527609929184535159919537 41645707446888401369939653)
                  ·
                    refine ⟨7808570146291575256863685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 41645707446888401369939653 7808570146291575256863685)
                    ·
                      refine ⟨1464106902429670360661941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7808570146291575256863685 1464106902429670360661941)
                      ·
                        rfl

theorem cell23_2851338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 1, 1, 2, 4, 4].length) (baseStart_2851338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2851338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2851338 prefixEnd_2851338 := by exact prefixLift 2851338
  have htrace : WordTrace (prefixWord ++ tailWord_2851338) baseStart_2851338 baseEnd_2851338 := by
    simpa [prefixWord, tailWord_2851338, baseEnd_2851338] using wordTrace_append hprefix tailTrace_2851338
  have hstable : (prefixWord ++ tailWord_2851338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2851338).length < 2 ^ (prefixWord ++ tailWord_2851338).sum := by decide
  have hdescent : baseEnd_2851338 < baseStart_2851338 := by decide
  rcases family_descends (prefixWord ++ tailWord_2851338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2851382 : List Nat := [5, 1, 2, 1, 2, 2, 1, 3, 6]
def baseStart_2851382 : Nat := 118140960795 + 2851382 * 2 ^ 59
def prefixEnd_2851382 : Nat := 4983230072969 + 3 ^ 40 * 2851382 * 2
def baseEnd_2851382 : Nat := 162681055064274243167971

theorem tailTrace_2851382 : CollatzResearch.WordTrace tailWord_2851382 prefixEnd_2851382 162681055064274243167971 := by
  unfold tailWord_2851382
  simp only [CollatzResearch.WordTrace]
  refine ⟨6499902834746091632529275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 69332296903958310746978933 6499902834746091632529275)
  ·
    refine ⟨9749854252119137448793913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6499902834746091632529275 9749854252119137448793913)
    ·
      refine ⟨7312390689089353086595435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9749854252119137448793913 7312390689089353086595435)
      ·
        refine ⟨10968586033634029629893153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7312390689089353086595435 10968586033634029629893153)
        ·
          refine ⟨8226439525225522222419865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10968586033634029629893153 8226439525225522222419865)
          ·
            refine ⟨6169829643919141666814899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8226439525225522222419865 6169829643919141666814899)
            ·
              refine ⟨9254744465878712500222349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6169829643919141666814899 9254744465878712500222349)
              ·
                refine ⟨3470529174704517187583381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9254744465878712500222349 3470529174704517187583381)
                ·
                  refine ⟨162681055064274243167971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3470529174704517187583381 162681055064274243167971)
                  ·
                    rfl

theorem cell23_2851382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 2, 1, 3, 6].length) (baseStart_2851382 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2851382 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2851382 prefixEnd_2851382 := by exact prefixLift 2851382
  have htrace : WordTrace (prefixWord ++ tailWord_2851382) baseStart_2851382 baseEnd_2851382 := by
    simpa [prefixWord, tailWord_2851382, baseEnd_2851382] using wordTrace_append hprefix tailTrace_2851382
  have hstable : (prefixWord ++ tailWord_2851382).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2851382).length < 2 ^ (prefixWord ++ tailWord_2851382).sum := by decide
  have hdescent : baseEnd_2851382 < baseStart_2851382 := by decide
  rcases family_descends (prefixWord ++ tailWord_2851382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2851402 : List Nat := [3, 1, 2, 1, 1, 4, 1, 3, 2, 3, 2]
def baseStart_2851402 : Nat := 118140960795 + 2851402 * 2 ^ 59
def prefixEnd_2851402 : Nat := 4983230072969 + 3 ^ 40 * 2851402 * 2
def baseEnd_2851402 : Nat := 1464139765191558110261647

theorem tailTrace_2851402 : CollatzResearch.WordTrace tailWord_2851402 prefixEnd_2851402 1464139765191558110261647 := by
  unfold tailWord_2851402
  simp only [CollatzResearch.WordTrace]
  refine ⟨25999793703966252384049115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69332783210576673024130973 25999793703966252384049115)
  ·
    refine ⟨38999690555949378576073673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25999793703966252384049115 38999690555949378576073673)
    ·
      refine ⟨29249767916962033932055255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38999690555949378576073673 29249767916962033932055255)
      ·
        refine ⟨43874651875443050898082883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29249767916962033932055255 43874651875443050898082883)
        ·
          refine ⟨65811977813164576347124325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43874651875443050898082883 65811977813164576347124325)
          ·
            refine ⟨12339745839968358065085811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 65811977813164576347124325 12339745839968358065085811)
            ·
              refine ⟨18509618759952537097628717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12339745839968358065085811 18509618759952537097628717)
              ·
                refine ⟨6941107034982201411610769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18509618759952537097628717 6941107034982201411610769)
                ·
                  refine ⟨5205830276236651058708077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6941107034982201411610769 5205830276236651058708077)
                  ·
                    refine ⟨1952186353588744147015529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5205830276236651058708077 1952186353588744147015529)
                    ·
                      refine ⟨1464139765191558110261647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1952186353588744147015529 1464139765191558110261647)
                      ·
                        rfl

theorem cell23_2851402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 1, 3, 2, 3, 2].length) (baseStart_2851402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2851402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2851402 prefixEnd_2851402 := by exact prefixLift 2851402
  have htrace : WordTrace (prefixWord ++ tailWord_2851402) baseStart_2851402 baseEnd_2851402 := by
    simpa [prefixWord, tailWord_2851402, baseEnd_2851402] using wordTrace_append hprefix tailTrace_2851402
  have hstable : (prefixWord ++ tailWord_2851402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2851402).length < 2 ^ (prefixWord ++ tailWord_2851402).sum := by decide
  have hdescent : baseEnd_2851402 < baseStart_2851402 := by decide
  rcases family_descends (prefixWord ++ tailWord_2851402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2851442 : List Nat := [3, 2, 1, 2, 4, 1, 2, 1, 1, 6]
def baseStart_2851442 : Nat := 118140960795 + 2851442 * 2 ^ 59
def prefixEnd_2851442 : Nat := 4983230072969 + 3 ^ 40 * 2851442 * 2
def baseEnd_2851442 : Nat := 488053434805912651253821

theorem tailTrace_2851442 : CollatzResearch.WordTrace tailWord_2851442 prefixEnd_2851442 488053434805912651253821 := by
  unfold tailWord_2851442
  simp only [CollatzResearch.WordTrace]
  refine ⟨26000158433930024091913145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69333755823813397578435053 26000158433930024091913145)
  ·
    refine ⟨19500118825447518068934859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26000158433930024091913145 19500118825447518068934859)
    ·
      refine ⟨29250178238171277103402289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19500118825447518068934859 29250178238171277103402289)
      ·
        refine ⟨21937633678628457827551717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29250178238171277103402289 21937633678628457827551717)
        ·
          refine ⟨4113306314742835842665947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21937633678628457827551717 4113306314742835842665947)
          ·
            refine ⟨6169959472114253763998921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4113306314742835842665947 6169959472114253763998921)
            ·
              refine ⟨4627469604085690322999191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6169959472114253763998921 4627469604085690322999191)
              ·
                refine ⟨6941204406128535484498787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4627469604085690322999191 6941204406128535484498787)
                ·
                  refine ⟨10411806609192803226748181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6941204406128535484498787 10411806609192803226748181)
                  ·
                    refine ⟨488053434805912651253821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10411806609192803226748181 488053434805912651253821)
                    ·
                      rfl

theorem cell23_2851442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 1, 2, 1, 1, 6].length) (baseStart_2851442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2851442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2851442 prefixEnd_2851442 := by exact prefixLift 2851442
  have htrace : WordTrace (prefixWord ++ tailWord_2851442) baseStart_2851442 baseEnd_2851442 := by
    simpa [prefixWord, tailWord_2851442, baseEnd_2851442] using wordTrace_append hprefix tailTrace_2851442
  have hstable : (prefixWord ++ tailWord_2851442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2851442).length < 2 ^ (prefixWord ++ tailWord_2851442).sum := by decide
  have hdescent : baseEnd_2851442 < baseStart_2851442 := by decide
  rcases family_descends (prefixWord ++ tailWord_2851442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2851449 : List Nat := [1, 2, 1, 3, 3, 3, 1, 2, 3, 2, 2]
def baseStart_2851449 : Nat := 118140960795 + 2851449 * 2 ^ 59
def prefixEnd_2851449 : Nat := 4983230072969 + 3 ^ 40 * 2851449 * 2
def baseEnd_2851449 : Nat := 1464163898782319426373931

theorem tailTrace_2851449 : CollatzResearch.WordTrace tailWord_2851449 prefixEnd_2851449 1464163898782319426373931 := by
  unfold tailWord_2851449
  simp only [CollatzResearch.WordTrace]
  refine ⟨104000889046694736563157401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69333926031129824375438267 104000889046694736563157401)
  ·
    refine ⟨78000666785021052422368051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104000889046694736563157401 78000666785021052422368051)
    ·
      refine ⟨117001000177531578633552077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78000666785021052422368051 117001000177531578633552077)
      ·
        refine ⟨43875375066574341987582029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 117001000177531578633552077 43875375066574341987582029)
        ·
          refine ⟨16453265649965378245343261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43875375066574341987582029 16453265649965378245343261)
          ·
            refine ⟨6169974618737016842003723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16453265649965378245343261 6169974618737016842003723)
            ·
              refine ⟨9254961928105525263005585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6169974618737016842003723 9254961928105525263005585)
              ·
                refine ⟨6941221446079143947254189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9254961928105525263005585 6941221446079143947254189)
                ·
                  refine ⟨2602958042279678980220321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6941221446079143947254189 2602958042279678980220321)
                  ·
                    refine ⟨1952218531709759235165241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2602958042279678980220321 1952218531709759235165241)
                    ·
                      refine ⟨1464163898782319426373931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1952218531709759235165241 1464163898782319426373931)
                      ·
                        rfl

theorem cell23_2851449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 3, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 3, 1, 2, 3, 2, 2].length) (baseStart_2851449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2851449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2851449 prefixEnd_2851449 := by exact prefixLift 2851449
  have htrace : WordTrace (prefixWord ++ tailWord_2851449) baseStart_2851449 baseEnd_2851449 := by
    simpa [prefixWord, tailWord_2851449, baseEnd_2851449] using wordTrace_append hprefix tailTrace_2851449
  have hstable : (prefixWord ++ tailWord_2851449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2851449).length < 2 ^ (prefixWord ++ tailWord_2851449).sum := by decide
  have hdescent : baseEnd_2851449 < baseStart_2851449 := by decide
  rcases family_descends (prefixWord ++ tailWord_2851449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2851466 : List Nat := [3, 1, 2, 3, 3, 2, 2, 1, 1, 1, 4]
def baseStart_2851466 : Nat := 118140960795 + 2851466 * 2 ^ 59
def prefixEnd_2851466 : Nat := 4983230072969 + 3 ^ 40 * 2851466 * 2
def baseEnd_2851466 : Nat := 1464172627953445859861353

theorem tailTrace_2851466 : CollatzResearch.WordTrace tailWord_2851466 prefixEnd_2851466 1464172627953445859861353 := by
  unfold tailWord_2851466
  simp only [CollatzResearch.WordTrace]
  refine ⟨26000377271908287116631563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69334339391755432311017501 26000377271908287116631563)
  ·
    refine ⟨39000565907862430674947345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26000377271908287116631563 39000565907862430674947345)
    ·
      refine ⟨29250424430896823006210509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39000565907862430674947345 29250424430896823006210509)
      ·
        refine ⟨10968909161586308627328941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29250424430896823006210509 10968909161586308627328941)
        ·
          refine ⟨4113340935594865735248353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10968909161586308627328941 4113340935594865735248353)
          ·
            refine ⟨3085005701696149301436265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4113340935594865735248353 3085005701696149301436265)
            ·
              refine ⟨2313754276272111976077199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3085005701696149301436265 2313754276272111976077199)
              ·
                refine ⟨3470631414408167964115799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2313754276272111976077199 3470631414408167964115799)
                ·
                  refine ⟨5205947121612251946173699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3470631414408167964115799 5205947121612251946173699)
                  ·
                    refine ⟨7808920682418377919260549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5205947121612251946173699 7808920682418377919260549)
                    ·
                      refine ⟨1464172627953445859861353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7808920682418377919260549 1464172627953445859861353)
                      ·
                        rfl

theorem cell23_2851466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 2, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 2, 2, 1, 1, 1, 4].length) (baseStart_2851466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2851466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2851466 prefixEnd_2851466 := by exact prefixLift 2851466
  have htrace : WordTrace (prefixWord ++ tailWord_2851466) baseStart_2851466 baseEnd_2851466 := by
    simpa [prefixWord, tailWord_2851466, baseEnd_2851466] using wordTrace_append hprefix tailTrace_2851466
  have hstable : (prefixWord ++ tailWord_2851466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2851466).length < 2 ^ (prefixWord ++ tailWord_2851466).sum := by decide
  have hdescent : baseEnd_2851466 < baseStart_2851466 := by decide
  rcases family_descends (prefixWord ++ tailWord_2851466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2851468 : List Nat := [2, 2, 1, 2, 1, 1, 2, 2, 1, 9]
def baseStart_2851468 : Nat := 118140960795 + 2851468 * 2 ^ 59
def prefixEnd_2851468 : Nat := 4983230072969 + 3 ^ 40 * 2851468 * 2
def baseEnd_2851468 : Nat := 488057884971584950678781

theorem tailTrace_2851468 : CollatzResearch.WordTrace tailWord_2851468 prefixEnd_2851468 488057884971584950678781 := by
  unfold tailWord_2851468
  simp only [CollatzResearch.WordTrace]
  refine ⟨52000791016812951404049529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69334388022417268538732705 52000791016812951404049529)
  ·
    refine ⟨39000593262609713553037147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52000791016812951404049529 39000593262609713553037147)
    ·
      refine ⟨58500889893914570329555721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39000593262609713553037147 58500889893914570329555721)
      ·
        refine ⟨43875667420435927747166791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58500889893914570329555721 43875667420435927747166791)
        ·
          refine ⟨65813501130653891620750187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43875667420435927747166791 65813501130653891620750187)
          ·
            refine ⟨98720251695980837431125281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65813501130653891620750187 98720251695980837431125281)
            ·
              refine ⟨74040188771985628073343961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 98720251695980837431125281 74040188771985628073343961)
              ·
                refine ⟨55530141578989221055007971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 74040188771985628073343961 55530141578989221055007971)
                ·
                  refine ⟨83295212368483831582511957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 55530141578989221055007971 83295212368483831582511957)
                  ·
                    refine ⟨488057884971584950678781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 83295212368483831582511957 488057884971584950678781)
                    ·
                      rfl

theorem cell23_2851468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 2, 1, 9].length) (baseStart_2851468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2851468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2851468 prefixEnd_2851468 := by exact prefixLift 2851468
  have htrace : WordTrace (prefixWord ++ tailWord_2851468) baseStart_2851468 baseEnd_2851468 := by
    simpa [prefixWord, tailWord_2851468, baseEnd_2851468] using wordTrace_append hprefix tailTrace_2851468
  have hstable : (prefixWord ++ tailWord_2851468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2851468).length < 2 ^ (prefixWord ++ tailWord_2851468).sum := by decide
  have hdescent : baseEnd_2851468 < baseStart_2851468 := by decide
  rcases family_descends (prefixWord ++ tailWord_2851468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2851476 : List Nat := [2, 4, 2, 2, 1, 3, 1, 2, 2, 4]
def baseStart_2851476 : Nat := 118140960795 + 2851476 * 2 ^ 59
def prefixEnd_2851476 : Nat := 4983230072969 + 3 ^ 40 * 2851476 * 2
def baseEnd_2851476 : Nat := 488059254253330273578769

theorem tailTrace_2851476 : CollatzResearch.WordTrace tailWord_2851476 prefixEnd_2851476 488059254253330273578769 := by
  unfold tailWord_2851476
  simp only [CollatzResearch.WordTrace]
  refine ⟨52000936908798460087195141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69334582545064613449593521 52000936908798460087195141)
  ·
    refine ⟨9750175670399711266349089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 52000936908798460087195141 9750175670399711266349089)
    ·
      refine ⟨7312631752799783449761817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9750175670399711266349089 7312631752799783449761817)
      ·
        refine ⟨5484473814599837587321363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7312631752799783449761817 5484473814599837587321363)
        ·
          refine ⟨8226710721899756380982045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5484473814599837587321363 8226710721899756380982045)
          ·
            refine ⟨3085016520712408642868267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8226710721899756380982045 3085016520712408642868267)
            ·
              refine ⟨4627524781068612964302401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3085016520712408642868267 4627524781068612964302401)
              ·
                refine ⟨3470643585801459723226801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4627524781068612964302401 3470643585801459723226801)
                ·
                  refine ⟨2602982689351094792420101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3470643585801459723226801 2602982689351094792420101)
                  ·
                    refine ⟨488059254253330273578769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2602982689351094792420101 488059254253330273578769)
                    ·
                      rfl

theorem cell23_2851476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 3, 1, 2, 2, 4].length) (baseStart_2851476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2851476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2851476 prefixEnd_2851476 := by exact prefixLift 2851476
  have htrace : WordTrace (prefixWord ++ tailWord_2851476) baseStart_2851476 baseEnd_2851476 := by
    simpa [prefixWord, tailWord_2851476, baseEnd_2851476] using wordTrace_append hprefix tailTrace_2851476
  have hstable : (prefixWord ++ tailWord_2851476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2851476).length < 2 ^ (prefixWord ++ tailWord_2851476).sum := by decide
  have hdescent : baseEnd_2851476 < baseStart_2851476 := by decide
  rcases family_descends (prefixWord ++ tailWord_2851476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2851556 : List Nat := [2, 3, 1, 1, 1, 5, 1, 3, 2, 2, 2]
def baseStart_2851556 : Nat := 118140960795 + 2851556 * 2 ^ 59
def prefixEnd_2851556 : Nat := 4983230072969 + 3 ^ 40 * 2851556 * 2
def baseEnd_2851556 : Nat := 1464218841212350507735939

theorem tailTrace_2851556 : CollatzResearch.WordTrace tailWord_2851556 prefixEnd_2851556 1464218841212350507735939 := by
  unfold tailWord_2851556
  simp only [CollatzResearch.WordTrace]
  refine ⟨52002395828653546918651261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69336527771538062558201681 52002395828653546918651261)
  ·
    refine ⟨19500898435745080094494223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52002395828653546918651261 19500898435745080094494223)
    ·
      refine ⟨29251347653617620141741335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19500898435745080094494223 29251347653617620141741335)
      ·
        refine ⟨43877021480426430212612003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29251347653617620141741335 43877021480426430212612003)
        ·
          refine ⟨65815532220639645318918005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43877021480426430212612003 65815532220639645318918005)
          ·
            refine ⟨6170206145684966748648563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 65815532220639645318918005 6170206145684966748648563)
            ·
              refine ⟨9255309218527450122972845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6170206145684966748648563 9255309218527450122972845)
              ·
                refine ⟨3470740956947793796114817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9255309218527450122972845 3470740956947793796114817)
                ·
                  refine ⟨2603055717710845347086113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3470740956947793796114817 2603055717710845347086113)
                  ·
                    refine ⟨1952291788283134010314585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2603055717710845347086113 1952291788283134010314585)
                    ·
                      refine ⟨1464218841212350507735939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1952291788283134010314585 1464218841212350507735939)
                      ·
                        rfl

theorem cell23_2851556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 5, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 5, 1, 3, 2, 2, 2].length) (baseStart_2851556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2851556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2851556 prefixEnd_2851556 := by exact prefixLift 2851556
  have htrace : WordTrace (prefixWord ++ tailWord_2851556) baseStart_2851556 baseEnd_2851556 := by
    simpa [prefixWord, tailWord_2851556, baseEnd_2851556] using wordTrace_append hprefix tailTrace_2851556
  have hstable : (prefixWord ++ tailWord_2851556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2851556).length < 2 ^ (prefixWord ++ tailWord_2851556).sum := by decide
  have hdescent : baseEnd_2851556 < baseStart_2851556 := by decide
  rcases family_descends (prefixWord ++ tailWord_2851556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2851592 : List Nat := [2, 1, 3, 2, 2, 2, 2, 2, 2, 5]
def baseStart_2851592 : Nat := 118140960795 + 2851592 * 2 ^ 59
def prefixEnd_2851592 : Nat := 4983230072969 + 3 ^ 40 * 2851592 * 2
def baseEnd_2851592 : Nat := 488079108838637455628591

theorem tailTrace_2851592 : CollatzResearch.WordTrace tailWord_2851592 prefixEnd_2851592 488079108838637455628591 := by
  unfold tailWord_2851592
  simp only [CollatzResearch.WordTrace]
  refine ⟨52003052342588335992806515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69337403123451114657075353 52003052342588335992806515)
  ·
    refine ⟨78004578513882503989209773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52003052342588335992806515 78004578513882503989209773)
    ·
      refine ⟨29251716942705938995953665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 78004578513882503989209773 29251716942705938995953665)
      ·
        refine ⟨21938787707029454246965249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29251716942705938995953665 21938787707029454246965249)
        ·
          refine ⟨16454090780272090685223937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21938787707029454246965249 16454090780272090685223937)
          ·
            refine ⟨12340568085204068013917953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16454090780272090685223937 12340568085204068013917953)
            ·
              refine ⟨9255426063903051010438465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12340568085204068013917953 9255426063903051010438465)
              ·
                refine ⟨6941569547927288257828849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9255426063903051010438465 6941569547927288257828849)
                ·
                  refine ⟨5206177160945466193371637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6941569547927288257828849 5206177160945466193371637)
                  ·
                    refine ⟨488079108838637455628591, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5206177160945466193371637 488079108838637455628591)
                    ·
                      rfl

theorem cell23_2851592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 2, 2, 2, 5].length) (baseStart_2851592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2851592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2851592 prefixEnd_2851592 := by exact prefixLift 2851592
  have htrace : WordTrace (prefixWord ++ tailWord_2851592) baseStart_2851592 baseEnd_2851592 := by
    simpa [prefixWord, tailWord_2851592, baseEnd_2851592] using wordTrace_append hprefix tailTrace_2851592
  have hstable : (prefixWord ++ tailWord_2851592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2851592).length < 2 ^ (prefixWord ++ tailWord_2851592).sum := by decide
  have hdescent : baseEnd_2851592 < baseStart_2851592 := by decide
  rcases family_descends (prefixWord ++ tailWord_2851592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2851595 : List Nat := [1, 1, 1, 1, 5, 1, 1, 2, 3, 3, 4]
def baseStart_2851595 : Nat := 118140960795 + 2851595 * 2 ^ 59
def prefixEnd_2851595 : Nat := 4983230072969 + 3 ^ 40 * 2851595 * 2
def baseEnd_2851595 : Nat := 1464238866957875855148259

theorem tailTrace_2851595 : CollatzResearch.WordTrace tailWord_2851595 prefixEnd_2851595 1464238866957875855148259 := by
  unfold tailWord_2851595
  simp only [CollatzResearch.WordTrace]
  refine ⟨104006214104165803497972239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69337476069443868998648159 104006214104165803497972239)
  ·
    refine ⟨156009321156248705246958359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104006214104165803497972239 156009321156248705246958359)
    ·
      refine ⟨234013981734373057870437539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 156009321156248705246958359 234013981734373057870437539)
      ·
        refine ⟨351020972601559586805656309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 234013981734373057870437539 351020972601559586805656309)
        ·
          refine ⟨32908216181396211263030279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 351020972601559586805656309 32908216181396211263030279)
          ·
            refine ⟨49362324272094316894545419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32908216181396211263030279 49362324272094316894545419)
            ·
              refine ⟨74043486408141475341818129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49362324272094316894545419 74043486408141475341818129)
              ·
                refine ⟨55532614806106106506363597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 74043486408141475341818129 55532614806106106506363597)
                ·
                  refine ⟨20824730552289789939886349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 55532614806106106506363597 20824730552289789939886349)
                  ·
                    refine ⟨7809273957108671227457381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20824730552289789939886349 7809273957108671227457381)
                    ·
                      refine ⟨1464238866957875855148259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7809273957108671227457381 1464238866957875855148259)
                      ·
                        rfl

theorem cell23_2851595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 2, 3, 3, 4].length) (baseStart_2851595 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2851595 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2851595 prefixEnd_2851595 := by exact prefixLift 2851595
  have htrace : WordTrace (prefixWord ++ tailWord_2851595) baseStart_2851595 baseEnd_2851595 := by
    simpa [prefixWord, tailWord_2851595, baseEnd_2851595] using wordTrace_append hprefix tailTrace_2851595
  have hstable : (prefixWord ++ tailWord_2851595).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2851595).length < 2 ^ (prefixWord ++ tailWord_2851595).sum := by decide
  have hdescent : baseEnd_2851595 < baseStart_2851595 := by decide
  rcases family_descends (prefixWord ++ tailWord_2851595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2851625 : List Nat := [1, 2, 1, 1, 1, 1, 1, 5, 2, 4, 4]
def baseStart_2851625 : Nat := 118140960795 + 2851625 * 2 ^ 59
def prefixEnd_2851625 : Nat := 4983230072969 + 3 ^ 40 * 2851625 * 2
def baseEnd_2851625 : Nat := 1464254271377510737773121

theorem tailTrace_2851625 : CollatzResearch.WordTrace tailWord_2851625 prefixEnd_2851625 1464254271377510737773121 := by
  unfold tailWord_2851625
  simp only [CollatzResearch.WordTrace]
  refine ⟨104007308294057118621564329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69338205529371412414376219 104007308294057118621564329)
  ·
    refine ⟨78005481220542838966173247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104007308294057118621564329 78005481220542838966173247)
    ·
      refine ⟨117008221830814258449259871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78005481220542838966173247 117008221830814258449259871)
      ·
        refine ⟨175512332746221387673889807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117008221830814258449259871 175512332746221387673889807)
        ·
          refine ⟨263268499119332081510834711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 175512332746221387673889807 263268499119332081510834711)
          ·
            refine ⟨394902748678998122266252067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 263268499119332081510834711 394902748678998122266252067)
            ·
              refine ⟨592354123018497183399378101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 394902748678998122266252067 592354123018497183399378101)
              ·
                refine ⟨55533199032984110943691697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 592354123018497183399378101 55533199032984110943691697)
                ·
                  refine ⟨41649899274738083207768773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 55533199032984110943691697 41649899274738083207768773)
                  ·
                    refine ⟨7809356114013390601456645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 41649899274738083207768773 7809356114013390601456645)
                    ·
                      refine ⟨1464254271377510737773121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7809356114013390601456645 1464254271377510737773121)
                      ·
                        rfl

theorem cell23_2851625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 5, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 5, 2, 4, 4].length) (baseStart_2851625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2851625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2851625 prefixEnd_2851625 := by exact prefixLift 2851625
  have htrace : WordTrace (prefixWord ++ tailWord_2851625) baseStart_2851625 baseEnd_2851625 := by
    simpa [prefixWord, tailWord_2851625, baseEnd_2851625] using wordTrace_append hprefix tailTrace_2851625
  have hstable : (prefixWord ++ tailWord_2851625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2851625).length < 2 ^ (prefixWord ++ tailWord_2851625).sum := by decide
  have hdescent : baseEnd_2851625 < baseStart_2851625 := by decide
  rcases family_descends (prefixWord ++ tailWord_2851625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2851669 : List Nat := [1, 3, 2, 2, 2, 1, 5, 1, 6]
def baseStart_2851669 : Nat := 118140960795 + 2851669 * 2 ^ 59
def prefixEnd_2851669 : Nat := 4983230072969 + 3 ^ 40 * 2851669 * 2
def baseEnd_2851669 : Nat := 162697429391812062846991

theorem tailTrace_2851669 : CollatzResearch.WordTrace tailWord_2851669 prefixEnd_2851669 162697429391812062846991 := by
  unfold tailWord_2851669
  simp only [CollatzResearch.WordTrace]
  refine ⟨104008913105897714136166061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69339275403931809424110707 104008913105897714136166061)
  ·
    refine ⟨39003342414711642801062273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 104008913105897714136166061 39003342414711642801062273)
    ·
      refine ⟨29252506811033732100796705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39003342414711642801062273 29252506811033732100796705)
      ·
        refine ⟨21939380108275299075597529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29252506811033732100796705 21939380108275299075597529)
        ·
          refine ⟨16454535081206474306698147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21939380108275299075597529 16454535081206474306698147)
          ·
            refine ⟨24681802621809711460047221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16454535081206474306698147 24681802621809711460047221)
            ·
              refine ⟨2313918995794660449379427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 24681802621809711460047221 2313918995794660449379427)
              ·
                refine ⟨3470878493691990674069141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2313918995794660449379427 3470878493691990674069141)
                ·
                  refine ⟨162697429391812062846991, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3470878493691990674069141 162697429391812062846991)
                  ·
                    rfl

theorem cell23_2851669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 5, 1, 6].length) (baseStart_2851669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2851669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2851669 prefixEnd_2851669 := by exact prefixLift 2851669
  have htrace : WordTrace (prefixWord ++ tailWord_2851669) baseStart_2851669 baseEnd_2851669 := by
    simpa [prefixWord, tailWord_2851669, baseEnd_2851669] using wordTrace_append hprefix tailTrace_2851669
  have hstable : (prefixWord ++ tailWord_2851669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2851669).length < 2 ^ (prefixWord ++ tailWord_2851669).sum := by decide
  have hdescent : baseEnd_2851669 < baseStart_2851669 := by decide
  rcases family_descends (prefixWord ++ tailWord_2851669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2851675 : List Nat := [1, 1, 1, 1, 1, 1, 1, 1, 6, 4, 5]
def baseStart_2851675 : Nat := 118140960795 + 2851675 * 2 ^ 59
def prefixEnd_2851675 : Nat := 4983230072969 + 3 ^ 40 * 2851675 * 2
def baseEnd_2851675 : Nat := 1464279945410235542147891

theorem tailTrace_2851675 : CollatzResearch.WordTrace tailWord_2851675 prefixEnd_2851675 1464279945410235542147891 := by
  unfold tailWord_2851675
  simp only [CollatzResearch.WordTrace]
  refine ⟨104009131943875977160884479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69339421295917318107256319 104009131943875977160884479)
  ·
    refine ⟨156013697915813965741326719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104009131943875977160884479 156013697915813965741326719)
    ·
      refine ⟨234020546873720948611990079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 156013697915813965741326719 234020546873720948611990079)
      ·
        refine ⟨351030820310581422917985119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 234020546873720948611990079 351030820310581422917985119)
        ·
          refine ⟨526546230465872134376977679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 351030820310581422917985119 526546230465872134376977679)
          ·
            refine ⟨789819345698808201565466519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 526546230465872134376977679 789819345698808201565466519)
            ·
              refine ⟨1184729018548212302348199779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 789819345698808201565466519 1184729018548212302348199779)
              ·
                refine ⟨1777093527822318453522299669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1184729018548212302348199779 1777093527822318453522299669)
                ·
                  refine ⟨83301259116671177508857797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1777093527822318453522299669 83301259116671177508857797)
                  ·
                    refine ⟨15618986084375845782910837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 83301259116671177508857797 15618986084375845782910837)
                    ·
                      refine ⟨1464279945410235542147891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15618986084375845782910837 1464279945410235542147891)
                      ·
                        rfl

theorem cell23_2851675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 6, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 6, 4, 5].length) (baseStart_2851675 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2851675 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2851675 prefixEnd_2851675 := by exact prefixLift 2851675
  have htrace : WordTrace (prefixWord ++ tailWord_2851675) baseStart_2851675 baseEnd_2851675 := by
    simpa [prefixWord, tailWord_2851675, baseEnd_2851675] using wordTrace_append hprefix tailTrace_2851675
  have hstable : (prefixWord ++ tailWord_2851675).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2851675).length < 2 ^ (prefixWord ++ tailWord_2851675).sum := by decide
  have hdescent : baseEnd_2851675 < baseStart_2851675 := by decide
  rcases family_descends (prefixWord ++ tailWord_2851675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2851679 : List Nat := [1, 1, 2, 3, 1, 3, 1, 4, 3, 1, 3]
def baseStart_2851679 : Nat := 118140960795 + 2851679 * 2 ^ 59
def prefixEnd_2851679 : Nat := 4983230072969 + 3 ^ 40 * 2851679 * 2
def baseEnd_2851679 : Nat := 1464281999332853526497873

theorem tailTrace_2851679 : CollatzResearch.WordTrace tailWord_2851679 prefixEnd_2851679 1464281999332853526497873 := by
  unfold tailWord_2851679
  simp only [CollatzResearch.WordTrace]
  refine ⟨104009277835861485844030091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69339518557240990562686727 104009277835861485844030091)
  ·
    refine ⟨156013916753792228766045137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104009277835861485844030091 156013916753792228766045137)
    ·
      refine ⟨117010437565344171574533853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 156013916753792228766045137 117010437565344171574533853)
      ·
        refine ⟨43878914087004064340450195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 117010437565344171574533853 43878914087004064340450195)
        ·
          refine ⟨65818371130506096510675293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43878914087004064340450195 65818371130506096510675293)
          ·
            refine ⟨24681889173939786191503235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 65818371130506096510675293 24681889173939786191503235)
            ·
              refine ⟨37022833760909679287254853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24681889173939786191503235 37022833760909679287254853)
              ·
                refine ⟨6941781330170564866360285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 37022833760909679287254853 6941781330170564866360285)
                ·
                  refine ⟨2603167998813961824885107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6941781330170564866360285 2603167998813961824885107)
                  ·
                    refine ⟨3904751998220942737327661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2603167998813961824885107 3904751998220942737327661)
                    ·
                      refine ⟨1464281999332853526497873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3904751998220942737327661 1464281999332853526497873)
                      ·
                        rfl

theorem cell23_2851679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 1, 4, 3, 1, 3].length) (baseStart_2851679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2851679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2851679 prefixEnd_2851679 := by exact prefixLift 2851679
  have htrace : WordTrace (prefixWord ++ tailWord_2851679) baseStart_2851679 baseEnd_2851679 := by
    simpa [prefixWord, tailWord_2851679, baseEnd_2851679] using wordTrace_append hprefix tailTrace_2851679
  have hstable : (prefixWord ++ tailWord_2851679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2851679).length < 2 ^ (prefixWord ++ tailWord_2851679).sum := by decide
  have hdescent : baseEnd_2851679 < baseStart_2851679 := by decide
  rcases family_descends (prefixWord ++ tailWord_2851679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2851753 : List Nat := [1, 2, 1, 1, 1, 1, 6, 5, 1, 2, 2]
def baseStart_2851753 : Nat := 118140960795 + 2851753 * 2 ^ 59
def prefixEnd_2851753 : Nat := 4983230072969 + 3 ^ 40 * 2851753 * 2
def baseEnd_2851753 : Nat := 1464319996901286236972533

theorem tailTrace_2851753 : CollatzResearch.WordTrace tailWord_2851753 prefixEnd_2851753 1464319996901286236972533 := by
  unfold tailWord_2851753
  simp only [CollatzResearch.WordTrace]
  refine ⟨104011976837593396482223913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69341317891728930988149275 104011976837593396482223913)
  ·
    refine ⟨78008982628195047361667935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104011976837593396482223913 78008982628195047361667935)
    ·
      refine ⟨117013473942292571042501903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78008982628195047361667935 117013473942292571042501903)
      ·
        refine ⟨175520210913438856563752855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117013473942292571042501903 175520210913438856563752855)
        ·
          refine ⟨263280316370158284845629283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 175520210913438856563752855 263280316370158284845629283)
          ·
            refine ⟨394920474555237427268443925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 263280316370158284845629283 394920474555237427268443925)
            ·
              refine ⟨18511897244776754403208309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 394920474555237427268443925 18511897244776754403208309)
              ·
                refine ⟨1735490366697820725300779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 18511897244776754403208309 1735490366697820725300779)
                ·
                  refine ⟨2603235550046731087951169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1735490366697820725300779 2603235550046731087951169)
                  ·
                    refine ⟨1952426662535048315963377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2603235550046731087951169 1952426662535048315963377)
                    ·
                      refine ⟨1464319996901286236972533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1952426662535048315963377 1464319996901286236972533)
                      ·
                        rfl

theorem cell23_2851753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 6, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 6, 5, 1, 2, 2].length) (baseStart_2851753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2851753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2851753 prefixEnd_2851753 := by exact prefixLift 2851753
  have htrace : WordTrace (prefixWord ++ tailWord_2851753) baseStart_2851753 baseEnd_2851753 := by
    simpa [prefixWord, tailWord_2851753, baseEnd_2851753] using wordTrace_append hprefix tailTrace_2851753
  have hstable : (prefixWord ++ tailWord_2851753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2851753).length < 2 ^ (prefixWord ++ tailWord_2851753).sum := by decide
  have hdescent : baseEnd_2851753 < baseStart_2851753 := by decide
  rcases family_descends (prefixWord ++ tailWord_2851753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2851764 : List Nat := [2, 5, 2, 1, 1, 3, 2, 2, 1, 1, 3]
def baseStart_2851764 : Nat := 118140960795 + 2851764 * 2 ^ 59
def prefixEnd_2851764 : Nat := 4983230072969 + 3 ^ 40 * 2851764 * 2
def baseEnd_2851764 : Nat := 1464325645188485693934983

theorem tailTrace_2851764 : CollatzResearch.WordTrace tailWord_2851764 prefixEnd_2851764 1464325645188485693934983 := by
  unfold tailWord_2851764
  simp only [CollatzResearch.WordTrace]
  refine ⟨52006189020276772680437173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69341585360369030240582897 52006189020276772680437173)
  ·
    refine ⟨4875580220650947438790985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 52006189020276772680437173 4875580220650947438790985)
    ·
      refine ⟨3656685165488210579093239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4875580220650947438790985 3656685165488210579093239)
      ·
        refine ⟨5485027748232315868639859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3656685165488210579093239 5485027748232315868639859)
        ·
          refine ⟨8227541622348473802959789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5485027748232315868639859 8227541622348473802959789)
          ·
            refine ⟨3085328108380677676109921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8227541622348473802959789 3085328108380677676109921)
            ·
              refine ⟨2313996081285508257082441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3085328108380677676109921 2313996081285508257082441)
              ·
                refine ⟨1735497060964131192811831, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2313996081285508257082441 1735497060964131192811831)
                ·
                  refine ⟨2603245591446196789217747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1735497060964131192811831 2603245591446196789217747)
                  ·
                    refine ⟨3904868387169295183826621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2603245591446196789217747 3904868387169295183826621)
                    ·
                      refine ⟨1464325645188485693934983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3904868387169295183826621 1464325645188485693934983)
                      ·
                        rfl

theorem cell23_2851764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 3, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 3, 2, 2, 1, 1, 3].length) (baseStart_2851764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2851764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2851764 prefixEnd_2851764 := by exact prefixLift 2851764
  have htrace : WordTrace (prefixWord ++ tailWord_2851764) baseStart_2851764 baseEnd_2851764 := by
    simpa [prefixWord, tailWord_2851764, baseEnd_2851764] using wordTrace_append hprefix tailTrace_2851764
  have hstable : (prefixWord ++ tailWord_2851764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2851764).length < 2 ^ (prefixWord ++ tailWord_2851764).sum := by decide
  have hdescent : baseEnd_2851764 < baseStart_2851764 := by decide
  rcases family_descends (prefixWord ++ tailWord_2851764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2851792 : List Nat := [2, 1, 1, 1, 1, 2, 3, 1, 4, 3, 4]
def baseStart_2851792 : Nat := 118140960795 + 2851792 * 2 ^ 59
def prefixEnd_2851792 : Nat := 4983230072969 + 3 ^ 40 * 2851792 * 2
def baseEnd_2851792 : Nat := 1464340022646811584384853

theorem tailTrace_2851792 : CollatzResearch.WordTrace tailWord_2851792 prefixEnd_2851792 1464340022646811584384853 := by
  unfold tailWord_2851792
  simp only [CollatzResearch.WordTrace]
  refine ⟨52006699642226053071446815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69342266189634737428595753 52006699642226053071446815)
  ·
    refine ⟨78010049463339079607170223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52006699642226053071446815 78010049463339079607170223)
    ·
      refine ⟨117015074195008619410755335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78010049463339079607170223 117015074195008619410755335)
      ·
        refine ⟨175522611292512929116133003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117015074195008619410755335 175522611292512929116133003)
        ·
          refine ⟨263283916938769393674199505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 175522611292512929116133003 263283916938769393674199505)
          ·
            refine ⟨197462937704077045255649629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 263283916938769393674199505 197462937704077045255649629)
            ·
              refine ⟨74048601639028891970868611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 197462937704077045255649629 74048601639028891970868611)
              ·
                refine ⟨111072902458543337956302917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 74048601639028891970868611 111072902458543337956302917)
                ·
                  refine ⟨20826169210976875866806797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 111072902458543337956302917 20826169210976875866806797)
                  ·
                    refine ⟨7809813454116328450052549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20826169210976875866806797 7809813454116328450052549)
                    ·
                      refine ⟨1464340022646811584384853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7809813454116328450052549 1464340022646811584384853)
                      ·
                        rfl

theorem cell23_2851792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 1, 4, 3, 4].length) (baseStart_2851792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2851792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2851792 prefixEnd_2851792 := by exact prefixLift 2851792
  have htrace : WordTrace (prefixWord ++ tailWord_2851792) baseStart_2851792 baseEnd_2851792 := by
    simpa [prefixWord, tailWord_2851792, baseEnd_2851792] using wordTrace_append hprefix tailTrace_2851792
  have hstable : (prefixWord ++ tailWord_2851792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2851792).length < 2 ^ (prefixWord ++ tailWord_2851792).sum := by decide
  have hdescent : baseEnd_2851792 < baseStart_2851792 := by decide
  rcases family_descends (prefixWord ++ tailWord_2851792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2851889 : List Nat := [1, 2, 2, 3, 1, 2, 3, 1, 1, 2, 5]
def baseStart_2851889 : Nat := 118140960795 + 2851889 * 2 ^ 59
def prefixEnd_2851889 : Nat := 4983230072969 + 3 ^ 40 * 2851889 * 2
def baseEnd_2851889 : Nat := 1464389830270297704871907

theorem tailTrace_2851889 : CollatzResearch.WordTrace tailWord_2851889 prefixEnd_2851889 1464389830270297704871907 := by
  unfold tailWord_2851889
  simp only [CollatzResearch.WordTrace]
  refine ⟨104016937165100691709174721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69344624776733794472783147 104016937165100691709174721)
  ·
    refine ⟨78012702873825518781881041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104016937165100691709174721 78012702873825518781881041)
    ·
      refine ⟨58509527155369139086410781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78012702873825518781881041 58509527155369139086410781)
      ·
        refine ⟨21941072683263427157404043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 58509527155369139086410781 21941072683263427157404043)
        ·
          refine ⟨32911609024895140736106065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21941072683263427157404043 32911609024895140736106065)
          ·
            refine ⟨24683706768671355552079549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32911609024895140736106065 24683706768671355552079549)
            ·
              refine ⟨9256390038251758332029831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24683706768671355552079549 9256390038251758332029831)
              ·
                refine ⟨13884585057377637498044747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9256390038251758332029831 13884585057377637498044747)
                ·
                  refine ⟨20826877586066456247067121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13884585057377637498044747 20826877586066456247067121)
                  ·
                    refine ⟨15620158189549842185300341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20826877586066456247067121 15620158189549842185300341)
                    ·
                      refine ⟨1464389830270297704871907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15620158189549842185300341 1464389830270297704871907)
                      ·
                        rfl

theorem cell23_2851889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 3, 1, 1, 2, 5].length) (baseStart_2851889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2851889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2851889 prefixEnd_2851889 := by exact prefixLift 2851889
  have htrace : WordTrace (prefixWord ++ tailWord_2851889) baseStart_2851889 baseEnd_2851889 := by
    simpa [prefixWord, tailWord_2851889, baseEnd_2851889] using wordTrace_append hprefix tailTrace_2851889
  have hstable : (prefixWord ++ tailWord_2851889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2851889).length < 2 ^ (prefixWord ++ tailWord_2851889).sum := by decide
  have hdescent : baseEnd_2851889 < baseStart_2851889 := by decide
  rcases family_descends (prefixWord ++ tailWord_2851889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2851894 : List Nat := [5, 1, 2, 1, 1, 4, 2, 1, 2, 2, 2]
def baseStart_2851894 : Nat := 118140960795 + 2851894 * 2 ^ 59
def prefixEnd_2851894 : Nat := 4983230072969 + 3 ^ 40 * 2851894 * 2
def baseEnd_2851894 : Nat := 1464392397673570185309385

theorem tailTrace_2851894 : CollatzResearch.WordTrace tailWord_2851894 prefixEnd_2851894 1464392397673570185309385 := by
  unfold tailWord_2851894
  simp only [CollatzResearch.WordTrace]
  refine ⟨6501069970630161097694171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 69344746353388385042071157 6501069970630161097694171)
  ·
    refine ⟨9751604955945241646541257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6501069970630161097694171 9751604955945241646541257)
    ·
      refine ⟨7313703716958931234905943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9751604955945241646541257 7313703716958931234905943)
      ·
        refine ⟨10970555575438396852358915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7313703716958931234905943 10970555575438396852358915)
        ·
          refine ⟨16455833363157595278538373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10970555575438396852358915 16455833363157595278538373)
          ·
            refine ⟨3085468755592049114725945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16455833363157595278538373 3085468755592049114725945)
            ·
              refine ⟨2314101566694036836044459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3085468755592049114725945 2314101566694036836044459)
              ·
                refine ⟨3471152350041055254066689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2314101566694036836044459 3471152350041055254066689)
                ·
                  refine ⟨2603364262530791440550017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3471152350041055254066689 2603364262530791440550017)
                  ·
                    refine ⟨1952523196898093580412513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2603364262530791440550017 1952523196898093580412513)
                    ·
                      refine ⟨1464392397673570185309385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1952523196898093580412513 1464392397673570185309385)
                      ·
                        rfl

theorem cell23_2851894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 4, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 4, 2, 1, 2, 2, 2].length) (baseStart_2851894 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2851894 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2851894 prefixEnd_2851894 := by exact prefixLift 2851894
  have htrace : WordTrace (prefixWord ++ tailWord_2851894) baseStart_2851894 baseEnd_2851894 := by
    simpa [prefixWord, tailWord_2851894, baseEnd_2851894] using wordTrace_append hprefix tailTrace_2851894
  have hstable : (prefixWord ++ tailWord_2851894).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2851894).length < 2 ^ (prefixWord ++ tailWord_2851894).sum := by decide
  have hdescent : baseEnd_2851894 < baseStart_2851894 := by decide
  rcases family_descends (prefixWord ++ tailWord_2851894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2851916 : List Nat := [2, 2, 1, 3, 1, 1, 1, 2, 4, 4, 2]
def baseStart_2851916 : Nat := 118140960795 + 2851916 * 2 ^ 59
def prefixEnd_2851916 : Nat := 4983230072969 + 3 ^ 40 * 2851916 * 2
def baseEnd_2851916 : Nat := 1464403694247969099234283

theorem tailTrace_2851916 : CollatzResearch.WordTrace tailWord_2851916 prefixEnd_2851916 1464403694247969099234283 := by
  unfold tailWord_2851916
  simp only [CollatzResearch.WordTrace]
  refine ⟨52008960968001437660203801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69345281290668583546938401 52008960968001437660203801)
  ·
    refine ⟨39006720726001078245152851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52008960968001437660203801 39006720726001078245152851)
    ·
      refine ⟨58510081089001617367729277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39006720726001078245152851 58510081089001617367729277)
      ·
        refine ⟨21941280408375606512898479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 58510081089001617367729277 21941280408375606512898479)
        ·
          refine ⟨32911920612563409769347719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21941280408375606512898479 32911920612563409769347719)
          ·
            refine ⟨49367880918845114654021579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32911920612563409769347719 49367880918845114654021579)
            ·
              refine ⟨74051821378267671981032369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49367880918845114654021579 74051821378267671981032369)
              ·
                refine ⟨55538866033700753985774277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 74051821378267671981032369 55538866033700753985774277)
                ·
                  refine ⟨10413537381318891372332677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 55538866033700753985774277 10413537381318891372332677)
                  ·
                    refine ⟨1952538258997292132312377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10413537381318891372332677 1952538258997292132312377)
                    ·
                      refine ⟨1464403694247969099234283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1952538258997292132312377 1464403694247969099234283)
                      ·
                        rfl

theorem cell23_2851916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 2, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 2, 4, 4, 2].length) (baseStart_2851916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2851916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2851916 prefixEnd_2851916 := by exact prefixLift 2851916
  have htrace : WordTrace (prefixWord ++ tailWord_2851916) baseStart_2851916 baseEnd_2851916 := by
    simpa [prefixWord, tailWord_2851916, baseEnd_2851916] using wordTrace_append hprefix tailTrace_2851916
  have hstable : (prefixWord ++ tailWord_2851916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2851916).length < 2 ^ (prefixWord ++ tailWord_2851916).sum := by decide
  have hdescent : baseEnd_2851916 < baseStart_2851916 := by decide
  rcases family_descends (prefixWord ++ tailWord_2851916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2851934 : List Nat := [4, 4, 1, 1, 1, 3, 2, 2, 5]
def baseStart_2851934 : Nat := 118140960795 + 2851934 * 2 ^ 59
def prefixEnd_2851934 : Nat := 4983230072969 + 3 ^ 40 * 2851934 * 2
def baseEnd_2851934 : Nat := 162712548544416669867689

theorem tailTrace_2851934 : CollatzResearch.WordTrace tailWord_2851934 prefixEnd_2851934 162712548544416669867689 := by
  unfold tailWord_2851934
  simp only [CollatzResearch.WordTrace]
  refine ⟨13002322306242208049320357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 69345718966625109596375237 13002322306242208049320357)
  ·
    refine ⟨2437935432420414009247567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13002322306242208049320357 2437935432420414009247567)
    ·
      refine ⟨3656903148630621013871351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2437935432420414009247567 3656903148630621013871351)
      ·
        refine ⟨5485354722945931520807027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3656903148630621013871351 5485354722945931520807027)
        ·
          refine ⟨8228032084418897281210541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5485354722945931520807027 8228032084418897281210541)
          ·
            refine ⟨3085512031657086480453953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8228032084418897281210541 3085512031657086480453953)
            ·
              refine ⟨2314134023742814860340465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3085512031657086480453953 2314134023742814860340465)
              ·
                refine ⟨1735600517807111145255349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2314134023742814860340465 1735600517807111145255349)
                ·
                  refine ⟨162712548544416669867689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1735600517807111145255349 162712548544416669867689)
                  ·
                    rfl

theorem cell23_2851934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 3, 2, 2, 5].length) (baseStart_2851934 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2851934 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2851934 prefixEnd_2851934 := by exact prefixLift 2851934
  have htrace : WordTrace (prefixWord ++ tailWord_2851934) baseStart_2851934 baseEnd_2851934 := by
    simpa [prefixWord, tailWord_2851934, baseEnd_2851934] using wordTrace_append hprefix tailTrace_2851934
  have hstable : (prefixWord ++ tailWord_2851934).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2851934).length < 2 ^ (prefixWord ++ tailWord_2851934).sum := by decide
  have hdescent : baseEnd_2851934 < baseStart_2851934 := by decide
  rcases family_descends (prefixWord ++ tailWord_2851934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2851936 : List Nat := [2, 1, 1, 3, 2, 2, 1, 4, 2, 2, 3]
def baseStart_2851936 : Nat := 118140960795 + 2851936 * 2 ^ 59
def prefixEnd_2851936 : Nat := 4983230072969 + 3 ^ 40 * 2851936 * 2
def baseEnd_2851936 : Nat := 1464413963861059020984191

theorem tailTrace_2851936 : CollatzResearch.WordTrace tailWord_2851936 prefixEnd_2851936 1464413963861059020984191 := by
  unfold tailWord_2851936
  simp only [CollatzResearch.WordTrace]
  refine ⟨52009325697965209368067831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69345767597286945824090441 52009325697965209368067831)
  ·
    refine ⟨78013988546947814052101747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52009325697965209368067831 78013988546947814052101747)
    ·
      refine ⟨117020982820421721078152621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78013988546947814052101747 117020982820421721078152621)
      ·
        refine ⟨43882868557658145404307233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 117020982820421721078152621 43882868557658145404307233)
        ·
          refine ⟨32912151418243609053230425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43882868557658145404307233 32912151418243609053230425)
          ·
            refine ⟨24684113563682706789922819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32912151418243609053230425 24684113563682706789922819)
            ·
              refine ⟨37026170345524060184884229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24684113563682706789922819 37026170345524060184884229)
              ·
                refine ⟨6942406939785761284665793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 37026170345524060184884229 6942406939785761284665793)
                ·
                  refine ⟨5206805204839320963499345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6942406939785761284665793 5206805204839320963499345)
                  ·
                    refine ⟨3905103903629490722624509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5206805204839320963499345 3905103903629490722624509)
                    ·
                      refine ⟨1464413963861059020984191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3905103903629490722624509 1464413963861059020984191)
                      ·
                        rfl

theorem cell23_2851936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 1, 4, 2, 2, 3].length) (baseStart_2851936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2851936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2851936 prefixEnd_2851936 := by exact prefixLift 2851936
  have htrace : WordTrace (prefixWord ++ tailWord_2851936) baseStart_2851936 baseEnd_2851936 := by
    simpa [prefixWord, tailWord_2851936, baseEnd_2851936] using wordTrace_append hprefix tailTrace_2851936
  have hstable : (prefixWord ++ tailWord_2851936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2851936).length < 2 ^ (prefixWord ++ tailWord_2851936).sum := by decide
  have hdescent : baseEnd_2851936 < baseStart_2851936 := by decide
  rcases family_descends (prefixWord ++ tailWord_2851936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2852000 : List Nat := [2, 1, 1, 4, 2, 1, 1, 6, 1, 1, 3]
def baseStart_2852000 : Nat := 118140960795 + 2852000 * 2 ^ 59
def prefixEnd_2852000 : Nat := 4983230072969 + 3 ^ 40 * 2852000 * 2
def baseEnd_2852000 : Nat := 1464446826622946770583897

theorem tailTrace_2852000 : CollatzResearch.WordTrace tailWord_2852000 prefixEnd_2852000 1464446826622946770583897 := by
  unfold tailWord_2852000
  simp only [CollatzResearch.WordTrace]
  refine ⟨52010492833849278833232727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69347323778465705110976969 52010492833849278833232727)
  ·
    refine ⟨78015739250773918249849091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52010492833849278833232727 78015739250773918249849091)
    ·
      refine ⟨117023608876160877374773637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78015739250773918249849091 117023608876160877374773637)
      ·
        refine ⟨21941926664280164507770057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 117023608876160877374773637 21941926664280164507770057)
        ·
          refine ⟨16456444998210123380827543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21941926664280164507770057 16456444998210123380827543)
          ·
            refine ⟨24684667497315185071241315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16456444998210123380827543 24684667497315185071241315)
            ·
              refine ⟨37027001245972777606861973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24684667497315185071241315 37027001245972777606861973)
              ·
                refine ⟨1735640683404973950321655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 37027001245972777606861973 1735640683404973950321655)
                ·
                  refine ⟨2603461025107460925482483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1735640683404973950321655 2603461025107460925482483)
                  ·
                    refine ⟨3905191537661191388223725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2603461025107460925482483 3905191537661191388223725)
                    ·
                      refine ⟨1464446826622946770583897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3905191537661191388223725 1464446826622946770583897)
                      ·
                        rfl

theorem cell23_2852000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 1, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 1, 6, 1, 1, 3].length) (baseStart_2852000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2852000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2852000 prefixEnd_2852000 := by exact prefixLift 2852000
  have htrace : WordTrace (prefixWord ++ tailWord_2852000) baseStart_2852000 baseEnd_2852000 := by
    simpa [prefixWord, tailWord_2852000, baseEnd_2852000] using wordTrace_append hprefix tailTrace_2852000
  have hstable : (prefixWord ++ tailWord_2852000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2852000).length < 2 ^ (prefixWord ++ tailWord_2852000).sum := by decide
  have hdescent : baseEnd_2852000 < baseStart_2852000 := by decide
  rcases family_descends (prefixWord ++ tailWord_2852000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2852010 : List Nat := [3, 1, 5, 1, 1, 1, 1, 2, 1, 5, 2]
def baseStart_2852010 : Nat := 118140960795 + 2852010 * 2 ^ 59
def prefixEnd_2852010 : Nat := 4983230072969 + 3 ^ 40 * 2852010 * 2
def baseEnd_2852010 : Nat := 1464451961429491731458851

theorem tailTrace_2852010 : CollatzResearch.WordTrace tailWord_2852010 prefixEnd_2852010 1464451961429491731458851 := by
  unfold tailWord_2852010
  simp only [CollatzResearch.WordTrace]
  refine ⟨26005337599415582343582371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69347566931774886249552989 26005337599415582343582371)
  ·
    refine ⟨39008006399123373515373557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26005337599415582343582371 39008006399123373515373557)
    ·
      refine ⟨3657000599917816267066271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 39008006399123373515373557 3657000599917816267066271)
      ·
        refine ⟨5485500899876724400599407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3657000599917816267066271 5485500899876724400599407)
        ·
          refine ⟨8228251349815086600899111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5485500899876724400599407 8228251349815086600899111)
          ·
            refine ⟨12342377024722629901348667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8228251349815086600899111 12342377024722629901348667)
            ·
              refine ⟨18513565537083944852023001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12342377024722629901348667 18513565537083944852023001)
              ·
                refine ⟨13885174152812958639017251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18513565537083944852023001 13885174152812958639017251)
                ·
                  refine ⟨20827761229219437958525877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13885174152812958639017251 20827761229219437958525877)
                  ·
                    refine ⟨1952602615239322308611801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 20827761229219437958525877 1952602615239322308611801)
                    ·
                      refine ⟨1464451961429491731458851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1952602615239322308611801 1464451961429491731458851)
                      ·
                        rfl

theorem cell23_2852010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 1, 2, 1, 5, 2].length) (baseStart_2852010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2852010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2852010 prefixEnd_2852010 := by exact prefixLift 2852010
  have htrace : WordTrace (prefixWord ++ tailWord_2852010) baseStart_2852010 baseEnd_2852010 := by
    simpa [prefixWord, tailWord_2852010, baseEnd_2852010] using wordTrace_append hprefix tailTrace_2852010
  have hstable : (prefixWord ++ tailWord_2852010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2852010).length < 2 ^ (prefixWord ++ tailWord_2852010).sum := by decide
  have hdescent : baseEnd_2852010 < baseStart_2852010 := by decide
  rcases family_descends (prefixWord ++ tailWord_2852010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2852023 : List Nat := [1, 1, 3, 1, 4, 1, 4, 2, 1, 1, 4]
def baseStart_2852023 : Nat := 118140960795 + 2852023 * 2 ^ 59
def prefixEnd_2852023 : Nat := 4983230072969 + 3 ^ 40 * 2852023 * 2
def baseEnd_2852023 : Nat := 1464458636678000180596291

theorem tailTrace_2852023 : CollatzResearch.WordTrace tailWord_2852023 prefixEnd_2852023 1464458636678000180596291 := by
  unfold tailWord_2852023
  simp only [CollatzResearch.WordTrace]
  refine ⟨104021824546615232594552723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69347883031076821729701815 104021824546615232594552723)
  ·
    refine ⟨156032736819922848891829085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104021824546615232594552723 156032736819922848891829085)
    ·
      refine ⟨58512276307471068334435907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 156032736819922848891829085 58512276307471068334435907)
      ·
        refine ⟨87768414461206602501653861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58512276307471068334435907 87768414461206602501653861)
        ·
          refine ⟨16456577711476237969060099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 87768414461206602501653861 16456577711476237969060099)
          ·
            refine ⟨24684866567214356953590149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16456577711476237969060099 24684866567214356953590149)
            ·
              refine ⟨4628412481352691928798153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24684866567214356953590149 4628412481352691928798153)
              ·
                refine ⟨3471309361014518946598615, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4628412481352691928798153 3471309361014518946598615)
                ·
                  refine ⟨5206964041521778419897923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3471309361014518946598615 5206964041521778419897923)
                  ·
                    refine ⟨7810446062282667629846885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5206964041521778419897923 7810446062282667629846885)
                    ·
                      refine ⟨1464458636678000180596291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7810446062282667629846885 1464458636678000180596291)
                      ·
                        rfl

theorem cell23_2852023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 4, 2, 1, 1, 4].length) (baseStart_2852023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2852023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2852023 prefixEnd_2852023 := by exact prefixLift 2852023
  have htrace : WordTrace (prefixWord ++ tailWord_2852023) baseStart_2852023 baseEnd_2852023 := by
    simpa [prefixWord, tailWord_2852023, baseEnd_2852023] using wordTrace_append hprefix tailTrace_2852023
  have hstable : (prefixWord ++ tailWord_2852023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2852023).length < 2 ^ (prefixWord ++ tailWord_2852023).sum := by decide
  have hdescent : baseEnd_2852023 < baseStart_2852023 := by decide
  rcases family_descends (prefixWord ++ tailWord_2852023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2852077 : List Nat := [1, 5, 1, 2, 2, 3, 1, 2, 1, 2, 3]
def baseStart_2852077 : Nat := 118140960795 + 2852077 * 2 ^ 59
def prefixEnd_2852077 : Nat := 4983230072969 + 3 ^ 40 * 2852077 * 2
def baseEnd_2852077 : Nat := 1464486364633342969321043

theorem tailTrace_2852077 : CollatzResearch.WordTrace tailWord_2852077 prefixEnd_2852077 1464486364633342969321043 := by
  unfold tailWord_2852077
  simp only [CollatzResearch.WordTrace]
  refine ⟨104023794088419599817018485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69349196058946399878012323 104023794088419599817018485)
  ·
    refine ⟨9752230695789337482845483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 104023794088419599817018485 9752230695789337482845483)
    ·
      refine ⟨14628346043684006224268225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9752230695789337482845483 14628346043684006224268225)
      ·
        refine ⟨10971259532763004668201169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14628346043684006224268225 10971259532763004668201169)
        ·
          refine ⟨8228444649572253501150877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10971259532763004668201169 8228444649572253501150877)
          ·
            refine ⟨3085666743589595062931579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8228444649572253501150877 3085666743589595062931579)
            ·
              refine ⟨4628500115384392594397369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3085666743589595062931579 4628500115384392594397369)
              ·
                refine ⟨3471375086538294445798027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4628500115384392594397369 3471375086538294445798027)
                ·
                  refine ⟨5207062629807441668697041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3471375086538294445798027 5207062629807441668697041)
                  ·
                    refine ⟨3905296972355581251522781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5207062629807441668697041 3905296972355581251522781)
                    ·
                      refine ⟨1464486364633342969321043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3905296972355581251522781 1464486364633342969321043)
                      ·
                        rfl

theorem cell23_2852077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 3, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 3, 1, 2, 1, 2, 3].length) (baseStart_2852077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2852077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2852077 prefixEnd_2852077 := by exact prefixLift 2852077
  have htrace : WordTrace (prefixWord ++ tailWord_2852077) baseStart_2852077 baseEnd_2852077 := by
    simpa [prefixWord, tailWord_2852077, baseEnd_2852077] using wordTrace_append hprefix tailTrace_2852077
  have hstable : (prefixWord ++ tailWord_2852077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2852077).length < 2 ^ (prefixWord ++ tailWord_2852077).sum := by decide
  have hdescent : baseEnd_2852077 < baseStart_2852077 := by decide
  rcases family_descends (prefixWord ++ tailWord_2852077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2852106 : List Nat := [3, 1, 2, 2, 1, 1, 1, 4, 2, 6]
def baseStart_2852106 : Nat := 118140960795 + 2852106 * 2 ^ 59
def prefixEnd_2852106 : Nat := 4983230072969 + 3 ^ 40 * 2852106 * 2
def baseEnd_2852106 : Nat := 488167085190774451952803

theorem tailTrace_2852106 : CollatzResearch.WordTrace tailWord_2852106 prefixEnd_2852106 488167085190774451952803 := by
  unfold tailWord_2852106
  simp only [CollatzResearch.WordTrace]
  refine ⟨26006212951328634442456043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69349901203543025179882781 26006212951328634442456043)
  ·
    refine ⟨39009319426992951663684065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26006212951328634442456043 39009319426992951663684065)
    ·
      refine ⟨29256989570244713747763049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39009319426992951663684065 29256989570244713747763049)
      ·
        refine ⟨21942742177683535310822287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29256989570244713747763049 21942742177683535310822287)
        ·
          refine ⟨32914113266525302966233431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21942742177683535310822287 32914113266525302966233431)
          ·
            refine ⟨49371169899787954449350147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32914113266525302966233431 49371169899787954449350147)
            ·
              refine ⟨74056754849681931674025221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49371169899787954449350147 74056754849681931674025221)
              ·
                refine ⟨13885641534315362188879729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 74056754849681931674025221 13885641534315362188879729)
                ·
                  refine ⟨10414231150736521641659797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13885641534315362188879729 10414231150736521641659797)
                  ·
                    refine ⟨488167085190774451952803, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10414231150736521641659797 488167085190774451952803)
                    ·
                      rfl

theorem cell23_2852106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 4, 2, 6].length) (baseStart_2852106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2852106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2852106 prefixEnd_2852106 := by exact prefixLift 2852106
  have htrace : WordTrace (prefixWord ++ tailWord_2852106) baseStart_2852106 baseEnd_2852106 := by
    simpa [prefixWord, tailWord_2852106, baseEnd_2852106] using wordTrace_append hprefix tailTrace_2852106
  have hstable : (prefixWord ++ tailWord_2852106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2852106).length < 2 ^ (prefixWord ++ tailWord_2852106).sum := by decide
  have hdescent : baseEnd_2852106 < baseStart_2852106 := by decide
  rcases family_descends (prefixWord ++ tailWord_2852106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2852113 : List Nat := [1, 2, 2, 1, 1, 4, 1, 2, 3, 4, 2]
def baseStart_2852113 : Nat := 118140960795 + 2852113 * 2 ^ 59
def prefixEnd_2852113 : Nat := 4983230072969 + 3 ^ 40 * 2852113 * 2
def baseEnd_2852113 : Nat := 1464504849936904828470877

theorem tailTrace_2852113 : CollatzResearch.WordTrace tailWord_2852113 prefixEnd_2852113 1464504849936904828470877 := by
  unfold tailWord_2852113
  simp only [CollatzResearch.WordTrace]
  refine ⟨104025107116289177965328993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69350071410859451976885995 104025107116289177965328993)
  ·
    refine ⟨78018830337216883473996745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104025107116289177965328993 78018830337216883473996745)
    ·
      refine ⟨58514122752912662605497559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78018830337216883473996745 58514122752912662605497559)
      ·
        refine ⟨87771184129368993908246339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58514122752912662605497559 87771184129368993908246339)
        ·
          refine ⟨131656776194053490862369509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87771184129368993908246339 131656776194053490862369509)
          ·
            refine ⟨24685645536385029536694283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 131656776194053490862369509 24685645536385029536694283)
            ·
              refine ⟨37028468304577544305041425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24685645536385029536694283 37028468304577544305041425)
              ·
                refine ⟨27771351228433158228781069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37028468304577544305041425 27771351228433158228781069)
                ·
                  refine ⟨10414256710662434335792901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27771351228433158228781069 10414256710662434335792901)
                  ·
                    refine ⟨1952673133249206437961169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10414256710662434335792901 1952673133249206437961169)
                    ·
                      refine ⟨1464504849936904828470877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1952673133249206437961169 1464504849936904828470877)
                      ·
                        rfl

theorem cell23_2852113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 4, 2].length) (baseStart_2852113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2852113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2852113 prefixEnd_2852113 := by exact prefixLift 2852113
  have htrace : WordTrace (prefixWord ++ tailWord_2852113) baseStart_2852113 baseEnd_2852113 := by
    simpa [prefixWord, tailWord_2852113, baseEnd_2852113] using wordTrace_append hprefix tailTrace_2852113
  have hstable : (prefixWord ++ tailWord_2852113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2852113).length < 2 ^ (prefixWord ++ tailWord_2852113).sum := by decide
  have hdescent : baseEnd_2852113 < baseStart_2852113 := by decide
  rcases family_descends (prefixWord ++ tailWord_2852113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2852164 : List Nat := [2, 3, 4, 1, 1, 2, 1, 1, 4, 2, 2]
def baseStart_2852164 : Nat := 118140960795 + 2852164 * 2 ^ 59
def prefixEnd_2852164 : Nat := 4983230072969 + 3 ^ 40 * 2852164 * 2
def baseEnd_2852164 : Nat := 1464531037450284128933143

theorem tailTrace_2852164 : CollatzResearch.WordTrace tailWord_2852164 prefixEnd_2852164 1464531037450284128933143 := by
  unfold tailWord_2852164
  simp only [CollatzResearch.WordTrace]
  refine ⟨52013483619552206837717773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69351311492736275783623697 52013483619552206837717773)
  ·
    refine ⟨19505056357332077564144165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52013483619552206837717773 19505056357332077564144165)
    ·
      refine ⟨3657198066999764543277031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19505056357332077564144165 3657198066999764543277031)
      ·
        refine ⟨5485797100499646814915547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3657198066999764543277031 5485797100499646814915547)
        ·
          refine ⟨8228695650749470222373321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5485797100499646814915547 8228695650749470222373321)
          ·
            refine ⟨6171521738062102666779991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8228695650749470222373321 6171521738062102666779991)
            ·
              refine ⟨9257282607093154000169987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6171521738062102666779991 9257282607093154000169987)
              ·
                refine ⟨13885923910639731000254981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9257282607093154000169987 13885923910639731000254981)
                ·
                  refine ⟨2603610733244949562547809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13885923910639731000254981 2603610733244949562547809)
                  ·
                    refine ⟨1952708049933712171910857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2603610733244949562547809 1952708049933712171910857)
                    ·
                      refine ⟨1464531037450284128933143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1952708049933712171910857 1464531037450284128933143)
                      ·
                        rfl

theorem cell23_2852164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 2, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 2, 1, 1, 4, 2, 2].length) (baseStart_2852164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2852164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2852164 prefixEnd_2852164 := by exact prefixLift 2852164
  have htrace : WordTrace (prefixWord ++ tailWord_2852164) baseStart_2852164 baseEnd_2852164 := by
    simpa [prefixWord, tailWord_2852164, baseEnd_2852164] using wordTrace_append hprefix tailTrace_2852164
  have hstable : (prefixWord ++ tailWord_2852164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2852164).length < 2 ^ (prefixWord ++ tailWord_2852164).sum := by decide
  have hdescent : baseEnd_2852164 < baseStart_2852164 := by decide
  rcases family_descends (prefixWord ++ tailWord_2852164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2852176 : List Nat := [2, 1, 1, 1, 1, 5, 2, 1, 1, 1, 7]
def baseStart_2852176 : Nat := 118140960795 + 2852176 * 2 ^ 59
def prefixEnd_2852176 : Nat := 4983230072969 + 3 ^ 40 * 2852176 * 2
def baseEnd_2852176 : Nat := 1464537199218138081983087

theorem tailTrace_2852176 : CollatzResearch.WordTrace tailWord_2852176 prefixEnd_2852176 1464537199218138081983087 := by
  unfold tailWord_2852176
  simp only [CollatzResearch.WordTrace]
  refine ⟨52013702457530469862436191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69351603276707293149914921 52013702457530469862436191)
  ·
    refine ⟨78020553686295704793654287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52013702457530469862436191 78020553686295704793654287)
    ·
      refine ⟨117030830529443557190481431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78020553686295704793654287 117030830529443557190481431)
      ·
        refine ⟨175546245794165335785722147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117030830529443557190481431 175546245794165335785722147)
        ·
          refine ⟨263319368691248003678583221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 175546245794165335785722147 263319368691248003678583221)
          ·
            refine ⟨24686190814804500344867177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 263319368691248003678583221 24686190814804500344867177)
            ·
              refine ⟨18514643111103375258650383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24686190814804500344867177 18514643111103375258650383)
              ·
                refine ⟨27771964666655062887975575, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18514643111103375258650383 27771964666655062887975575)
                ·
                  refine ⟨41657946999982594331963363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27771964666655062887975575 41657946999982594331963363)
                  ·
                    refine ⟨62486920499973891497945045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 41657946999982594331963363 62486920499973891497945045)
                    ·
                      refine ⟨1464537199218138081983087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 62486920499973891497945045 1464537199218138081983087)
                      ·
                        rfl

theorem cell23_2852176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 2, 1, 1, 1, 7].length) (baseStart_2852176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2852176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2852176 prefixEnd_2852176 := by exact prefixLift 2852176
  have htrace : WordTrace (prefixWord ++ tailWord_2852176) baseStart_2852176 baseEnd_2852176 := by
    simpa [prefixWord, tailWord_2852176, baseEnd_2852176] using wordTrace_append hprefix tailTrace_2852176
  have hstable : (prefixWord ++ tailWord_2852176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2852176).length < 2 ^ (prefixWord ++ tailWord_2852176).sum := by decide
  have hdescent : baseEnd_2852176 < baseStart_2852176 := by decide
  rcases family_descends (prefixWord ++ tailWord_2852176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2852254 : List Nat := [4, 3, 1, 2, 2, 1, 2, 1, 2, 1, 4]
def baseStart_2852254 : Nat := 118140960795 + 2852254 * 2 ^ 59
def prefixEnd_2852254 : Nat := 4983230072969 + 3 ^ 40 * 2852254 * 2
def baseEnd_2852254 : Nat := 1464577250709188776807729

theorem tailTrace_2852254 : CollatzResearch.WordTrace tailWord_2852254 prefixEnd_2852254 1464577250709188776807729 := by
  unfold tailWord_2852254
  simp only [CollatzResearch.WordTrace]
  refine ⟨13003781226097294880776477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 69353499872518906030807877 13003781226097294880776477)
  ·
    refine ⟨4876417959786485580291179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13003781226097294880776477 4876417959786485580291179)
    ·
      refine ⟨7314626939679728370436769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4876417959786485580291179 7314626939679728370436769)
      ·
        refine ⟨5485970204759796277827577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7314626939679728370436769 5485970204759796277827577)
        ·
          refine ⟨4114477653569847208370683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5485970204759796277827577 4114477653569847208370683)
          ·
            refine ⟨6171716480354770812556025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4114477653569847208370683 6171716480354770812556025)
            ·
              refine ⟨4628787360266078109417019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6171716480354770812556025 4628787360266078109417019)
              ·
                refine ⟨6943181040399117164125529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4628787360266078109417019 6943181040399117164125529)
                ·
                  refine ⟨5207385780299337873094147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6943181040399117164125529 5207385780299337873094147)
                  ·
                    refine ⟨7811078670449006809641221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5207385780299337873094147 7811078670449006809641221)
                    ·
                      refine ⟨1464577250709188776807729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7811078670449006809641221 1464577250709188776807729)
                      ·
                        rfl

theorem cell23_2852254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 1, 2, 1, 2, 1, 4].length) (baseStart_2852254 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2852254 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2852254 prefixEnd_2852254 := by exact prefixLift 2852254
  have htrace : WordTrace (prefixWord ++ tailWord_2852254) baseStart_2852254 baseEnd_2852254 := by
    simpa [prefixWord, tailWord_2852254, baseEnd_2852254] using wordTrace_append hprefix tailTrace_2852254
  have hstable : (prefixWord ++ tailWord_2852254).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2852254).length < 2 ^ (prefixWord ++ tailWord_2852254).sum := by decide
  have hdescent : baseEnd_2852254 < baseStart_2852254 := by decide
  rcases family_descends (prefixWord ++ tailWord_2852254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2852281 : List Nat := [1, 2, 1, 4, 4, 2, 2, 2, 1, 4]
def baseStart_2852281 : Nat := 118140960795 + 2852281 * 2 ^ 59
def prefixEnd_2852281 : Nat := 4983230072969 + 3 ^ 40 * 2852281 * 2
def baseEnd_2852281 : Nat := 488197038228953390390035

theorem tailTrace_2852281 : CollatzResearch.WordTrace tailWord_2852281 prefixEnd_2852281 488197038228953390390035 := by
  unfold tailWord_2852281
  simp only [CollatzResearch.WordTrace]
  refine ⟨104031234579680542657444697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69354156386453695104963131 104031234579680542657444697)
  ·
    refine ⟨78023425934760406993083523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104031234579680542657444697 78023425934760406993083523)
    ·
      refine ⟨117035138902140610489625285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78023425934760406993083523 117035138902140610489625285)
      ·
        refine ⟨21944088544151364466804741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 117035138902140610489625285 21944088544151364466804741)
        ·
          refine ⟨4114516602028380837525889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21944088544151364466804741 4114516602028380837525889)
          ·
            refine ⟨3085887451521285628144417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4114516602028380837525889 3085887451521285628144417)
            ·
              refine ⟨2314415588640964221108313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3085887451521285628144417 2314415588640964221108313)
              ·
                refine ⟨1735811691480723165831235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2314415588640964221108313 1735811691480723165831235)
                ·
                  refine ⟨2603717537221084748746853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1735811691480723165831235 2603717537221084748746853)
                  ·
                    refine ⟨488197038228953390390035, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2603717537221084748746853 488197038228953390390035)
                    ·
                      rfl

theorem cell23_2852281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 2, 2, 2, 1, 4].length) (baseStart_2852281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2852281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2852281 prefixEnd_2852281 := by exact prefixLift 2852281
  have htrace : WordTrace (prefixWord ++ tailWord_2852281) baseStart_2852281 baseEnd_2852281 := by
    simpa [prefixWord, tailWord_2852281, baseEnd_2852281] using wordTrace_append hprefix tailTrace_2852281
  have hstable : (prefixWord ++ tailWord_2852281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2852281).length < 2 ^ (prefixWord ++ tailWord_2852281).sum := by decide
  have hdescent : baseEnd_2852281 < baseStart_2852281 := by decide
  rcases family_descends (prefixWord ++ tailWord_2852281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2852303 : List Nat := [1, 1, 2, 1, 1, 4, 3, 3, 1, 6]
def baseStart_2852303 : Nat := 118140960795 + 2852303 * 2 ^ 59
def prefixEnd_2852303 : Nat := 4983230072969 + 3 ^ 40 * 2852303 * 2
def baseEnd_2852303 : Nat := 488200803753753028365001

theorem tailTrace_2852303 : CollatzResearch.WordTrace tailWord_2852303 prefixEnd_2852303 488200803753753028365001 := by
  unfold tailWord_2852303
  simp only [CollatzResearch.WordTrace]
  refine ⟨104032036985600840414745563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69354691323733893609830375 104032036985600840414745563)
  ·
    refine ⟨156048055478401260622118345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104032036985600840414745563 156048055478401260622118345)
    ·
      refine ⟨117036041608800945466588759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 156048055478401260622118345 117036041608800945466588759)
      ·
        refine ⟨175554062413201418199883139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117036041608800945466588759 175554062413201418199883139)
        ·
          refine ⟨263331093619802127299824709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 175554062413201418199883139 263331093619802127299824709)
          ·
            refine ⟨49374580053712898868717133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 263331093619802127299824709 49374580053712898868717133)
            ·
              refine ⟨18515467520142337075768925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 49374580053712898868717133 18515467520142337075768925)
              ·
                refine ⟨6943300320053376403413347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18515467520142337075768925 6943300320053376403413347)
                ·
                  refine ⟨10414950480080064605120021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6943300320053376403413347 10414950480080064605120021)
                  ·
                    refine ⟨488200803753753028365001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10414950480080064605120021 488200803753753028365001)
                    ·
                      rfl

theorem cell23_2852303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 3, 3, 1, 6].length) (baseStart_2852303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2852303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2852303 prefixEnd_2852303 := by exact prefixLift 2852303
  have htrace : WordTrace (prefixWord ++ tailWord_2852303) baseStart_2852303 baseEnd_2852303 := by
    simpa [prefixWord, tailWord_2852303, baseEnd_2852303] using wordTrace_append hprefix tailTrace_2852303
  have hstable : (prefixWord ++ tailWord_2852303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2852303).length < 2 ^ (prefixWord ++ tailWord_2852303).sum := by decide
  have hdescent : baseEnd_2852303 < baseStart_2852303 := by decide
  rcases family_descends (prefixWord ++ tailWord_2852303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2852314 : List Nat := [3, 1, 1, 2, 3, 4, 1, 1, 2, 3, 2]
def baseStart_2852314 : Nat := 118140960795 + 2852314 * 2 ^ 59
def prefixEnd_2852314 : Nat := 4983230072969 + 3 ^ 40 * 2852314 * 2
def baseEnd_2852314 : Nat := 1464608059548458542057453

theorem tailTrace_2852314 : CollatzResearch.WordTrace tailWord_2852314 prefixEnd_2852314 1464608059548458542057453 := by
  unfold tailWord_2852314
  simp only [CollatzResearch.WordTrace]
  refine ⟨26008109547140247323348999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69354958792373992862263997 26008109547140247323348999)
  ·
    refine ⟨39012164320710370985023499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26008109547140247323348999 39012164320710370985023499)
    ·
      refine ⟨58518246481065556477535249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39012164320710370985023499 58518246481065556477535249)
      ·
        refine ⟨43888684860799167358151437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58518246481065556477535249 43888684860799167358151437)
        ·
          refine ⟨16458256822799687759306789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43888684860799167358151437 16458256822799687759306789)
          ·
            refine ⟨3085923154274941454870023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16458256822799687759306789 3085923154274941454870023)
            ·
              refine ⟨4628884731412412182305035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3085923154274941454870023 4628884731412412182305035)
              ·
                refine ⟨6943327097118618273457553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4628884731412412182305035 6943327097118618273457553)
                ·
                  refine ⟨5207495322838963705093165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6943327097118618273457553 5207495322838963705093165)
                  ·
                    refine ⟨1952810746064611389409937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5207495322838963705093165 1952810746064611389409937)
                    ·
                      refine ⟨1464608059548458542057453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1952810746064611389409937 1464608059548458542057453)
                      ·
                        rfl

theorem cell23_2852314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 4, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 4, 1, 1, 2, 3, 2].length) (baseStart_2852314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2852314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2852314 prefixEnd_2852314 := by exact prefixLift 2852314
  have htrace : WordTrace (prefixWord ++ tailWord_2852314) baseStart_2852314 baseEnd_2852314 := by
    simpa [prefixWord, tailWord_2852314, baseEnd_2852314] using wordTrace_append hprefix tailTrace_2852314
  have hstable : (prefixWord ++ tailWord_2852314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2852314).length < 2 ^ (prefixWord ++ tailWord_2852314).sum := by decide
  have hdescent : baseEnd_2852314 < baseStart_2852314 := by decide
  rcases family_descends (prefixWord ++ tailWord_2852314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2852327 : List Nat := [1, 1, 5, 2, 1, 3, 1, 3, 1, 1, 4]
def baseStart_2852327 : Nat := 118140960795 + 2852327 * 2 ^ 59
def prefixEnd_2852327 : Nat := 4983230072969 + 3 ^ 40 * 2852327 * 2
def baseEnd_2852327 : Nat := 1464614734796966991194893

theorem tailTrace_2852327 : CollatzResearch.WordTrace tailWord_2852327 prefixEnd_2852327 1464614734796966991194893 := by
  unfold tailWord_2852327
  simp only [CollatzResearch.WordTrace]
  refine ⟨104032912337513892513619235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69355274891675928342412823 104032912337513892513619235)
  ·
    refine ⟨156049368506270838770428853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104032912337513892513619235 156049368506270838770428853)
    ·
      refine ⟨14629628297462891134727705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 156049368506270838770428853 14629628297462891134727705)
      ·
        refine ⟨10972221223097168351045779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14629628297462891134727705 10972221223097168351045779)
        ·
          refine ⟨16458331834645752526568669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10972221223097168351045779 16458331834645752526568669)
          ·
            refine ⟨6171874437992157197463251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16458331834645752526568669 6171874437992157197463251)
            ·
              refine ⟨9257811656988235796194877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6171874437992157197463251 9257811656988235796194877)
              ·
                refine ⟨3471679371370588423573079, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9257811656988235796194877 3471679371370588423573079)
                ·
                  refine ⟨5207519057055882635359619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3471679371370588423573079 5207519057055882635359619)
                  ·
                    refine ⟨7811278585583823953039429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5207519057055882635359619 7811278585583823953039429)
                    ·
                      refine ⟨1464614734796966991194893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7811278585583823953039429 1464614734796966991194893)
                      ·
                        rfl

theorem cell23_2852327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 3, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 3, 1, 3, 1, 1, 4].length) (baseStart_2852327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2852327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2852327 prefixEnd_2852327 := by exact prefixLift 2852327
  have htrace : WordTrace (prefixWord ++ tailWord_2852327) baseStart_2852327 baseEnd_2852327 := by
    simpa [prefixWord, tailWord_2852327, baseEnd_2852327] using wordTrace_append hprefix tailTrace_2852327
  have hstable : (prefixWord ++ tailWord_2852327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2852327).length < 2 ^ (prefixWord ++ tailWord_2852327).sum := by decide
  have hdescent : baseEnd_2852327 < baseStart_2852327 := by decide
  rcases family_descends (prefixWord ++ tailWord_2852327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2852337 : List Nat := [1, 2, 2, 2, 3, 2, 3, 2, 2, 4]
def baseStart_2852337 : Nat := 118140960795 + 2852337 * 2 ^ 59
def prefixEnd_2852337 : Nat := 4983230072969 + 3 ^ 40 * 2852337 * 2
def baseEnd_2852337 : Nat := 488206623201170650689949

theorem tailTrace_2852337 : CollatzResearch.WordTrace tailWord_2852337 prefixEnd_2852337 488206623201170650689949 := by
  unfold tailWord_2852337
  simp only [CollatzResearch.WordTrace]
  refine ⟨104033277067477664221483265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69355518044985109480988843 104033277067477664221483265)
  ·
    refine ⟨78024957800608248166112449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104033277067477664221483265 78024957800608248166112449)
    ·
      refine ⟨58518718350456186124584337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78024957800608248166112449 58518718350456186124584337)
      ·
        refine ⟨43889038762842139593438253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58518718350456186124584337 43889038762842139593438253)
        ·
          refine ⟨16458389536065802347539345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43889038762842139593438253 16458389536065802347539345)
          ·
            refine ⟨12343792152049351760654509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16458389536065802347539345 12343792152049351760654509)
            ·
              refine ⟨4628922057018506910245441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12343792152049351760654509 4628922057018506910245441)
              ·
                refine ⟨3471691542763880182684081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4628922057018506910245441 3471691542763880182684081)
                ·
                  refine ⟨2603768657072910137013061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3471691542763880182684081 2603768657072910137013061)
                  ·
                    refine ⟨488206623201170650689949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2603768657072910137013061 488206623201170650689949)
                    ·
                      rfl

theorem cell23_2852337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 3, 2, 2, 4].length) (baseStart_2852337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2852337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2852337 prefixEnd_2852337 := by exact prefixLift 2852337
  have htrace : WordTrace (prefixWord ++ tailWord_2852337) baseStart_2852337 baseEnd_2852337 := by
    simpa [prefixWord, tailWord_2852337, baseEnd_2852337] using wordTrace_append hprefix tailTrace_2852337
  have hstable : (prefixWord ++ tailWord_2852337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2852337).length < 2 ^ (prefixWord ++ tailWord_2852337).sum := by decide
  have hdescent : baseEnd_2852337 < baseStart_2852337 := by decide
  rcases family_descends (prefixWord ++ tailWord_2852337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2852344 : List Nat := [2, 1, 2, 1, 1, 6, 2, 1, 3, 2, 2]
def baseStart_2852344 : Nat := 118140960795 + 2852344 * 2 ^ 59
def prefixEnd_2852344 : Nat := 4983230072969 + 3 ^ 40 * 2852344 * 2
def baseEnd_2852344 : Nat := 1464623463968093424682315

theorem tailTrace_2852344 : CollatzResearch.WordTrace tailWord_2852344 prefixEnd_2852344 1464623463968093424682315 := by
  unfold tailWord_2852344
  simp only [CollatzResearch.WordTrace]
  refine ⟨52016766189226152208494043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69355688252301536277992057 52016766189226152208494043)
  ·
    refine ⟨78025149283839228312741065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52016766189226152208494043 78025149283839228312741065)
    ·
      refine ⟨58518861962879421234555799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78025149283839228312741065 58518861962879421234555799)
      ·
        refine ⟨87778292944319131851833699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58518861962879421234555799 87778292944319131851833699)
        ·
          refine ⟨131667439416478697777750549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87778292944319131851833699 131667439416478697777750549)
          ·
            refine ⟨6171911222647438958332057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 131667439416478697777750549 6171911222647438958332057)
            ·
              refine ⟨4628933416985579218749043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6171911222647438958332057 4628933416985579218749043)
              ·
                refine ⟨6943400125478368828123565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4628933416985579218749043 6943400125478368828123565)
                ·
                  refine ⟨2603775047054388310546337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6943400125478368828123565 2603775047054388310546337)
                  ·
                    refine ⟨1952831285290791232909753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2603775047054388310546337 1952831285290791232909753)
                    ·
                      refine ⟨1464623463968093424682315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1952831285290791232909753 1464623463968093424682315)
                      ·
                        rfl

theorem cell23_2852344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 6, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 6, 2, 1, 3, 2, 2].length) (baseStart_2852344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2852344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2852344 prefixEnd_2852344 := by exact prefixLift 2852344
  have htrace : WordTrace (prefixWord ++ tailWord_2852344) baseStart_2852344 baseEnd_2852344 := by
    simpa [prefixWord, tailWord_2852344, baseEnd_2852344] using wordTrace_append hprefix tailTrace_2852344
  have hstable : (prefixWord ++ tailWord_2852344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2852344).length < 2 ^ (prefixWord ++ tailWord_2852344).sum := by decide
  have hdescent : baseEnd_2852344 < baseStart_2852344 := by decide
  rcases family_descends (prefixWord ++ tailWord_2852344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2852354 : List Nat := [3, 4, 1, 2, 1, 3, 1, 1, 1, 6]
def baseStart_2852354 : Nat := 118140960795 + 2852354 * 2 ^ 59
def prefixEnd_2852354 : Nat := 4983230072969 + 3 ^ 40 * 2852354 * 2
def baseEnd_2852354 : Nat := 488209532924879461852423

theorem tailTrace_2852354 : CollatzResearch.WordTrace tailWord_2852354 prefixEnd_2852354 488209532924879461852423 := by
  unfold tailWord_2852354
  simp only [CollatzResearch.WordTrace]
  refine ⟨26008474277104019031213029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69355931405610717416568077 26008474277104019031213029)
  ·
    refine ⟨4876588926957003568352443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 26008474277104019031213029 4876588926957003568352443)
    ·
      refine ⟨7314883390435505352528665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4876588926957003568352443 7314883390435505352528665)
      ·
        refine ⟨5486162542826629014396499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7314883390435505352528665 5486162542826629014396499)
        ·
          refine ⟨8229243814239943521594749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5486162542826629014396499 8229243814239943521594749)
          ·
            refine ⟨3085966430339978820598031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8229243814239943521594749 3085966430339978820598031)
            ·
              refine ⟨4628949645509968230897047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3085966430339978820598031 4628949645509968230897047)
              ·
                refine ⟨6943424468264952346345571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4628949645509968230897047 6943424468264952346345571)
                ·
                  refine ⟨10415136702397428519518357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6943424468264952346345571 10415136702397428519518357)
                  ·
                    refine ⟨488209532924879461852423, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10415136702397428519518357 488209532924879461852423)
                    ·
                      rfl

theorem cell23_2852354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 3, 1, 1, 1, 6].length) (baseStart_2852354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2852354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2852354 prefixEnd_2852354 := by exact prefixLift 2852354
  have htrace : WordTrace (prefixWord ++ tailWord_2852354) baseStart_2852354 baseEnd_2852354 := by
    simpa [prefixWord, tailWord_2852354, baseEnd_2852354] using wordTrace_append hprefix tailTrace_2852354
  have hstable : (prefixWord ++ tailWord_2852354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2852354).length < 2 ^ (prefixWord ++ tailWord_2852354).sum := by decide
  have hdescent : baseEnd_2852354 < baseStart_2852354 := by decide
  rcases family_descends (prefixWord ++ tailWord_2852354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2852358 : List Nat := [6, 2, 1, 1, 2, 1, 2, 2, 1, 5]
def baseStart_2852358 : Nat := 118140960795 + 2852358 * 2 ^ 59
def prefixEnd_2852358 : Nat := 4983230072969 + 3 ^ 40 * 2852358 * 2
def baseEnd_2852358 : Nat := 488210217565752123302417

theorem tailTrace_2852358 : CollatzResearch.WordTrace tailWord_2852358 prefixEnd_2852358 488210217565752123302417 := by
  unfold tailWord_2852358
  simp only [CollatzResearch.WordTrace]
  refine ⟨3251063843762549525249929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 69356028666934389871998485 3251063843762549525249929)
  ·
    refine ⟨2438297882821912143937447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3251063843762549525249929 2438297882821912143937447)
    ·
      refine ⟨3657446824232868215906171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2438297882821912143937447 3657446824232868215906171)
      ·
        refine ⟨5486170236349302323859257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3657446824232868215906171 5486170236349302323859257)
        ·
          refine ⟨4114627677261976742894443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5486170236349302323859257 4114627677261976742894443)
          ·
            refine ⟨6171941515892965114341665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4114627677261976742894443 6171941515892965114341665)
            ·
              refine ⟨4628956136919723835756249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6171941515892965114341665 4628956136919723835756249)
              ·
                refine ⟨3471717102689792876817187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4628956136919723835756249 3471717102689792876817187)
                ·
                  refine ⟨5207575654034689315225781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3471717102689792876817187 5207575654034689315225781)
                  ·
                    refine ⟨488210217565752123302417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5207575654034689315225781 488210217565752123302417)
                    ·
                      rfl

theorem cell23_2852358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 1, 2, 2, 1, 5].length) (baseStart_2852358 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2852358 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2852358 prefixEnd_2852358 := by exact prefixLift 2852358
  have htrace : WordTrace (prefixWord ++ tailWord_2852358) baseStart_2852358 baseEnd_2852358 := by
    simpa [prefixWord, tailWord_2852358, baseEnd_2852358] using wordTrace_append hprefix tailTrace_2852358
  have hstable : (prefixWord ++ tailWord_2852358).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2852358).length < 2 ^ (prefixWord ++ tailWord_2852358).sum := by decide
  have hdescent : baseEnd_2852358 < baseStart_2852358 := by decide
  rcases family_descends (prefixWord ++ tailWord_2852358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2852364 : List Nat := [2, 2, 1, 2, 5, 1, 2, 2, 1, 2, 3]
def baseStart_2852364 : Nat := 118140960795 + 2852364 * 2 ^ 59
def prefixEnd_2852364 : Nat := 4983230072969 + 3 ^ 40 * 2852364 * 2
def baseEnd_2852364 : Nat := 1464633733581183346432223

theorem tailTrace_2852364 : CollatzResearch.WordTrace tailWord_2852364 prefixEnd_2852364 1464633733581183346432223 := by
  unfold tailWord_2852364
  simp only [CollatzResearch.WordTrace]
  refine ⟨52017130919189923916358073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69356174558919898555144097 52017130919189923916358073)
  ·
    refine ⟨39012848189392442937268555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52017130919189923916358073 39012848189392442937268555)
    ·
      refine ⟨58519272284088664405902833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39012848189392442937268555 58519272284088664405902833)
      ·
        refine ⟨43889454213066498304427125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58519272284088664405902833 43889454213066498304427125)
        ·
          refine ⟨4114636332474984216040043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 43889454213066498304427125 4114636332474984216040043)
          ·
            refine ⟨6171954498712476324060065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4114636332474984216040043 6171954498712476324060065)
            ·
              refine ⟨4628965874034357243045049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6171954498712476324060065 4628965874034357243045049)
              ·
                refine ⟨3471724405525767932283787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4628965874034357243045049 3471724405525767932283787)
                ·
                  refine ⟨5207586608288651898425681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3471724405525767932283787 5207586608288651898425681)
                  ·
                    refine ⟨3905689956216488923819261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5207586608288651898425681 3905689956216488923819261)
                    ·
                      refine ⟨1464633733581183346432223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3905689956216488923819261 1464633733581183346432223)
                      ·
                        rfl

theorem cell23_2852364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 1, 2, 2, 1, 2, 3].length) (baseStart_2852364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2852364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2852364 prefixEnd_2852364 := by exact prefixLift 2852364
  have htrace : WordTrace (prefixWord ++ tailWord_2852364) baseStart_2852364 baseEnd_2852364 := by
    simpa [prefixWord, tailWord_2852364, baseEnd_2852364] using wordTrace_append hprefix tailTrace_2852364
  have hstable : (prefixWord ++ tailWord_2852364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2852364).length < 2 ^ (prefixWord ++ tailWord_2852364).sum := by decide
  have hdescent : baseEnd_2852364 < baseStart_2852364 := by decide
  rcases family_descends (prefixWord ++ tailWord_2852364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2852394 : List Nat := [3, 1, 4, 1, 1, 1, 2, 4, 2, 1, 3]
def baseStart_2852394 : Nat := 118140960795 + 2852394 * 2 ^ 59
def prefixEnd_2852394 : Nat := 4983230072969 + 3 ^ 40 * 2852394 * 2
def baseEnd_2852394 : Nat := 1464649138000818229057085

theorem tailTrace_2852394 : CollatzResearch.WordTrace tailWord_2852394 prefixEnd_2852394 1464649138000818229057085 := by
  unfold tailWord_2852394
  simp only [CollatzResearch.WordTrace]
  refine ⟨26008839007067790739077059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69356904018847441970872157 26008839007067790739077059)
  ·
    refine ⟨39013258510601686108615589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26008839007067790739077059 39013258510601686108615589)
    ·
      refine ⟨7314985970737816145365423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 39013258510601686108615589 7314985970737816145365423)
      ·
        refine ⟨10972478956106724218048135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7314985970737816145365423 10972478956106724218048135)
        ·
          refine ⟨16458718434160086327072203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10972478956106724218048135 16458718434160086327072203)
          ·
            refine ⟨24688077651240129490608305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16458718434160086327072203 24688077651240129490608305)
            ·
              refine ⟨18516058238430097117956229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24688077651240129490608305 18516058238430097117956229)
              ·
                refine ⟨3471760919705643209616793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18516058238430097117956229 3471760919705643209616793)
                ·
                  refine ⟨2603820689779232407212595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3471760919705643209616793 2603820689779232407212595)
                  ·
                    refine ⟨3905731034668848610818893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2603820689779232407212595 3905731034668848610818893)
                    ·
                      refine ⟨1464649138000818229057085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3905731034668848610818893 1464649138000818229057085)
                      ·
                        rfl

theorem cell23_2852394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 2, 4, 2, 1, 3].length) (baseStart_2852394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2852394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2852394 prefixEnd_2852394 := by exact prefixLift 2852394
  have htrace : WordTrace (prefixWord ++ tailWord_2852394) baseStart_2852394 baseEnd_2852394 := by
    simpa [prefixWord, tailWord_2852394, baseEnd_2852394] using wordTrace_append hprefix tailTrace_2852394
  have hstable : (prefixWord ++ tailWord_2852394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2852394).length < 2 ^ (prefixWord ++ tailWord_2852394).sum := by decide
  have hdescent : baseEnd_2852394 < baseStart_2852394 := by decide
  rcases family_descends (prefixWord ++ tailWord_2852394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2852430 : List Nat := [4, 1, 1, 1, 1, 2, 1, 2, 4, 2, 4]
def baseStart_2852430 : Nat := 118140960795 + 2852430 * 2 ^ 59
def prefixEnd_2852430 : Nat := 4983230072969 + 3 ^ 40 * 2852430 * 2
def baseEnd_2852430 : Nat := 1464667623304380088206919

theorem tailTrace_2852430 : CollatzResearch.WordTrace tailWord_2852430 prefixEnd_2852430 1464667623304380088206919 := by
  unfold tailWord_2852430
  simp only [CollatzResearch.WordTrace]
  refine ⟨13004583632017592638077343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 69357779370760494069745829 13004583632017592638077343)
  ·
    refine ⟨19506875448026388957116015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13004583632017592638077343 19506875448026388957116015)
    ·
      refine ⟨29260313172039583435674023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19506875448026388957116015 29260313172039583435674023)
      ·
        refine ⟨43890469758059375153511035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29260313172039583435674023 43890469758059375153511035)
        ·
          refine ⟨65835704637089062730266553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43890469758059375153511035 65835704637089062730266553)
          ·
            refine ⟨49376778477816797047699915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65835704637089062730266553 49376778477816797047699915)
            ·
              refine ⟨74065167716725195571549873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49376778477816797047699915 74065167716725195571549873)
              ·
                refine ⟨55548875787543896678662405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 74065167716725195571549873 55548875787543896678662405)
                ·
                  refine ⟨10415414210164480627249201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 55548875787543896678662405 10415414210164480627249201)
                  ·
                    refine ⟨7811560657623360470436901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10415414210164480627249201 7811560657623360470436901)
                    ·
                      refine ⟨1464667623304380088206919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7811560657623360470436901 1464667623304380088206919)
                      ·
                        rfl

theorem cell23_2852430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 2, 4, 2, 4].length) (baseStart_2852430 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2852430 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2852430 prefixEnd_2852430 := by exact prefixLift 2852430
  have htrace : WordTrace (prefixWord ++ tailWord_2852430) baseStart_2852430 baseEnd_2852430 := by
    simpa [prefixWord, tailWord_2852430, baseEnd_2852430] using wordTrace_append hprefix tailTrace_2852430
  have hstable : (prefixWord ++ tailWord_2852430).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2852430).length < 2 ^ (prefixWord ++ tailWord_2852430).sum := by decide
  have hdescent : baseEnd_2852430 < baseStart_2852430 := by decide
  rcases family_descends (prefixWord ++ tailWord_2852430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2852434 : List Nat := [3, 2, 2, 1, 2, 3, 1, 2, 1, 4, 2]
def baseStart_2852434 : Nat := 118140960795 + 2852434 * 2 ^ 59
def prefixEnd_2852434 : Nat := 4983230072969 + 3 ^ 40 * 2852434 * 2
def baseEnd_2852434 : Nat := 1464669677226998072556901

theorem tailTrace_2852434 : CollatzResearch.WordTrace tailWord_2852434 prefixEnd_2852434 1464669677226998072556901 := by
  unfold tailWord_2852434
  simp only [CollatzResearch.WordTrace]
  refine ⟨26009203737031562446941089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69357876632084166525176237 26009203737031562446941089)
  ·
    refine ⟨19506902802773671835205817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26009203737031562446941089 19506902802773671835205817)
    ·
      refine ⟨14630177102080253876404363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19506902802773671835205817 14630177102080253876404363)
      ·
        refine ⟨21945265653120380814606545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14630177102080253876404363 21945265653120380814606545)
        ·
          refine ⟨16458949239840285610954909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21945265653120380814606545 16458949239840285610954909)
          ·
            refine ⟨6172105964940107104108091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16458949239840285610954909 6172105964940107104108091)
            ·
              refine ⟨9258158947410160656162137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6172105964940107104108091 9258158947410160656162137)
              ·
                refine ⟨6943619210557620492121603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9258158947410160656162137 6943619210557620492121603)
                ·
                  refine ⟨10415428815836430738182405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6943619210557620492121603 10415428815836430738182405)
                  ·
                    refine ⟨1952892902969330763409201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10415428815836430738182405 1952892902969330763409201)
                    ·
                      refine ⟨1464669677226998072556901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1952892902969330763409201 1464669677226998072556901)
                      ·
                        rfl

theorem cell23_2852434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 3, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 3, 1, 2, 1, 4, 2].length) (baseStart_2852434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2852434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2852434 prefixEnd_2852434 := by exact prefixLift 2852434
  have htrace : WordTrace (prefixWord ++ tailWord_2852434) baseStart_2852434 baseEnd_2852434 := by
    simpa [prefixWord, tailWord_2852434, baseEnd_2852434] using wordTrace_append hprefix tailTrace_2852434
  have hstable : (prefixWord ++ tailWord_2852434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2852434).length < 2 ^ (prefixWord ++ tailWord_2852434).sum := by decide
  have hdescent : baseEnd_2852434 < baseStart_2852434 := by decide
  rcases family_descends (prefixWord ++ tailWord_2852434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2852451 : List Nat := [1, 1, 1, 5, 1, 4, 2, 2, 2, 2, 2]
def baseStart_2852451 : Nat := 118140960795 + 2852451 * 2 ^ 59
def prefixEnd_2852451 : Nat := 4983230072969 + 3 ^ 40 * 2852451 * 2
def baseEnd_2852451 : Nat := 1464678406398124506044323

theorem tailTrace_2852451 : CollatzResearch.WordTrace tailWord_2852451 prefixEnd_2852451 1464678406398124506044323 := by
  unfold tailWord_2852451
  simp only [CollatzResearch.WordTrace]
  refine ⟨104037434989064661691133207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69358289992709774460755471 104037434989064661691133207)
  ·
    refine ⟨156056152483596992536699811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104037434989064661691133207 156056152483596992536699811)
    ·
      refine ⟨234084228725395488805049717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 156056152483596992536699811 234084228725395488805049717)
      ·
        refine ⟨21945396443005827075473411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 234084228725395488805049717 21945396443005827075473411)
        ·
          refine ⟨32918094664508740613210117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21945396443005827075473411 32918094664508740613210117)
          ·
            refine ⟨6172142749595388864976897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 32918094664508740613210117 6172142749595388864976897)
            ·
              refine ⟨4629107062196541648732673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6172142749595388864976897 4629107062196541648732673)
              ·
                refine ⟨3471830296647406236549505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4629107062196541648732673 3471830296647406236549505)
                ·
                  refine ⟨2603872722485554677412129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3471830296647406236549505 2603872722485554677412129)
                  ·
                    refine ⟨1952904541864166008059097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2603872722485554677412129 1952904541864166008059097)
                    ·
                      refine ⟨1464678406398124506044323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1952904541864166008059097 1464678406398124506044323)
                      ·
                        rfl

theorem cell23_2852451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 4, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 4, 2, 2, 2, 2, 2].length) (baseStart_2852451 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2852451 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2852451 prefixEnd_2852451 := by exact prefixLift 2852451
  have htrace : WordTrace (prefixWord ++ tailWord_2852451) baseStart_2852451 baseEnd_2852451 := by
    simpa [prefixWord, tailWord_2852451, baseEnd_2852451] using wordTrace_append hprefix tailTrace_2852451
  have hstable : (prefixWord ++ tailWord_2852451).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2852451).length < 2 ^ (prefixWord ++ tailWord_2852451).sum := by decide
  have hdescent : baseEnd_2852451 < baseStart_2852451 := by decide
  rcases family_descends (prefixWord ++ tailWord_2852451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2852487 : List Nat := [1, 1, 4, 2, 1, 3, 3, 1, 2, 5]
def baseStart_2852487 : Nat := 118140960795 + 2852487 * 2 ^ 59
def prefixEnd_2852487 : Nat := 4983230072969 + 3 ^ 40 * 2852487 * 2
def baseEnd_2852487 : Nat := 488232297233895455064719

theorem tailTrace_2852487 : CollatzResearch.WordTrace tailWord_2852487 prefixEnd_2852487 488232297233895455064719 := by
  unfold tailWord_2852487
  simp only [CollatzResearch.WordTrace]
  refine ⟨104038748016934239839443715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69359165344622826559629143 104038748016934239839443715)
  ·
    refine ⟨156058122025401359759165573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104038748016934239839443715 156058122025401359759165573)
    ·
      refine ⟨29260897879762754954843545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 156058122025401359759165573 29260897879762754954843545)
      ·
        refine ⟨21945673409822066216132659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29260897879762754954843545 21945673409822066216132659)
        ·
          refine ⟨32918510114733099324198989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21945673409822066216132659 32918510114733099324198989)
          ·
            refine ⟨12344441293024912246574621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32918510114733099324198989 12344441293024912246574621)
            ·
              refine ⟨4629165484884342092465483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12344441293024912246574621 4629165484884342092465483)
              ·
                refine ⟨6943748227326513138698225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4629165484884342092465483 6943748227326513138698225)
                ·
                  refine ⟨5207811170494884854023669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6943748227326513138698225 5207811170494884854023669)
                  ·
                    refine ⟨488232297233895455064719, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5207811170494884854023669 488232297233895455064719)
                    ·
                      rfl

theorem cell23_2852487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 3, 1, 2, 5].length) (baseStart_2852487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2852487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2852487 prefixEnd_2852487 := by exact prefixLift 2852487
  have htrace : WordTrace (prefixWord ++ tailWord_2852487) baseStart_2852487 baseEnd_2852487 := by
    simpa [prefixWord, tailWord_2852487, baseEnd_2852487] using wordTrace_append hprefix tailTrace_2852487
  have hstable : (prefixWord ++ tailWord_2852487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2852487).length < 2 ^ (prefixWord ++ tailWord_2852487).sum := by decide
  have hdescent : baseEnd_2852487 < baseStart_2852487 := by decide
  rcases family_descends (prefixWord ++ tailWord_2852487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2852517 : List Nat := [1, 3, 1, 2, 1, 2, 3, 3, 3, 4]
def baseStart_2852517 : Nat := 118140960795 + 2852517 * 2 ^ 59
def prefixEnd_2852517 : Nat := 4983230072969 + 3 ^ 40 * 2852517 * 2
def baseEnd_2852517 : Nat := 488237432040440415939673

theorem tailTrace_2852517 : CollatzResearch.WordTrace tailWord_2852517 prefixEnd_2852517 488237432040440415939673 := by
  unfold tailWord_2852517
  simp only [CollatzResearch.WordTrace]
  refine ⟨104039842206825554963035805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69359894804550369975357203 104039842206825554963035805)
  ·
    refine ⟨39014940827559583111138427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 104039842206825554963035805 39014940827559583111138427)
    ·
      refine ⟨58522411241339374666707641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39014940827559583111138427 58522411241339374666707641)
      ·
        refine ⟨43891808431004531000030731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58522411241339374666707641 43891808431004531000030731)
        ·
          refine ⟨65837712646506796500046097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43891808431004531000030731 65837712646506796500046097)
          ·
            refine ⟨49378284484880097375034573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65837712646506796500046097 49378284484880097375034573)
            ·
              refine ⟨18516856681830036515637965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 49378284484880097375034573 18516856681830036515637965)
              ·
                refine ⟨6943821255686263693364237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18516856681830036515637965 6943821255686263693364237)
                ·
                  refine ⟨2603932970882348885011589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6943821255686263693364237 2603932970882348885011589)
                  ·
                    refine ⟨488237432040440415939673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2603932970882348885011589 488237432040440415939673)
                    ·
                      rfl

theorem cell23_2852517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 3, 3, 3, 4].length) (baseStart_2852517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2852517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2852517 prefixEnd_2852517 := by exact prefixLift 2852517
  have htrace : WordTrace (prefixWord ++ tailWord_2852517) baseStart_2852517 baseEnd_2852517 := by
    simpa [prefixWord, tailWord_2852517, baseEnd_2852517] using wordTrace_append hprefix tailTrace_2852517
  have hstable : (prefixWord ++ tailWord_2852517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2852517).length < 2 ^ (prefixWord ++ tailWord_2852517).sum := by decide
  have hdescent : baseEnd_2852517 < baseStart_2852517 := by decide
  rcases family_descends (prefixWord ++ tailWord_2852517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2852607 : List Nat := [1, 1, 2, 2, 1, 3, 2, 1, 6, 4]
def baseStart_2852607 : Nat := 118140960795 + 2852607 * 2 ^ 59
def prefixEnd_2852607 : Nat := 4983230072969 + 3 ^ 40 * 2852607 * 2
def baseEnd_2852607 : Nat := 488252836460075298564535

theorem tailTrace_2852607 : CollatzResearch.WordTrace tailWord_2852607 prefixEnd_2852607 488252836460075298564535 := by
  unfold tailWord_2852607
  simp only [CollatzResearch.WordTrace]
  refine ⟨104043124776499500333812075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69362083184333000222541383 104043124776499500333812075)
  ·
    refine ⟨156064687164749250500718113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104043124776499500333812075 156064687164749250500718113)
    ·
      refine ⟨117048515373561937875538585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 156064687164749250500718113 117048515373561937875538585)
      ·
        refine ⟨87786386530171453406653939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 117048515373561937875538585 87786386530171453406653939)
        ·
          refine ⟨131679579795257180109980909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87786386530171453406653939 131679579795257180109980909)
          ·
            refine ⟨49379842423221442541242841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 131679579795257180109980909 49379842423221442541242841)
            ·
              refine ⟨37034881817416081905932131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49379842423221442541242841 37034881817416081905932131)
              ·
                refine ⟨55552322726124122858898197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37034881817416081905932131 55552322726124122858898197)
                ·
                  refine ⟨2604015127787068259010853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 55552322726124122858898197 2604015127787068259010853)
                  ·
                    refine ⟨488252836460075298564535, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2604015127787068259010853 488252836460075298564535)
                    ·
                      rfl

theorem cell23_2852607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 2, 1, 6, 4].length) (baseStart_2852607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2852607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2852607 prefixEnd_2852607 := by exact prefixLift 2852607
  have htrace : WordTrace (prefixWord ++ tailWord_2852607) baseStart_2852607 baseEnd_2852607 := by
    simpa [prefixWord, tailWord_2852607, baseEnd_2852607] using wordTrace_append hprefix tailTrace_2852607
  have hstable : (prefixWord ++ tailWord_2852607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2852607).length < 2 ^ (prefixWord ++ tailWord_2852607).sum := by decide
  have hdescent : baseEnd_2852607 < baseStart_2852607 := by decide
  rcases family_descends (prefixWord ++ tailWord_2852607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2852634 : List Nat := [3, 1, 1, 3, 2, 2, 1, 2, 3, 2, 3]
def baseStart_2852634 : Nat := 118140960795 + 2852634 * 2 ^ 59
def prefixEnd_2852634 : Nat := 4983230072969 + 3 ^ 40 * 2852634 * 2
def baseEnd_2852634 : Nat := 1464772373357897290055981

theorem tailTrace_2852634 : CollatzResearch.WordTrace tailWord_2852634 prefixEnd_2852634 1464772373357897290055981 := by
  unfold tailWord_2852634
  simp only [CollatzResearch.WordTrace]
  refine ⟨26011027386850420986261239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69362739698267789296696637 26011027386850420986261239)
  ·
    refine ⟨39016541080275631479391859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26011027386850420986261239 39016541080275631479391859)
    ·
      refine ⟨58524811620413447219087789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39016541080275631479391859 58524811620413447219087789)
      ·
        refine ⟨21946804357655042707157921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 58524811620413447219087789 21946804357655042707157921)
        ·
          refine ⟨16460103268241282030368441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21946804357655042707157921 16460103268241282030368441)
          ·
            refine ⟨12345077451180961522776331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16460103268241282030368441 12345077451180961522776331)
            ·
              refine ⟨18517616176771442284164497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12345077451180961522776331 18517616176771442284164497)
              ·
                refine ⟨13888212132578581713123373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18517616176771442284164497 13888212132578581713123373)
                ·
                  refine ⟨5208079549716968142421265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13888212132578581713123373 5208079549716968142421265)
                  ·
                    refine ⟨3906059662287726106815949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5208079549716968142421265 3906059662287726106815949)
                    ·
                      refine ⟨1464772373357897290055981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3906059662287726106815949 1464772373357897290055981)
                      ·
                        rfl

theorem cell23_2852634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 1, 2, 3, 2, 3].length) (baseStart_2852634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2852634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2852634 prefixEnd_2852634 := by exact prefixLift 2852634
  have htrace : WordTrace (prefixWord ++ tailWord_2852634) baseStart_2852634 baseEnd_2852634 := by
    simpa [prefixWord, tailWord_2852634, baseEnd_2852634] using wordTrace_append hprefix tailTrace_2852634
  have hstable : (prefixWord ++ tailWord_2852634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2852634).length < 2 ^ (prefixWord ++ tailWord_2852634).sum := by decide
  have hdescent : baseEnd_2852634 < baseStart_2852634 := by decide
  rcases family_descends (prefixWord ++ tailWord_2852634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2852644 : List Nat := [2, 3, 1, 3, 2, 1, 1, 3, 1, 2, 4]
def baseStart_2852644 : Nat := 118140960795 + 2852644 * 2 ^ 59
def prefixEnd_2852644 : Nat := 4983230072969 + 3 ^ 40 * 2852644 * 2
def baseEnd_2852644 : Nat := 1464777508164442250930935

theorem tailTrace_2852644 : CollatzResearch.WordTrace tailWord_2852644 prefixEnd_2852644 1464777508164442250930935 := by
  unfold tailWord_2852644
  simp only [CollatzResearch.WordTrace]
  refine ⟨52022237138682727826454493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69362982851576970435272657 52022237138682727826454493)
  ·
    refine ⟨19508338927006022934920435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52022237138682727826454493 19508338927006022934920435)
    ·
      refine ⟨29262508390509034402380653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19508338927006022934920435 29262508390509034402380653)
      ·
        refine ⟨10973440646440887900892745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29262508390509034402380653 10973440646440887900892745)
        ·
          refine ⟨8230080484830665925669559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10973440646440887900892745 8230080484830665925669559)
          ·
            refine ⟨12345120727245998888504339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8230080484830665925669559 12345120727245998888504339)
            ·
              refine ⟨18517681090868998332756509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12345120727245998888504339 18517681090868998332756509)
              ·
                refine ⟨6944130409075874374783691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18517681090868998332756509 6944130409075874374783691)
                ·
                  refine ⟨10416195613613811562175537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6944130409075874374783691 10416195613613811562175537)
                  ·
                    refine ⟨7812146710210358671631653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10416195613613811562175537 7812146710210358671631653)
                    ·
                      refine ⟨1464777508164442250930935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7812146710210358671631653 1464777508164442250930935)
                      ·
                        rfl

theorem cell23_2852644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 1, 3, 1, 2, 4].length) (baseStart_2852644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2852644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2852644 prefixEnd_2852644 := by exact prefixLift 2852644
  have htrace : WordTrace (prefixWord ++ tailWord_2852644) baseStart_2852644 baseEnd_2852644 := by
    simpa [prefixWord, tailWord_2852644, baseEnd_2852644] using wordTrace_append hprefix tailTrace_2852644
  have hstable : (prefixWord ++ tailWord_2852644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2852644).length < 2 ^ (prefixWord ++ tailWord_2852644).sum := by decide
  have hdescent : baseEnd_2852644 < baseStart_2852644 := by decide
  rcases family_descends (prefixWord ++ tailWord_2852644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2852648 : List Nat := [2, 1, 5, 1, 1, 3, 1, 2, 3, 2, 2]
def baseStart_2852648 : Nat := 118140960795 + 2852648 * 2 ^ 59
def prefixEnd_2852648 : Nat := 4983230072969 + 3 ^ 40 * 2852648 * 2
def baseEnd_2852648 : Nat := 1464779562087060235280917

theorem tailTrace_2852648 : CollatzResearch.WordTrace tailWord_2852648 prefixEnd_2852648 1464779562087060235280917 := by
  unfold tailWord_2852648
  simp only [CollatzResearch.WordTrace]
  refine ⟨52022310084675482168027299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69363080112900642890703065 52022310084675482168027299)
  ·
    refine ⟨78033465127013223252040949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52022310084675482168027299 78033465127013223252040949)
    ·
      refine ⟨7315637355657489679878839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 78033465127013223252040949 7315637355657489679878839)
      ·
        refine ⟨10973456033486234519818259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7315637355657489679878839 10973456033486234519818259)
        ·
          refine ⟨16460184050229351779727389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10973456033486234519818259 16460184050229351779727389)
          ·
            refine ⟨6172569018836006917397771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16460184050229351779727389 6172569018836006917397771)
            ·
              refine ⟨9258853528254010376096657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6172569018836006917397771 9258853528254010376096657)
              ·
                refine ⟨6944140146190507782072493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9258853528254010376096657 6944140146190507782072493)
                ·
                  refine ⟨2604052554821440418277185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6944140146190507782072493 2604052554821440418277185)
                  ·
                    refine ⟨1953039416116080313707889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2604052554821440418277185 1953039416116080313707889)
                    ·
                      refine ⟨1464779562087060235280917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1953039416116080313707889 1464779562087060235280917)
                      ·
                        rfl

theorem cell23_2852648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 3, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 3, 1, 2, 3, 2, 2].length) (baseStart_2852648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2852648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2852648 prefixEnd_2852648 := by exact prefixLift 2852648
  have htrace : WordTrace (prefixWord ++ tailWord_2852648) baseStart_2852648 baseEnd_2852648 := by
    simpa [prefixWord, tailWord_2852648, baseEnd_2852648] using wordTrace_append hprefix tailTrace_2852648
  have hstable : (prefixWord ++ tailWord_2852648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2852648).length < 2 ^ (prefixWord ++ tailWord_2852648).sum := by decide
  have hdescent : baseEnd_2852648 < baseStart_2852648 := by decide
  rcases family_descends (prefixWord ++ tailWord_2852648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2852664 : List Nat := [2, 1, 2, 1, 3, 3, 2, 2, 1, 3, 3]
def baseStart_2852664 : Nat := 118140960795 + 2852664 * 2 ^ 59
def prefixEnd_2852664 : Nat := 4983230072969 + 3 ^ 40 * 2852664 * 2
def baseEnd_2852664 : Nat := 1464787777777532172680843

theorem tailTrace_2852664 : CollatzResearch.WordTrace tailWord_2852664 prefixEnd_2852664 1464787777777532172680843 := by
  unfold tailWord_2852664
  simp only [CollatzResearch.WordTrace]
  refine ⟨52022601868646499534318523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69363469158195332712424697 52022601868646499534318523)
  ·
    refine ⟨78033902802969749301477785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52022601868646499534318523 78033902802969749301477785)
    ·
      refine ⟨58525427102227311976108339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78033902802969749301477785 58525427102227311976108339)
      ·
        refine ⟨87788140653340967964162509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58525427102227311976108339 87788140653340967964162509)
        ·
          refine ⟨32920552745002862986560941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 87788140653340967964162509 32920552745002862986560941)
          ·
            refine ⟨12345207279376073619960353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32920552745002862986560941 12345207279376073619960353)
            ·
              refine ⟨9258905459532055214970265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12345207279376073619960353 9258905459532055214970265)
              ·
                refine ⟨6944179094649041411227699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9258905459532055214970265 6944179094649041411227699)
                ·
                  refine ⟨10416268641973562116841549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6944179094649041411227699 10416268641973562116841549)
                  ·
                    refine ⟨3906100740740085793815581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10416268641973562116841549 3906100740740085793815581)
                    ·
                      refine ⟨1464787777777532172680843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3906100740740085793815581 1464787777777532172680843)
                      ·
                        rfl

theorem cell23_2852664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 2, 2, 1, 3, 3].length) (baseStart_2852664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2852664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2852664 prefixEnd_2852664 := by exact prefixLift 2852664
  have htrace : WordTrace (prefixWord ++ tailWord_2852664) baseStart_2852664 baseEnd_2852664 := by
    simpa [prefixWord, tailWord_2852664, baseEnd_2852664] using wordTrace_append hprefix tailTrace_2852664
  have hstable : (prefixWord ++ tailWord_2852664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2852664).length < 2 ^ (prefixWord ++ tailWord_2852664).sum := by decide
  have hdescent : baseEnd_2852664 < baseStart_2852664 := by decide
  rcases family_descends (prefixWord ++ tailWord_2852664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2852665 : List Nat := [1, 2, 1, 7, 1, 2, 2, 1, 1, 1, 4]
def baseStart_2852665 : Nat := 118140960795 + 2852665 * 2 ^ 59
def prefixEnd_2852665 : Nat := 4983230072969 + 3 ^ 40 * 2852665 * 2
def baseEnd_2852665 : Nat := 1464788291258186668768339

theorem tailTrace_2852665 : CollatzResearch.WordTrace tailWord_2852665 prefixEnd_2852665 1464788291258186668768339 := by
  unfold tailWord_2852665
  simp only [CollatzResearch.WordTrace]
  refine ⟨104045240210289376239423449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69363493473526250826282299 104045240210289376239423449)
  ·
    refine ⟨78033930157717032179567587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104045240210289376239423449 78033930157717032179567587)
    ·
      refine ⟨117050895236575548269351381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78033930157717032179567587 117050895236575548269351381)
      ·
        refine ⟨2743380357107239412562923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 117050895236575548269351381 2743380357107239412562923)
        ·
          refine ⟨4115070535660859118844385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2743380357107239412562923 4115070535660859118844385)
          ·
            refine ⟨3086302901745644339133289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4115070535660859118844385 3086302901745644339133289)
            ·
              refine ⟨2314727176309233254349967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3086302901745644339133289 2314727176309233254349967)
              ·
                refine ⟨3472090764463849881524951, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2314727176309233254349967 3472090764463849881524951)
                ·
                  refine ⟨5208136146695774822287427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3472090764463849881524951 5208136146695774822287427)
                  ·
                    refine ⟨7812204220043662233431141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5208136146695774822287427 7812204220043662233431141)
                    ·
                      refine ⟨1464788291258186668768339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7812204220043662233431141 1464788291258186668768339)
                      ·
                        rfl

theorem cell23_2852665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 2, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 2, 2, 1, 1, 1, 4].length) (baseStart_2852665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2852665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2852665 prefixEnd_2852665 := by exact prefixLift 2852665
  have htrace : WordTrace (prefixWord ++ tailWord_2852665) baseStart_2852665 baseEnd_2852665 := by
    simpa [prefixWord, tailWord_2852665, baseEnd_2852665] using wordTrace_append hprefix tailTrace_2852665
  have hstable : (prefixWord ++ tailWord_2852665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2852665).length < 2 ^ (prefixWord ++ tailWord_2852665).sum := by decide
  have hdescent : baseEnd_2852665 < baseStart_2852665 := by decide
  rcases family_descends (prefixWord ++ tailWord_2852665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2852697 : List Nat := [1, 2, 1, 2, 2, 3, 1, 3, 2, 6]
def baseStart_2852697 : Nat := 118140960795 + 2852697 * 2 ^ 59
def prefixEnd_2852697 : Nat := 4983230072969 + 3 ^ 40 * 2852697 * 2
def baseEnd_2852697 : Nat := 488268240879710181189397

theorem tailTrace_2852697 : CollatzResearch.WordTrace tailWord_2852697 prefixEnd_2852697 488268240879710181189397 := by
  unfold tailWord_2852697
  simp only [CollatzResearch.WordTrace]
  refine ⟨104046407346173445704588345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69364271564115630469725563 104046407346173445704588345)
  ·
    refine ⟨78034805509630084278441259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104046407346173445704588345 78034805509630084278441259)
    ·
      refine ⟨117052208264445126417661889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78034805509630084278441259 117052208264445126417661889)
      ·
        refine ⟨87789156198333844813246417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 117052208264445126417661889 87789156198333844813246417)
        ·
          refine ⟨65841867148750383609934813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 87789156198333844813246417 65841867148750383609934813)
          ·
            refine ⟨24690700180781393853725555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 65841867148750383609934813 24690700180781393853725555)
            ·
              refine ⟨37036050271172090780588333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24690700180781393853725555 37036050271172090780588333)
              ·
                refine ⟨13888518851689534042720625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37036050271172090780588333 13888518851689534042720625)
                ·
                  refine ⟨10416389138767150532040469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13888518851689534042720625 10416389138767150532040469)
                  ·
                    refine ⟨488268240879710181189397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10416389138767150532040469 488268240879710181189397)
                    ·
                      rfl

theorem cell23_2852697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 1, 3, 2, 6].length) (baseStart_2852697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2852697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2852697 prefixEnd_2852697 := by exact prefixLift 2852697
  have htrace : WordTrace (prefixWord ++ tailWord_2852697) baseStart_2852697 baseEnd_2852697 := by
    simpa [prefixWord, tailWord_2852697, baseEnd_2852697] using wordTrace_append hprefix tailTrace_2852697
  have hstable : (prefixWord ++ tailWord_2852697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2852697).length < 2 ^ (prefixWord ++ tailWord_2852697).sum := by decide
  have hdescent : baseEnd_2852697 < baseStart_2852697 := by decide
  rcases family_descends (prefixWord ++ tailWord_2852697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2852698 : List Nat := [3, 1, 1, 2, 1, 3, 5, 1, 2, 1, 3]
def baseStart_2852698 : Nat := 118140960795 + 2852698 * 2 ^ 59
def prefixEnd_2852698 : Nat := 4983230072969 + 3 ^ 40 * 2852698 * 2
def baseEnd_2852698 : Nat := 1464805236119785039655687

theorem tailTrace_2852698 : CollatzResearch.WordTrace tailWord_2852698 prefixEnd_2852698 1464805236119785039655687 := by
  unfold tailWord_2852698
  simp only [CollatzResearch.WordTrace]
  refine ⟨26011610954792455718843687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69364295879446548583583165 26011610954792455718843687)
  ·
    refine ⟨39017416432188683578265531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26011610954792455718843687 39017416432188683578265531)
    ·
      refine ⟨58526124648283025367398297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39017416432188683578265531 58526124648283025367398297)
      ·
        refine ⟨43894593486212269025548723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58526124648283025367398297 43894593486212269025548723)
        ·
          refine ⟨65841890229318403538323085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43894593486212269025548723 65841890229318403538323085)
          ·
            refine ⟨24690708835994401326871157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 65841890229318403538323085 24690708835994401326871157)
            ·
              refine ⟨2314753953374475124394171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 24690708835994401326871157 2314753953374475124394171)
              ·
                refine ⟨3472130930061712686591257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2314753953374475124394171 3472130930061712686591257)
                ·
                  refine ⟨2604098197546284514943443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3472130930061712686591257 2604098197546284514943443)
                  ·
                    refine ⟨3906147296319426772415165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2604098197546284514943443 3906147296319426772415165)
                    ·
                      refine ⟨1464805236119785039655687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3906147296319426772415165 1464805236119785039655687)
                      ·
                        rfl

theorem cell23_2852698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 5, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 5, 1, 2, 1, 3].length) (baseStart_2852698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2852698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2852698 prefixEnd_2852698 := by exact prefixLift 2852698
  have htrace : WordTrace (prefixWord ++ tailWord_2852698) baseStart_2852698 baseEnd_2852698 := by
    simpa [prefixWord, tailWord_2852698, baseEnd_2852698] using wordTrace_append hprefix tailTrace_2852698
  have hstable : (prefixWord ++ tailWord_2852698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2852698).length < 2 ^ (prefixWord ++ tailWord_2852698).sum := by decide
  have hdescent : baseEnd_2852698 < baseStart_2852698 := by decide
  rcases family_descends (prefixWord ++ tailWord_2852698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2852721 : List Nat := [1, 2, 2, 2, 1, 3, 1, 1, 6, 2, 2]
def baseStart_2852721 : Nat := 118140960795 + 2852721 * 2 ^ 59
def prefixEnd_2852721 : Nat := 4983230072969 + 3 ^ 40 * 2852721 * 2
def baseEnd_2852721 : Nat := 1464817046174838449668081

theorem tailTrace_2852721 : CollatzResearch.WordTrace tailWord_2852721 prefixEnd_2852721 1464817046174838449668081 := by
  unfold tailWord_2852721
  simp only [CollatzResearch.WordTrace]
  refine ⟨104047282698086497803462017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69364855132057665202308011 104047282698086497803462017)
  ·
    refine ⟨78035462023564873352596513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104047282698086497803462017 78035462023564873352596513)
    ·
      refine ⟨58526596517673655014447385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78035462023564873352596513 58526596517673655014447385)
      ·
        refine ⟨43894947388255241260835539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58526596517673655014447385 43894947388255241260835539)
        ·
          refine ⟨65842421082382861891253309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43894947388255241260835539 65842421082382861891253309)
          ·
            refine ⟨24690907905893573209219991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 65842421082382861891253309 24690907905893573209219991)
            ·
              refine ⟨37036361858840359813829987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24690907905893573209219991 37036361858840359813829987)
              ·
                refine ⟨55554542788260539720744981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37036361858840359813829987 55554542788260539720744981)
                ·
                  refine ⟨2604119193199712799409921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 55554542788260539720744981 2604119193199712799409921)
                  ·
                    refine ⟨1953089394899784599557441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2604119193199712799409921 1953089394899784599557441)
                    ·
                      refine ⟨1464817046174838449668081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1953089394899784599557441 1464817046174838449668081)
                      ·
                        rfl

theorem cell23_2852721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 1, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 1, 1, 6, 2, 2].length) (baseStart_2852721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2852721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2852721 prefixEnd_2852721 := by exact prefixLift 2852721
  have htrace : WordTrace (prefixWord ++ tailWord_2852721) baseStart_2852721 baseEnd_2852721 := by
    simpa [prefixWord, tailWord_2852721, baseEnd_2852721] using wordTrace_append hprefix tailTrace_2852721
  have hstable : (prefixWord ++ tailWord_2852721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2852721).length < 2 ^ (prefixWord ++ tailWord_2852721).sum := by decide
  have hdescent : baseEnd_2852721 < baseStart_2852721 := by decide
  rcases family_descends (prefixWord ++ tailWord_2852721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2852794 : List Nat := [3, 1, 1, 1, 2, 1, 2, 3, 4, 1, 4]
def baseStart_2852794 : Nat := 118140960795 + 2852794 * 2 ^ 59
def prefixEnd_2852794 : Nat := 4983230072969 + 3 ^ 40 * 2852794 * 2
def baseEnd_2852794 : Nat := 1464854530262616664055245

theorem tailTrace_2852794 : CollatzResearch.WordTrace tailWord_2852794 prefixEnd_2852794 1464854530262616664055245 := by
  unfold tailWord_2852794
  simp only [CollatzResearch.WordTrace]
  refine ⟨26012486306705507817717359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69366630151214687513912957 26012486306705507817717359)
  ·
    refine ⟨39018729460058261726576039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26012486306705507817717359 39018729460058261726576039)
    ·
      refine ⟨58528094190087392589864059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39018729460058261726576039 58528094190087392589864059)
      ·
        refine ⟨87792141285131088884796089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58528094190087392589864059 87792141285131088884796089)
        ·
          refine ⟨65844105963848316663597067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 87792141285131088884796089 65844105963848316663597067)
          ·
            refine ⟨98766158945772474995395601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65844105963848316663597067 98766158945772474995395601)
            ·
              refine ⟨74074619209329356246546701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 98766158945772474995395601 74074619209329356246546701)
              ·
                refine ⟨27777982203498508592455013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 74074619209329356246546701 27777982203498508592455013)
                ·
                  refine ⟨5208371663155970361085315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27777982203498508592455013 5208371663155970361085315)
                  ·
                    refine ⟨7812557494733955541627973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5208371663155970361085315 7812557494733955541627973)
                    ·
                      refine ⟨1464854530262616664055245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7812557494733955541627973 1464854530262616664055245)
                      ·
                        rfl

theorem cell23_2852794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 3, 4, 1, 4].length) (baseStart_2852794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2852794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2852794 prefixEnd_2852794 := by exact prefixLift 2852794
  have htrace : WordTrace (prefixWord ++ tailWord_2852794) baseStart_2852794 baseEnd_2852794 := by
    simpa [prefixWord, tailWord_2852794, baseEnd_2852794] using wordTrace_append hprefix tailTrace_2852794
  have hstable : (prefixWord ++ tailWord_2852794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2852794).length < 2 ^ (prefixWord ++ tailWord_2852794).sum := by decide
  have hdescent : baseEnd_2852794 < baseStart_2852794 := by decide
  rcases family_descends (prefixWord ++ tailWord_2852794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2852811 : List Nat := [1, 1, 1, 1, 3, 4, 3, 1, 2, 4, 2]
def baseStart_2852811 : Nat := 118140960795 + 2852811 * 2 ^ 59
def prefixEnd_2852811 : Nat := 4983230072969 + 3 ^ 40 * 2852811 * 2
def baseEnd_2852811 : Nat := 1464863259433743097542667

theorem tailTrace_2852811 : CollatzResearch.WordTrace tailWord_2852811 prefixEnd_2852811 1464863259433743097542667 := by
  unfold tailWord_2852811
  simp only [CollatzResearch.WordTrace]
  refine ⟨104050565267760443174238287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69367043511840295449492191 104050565267760443174238287)
  ·
    refine ⟨156075847901640664761357431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104050565267760443174238287 156075847901640664761357431)
    ·
      refine ⟨234113771852460997142036147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 156075847901640664761357431 234113771852460997142036147)
      ·
        refine ⟨351170657778691495713054221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 234113771852460997142036147 351170657778691495713054221)
        ·
          refine ⟨131688996667009310892395333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 351170657778691495713054221 131688996667009310892395333)
          ·
            refine ⟨24691686875064245792324125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 131688996667009310892395333 24691686875064245792324125)
            ·
              refine ⟨9259382578149092172121547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24691686875064245792324125 9259382578149092172121547)
              ·
                refine ⟨13889073867223638258182321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9259382578149092172121547 13889073867223638258182321)
                ·
                  refine ⟨10416805400417728693636741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13889073867223638258182321 10416805400417728693636741)
                  ·
                    refine ⟨1953151012578324130056889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10416805400417728693636741 1953151012578324130056889)
                    ·
                      refine ⟨1464863259433743097542667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1953151012578324130056889 1464863259433743097542667)
                      ·
                        rfl

theorem cell23_2852811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 3, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 3, 1, 2, 4, 2].length) (baseStart_2852811 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2852811 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2852811 prefixEnd_2852811 := by exact prefixLift 2852811
  have htrace : WordTrace (prefixWord ++ tailWord_2852811) baseStart_2852811 baseEnd_2852811 := by
    simpa [prefixWord, tailWord_2852811, baseEnd_2852811] using wordTrace_append hprefix tailTrace_2852811
  have hstable : (prefixWord ++ tailWord_2852811).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2852811).length < 2 ^ (prefixWord ++ tailWord_2852811).sum := by decide
  have hdescent : baseEnd_2852811 < baseStart_2852811 := by decide
  rcases family_descends (prefixWord ++ tailWord_2852811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2852821 : List Nat := [1, 3, 2, 3, 2, 1, 1, 1, 5, 4]
def baseStart_2852821 : Nat := 118140960795 + 2852821 * 2 ^ 59
def prefixEnd_2852821 : Nat := 4983230072969 + 3 ^ 40 * 2852821 * 2
def baseEnd_2852821 : Nat := 488289464746762686139207

theorem tailTrace_2852821 : CollatzResearch.WordTrace tailWord_2852821 prefixEnd_2852821 488289464746762686139207 := by
  unfold tailWord_2852821
  simp only [CollatzResearch.WordTrace]
  refine ⟨104050929997724214882102317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69367286665149476588068211 104050929997724214882102317)
  ·
    refine ⟨39019098749146580580788369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 104050929997724214882102317 39019098749146580580788369)
    ·
      refine ⟨29264324061859935435591277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39019098749146580580788369 29264324061859935435591277)
      ·
        refine ⟨10974121523197475788346729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29264324061859935435591277 10974121523197475788346729)
        ·
          refine ⟨8230591142398106841260047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10974121523197475788346729 8230591142398106841260047)
          ·
            refine ⟨12345886713597160261890071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8230591142398106841260047 12345886713597160261890071)
            ·
              refine ⟨18518830070395740392835107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12345886713597160261890071 18518830070395740392835107)
              ·
                refine ⟨27778245105593610589252661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18518830070395740392835107 27778245105593610589252661)
                ·
                  refine ⟨2604210478649400992742437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 27778245105593610589252661 2604210478649400992742437)
                  ·
                    refine ⟨488289464746762686139207, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2604210478649400992742437 488289464746762686139207)
                    ·
                      rfl

theorem cell23_2852821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 1, 1, 5, 4].length) (baseStart_2852821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2852821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2852821 prefixEnd_2852821 := by exact prefixLift 2852821
  have htrace : WordTrace (prefixWord ++ tailWord_2852821) baseStart_2852821 baseEnd_2852821 := by
    simpa [prefixWord, tailWord_2852821, baseEnd_2852821] using wordTrace_append hprefix tailTrace_2852821
  have hstable : (prefixWord ++ tailWord_2852821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2852821).length < 2 ^ (prefixWord ++ tailWord_2852821).sum := by decide
  have hdescent : baseEnd_2852821 < baseStart_2852821 := by decide
  rcases family_descends (prefixWord ++ tailWord_2852821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2852831 : List Nat := [1, 1, 2, 3, 4, 2, 1, 1, 1, 4, 3]
def baseStart_2852831 : Nat := 118140960795 + 2852831 * 2 ^ 59
def prefixEnd_2852831 : Nat := 4983230072969 + 3 ^ 40 * 2852831 * 2
def baseEnd_2852831 : Nat := 1464873529046833019292575

theorem tailTrace_2852831 : CollatzResearch.WordTrace tailWord_2852831 prefixEnd_2852831 1464873529046833019292575 := by
  unfold tailWord_2852831
  simp only [CollatzResearch.WordTrace]
  refine ⟨104051294727687986589966347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69367529818458657726644231 104051294727687986589966347)
  ·
    refine ⟨156076942091531979884949521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104051294727687986589966347 156076942091531979884949521)
    ·
      refine ⟨117057706568648984913712141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 156076942091531979884949521 117057706568648984913712141)
      ·
        refine ⟨43896639963243369342642053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 117057706568648984913712141 43896639963243369342642053)
        ·
          refine ⟨8230619993108131751745385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 43896639963243369342642053 8230619993108131751745385)
          ·
            refine ⟨6172964994831098813809039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8230619993108131751745385 6172964994831098813809039)
            ·
              refine ⟨9259447492246648220713559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6172964994831098813809039 9259447492246648220713559)
              ·
                refine ⟨13889171238369972331070339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9259447492246648220713559 13889171238369972331070339)
                ·
                  refine ⟨20833756857554958496605509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13889171238369972331070339 20833756857554958496605509)
                  ·
                    refine ⟨3906329410791554718113533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20833756857554958496605509 3906329410791554718113533)
                    ·
                      refine ⟨1464873529046833019292575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3906329410791554718113533 1464873529046833019292575)
                      ·
                        rfl

theorem cell23_2852831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 2, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 2, 1, 1, 1, 4, 3].length) (baseStart_2852831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2852831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2852831 prefixEnd_2852831 := by exact prefixLift 2852831
  have htrace : WordTrace (prefixWord ++ tailWord_2852831) baseStart_2852831 baseEnd_2852831 := by
    simpa [prefixWord, tailWord_2852831, baseEnd_2852831] using wordTrace_append hprefix tailTrace_2852831
  have hstable : (prefixWord ++ tailWord_2852831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2852831).length < 2 ^ (prefixWord ++ tailWord_2852831).sum := by decide
  have hdescent : baseEnd_2852831 < baseStart_2852831 := by decide
  rcases family_descends (prefixWord ++ tailWord_2852831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2852844 : List Nat := [2, 2, 1, 1, 2, 1, 1, 2, 1, 7, 3]
def baseStart_2852844 : Nat := 118140960795 + 2852844 * 2 ^ 59
def prefixEnd_2852844 : Nat := 4983230072969 + 3 ^ 40 * 2852844 * 2
def baseEnd_2852844 : Nat := 1464880204295341468430015

theorem tailTrace_2852844 : CollatzResearch.WordTrace tailWord_2852844 prefixEnd_2852844 1464880204295341468430015 := by
  unfold tailWord_2852844
  simp only [CollatzResearch.WordTrace]
  refine ⟨52025884438320444905094793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69367845917760593206793057 52025884438320444905094793)
  ·
    refine ⟨39019413328740333678821095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52025884438320444905094793 39019413328740333678821095)
    ·
      refine ⟨58529119993110500518231643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39019413328740333678821095 58529119993110500518231643)
      ·
        refine ⟨87793679989665750777347465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58529119993110500518231643 87793679989665750777347465)
        ·
          refine ⟨65845259992249313083010599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 87793679989665750777347465 65845259992249313083010599)
          ·
            refine ⟨98767889988373969624515899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65845259992249313083010599 98767889988373969624515899)
            ·
              refine ⟨148151834982560954436773849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 98767889988373969624515899 148151834982560954436773849)
              ·
                refine ⟨111113876236920715827580387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 148151834982560954436773849 111113876236920715827580387)
                ·
                  refine ⟨166670814355381073741370581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 111113876236920715827580387 166670814355381073741370581)
                  ·
                    refine ⟨3906347211454243915813373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 166670814355381073741370581 3906347211454243915813373)
                    ·
                      refine ⟨1464880204295341468430015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3906347211454243915813373 1464880204295341468430015)
                      ·
                        rfl

theorem cell23_2852844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 7, 3].length) (baseStart_2852844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2852844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2852844 prefixEnd_2852844 := by exact prefixLift 2852844
  have htrace : WordTrace (prefixWord ++ tailWord_2852844) baseStart_2852844 baseEnd_2852844 := by
    simpa [prefixWord, tailWord_2852844, baseEnd_2852844] using wordTrace_append hprefix tailTrace_2852844
  have hstable : (prefixWord ++ tailWord_2852844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2852844).length < 2 ^ (prefixWord ++ tailWord_2852844).sum := by decide
  have hdescent : baseEnd_2852844 < baseStart_2852844 := by decide
  rcases family_descends (prefixWord ++ tailWord_2852844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2852864 : List Nat := [2, 1, 1, 2, 1, 1, 1, 6, 3, 5]
def baseStart_2852864 : Nat := 118140960795 + 2852864 * 2 ^ 59
def prefixEnd_2852864 : Nat := 4983230072969 + 3 ^ 40 * 2852864 * 2
def baseEnd_2852864 : Nat := 488296824636143796726641

theorem tailTrace_2852864 : CollatzResearch.WordTrace tailWord_2852864 prefixEnd_2852864 488296824636143796726641 := by
  unfold tailWord_2852864
  simp only [CollatzResearch.WordTrace]
  refine ⟨52026249168284216612958823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69368332224378955483945097 52026249168284216612958823)
  ·
    refine ⟨78039373752426324919438235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52026249168284216612958823 78039373752426324919438235)
    ·
      refine ⟨117059060628639487379157353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78039373752426324919438235 117059060628639487379157353)
      ·
        refine ⟨87794295471479615534368015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 117059060628639487379157353 87794295471479615534368015)
        ·
          refine ⟨131691443207219423301552023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87794295471479615534368015 131691443207219423301552023)
          ·
            refine ⟨197537164810829134952328035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 131691443207219423301552023 197537164810829134952328035)
            ·
              refine ⟨296305747216243702428492053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 197537164810829134952328035 296305747216243702428492053)
              ·
                refine ⟨13889331900761423551335565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 296305747216243702428492053 13889331900761423551335565)
                ·
                  refine ⟨5208499462785533831750837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13889331900761423551335565 5208499462785533831750837)
                  ·
                    refine ⟨488296824636143796726641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5208499462785533831750837 488296824636143796726641)
                    ·
                      rfl

theorem cell23_2852864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 6, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 6, 3, 5].length) (baseStart_2852864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2852864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2852864 prefixEnd_2852864 := by exact prefixLift 2852864
  have htrace : WordTrace (prefixWord ++ tailWord_2852864) baseStart_2852864 baseEnd_2852864 := by
    simpa [prefixWord, tailWord_2852864, baseEnd_2852864] using wordTrace_append hprefix tailTrace_2852864
  have hstable : (prefixWord ++ tailWord_2852864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2852864).length < 2 ^ (prefixWord ++ tailWord_2852864).sum := by decide
  have hdescent : baseEnd_2852864 < baseStart_2852864 := by decide
  rcases family_descends (prefixWord ++ tailWord_2852864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2852878 : List Nat := [4, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3]
def baseStart_2852878 : Nat := 118140960795 + 2852878 * 2 ^ 59
def prefixEnd_2852878 : Nat := 4983230072969 + 3 ^ 40 * 2852878 * 2
def baseEnd_2852878 : Nat := 1464897662637594335404859

theorem tailTrace_2852878 : CollatzResearch.WordTrace tailWord_2852878 prefixEnd_2852878 1464897662637594335404859 := by
  unfold tailWord_2852878
  simp only [CollatzResearch.WordTrace]
  refine ⟨13006626119814714202115911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 69368672639011809077951525 13006626119814714202115911)
  ·
    refine ⟨19509939179722071303173867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13006626119814714202115911 19509939179722071303173867)
    ·
      refine ⟨29264908769583106954760801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19509939179722071303173867 29264908769583106954760801)
      ·
        refine ⟨21948681577187330216070601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29264908769583106954760801 21948681577187330216070601)
        ·
          refine ⟨16461511182890497662052951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21948681577187330216070601 16461511182890497662052951)
          ·
            refine ⟨24692266774335746493079427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16461511182890497662052951 24692266774335746493079427)
            ·
              refine ⟨37038400161503619739619141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24692266774335746493079427 37038400161503619739619141)
              ·
                refine ⟨6944700030281928701178589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 37038400161503619739619141 6944700030281928701178589)
                ·
                  refine ⟨2604262511355723262941971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6944700030281928701178589 2604262511355723262941971)
                  ·
                    refine ⟨3906393767033584894412957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2604262511355723262941971 3906393767033584894412957)
                    ·
                      refine ⟨1464897662637594335404859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3906393767033584894412957 1464897662637594335404859)
                      ·
                        rfl

theorem cell23_2852878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3].length) (baseStart_2852878 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2852878 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2852878 prefixEnd_2852878 := by exact prefixLift 2852878
  have htrace : WordTrace (prefixWord ++ tailWord_2852878) baseStart_2852878 baseEnd_2852878 := by
    simpa [prefixWord, tailWord_2852878, baseEnd_2852878] using wordTrace_append hprefix tailTrace_2852878
  have hstable : (prefixWord ++ tailWord_2852878).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2852878).length < 2 ^ (prefixWord ++ tailWord_2852878).sum := by decide
  have hdescent : baseEnd_2852878 < baseStart_2852878 := by decide
  rcases family_descends (prefixWord ++ tailWord_2852878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2852888 : List Nat := [2, 1, 2, 3, 2, 1, 2, 3, 2, 3, 2]
def baseStart_2852888 : Nat := 118140960795 + 2852888 * 2 ^ 59
def prefixEnd_2852888 : Nat := 4983230072969 + 3 ^ 40 * 2852888 * 2
def baseEnd_2852888 : Nat := 1464902797444139296279813

theorem tailTrace_2852888 : CollatzResearch.WordTrace tailWord_2852888 prefixEnd_2852888 1464902797444139296279813 := by
  unfold tailWord_2852888
  simp only [CollatzResearch.WordTrace]
  refine ⟨52026686844240742662395659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69368915792320990216527545 52026686844240742662395659)
  ·
    refine ⟨78040030266361113993593489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52026686844240742662395659 78040030266361113993593489)
    ·
      refine ⟨58530022699770835495195117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78040030266361113993593489 58530022699770835495195117)
      ·
        refine ⟨21948758512414063310698169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 58530022699770835495195117 21948758512414063310698169)
        ·
          refine ⟨16461568884310547483023627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21948758512414063310698169 16461568884310547483023627)
          ·
            refine ⟨24692353326465821224535441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16461568884310547483023627 24692353326465821224535441)
            ·
              refine ⟨18519264994849365918401581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24692353326465821224535441 18519264994849365918401581)
              ·
                refine ⟨6944724373068512219400593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18519264994849365918401581 6944724373068512219400593)
                ·
                  refine ⟨5208543279801384164550445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6944724373068512219400593 5208543279801384164550445)
                  ·
                    refine ⟨1953203729925519061706417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5208543279801384164550445 1953203729925519061706417)
                    ·
                      refine ⟨1464902797444139296279813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1953203729925519061706417 1464902797444139296279813)
                      ·
                        rfl

theorem cell23_2852888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 2, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 2, 3, 2, 3, 2].length) (baseStart_2852888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2852888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2852888 prefixEnd_2852888 := by exact prefixLift 2852888
  have htrace : WordTrace (prefixWord ++ tailWord_2852888) baseStart_2852888 baseEnd_2852888 := by
    simpa [prefixWord, tailWord_2852888, baseEnd_2852888] using wordTrace_append hprefix tailTrace_2852888
  have hstable : (prefixWord ++ tailWord_2852888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2852888).length < 2 ^ (prefixWord ++ tailWord_2852888).sum := by decide
  have hdescent : baseEnd_2852888 < baseStart_2852888 := by decide
  rcases family_descends (prefixWord ++ tailWord_2852888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2852912 : List Nat := [2, 1, 1, 1, 2, 6, 3, 2, 1, 1, 3]
def baseStart_2852912 : Nat := 118140960795 + 2852912 * 2 ^ 59
def prefixEnd_2852912 : Nat := 4983230072969 + 3 ^ 40 * 2852912 * 2
def baseEnd_2852912 : Nat := 1464915120979847202379703

theorem tailTrace_2852912 : CollatzResearch.WordTrace tailWord_2852912 prefixEnd_2852912 1464915120979847202379703 := by
  unfold tailWord_2852912
  simp only [CollatzResearch.WordTrace]
  refine ⟨52027124520197268711832495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69369499360263024949109993 52027124520197268711832495)
  ·
    refine ⟨78040686780295903067748743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52027124520197268711832495 78040686780295903067748743)
    ·
      refine ⟨117061030170443854601623115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78040686780295903067748743 117061030170443854601623115)
      ·
        refine ⟨175591545255665781902434673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117061030170443854601623115 175591545255665781902434673)
        ·
          refine ⟨131693658941749336426826005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 175591545255665781902434673 131693658941749336426826005)
          ·
            refine ⟨6173140262894500145007469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 131693658941749336426826005 6173140262894500145007469)
            ·
              refine ⟨2314927598585437554377801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6173140262894500145007469 2314927598585437554377801)
              ·
                refine ⟨1736195698939078165783351, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2314927598585437554377801 1736195698939078165783351)
                ·
                  refine ⟨2604293548408617248675027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1736195698939078165783351 2604293548408617248675027)
                  ·
                    refine ⟨3906440322612925873012541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2604293548408617248675027 3906440322612925873012541)
                    ·
                      refine ⟨1464915120979847202379703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3906440322612925873012541 1464915120979847202379703)
                      ·
                        rfl

theorem cell23_2852912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 6, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 6, 3, 2, 1, 1, 3].length) (baseStart_2852912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2852912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2852912 prefixEnd_2852912 := by exact prefixLift 2852912
  have htrace : WordTrace (prefixWord ++ tailWord_2852912) baseStart_2852912 baseEnd_2852912 := by
    simpa [prefixWord, tailWord_2852912, baseEnd_2852912] using wordTrace_append hprefix tailTrace_2852912
  have hstable : (prefixWord ++ tailWord_2852912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2852912).length < 2 ^ (prefixWord ++ tailWord_2852912).sum := by decide
  have hdescent : baseEnd_2852912 < baseStart_2852912 := by decide
  rcases family_descends (prefixWord ++ tailWord_2852912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2852918 : List Nat := [5, 1, 2, 1, 1, 1, 2, 2, 3, 1, 4]
def baseStart_2852918 : Nat := 118140960795 + 2852918 * 2 ^ 59
def prefixEnd_2852918 : Nat := 4983230072969 + 3 ^ 40 * 2852918 * 2
def baseEnd_2852918 : Nat := 1464918201863774178904675

theorem tailTrace_2852918 : CollatzResearch.WordTrace tailWord_2852918 prefixEnd_2852918 1464918201863774178904675 := by
  unfold tailWord_2852918
  simp only [CollatzResearch.WordTrace]
  refine ⟨6503404242398300028023963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 69369645252248533632255605 6503404242398300028023963)
  ·
    refine ⟨9755106363597450042035945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6503404242398300028023963 9755106363597450042035945)
    ·
      refine ⟨7316329772698087531526959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9755106363597450042035945 7316329772698087531526959)
      ·
        refine ⟨10974494659047131297290439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7316329772698087531526959 10974494659047131297290439)
        ·
          refine ⟨16461741988570696945935659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10974494659047131297290439 16461741988570696945935659)
          ·
            refine ⟨24692612982856045418903489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16461741988570696945935659 24692612982856045418903489)
            ·
              refine ⟨18519459737142034064177617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24692612982856045418903489 18519459737142034064177617)
              ·
                refine ⟨13889594802856525548133213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18519459737142034064177617 13889594802856525548133213)
                ·
                  refine ⟨5208598051071197080549955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13889594802856525548133213 5208598051071197080549955)
                  ·
                    refine ⟨7812897076606795620824933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5208598051071197080549955 7812897076606795620824933)
                    ·
                      refine ⟨1464918201863774178904675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7812897076606795620824933 1464918201863774178904675)
                      ·
                        rfl

theorem cell23_2852918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 2, 2, 3, 1, 4].length) (baseStart_2852918 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2852918 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2852918 prefixEnd_2852918 := by exact prefixLift 2852918
  have htrace : WordTrace (prefixWord ++ tailWord_2852918) baseStart_2852918 baseEnd_2852918 := by
    simpa [prefixWord, tailWord_2852918, baseEnd_2852918] using wordTrace_append hprefix tailTrace_2852918
  have hstable : (prefixWord ++ tailWord_2852918).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2852918).length < 2 ^ (prefixWord ++ tailWord_2852918).sum := by decide
  have hdescent : baseEnd_2852918 < baseStart_2852918 := by decide
  rcases family_descends (prefixWord ++ tailWord_2852918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2852928 : List Nat := [2, 1, 1, 2, 2, 5, 1, 3, 2, 4]
def baseStart_2852928 : Nat := 118140960795 + 2852928 * 2 ^ 59
def prefixEnd_2852928 : Nat := 4983230072969 + 3 ^ 40 * 2852928 * 2
def baseEnd_2852928 : Nat := 488307778890106379926543

theorem tailTrace_2852928 : CollatzResearch.WordTrace tailWord_2852928 prefixEnd_2852928 488307778890106379926543 := by
  unfold tailWord_2852928
  simp only [CollatzResearch.WordTrace]
  refine ⟨52027416304168286078123719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69369888405557714770831625 52027416304168286078123719)
  ·
    refine ⟨78041124456252429117185579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52027416304168286078123719 78041124456252429117185579)
    ·
      refine ⟨117061686684378643675778369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78041124456252429117185579 117061686684378643675778369)
      ·
        refine ⟨87796265013283982756833777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 117061686684378643675778369 87796265013283982756833777)
        ·
          refine ⟨65847198759962987067625333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 87796265013283982756833777 65847198759962987067625333)
          ·
            refine ⟨6173174883746530037589875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 65847198759962987067625333 6173174883746530037589875)
            ·
              refine ⟨9259762325619795056384813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6173174883746530037589875 9259762325619795056384813)
              ·
                refine ⟨3472410872107423146144305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9259762325619795056384813 3472410872107423146144305)
                ·
                  refine ⟨2604308154080567359608229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3472410872107423146144305 2604308154080567359608229)
                  ·
                    refine ⟨488307778890106379926543, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2604308154080567359608229 488307778890106379926543)
                    ·
                      rfl

theorem cell23_2852928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 5, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 5, 1, 3, 2, 4].length) (baseStart_2852928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2852928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2852928 prefixEnd_2852928 := by exact prefixLift 2852928
  have htrace : WordTrace (prefixWord ++ tailWord_2852928) baseStart_2852928 baseEnd_2852928 := by
    simpa [prefixWord, tailWord_2852928, baseEnd_2852928] using wordTrace_append hprefix tailTrace_2852928
  have hstable : (prefixWord ++ tailWord_2852928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2852928).length < 2 ^ (prefixWord ++ tailWord_2852928).sum := by decide
  have hdescent : baseEnd_2852928 < baseStart_2852928 := by decide
  rcases family_descends (prefixWord ++ tailWord_2852928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2852941 : List Nat := [1, 6, 1, 1, 1, 1, 1, 11]
def baseStart_2852941 : Nat := 118140960795 + 2852941 * 2 ^ 59
def prefixEnd_2852941 : Nat := 4983230072969 + 3 ^ 40 * 2852941 * 2
def baseEnd_2852941 : Nat := 54256667108104725515447

theorem tailTrace_2852941 : CollatzResearch.WordTrace tailWord_2852941 prefixEnd_2852941 54256667108104725515447 := by
  unfold tailWord_2852941
  simp only [CollatzResearch.WordTrace]
  refine ⟨104055306757289475376470677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69370204504859650250980451 104055306757289475376470677)
  ·
    refine ⟨4877592504247944158272063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 104055306757289475376470677 4877592504247944158272063)
    ·
      refine ⟨7316388756371916237408095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4877592504247944158272063 7316388756371916237408095)
      ·
        refine ⟨10974583134557874356112143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7316388756371916237408095 10974583134557874356112143)
        ·
          refine ⟨16461874701836811534168215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10974583134557874356112143 16461874701836811534168215)
          ·
            refine ⟨24692812052755217301252323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16461874701836811534168215 24692812052755217301252323)
            ·
              refine ⟨37039218079132825951878485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24692812052755217301252323 37039218079132825951878485)
              ·
                refine ⟨54256667108104725515447, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 37039218079132825951878485 54256667108104725515447)
                ·
                  rfl

theorem cell23_2852941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 1, 11].length) (baseStart_2852941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2852941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2852941 prefixEnd_2852941 := by exact prefixLift 2852941
  have htrace : WordTrace (prefixWord ++ tailWord_2852941) baseStart_2852941 baseEnd_2852941 := by
    simpa [prefixWord, tailWord_2852941, baseEnd_2852941] using wordTrace_append hprefix tailTrace_2852941
  have hstable : (prefixWord ++ tailWord_2852941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2852941).length < 2 ^ (prefixWord ++ tailWord_2852941).sum := by decide
  have hdescent : baseEnd_2852941 < baseStart_2852941 := by decide
  rcases family_descends (prefixWord ++ tailWord_2852941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2852951 : List Nat := [1, 1, 3, 2, 2, 1, 3, 1, 3, 3, 3]
def baseStart_2852951 : Nat := 118140960795 + 2852951 * 2 ^ 59
def prefixEnd_2852951 : Nat := 4983230072969 + 3 ^ 40 * 2852951 * 2
def baseEnd_2852951 : Nat := 1464935146725372549792023

theorem tailTrace_2852951 : CollatzResearch.WordTrace tailWord_2852951 prefixEnd_2852951 1464935146725372549792023 := by
  unfold tailWord_2852951
  simp only [CollatzResearch.WordTrace]
  refine ⟨104055671487253247084334707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69370447658168831389556471 104055671487253247084334707)
  ·
    refine ⟨156083507230879870626502061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104055671487253247084334707 156083507230879870626502061)
    ·
      refine ⟨58531315211579951484938273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 156083507230879870626502061 58531315211579951484938273)
      ·
        refine ⟨43898486408684963613703705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58531315211579951484938273 43898486408684963613703705)
        ·
          refine ⟨32923864806513722710277779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43898486408684963613703705 32923864806513722710277779)
          ·
            refine ⟨49385797209770584065416669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32923864806513722710277779 49385797209770584065416669)
            ·
              refine ⟨18519673953663969024531251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 49385797209770584065416669 18519673953663969024531251)
              ·
                refine ⟨27779510930495953536796877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18519673953663969024531251 27779510930495953536796877)
                ·
                  refine ⟨10417316598935982576298829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27779510930495953536796877 10417316598935982576298829)
                  ·
                    refine ⟨3906493724600993466112061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10417316598935982576298829 3906493724600993466112061)
                    ·
                      refine ⟨1464935146725372549792023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3906493724600993466112061 1464935146725372549792023)
                      ·
                        rfl

theorem cell23_2852951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 3, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 3, 1, 3, 3, 3].length) (baseStart_2852951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2852951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2852951 prefixEnd_2852951 := by exact prefixLift 2852951
  have htrace : WordTrace (prefixWord ++ tailWord_2852951) baseStart_2852951 baseEnd_2852951 := by
    simpa [prefixWord, tailWord_2852951, baseEnd_2852951] using wordTrace_append hprefix tailTrace_2852951
  have hstable : (prefixWord ++ tailWord_2852951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2852951).length < 2 ^ (prefixWord ++ tailWord_2852951).sum := by decide
  have hdescent : baseEnd_2852951 < baseStart_2852951 := by decide
  rcases family_descends (prefixWord ++ tailWord_2852951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2852958 : List Nat := [4, 4, 1, 1, 13]
def baseStart_2852958 : Nat := 118140960795 + 2852958 * 2 ^ 59
def prefixEnd_2852958 : Nat := 4983230072969 + 3 ^ 40 * 2852958 * 2
def baseEnd_2852958 : Nat := 2009518163360705106179

theorem tailTrace_2852958 : CollatzResearch.WordTrace tailWord_2852958 prefixEnd_2852958 2009518163360705106179 := by
  unfold tailWord_2852958
  simp only [CollatzResearch.WordTrace]
  refine ⟨13006990849778485909979941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 69370617865485258186559685 13006990849778485909979941)
  ·
    refine ⟨2438810784333466108121239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13006990849778485909979941 2438810784333466108121239)
    ·
      refine ⟨3658216176500199162181859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2438810784333466108121239 3658216176500199162181859)
      ·
        refine ⟨5487324264750298743272789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3658216176500199162181859 5487324264750298743272789)
        ·
          refine ⟨2009518163360705106179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 13 5487324264750298743272789 2009518163360705106179)
          ·
            rfl

theorem cell23_2852958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 13].length) (baseStart_2852958 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2852958 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2852958 prefixEnd_2852958 := by exact prefixLift 2852958
  have htrace : WordTrace (prefixWord ++ tailWord_2852958) baseStart_2852958 baseEnd_2852958 := by
    simpa [prefixWord, tailWord_2852958, baseEnd_2852958] using wordTrace_append hprefix tailTrace_2852958
  have hstable : (prefixWord ++ tailWord_2852958).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2852958).length < 2 ^ (prefixWord ++ tailWord_2852958).sum := by decide
  have hdescent : baseEnd_2852958 < baseStart_2852958 := by decide
  rcases family_descends (prefixWord ++ tailWord_2852958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2852962 : List Nat := [3, 3, 2, 2, 2, 1, 2, 2, 2, 4]
def baseStart_2852962 : Nat := 118140960795 + 2852962 * 2 ^ 59
def prefixEnd_2852962 : Nat := 4983230072969 + 3 ^ 40 * 2852962 * 2
def baseEnd_2852962 : Nat := 488313598337524002251491

theorem tailTrace_2852962 : CollatzResearch.WordTrace tailWord_2852962 prefixEnd_2852962 488313598337524002251491 := by
  unfold tailWord_2852962
  simp only [CollatzResearch.WordTrace]
  refine ⟨26014018172553348990746285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69370715126808930641990093 26014018172553348990746285)
  ·
    refine ⟨9755256814707505871529857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26014018172553348990746285 9755256814707505871529857)
    ·
      refine ⟨7316442611030629403647393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9755256814707505871529857 7316442611030629403647393)
      ·
        refine ⟨5487331958272972052735545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7316442611030629403647393 5487331958272972052735545)
        ·
          refine ⟨4115498968704729039551659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5487331958272972052735545 4115498968704729039551659)
          ·
            refine ⟨6173248453057093559327489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4115498968704729039551659 6173248453057093559327489)
            ·
              refine ⟨4629936339792820169495617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6173248453057093559327489 4629936339792820169495617)
              ·
                refine ⟨3472452254844615127121713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4629936339792820169495617 3472452254844615127121713)
                ·
                  refine ⟨2604339191133461345341285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3472452254844615127121713 2604339191133461345341285)
                  ·
                    refine ⟨488313598337524002251491, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2604339191133461345341285 488313598337524002251491)
                    ·
                      rfl

theorem cell23_2852962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 1, 2, 2, 2, 4].length) (baseStart_2852962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2852962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2852962 prefixEnd_2852962 := by exact prefixLift 2852962
  have htrace : WordTrace (prefixWord ++ tailWord_2852962) baseStart_2852962 baseEnd_2852962 := by
    simpa [prefixWord, tailWord_2852962, baseEnd_2852962] using wordTrace_append hprefix tailTrace_2852962
  have hstable : (prefixWord ++ tailWord_2852962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2852962).length < 2 ^ (prefixWord ++ tailWord_2852962).sum := by decide
  have hdescent : baseEnd_2852962 < baseStart_2852962 := by decide
  rcases family_descends (prefixWord ++ tailWord_2852962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2852985 : List Nat := [1, 2, 1, 3, 4, 1, 2, 3, 2, 1, 3]
def baseStart_2852985 : Nat := 118140960795 + 2852985 * 2 ^ 59
def prefixEnd_2852985 : Nat := 4983230072969 + 3 ^ 40 * 2852985 * 2
def baseEnd_2852985 : Nat := 1464952605067625416766867

theorem tailTrace_2852985 : CollatzResearch.WordTrace tailWord_2852985 prefixEnd_2852985 1464952605067625416766867 := by
  unfold tailWord_2852985
  simp only [CollatzResearch.WordTrace]
  refine ⟨104056911569130070891072409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69371274379420047260714939 104056911569130070891072409)
  ·
    refine ⟨78042683676847553168304307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104056911569130070891072409 78042683676847553168304307)
    ·
      refine ⟨117064025515271329752456461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78042683676847553168304307 117064025515271329752456461)
      ·
        refine ⟨43899009568226748657171173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 117064025515271329752456461 43899009568226748657171173)
        ·
          refine ⟨8231064294042515373219595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 43899009568226748657171173 8231064294042515373219595)
          ·
            refine ⟨12346596441063773059829393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8231064294042515373219595 12346596441063773059829393)
            ·
              refine ⟨9259947330797829794872045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12346596441063773059829393 9259947330797829794872045)
              ·
                refine ⟨3472480249049186173077017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9259947330797829794872045 3472480249049186173077017)
                ·
                  refine ⟨2604360186786889629807763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3472480249049186173077017 2604360186786889629807763)
                  ·
                    refine ⟨3906540280180334444711645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2604360186786889629807763 3906540280180334444711645)
                    ·
                      refine ⟨1464952605067625416766867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3906540280180334444711645 1464952605067625416766867)
                      ·
                        rfl

theorem cell23_2852985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 2, 3, 2, 1, 3].length) (baseStart_2852985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2852985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2852985 prefixEnd_2852985 := by exact prefixLift 2852985
  have htrace : WordTrace (prefixWord ++ tailWord_2852985) baseStart_2852985 baseEnd_2852985 := by
    simpa [prefixWord, tailWord_2852985, baseEnd_2852985] using wordTrace_append hprefix tailTrace_2852985
  have hstable : (prefixWord ++ tailWord_2852985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2852985).length < 2 ^ (prefixWord ++ tailWord_2852985).sum := by decide
  have hdescent : baseEnd_2852985 < baseStart_2852985 := by decide
  rcases family_descends (prefixWord ++ tailWord_2852985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2853008 : List Nat := [2, 1, 1, 1, 1, 1, 5, 4, 1, 4, 2]
def baseStart_2853008 : Nat := 118140960795 + 2853008 * 2 ^ 59
def prefixEnd_2853008 : Nat := 4983230072969 + 3 ^ 40 * 2853008 * 2
def baseEnd_2853008 : Nat := 1464964415122678826779261

theorem tailTrace_2853008 : CollatzResearch.WordTrace tailWord_2853008 prefixEnd_2853008 1464964415122678826779261 := by
  unfold tailWord_2853008
  simp only [CollatzResearch.WordTrace]
  refine ⟨52028875224023372909579839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69371833632031163879439785 52028875224023372909579839)
  ·
    refine ⟨78043312836035059364369759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52028875224023372909579839 78043312836035059364369759)
    ·
      refine ⟨117064969254052589046554639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78043312836035059364369759 117064969254052589046554639)
      ·
        refine ⟨175597453881078883569831959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117064969254052589046554639 175597453881078883569831959)
        ·
          refine ⟨263396180821618325354747939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 175597453881078883569831959 263396180821618325354747939)
          ·
            refine ⟨395094271232427488032121909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 263396180821618325354747939 395094271232427488032121909)
            ·
              refine ⟨37040087928040077003011429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 395094271232427488032121909 37040087928040077003011429)
              ·
                refine ⟨6945016486507514438064643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 37040087928040077003011429 6945016486507514438064643)
                ·
                  refine ⟨10417524729761271657096965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6945016486507514438064643 10417524729761271657096965)
                  ·
                    refine ⟨1953285886830238435705681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10417524729761271657096965 1953285886830238435705681)
                    ·
                      refine ⟨1464964415122678826779261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1953285886830238435705681 1464964415122678826779261)
                      ·
                        rfl

theorem cell23_2853008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 5, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 5, 4, 1, 4, 2].length) (baseStart_2853008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2853008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2853008 prefixEnd_2853008 := by exact prefixLift 2853008
  have htrace : WordTrace (prefixWord ++ tailWord_2853008) baseStart_2853008 baseEnd_2853008 := by
    simpa [prefixWord, tailWord_2853008, baseEnd_2853008] using wordTrace_append hprefix tailTrace_2853008
  have hstable : (prefixWord ++ tailWord_2853008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2853008).length < 2 ^ (prefixWord ++ tailWord_2853008).sum := by decide
  have hdescent : baseEnd_2853008 < baseStart_2853008 := by decide
  rcases family_descends (prefixWord ++ tailWord_2853008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2853061 : List Nat := [1, 3, 1, 1, 1, 1, 6, 1, 1, 7]
def baseStart_2853061 : Nat := 118140960795 + 2853061 * 2 ^ 59
def prefixEnd_2853061 : Nat := 4983230072969 + 3 ^ 40 * 2853061 * 2
def baseEnd_2853061 : Nat := 488330543199122373138839

theorem tailTrace_2853061 : CollatzResearch.WordTrace tailWord_2853061 prefixEnd_2853061 488330543199122373138839 := by
  unfold tailWord_2853061
  simp only [CollatzResearch.WordTrace]
  refine ⟨104059683516854735870839037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69373122344569823913892691 104059683516854735870839037)
  ·
    refine ⟨39022381318820525951564639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 104059683516854735870839037 39022381318820525951564639)
    ·
      refine ⟨58533571978230788927346959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39022381318820525951564639 58533571978230788927346959)
      ·
        refine ⟨87800357967346183391020439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58533571978230788927346959 87800357967346183391020439)
        ·
          refine ⟨131700536951019275086530659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87800357967346183391020439 131700536951019275086530659)
          ·
            refine ⟨197550805426528912629795989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 131700536951019275086530659 197550805426528912629795989)
            ·
              refine ⟨9260194004368542779521687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 197550805426528912629795989 9260194004368542779521687)
              ·
                refine ⟨13890291006552814169282531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9260194004368542779521687 13890291006552814169282531)
                ·
                  refine ⟨20835436509829221253923797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13890291006552814169282531 20835436509829221253923797)
                  ·
                    refine ⟨488330543199122373138839, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 20835436509829221253923797 488330543199122373138839)
                    ·
                      rfl

theorem cell23_2853061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 6, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 6, 1, 1, 7].length) (baseStart_2853061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2853061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2853061 prefixEnd_2853061 := by exact prefixLift 2853061
  have htrace : WordTrace (prefixWord ++ tailWord_2853061) baseStart_2853061 baseEnd_2853061 := by
    simpa [prefixWord, tailWord_2853061, baseEnd_2853061] using wordTrace_append hprefix tailTrace_2853061
  have hstable : (prefixWord ++ tailWord_2853061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2853061).length < 2 ^ (prefixWord ++ tailWord_2853061).sum := by decide
  have hdescent : baseEnd_2853061 < baseStart_2853061 := by decide
  rcases family_descends (prefixWord ++ tailWord_2853061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2853071 : List Nat := [1, 1, 2, 1, 1, 3, 4, 2, 1, 2, 5]
def baseStart_2853071 : Nat := 118140960795 + 2853071 * 2 ^ 59
def prefixEnd_2853071 : Nat := 4983230072969 + 3 ^ 40 * 2853071 * 2
def baseEnd_2853071 : Nat := 1464996764403912080291471

theorem tailTrace_2853071 : CollatzResearch.WordTrace tailWord_2853071 prefixEnd_2853071 1464996764403912080291471 := by
  unfold tailWord_2853071
  simp only [CollatzResearch.WordTrace]
  refine ⟨104060048246818507578703067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69373365497879005052468711 104060048246818507578703067)
  ·
    refine ⟨156090072370227761368054601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104060048246818507578703067 156090072370227761368054601)
    ·
      refine ⟨117067554277670821026040951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 156090072370227761368054601 117067554277670821026040951)
      ·
        refine ⟨175601331416506231539061427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117067554277670821026040951 175601331416506231539061427)
        ·
          refine ⟨263401997124759347308592141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 175601331416506231539061427 263401997124759347308592141)
          ·
            refine ⟨98775748921784755240722053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 263401997124759347308592141 98775748921784755240722053)
            ·
              refine ⟨18520452922834641607635385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 98775748921784755240722053 18520452922834641607635385)
              ·
                refine ⟨13890339692125981205726539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18520452922834641607635385 13890339692125981205726539)
                ·
                  refine ⟨20835509538188971808589809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13890339692125981205726539 20835509538188971808589809)
                  ·
                    refine ⟨15626632153641728856442357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20835509538188971808589809 15626632153641728856442357)
                    ·
                      refine ⟨1464996764403912080291471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15626632153641728856442357 1464996764403912080291471)
                      ·
                        rfl

theorem cell23_2853071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 4, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 4, 2, 1, 2, 5].length) (baseStart_2853071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2853071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2853071 prefixEnd_2853071 := by exact prefixLift 2853071
  have htrace : WordTrace (prefixWord ++ tailWord_2853071) baseStart_2853071 baseEnd_2853071 := by
    simpa [prefixWord, tailWord_2853071, baseEnd_2853071] using wordTrace_append hprefix tailTrace_2853071
  have hstable : (prefixWord ++ tailWord_2853071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2853071).length < 2 ^ (prefixWord ++ tailWord_2853071).sum := by decide
  have hdescent : baseEnd_2853071 < baseStart_2853071 := by decide
  rcases family_descends (prefixWord ++ tailWord_2853071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2853098 : List Nat := [3, 1, 3, 1, 1, 2, 1, 2, 4, 1, 4]
def baseStart_2853098 : Nat := 118140960795 + 2853098 * 2 ^ 59
def prefixEnd_2853098 : Nat := 4983230072969 + 3 ^ 40 * 2853098 * 2
def baseEnd_2853098 : Nat := 1465010628381583474653847

theorem tailTrace_2853098 : CollatzResearch.WordTrace tailWord_2853098 prefixEnd_2853098 1465010628381583474653847 := by
  unfold tailWord_2853098
  simp only [CollatzResearch.WordTrace]
  refine ⟨26015258254430172797483987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69374022011813794126623965 26015258254430172797483987)
  ·
    refine ⟨39022887381645259196225981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26015258254430172797483987 39022887381645259196225981)
    ·
      refine ⟨14633582768116972198584743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39022887381645259196225981 14633582768116972198584743)
      ·
        refine ⟨21950374152175458297877115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14633582768116972198584743 21950374152175458297877115)
        ·
          refine ⟨32925561228263187446815673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21950374152175458297877115 32925561228263187446815673)
          ·
            refine ⟨24694170921197390585111755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32925561228263187446815673 24694170921197390585111755)
            ·
              refine ⟨37041256381796085877667633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24694170921197390585111755 37041256381796085877667633)
              ·
                refine ⟨27780942286347064408250725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37041256381796085877667633 27780942286347064408250725)
                ·
                  refine ⟨5208926678690074576547011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27780942286347064408250725 5208926678690074576547011)
                  ·
                    refine ⟨7813390018035111864820517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5208926678690074576547011 7813390018035111864820517)
                    ·
                      refine ⟨1465010628381583474653847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7813390018035111864820517 1465010628381583474653847)
                      ·
                        rfl

theorem cell23_2853098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 1, 2, 4, 1, 4].length) (baseStart_2853098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2853098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2853098 prefixEnd_2853098 := by exact prefixLift 2853098
  have htrace : WordTrace (prefixWord ++ tailWord_2853098) baseStart_2853098 baseEnd_2853098 := by
    simpa [prefixWord, tailWord_2853098, baseEnd_2853098] using wordTrace_append hprefix tailTrace_2853098
  have hstable : (prefixWord ++ tailWord_2853098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2853098).length < 2 ^ (prefixWord ++ tailWord_2853098).sum := by decide
  have hdescent : baseEnd_2853098 < baseStart_2853098 := by decide
  rcases family_descends (prefixWord ++ tailWord_2853098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2853148 : List Nat := [2, 2, 3, 1, 1, 1, 1, 2, 2, 5, 3]
def baseStart_2853148 : Nat := 118140960795 + 2853148 * 2 ^ 59
def prefixEnd_2853148 : Nat := 4983230072969 + 3 ^ 40 * 2853148 * 2
def baseEnd_2853148 : Nat := 1465036302414308279028617

theorem tailTrace_2853148 : CollatzResearch.WordTrace tailWord_2853148 prefixEnd_2853148 1465036302414308279028617 := by
  unfold tailWord_2853148
  simp only [CollatzResearch.WordTrace]
  refine ⟨52031428333769774864628049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69375237778359699819504065 52031428333769774864628049)
  ·
    refine ⟨39023571250327331148471037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52031428333769774864628049 39023571250327331148471037)
    ·
      refine ⟨14633839218872749180676639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39023571250327331148471037 14633839218872749180676639)
      ·
        refine ⟨21950758828309123771014959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14633839218872749180676639 21950758828309123771014959)
        ·
          refine ⟨32926138242463685656522439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21950758828309123771014959 32926138242463685656522439)
          ·
            refine ⟨49389207363695528484783659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32926138242463685656522439 49389207363695528484783659)
            ·
              refine ⟨74083811045543292727175489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49389207363695528484783659 74083811045543292727175489)
              ·
                refine ⟨55562858284157469545381617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 74083811045543292727175489 55562858284157469545381617)
                ·
                  refine ⟨41672143713118102159036213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 55562858284157469545381617 41672143713118102159036213)
                  ·
                    refine ⟨3906763473104822077409645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 41672143713118102159036213 3906763473104822077409645)
                    ·
                      refine ⟨1465036302414308279028617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3906763473104822077409645 1465036302414308279028617)
                      ·
                        rfl

theorem cell23_2853148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 2, 2, 5, 3].length) (baseStart_2853148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2853148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2853148 prefixEnd_2853148 := by exact prefixLift 2853148
  have htrace : WordTrace (prefixWord ++ tailWord_2853148) baseStart_2853148 baseEnd_2853148 := by
    simpa [prefixWord, tailWord_2853148, baseEnd_2853148] using wordTrace_append hprefix tailTrace_2853148
  have hstable : (prefixWord ++ tailWord_2853148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2853148).length < 2 ^ (prefixWord ++ tailWord_2853148).sum := by decide
  have hdescent : baseEnd_2853148 < baseStart_2853148 := by decide
  rcases family_descends (prefixWord ++ tailWord_2853148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2853166 : List Nat := [4, 1, 3, 3, 2, 1, 1, 1, 2, 1, 4]
def baseStart_2853166 : Nat := 118140960795 + 2853166 * 2 ^ 59
def prefixEnd_2853166 : Nat := 4983230072969 + 3 ^ 40 * 2853166 * 2
def baseEnd_2853166 : Nat := 1465045545066089208603535

theorem tailTrace_2853166 : CollatzResearch.WordTrace tailWord_2853166 prefixEnd_2853166 1465045545066089208603535 := by
  unfold tailWord_2853166
  simp only [CollatzResearch.WordTrace]
  refine ⟨13007939147684292350426419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 69375675454316225868940901 13007939147684292350426419)
  ·
    refine ⟨19511908721526438525639629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13007939147684292350426419 19511908721526438525639629)
    ·
      refine ⟨7316965770572414447114861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19511908721526438525639629 7316965770572414447114861)
      ·
        refine ⟨2743862163964655417668073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7316965770572414447114861 2743862163964655417668073)
        ·
          refine ⟨2057896622973491563251055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2743862163964655417668073 2057896622973491563251055)
          ·
            refine ⟨3086844934460237344876583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2057896622973491563251055 3086844934460237344876583)
            ·
              refine ⟨4630267401690356017314875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3086844934460237344876583 4630267401690356017314875)
              ·
                refine ⟨6945401102535534025972313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4630267401690356017314875 6945401102535534025972313)
                ·
                  refine ⟨5209050826901650519479235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6945401102535534025972313 5209050826901650519479235)
                  ·
                    refine ⟨7813576240352475779218853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5209050826901650519479235 7813576240352475779218853)
                    ·
                      refine ⟨1465045545066089208603535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7813576240352475779218853 1465045545066089208603535)
                      ·
                        rfl

theorem cell23_2853166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 2, 1, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 2, 1, 1, 1, 2, 1, 4].length) (baseStart_2853166 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2853166 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2853166 prefixEnd_2853166 := by exact prefixLift 2853166
  have htrace : WordTrace (prefixWord ++ tailWord_2853166) baseStart_2853166 baseEnd_2853166 := by
    simpa [prefixWord, tailWord_2853166, baseEnd_2853166] using wordTrace_append hprefix tailTrace_2853166
  have hstable : (prefixWord ++ tailWord_2853166).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2853166).length < 2 ^ (prefixWord ++ tailWord_2853166).sum := by decide
  have hdescent : baseEnd_2853166 < baseStart_2853166 := by decide
  rcases family_descends (prefixWord ++ tailWord_2853166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2853169 : List Nat := [1, 2, 2, 3, 5, 1, 1, 1, 2, 2, 3]
def baseStart_2853169 : Nat := 118140960795 + 2853169 * 2 ^ 59
def prefixEnd_2853169 : Nat := 4983230072969 + 3 ^ 40 * 2853169 * 2
def baseEnd_2853169 : Nat := 1465047085508052696866021

theorem tailTrace_2853169 : CollatzResearch.WordTrace tailWord_2853169 prefixEnd_2853169 1465047085508052696866021 := by
  unfold tailWord_2853169
  simp only [CollatzResearch.WordTrace]
  refine ⟨104063622600463470315770561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69375748400308980210513707 104063622600463470315770561)
  ·
    refine ⟨78047716950347602736827921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104063622600463470315770561 78047716950347602736827921)
    ·
      refine ⟨58535787712760702052620941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78047716950347602736827921 58535787712760702052620941)
      ·
        refine ⟨21950920392285263269732853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 58535787712760702052620941 21950920392285263269732853)
        ·
          refine ⟨2057898786776743431537455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 21950920392285263269732853 2057898786776743431537455)
          ·
            refine ⟨3086848180165115147306183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2057898786776743431537455 3086848180165115147306183)
            ·
              refine ⟨4630272270247672720959275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3086848180165115147306183 4630272270247672720959275)
              ·
                refine ⟨6945408405371509081438913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4630272270247672720959275 6945408405371509081438913)
                ·
                  refine ⟨5209056304028631811079185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6945408405371509081438913 5209056304028631811079185)
                  ·
                    refine ⟨3906792228021473858309389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5209056304028631811079185 3906792228021473858309389)
                    ·
                      refine ⟨1465047085508052696866021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3906792228021473858309389 1465047085508052696866021)
                      ·
                        rfl

theorem cell23_2853169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 5, 1, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 5, 1, 1, 1, 2, 2, 3].length) (baseStart_2853169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2853169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2853169 prefixEnd_2853169 := by exact prefixLift 2853169
  have htrace : WordTrace (prefixWord ++ tailWord_2853169) baseStart_2853169 baseEnd_2853169 := by
    simpa [prefixWord, tailWord_2853169, baseEnd_2853169] using wordTrace_append hprefix tailTrace_2853169
  have hstable : (prefixWord ++ tailWord_2853169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2853169).length < 2 ^ (prefixWord ++ tailWord_2853169).sum := by decide
  have hdescent : baseEnd_2853169 < baseStart_2853169 := by decide
  rcases family_descends (prefixWord ++ tailWord_2853169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2853208 : List Nat := [2, 1, 2, 2, 1, 1, 2, 1, 2, 6, 3]
def baseStart_2853208 : Nat := 118140960795 + 2853208 * 2 ^ 59
def prefixEnd_2853208 : Nat := 4983230072969 + 3 ^ 40 * 2853208 * 2
def baseEnd_2853208 : Nat := 1465067111253578044278341

theorem tailTrace_2853208 : CollatzResearch.WordTrace tailWord_2853208 prefixEnd_2853208 1465067111253578044278341 := by
  unfold tailWord_2853208
  simp only [CollatzResearch.WordTrace]
  refine ⟨52032522523661089988220139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69376696698214786650960185 52032522523661089988220139)
  ·
    refine ⟨78048783785491634982330209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52032522523661089988220139 78048783785491634982330209)
    ·
      refine ⟨58536587839118726236747657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78048783785491634982330209 58536587839118726236747657)
      ·
        refine ⟨43902440879339044677560743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58536587839118726236747657 43902440879339044677560743)
        ·
          refine ⟨65853661319008567016341115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43902440879339044677560743 65853661319008567016341115)
          ·
            refine ⟨98780491978512850524511673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65853661319008567016341115 98780491978512850524511673)
            ·
              refine ⟨74085368983884637893383755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 98780491978512850524511673 74085368983884637893383755)
              ·
                refine ⟨111128053475826956840075633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 74085368983884637893383755 111128053475826956840075633)
                ·
                  refine ⟨83346040106870217630056725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 111128053475826956840075633 83346040106870217630056725)
                  ·
                    refine ⟨3906845630009541451408909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 83346040106870217630056725 3906845630009541451408909)
                    ·
                      refine ⟨1465067111253578044278341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3906845630009541451408909 1465067111253578044278341)
                      ·
                        rfl

theorem cell23_2853208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 1, 2, 6, 3].length) (baseStart_2853208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2853208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2853208 prefixEnd_2853208 := by exact prefixLift 2853208
  have htrace : WordTrace (prefixWord ++ tailWord_2853208) baseStart_2853208 baseEnd_2853208 := by
    simpa [prefixWord, tailWord_2853208, baseEnd_2853208] using wordTrace_append hprefix tailTrace_2853208
  have hstable : (prefixWord ++ tailWord_2853208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2853208).length < 2 ^ (prefixWord ++ tailWord_2853208).sum := by decide
  have hdescent : baseEnd_2853208 < baseStart_2853208 := by decide
  rcases family_descends (prefixWord ++ tailWord_2853208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2853215 : List Nat := [1, 1, 2, 3, 1, 2, 2, 5, 2, 4]
def baseStart_2853215 : Nat := 118140960795 + 2853215 * 2 ^ 59
def prefixEnd_2853215 : Nat := 4983230072969 + 3 ^ 40 * 2853215 * 2
def baseEnd_2853215 : Nat := 488356901872719838963603

theorem tailTrace_2853215 : CollatzResearch.WordTrace tailWord_2853215 prefixEnd_2853215 488356901872719838963603 := by
  unfold tailWord_2853215
  simp only [CollatzResearch.WordTrace]
  refine ⟨104065300358296820171945099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69376866905531213447963399 104065300358296820171945099)
  ·
    refine ⟨156097950537445230257917649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104065300358296820171945099 156097950537445230257917649)
    ·
      refine ⟨117073462903083922693438237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 156097950537445230257917649 117073462903083922693438237)
      ·
        refine ⟨43902548588656471010039339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 117073462903083922693438237 43902548588656471010039339)
        ·
          refine ⟨65853822882984706515059009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43902548588656471010039339 65853822882984706515059009)
          ·
            refine ⟨49390367162238529886294257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65853822882984706515059009 49390367162238529886294257)
            ·
              refine ⟨37042775371678897414720693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49390367162238529886294257 37042775371678897414720693)
              ·
                refine ⟨3472760191094896632630065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 37042775371678897414720693 3472760191094896632630065)
                ·
                  refine ⟨2604570143321172474472549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3472760191094896632630065 2604570143321172474472549)
                  ·
                    refine ⟨488356901872719838963603, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2604570143321172474472549 488356901872719838963603)
                    ·
                      rfl

theorem cell23_2853215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 2, 5, 2, 4].length) (baseStart_2853215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2853215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2853215 prefixEnd_2853215 := by exact prefixLift 2853215
  have htrace : WordTrace (prefixWord ++ tailWord_2853215) baseStart_2853215 baseEnd_2853215 := by
    simpa [prefixWord, tailWord_2853215, baseEnd_2853215] using wordTrace_append hprefix tailTrace_2853215
  have hstable : (prefixWord ++ tailWord_2853215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2853215).length < 2 ^ (prefixWord ++ tailWord_2853215).sum := by decide
  have hdescent : baseEnd_2853215 < baseStart_2853215 := by decide
  rcases family_descends (prefixWord ++ tailWord_2853215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2853239 : List Nat := [1, 1, 3, 1, 1, 2, 2, 7, 1, 2, 2]
def baseStart_2853239 : Nat := 118140960795 + 2853239 * 2 ^ 59
def prefixEnd_2853239 : Nat := 4983230072969 + 3 ^ 40 * 2853239 * 2
def baseEnd_2853239 : Nat := 1465083029153867422990699

theorem tailTrace_2853239 : CollatzResearch.WordTrace tailWord_2853239 prefixEnd_2853239 1465083029153867422990699 := by
  unfold tailWord_2853239
  simp only [CollatzResearch.WordTrace]
  refine ⟨104066175710209872270818771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69377450473473248180545847 104066175710209872270818771)
  ·
    refine ⟨156099263565314808406228157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104066175710209872270818771 156099263565314808406228157)
    ·
      refine ⟨58537223836993053152335559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 156099263565314808406228157 58537223836993053152335559)
      ·
        refine ⟨87805835755489579728503339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58537223836993053152335559 87805835755489579728503339)
        ·
          refine ⟨131708753633234369592755009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87805835755489579728503339 131708753633234369592755009)
          ·
            refine ⟨98781565224925777194566257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 131708753633234369592755009 98781565224925777194566257)
            ·
              refine ⟨74086173918694332895924693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 98781565224925777194566257 74086173918694332895924693)
              ·
                refine ⟨1736394701219398427248235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 74086173918694332895924693 1736394701219398427248235)
                ·
                  refine ⟨2604592051829097640872353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1736394701219398427248235 2604592051829097640872353)
                  ·
                    refine ⟨1953444038871823230654265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2604592051829097640872353 1953444038871823230654265)
                    ·
                      refine ⟨1465083029153867422990699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1953444038871823230654265 1465083029153867422990699)
                      ·
                        rfl

theorem cell23_2853239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 7, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 7, 1, 2, 2].length) (baseStart_2853239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2853239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2853239 prefixEnd_2853239 := by exact prefixLift 2853239
  have htrace : WordTrace (prefixWord ++ tailWord_2853239) baseStart_2853239 baseEnd_2853239 := by
    simpa [prefixWord, tailWord_2853239, baseEnd_2853239] using wordTrace_append hprefix tailTrace_2853239
  have hstable : (prefixWord ++ tailWord_2853239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2853239).length < 2 ^ (prefixWord ++ tailWord_2853239).sum := by decide
  have hdescent : baseEnd_2853239 < baseStart_2853239 := by decide
  rcases family_descends (prefixWord ++ tailWord_2853239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2853250 : List Nat := [3, 4, 2, 1, 2, 1, 3, 2, 1, 1, 3]
def baseStart_2853250 : Nat := 118140960795 + 2853250 * 2 ^ 59
def prefixEnd_2853250 : Nat := 4983230072969 + 3 ^ 40 * 2853250 * 2
def baseEnd_2853250 : Nat := 1465088677441066879953149

theorem tailTrace_2853250 : CollatzResearch.WordTrace tailWord_2853250 prefixEnd_2853250 1465088677441066879953149 := by
  unfold tailWord_2853250
  simp only [CollatzResearch.WordTrace]
  refine ⟨26016644228292505287367301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69377717942113347432979469 26016644228292505287367301)
  ·
    refine ⟨4878120792804844741381369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 26016644228292505287367301 4878120792804844741381369)
    ·
      refine ⟨3658590594603633556036027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4878120792804844741381369 3658590594603633556036027)
      ·
        refine ⟨5487885891905450334054041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3658590594603633556036027 5487885891905450334054041)
        ·
          refine ⟨4115914418929087750540531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5487885891905450334054041 4115914418929087750540531)
          ·
            refine ⟨6173871628393631625810797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4115914418929087750540531 6173871628393631625810797)
            ·
              refine ⟨2315201860647611859679049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6173871628393631625810797 2315201860647611859679049)
              ·
                refine ⟨1736401395485708894759287, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2315201860647611859679049 1736401395485708894759287)
                ·
                  refine ⟨2604602093228563342138931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1736401395485708894759287 2604602093228563342138931)
                  ·
                    refine ⟨3906903139842845013208397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2604602093228563342138931 3906903139842845013208397)
                    ·
                      refine ⟨1465088677441066879953149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3906903139842845013208397 1465088677441066879953149)
                      ·
                        rfl

theorem cell23_2853250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 1, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 1, 3, 2, 1, 1, 3].length) (baseStart_2853250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2853250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2853250 prefixEnd_2853250 := by exact prefixLift 2853250
  have htrace : WordTrace (prefixWord ++ tailWord_2853250) baseStart_2853250 baseEnd_2853250 := by
    simpa [prefixWord, tailWord_2853250, baseEnd_2853250] using wordTrace_append hprefix tailTrace_2853250
  have hstable : (prefixWord ++ tailWord_2853250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2853250).length < 2 ^ (prefixWord ++ tailWord_2853250).sum := by decide
  have hdescent : baseEnd_2853250 < baseStart_2853250 := by decide
  rcases family_descends (prefixWord ++ tailWord_2853250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2853270 : List Nat := [5, 3, 1, 2, 2, 1, 1, 2, 1, 5]
def baseStart_2853270 : Nat := 118140960795 + 2853270 * 2 ^ 59
def prefixEnd_2853270 : Nat := 4983230072969 + 3 ^ 40 * 2853270 * 2
def baseEnd_2853270 : Nat := 488366315684718933901019

theorem tailTrace_2853270 : CollatzResearch.WordTrace tailWord_2853270 prefixEnd_2853270 488366315684718933901019 := by
  unfold tailWord_2853270
  simp only [CollatzResearch.WordTrace]
  refine ⟨6504206648318597785324829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 69378204248731709710131509 6504206648318597785324829)
  ·
    refine ⟨2439077493119474169496811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6504206648318597785324829 2439077493119474169496811)
    ·
      refine ⟨3658616239679211254245217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2439077493119474169496811 3658616239679211254245217)
      ·
        refine ⟨2743962179759408440683913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3658616239679211254245217 2743962179759408440683913)
        ·
          refine ⟨2057971634819556330512935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2743962179759408440683913 2057971634819556330512935)
          ·
            refine ⟨3086957452229334495769403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2057971634819556330512935 3086957452229334495769403)
            ·
              refine ⟨4630436178344001743654105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3086957452229334495769403 4630436178344001743654105)
              ·
                refine ⟨3472827133758001307740579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4630436178344001743654105 3472827133758001307740579)
                ·
                  refine ⟨5209240700637001961610869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3472827133758001307740579 5209240700637001961610869)
                  ·
                    refine ⟨488366315684718933901019, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5209240700637001961610869 488366315684718933901019)
                    ·
                      rfl

theorem cell23_2853270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 2, 1, 1, 2, 1, 5].length) (baseStart_2853270 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2853270 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2853270 prefixEnd_2853270 := by exact prefixLift 2853270
  have htrace : WordTrace (prefixWord ++ tailWord_2853270) baseStart_2853270 baseEnd_2853270 := by
    simpa [prefixWord, tailWord_2853270, baseEnd_2853270] using wordTrace_append hprefix tailTrace_2853270
  have hstable : (prefixWord ++ tailWord_2853270).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2853270).length < 2 ^ (prefixWord ++ tailWord_2853270).sum := by decide
  have hdescent : baseEnd_2853270 < baseStart_2853270 := by decide
  rcases family_descends (prefixWord ++ tailWord_2853270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2853345 : List Nat := [1, 2, 3, 1, 2, 2, 1, 2, 1, 5, 3]
def baseStart_2853345 : Nat := 118140960795 + 2853345 * 2 ^ 59
def prefixEnd_2853345 : Nat := 4983230072969 + 3 ^ 40 * 2853345 * 2
def baseEnd_2853345 : Nat := 1465137458103244008265211

theorem tailTrace_2853345 : CollatzResearch.WordTrace tailWord_2853345 prefixEnd_2853345 1465137458103244008265211 := by
  unfold tailWord_2853345
  simp only [CollatzResearch.WordTrace]
  refine ⟨104070041847825852374177489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69380027898550568249451659 104070041847825852374177489)
  ·
    refine ⟨78052531385869389280633117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104070041847825852374177489 78052531385869389280633117)
    ·
      refine ⟨29269699269701020980237419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 78052531385869389280633117 29269699269701020980237419)
      ·
        refine ⟨43904548904551531470356129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29269699269701020980237419 43904548904551531470356129)
        ·
          refine ⟨32928411678413648602767097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43904548904551531470356129 32928411678413648602767097)
          ·
            refine ⟨24696308758810236452075323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32928411678413648602767097 24696308758810236452075323)
            ·
              refine ⟨37044463138215354678112985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24696308758810236452075323 37044463138215354678112985)
              ·
                refine ⟨27783347353661516008584739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37044463138215354678112985 27783347353661516008584739)
                ·
                  refine ⟨41675021030492274012877109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27783347353661516008584739 41675021030492274012877109)
                  ·
                    refine ⟨3907033221608650688707229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 41675021030492274012877109 3907033221608650688707229)
                    ·
                      refine ⟨1465137458103244008265211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3907033221608650688707229 1465137458103244008265211)
                      ·
                        rfl

theorem cell23_2853345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 1, 2, 1, 5, 3].length) (baseStart_2853345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2853345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2853345 prefixEnd_2853345 := by exact prefixLift 2853345
  have htrace : WordTrace (prefixWord ++ tailWord_2853345) baseStart_2853345 baseEnd_2853345 := by
    simpa [prefixWord, tailWord_2853345, baseEnd_2853345] using wordTrace_append hprefix tailTrace_2853345
  have hstable : (prefixWord ++ tailWord_2853345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2853345).length < 2 ^ (prefixWord ++ tailWord_2853345).sum := by decide
  have hdescent : baseEnd_2853345 < baseStart_2853345 := by decide
  rcases family_descends (prefixWord ++ tailWord_2853345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2853352 : List Nat := [2, 1, 4, 1, 1, 3, 1, 5, 5]
def baseStart_2853352 : Nat := 118140960795 + 2853352 * 2 ^ 59
def prefixEnd_2853352 : Nat := 4983230072969 + 3 ^ 40 * 2853352 * 2
def baseEnd_2853352 : Nat := 162793450274202831208631

theorem tailTrace_2853352 : CollatzResearch.WordTrace tailWord_2853352 prefixEnd_2853352 162793450274202831208631 := by
  unfold tailWord_2853352
  simp only [CollatzResearch.WordTrace]
  refine ⟨52035148579400246284841155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69380198105866995046454873 52035148579400246284841155)
  ·
    refine ⟨78052722869100369427261733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52035148579400246284841155 78052722869100369427261733)
    ·
      refine ⟨14634885537956319267611575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 78052722869100369427261733 14634885537956319267611575)
      ·
        refine ⟨21952328306934478901417363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14634885537956319267611575 21952328306934478901417363)
        ·
          refine ⟨32928492460401718352126045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21952328306934478901417363 32928492460401718352126045)
          ·
            refine ⟨12348184672650644382047267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32928492460401718352126045 12348184672650644382047267)
            ·
              refine ⟨18522277008975966573070901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12348184672650644382047267 18522277008975966573070901)
              ·
                refine ⟨1736463469591496866225397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 18522277008975966573070901 1736463469591496866225397)
                ·
                  refine ⟨162793450274202831208631, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1736463469591496866225397 162793450274202831208631)
                  ·
                    rfl

theorem cell23_2853352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 1, 5, 5].length) (baseStart_2853352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2853352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2853352 prefixEnd_2853352 := by exact prefixLift 2853352
  have htrace : WordTrace (prefixWord ++ tailWord_2853352) baseStart_2853352 baseEnd_2853352 := by
    simpa [prefixWord, tailWord_2853352, baseEnd_2853352] using wordTrace_append hprefix tailTrace_2853352
  have hstable : (prefixWord ++ tailWord_2853352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2853352).length < 2 ^ (prefixWord ++ tailWord_2853352).sum := by decide
  have hdescent : baseEnd_2853352 < baseStart_2853352 := by decide
  rcases family_descends (prefixWord ++ tailWord_2853352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2853385 : List Nat := [1, 2, 1, 1, 3, 1, 2, 1, 6, 1, 4]
def baseStart_2853385 : Nat := 118140960795 + 2853385 * 2 ^ 59
def prefixEnd_2853385 : Nat := 4983230072969 + 3 ^ 40 * 2853385 * 2
def baseEnd_2853385 : Nat := 1465157997329423851765027

theorem tailTrace_2853385 : CollatzResearch.WordTrace tailWord_2853385 prefixEnd_2853385 1465157997329423851765027 := by
  unfold tailWord_2853385
  simp only [CollatzResearch.WordTrace]
  refine ⟨104071500767680939205633609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69381000511787292803755739 104071500767680939205633609)
  ·
    refine ⟨78053625575760704404225207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104071500767680939205633609 78053625575760704404225207)
    ·
      refine ⟨117080438363641056606337811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78053625575760704404225207 117080438363641056606337811)
      ·
        refine ⟨175620657545461584909506717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117080438363641056606337811 175620657545461584909506717)
        ·
          refine ⟨65857746579548094341065019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 175620657545461584909506717 65857746579548094341065019)
          ·
            refine ⟨98786619869322141511597529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65857746579548094341065019 98786619869322141511597529)
            ·
              refine ⟨74089964901991606133698147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 98786619869322141511597529 74089964901991606133698147)
              ·
                refine ⟨111134947352987409200547221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 74089964901991606133698147 111134947352987409200547221)
                ·
                  refine ⟨5209450657171284806275651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 111134947352987409200547221 5209450657171284806275651)
                  ·
                    refine ⟨7814175985756927209413477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5209450657171284806275651 7814175985756927209413477)
                    ·
                      refine ⟨1465157997329423851765027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7814175985756927209413477 1465157997329423851765027)
                      ·
                        rfl

theorem cell23_2853385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 1, 6, 1, 4].length) (baseStart_2853385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2853385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2853385 prefixEnd_2853385 := by exact prefixLift 2853385
  have htrace : WordTrace (prefixWord ++ tailWord_2853385) baseStart_2853385 baseEnd_2853385 := by
    simpa [prefixWord, tailWord_2853385, baseEnd_2853385] using wordTrace_append hprefix tailTrace_2853385
  have hstable : (prefixWord ++ tailWord_2853385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2853385).length < 2 ^ (prefixWord ++ tailWord_2853385).sum := by decide
  have hdescent : baseEnd_2853385 < baseStart_2853385 := by decide
  rcases family_descends (prefixWord ++ tailWord_2853385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2853402 : List Nat := [3, 1, 1, 3, 1, 1, 2, 2, 1, 6, 2]
def baseStart_2853402 : Nat := 118140960795 + 2853402 * 2 ^ 59
def prefixEnd_2853402 : Nat := 4983230072969 + 3 ^ 40 * 2853402 * 2
def baseEnd_2853402 : Nat := 1465166726500550285252449

theorem tailTrace_2853402 : CollatzResearch.WordTrace tailWord_2853402 prefixEnd_2853402 1465166726500550285252449 := by
  unfold tailWord_2853402
  simp only [CollatzResearch.WordTrace]
  refine ⟨26018030202154837777250615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69381413872412900739334973 26018030202154837777250615)
  ·
    refine ⟨39027045303232256665875923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26018030202154837777250615 39027045303232256665875923)
    ·
      refine ⟨58540567954848384998813885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39027045303232256665875923 58540567954848384998813885)
      ·
        refine ⟨21952712983068144374555207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 58540567954848384998813885 21952712983068144374555207)
        ·
          refine ⟨32929069474602216561832811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21952712983068144374555207 32929069474602216561832811)
          ·
            refine ⟨49393604211903324842749217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32929069474602216561832811 49393604211903324842749217)
            ·
              refine ⟨37045203158927493632061913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49393604211903324842749217 37045203158927493632061913)
              ·
                refine ⟨27783902369195620224046435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37045203158927493632061913 27783902369195620224046435)
                ·
                  refine ⟨41675853553793430336069653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27783902369195620224046435 41675853553793430336069653)
                  ·
                    refine ⟨1953555635334067047003265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 41675853553793430336069653 1953555635334067047003265)
                    ·
                      refine ⟨1465166726500550285252449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1953555635334067047003265 1465166726500550285252449)
                      ·
                        rfl

theorem cell23_2853402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 2, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 2, 2, 1, 6, 2].length) (baseStart_2853402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2853402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2853402 prefixEnd_2853402 := by exact prefixLift 2853402
  have htrace : WordTrace (prefixWord ++ tailWord_2853402) baseStart_2853402 baseEnd_2853402 := by
    simpa [prefixWord, tailWord_2853402, baseEnd_2853402] using wordTrace_append hprefix tailTrace_2853402
  have hstable : (prefixWord ++ tailWord_2853402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2853402).length < 2 ^ (prefixWord ++ tailWord_2853402).sum := by decide
  have hdescent : baseEnd_2853402 < baseStart_2853402 := by decide
  rcases family_descends (prefixWord ++ tailWord_2853402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2853425 : List Nat := [1, 2, 2, 3, 1, 1, 4, 1, 8]
def baseStart_2853425 : Nat := 118140960795 + 2853425 * 2 ^ 59
def prefixEnd_2853425 : Nat := 4983230072969 + 3 ^ 40 * 2853425 * 2
def baseEnd_2853425 : Nat := 162797615172844855029427

theorem tailTrace_2853425 : CollatzResearch.WordTrace tailWord_2853425 prefixEnd_2853425 162797615172844855029427 := by
  unfold tailWord_2853425
  simp only [CollatzResearch.WordTrace]
  refine ⟨104072959687536026037089729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69381973125024017358059819 104072959687536026037089729)
  ·
    refine ⟨78054719765652019527817297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104072959687536026037089729 78054719765652019527817297)
    ·
      refine ⟨58541039824239014645862973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78054719765652019527817297 58541039824239014645862973)
      ·
        refine ⟨21952889934089630492198615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 58541039824239014645862973 21952889934089630492198615)
        ·
          refine ⟨32929334901134445738297923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21952889934089630492198615 32929334901134445738297923)
          ·
            refine ⟨49394002351701668607446885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32929334901134445738297923 49394002351701668607446885)
            ·
              refine ⟨9261375440944062863896291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 49394002351701668607446885 9261375440944062863896291)
              ·
                refine ⟨13892063161416094295844437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9261375440944062863896291 13892063161416094295844437)
                ·
                  refine ⟨162797615172844855029427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 13892063161416094295844437 162797615172844855029427)
                  ·
                    rfl

theorem cell23_2853425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 4, 1, 8].length) (baseStart_2853425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2853425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2853425 prefixEnd_2853425 := by exact prefixLift 2853425
  have htrace : WordTrace (prefixWord ++ tailWord_2853425) baseStart_2853425 baseEnd_2853425 := by
    simpa [prefixWord, tailWord_2853425, baseEnd_2853425] using wordTrace_append hprefix tailTrace_2853425
  have hstable : (prefixWord ++ tailWord_2853425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2853425).length < 2 ^ (prefixWord ++ tailWord_2853425).sum := by decide
  have hdescent : baseEnd_2853425 < baseStart_2853425 := by decide
  rcases family_descends (prefixWord ++ tailWord_2853425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2853435 : List Nat := [1, 1, 1, 1, 1, 2, 1, 2, 3, 7, 3]
def baseStart_2853435 : Nat := 118140960795 + 2853435 * 2 ^ 59
def prefixEnd_2853435 : Nat := 4983230072969 + 3 ^ 40 * 2853435 * 2
def baseEnd_2853435 : Nat := 1465183671362148656139797

theorem tailTrace_2853435 : CollatzResearch.WordTrace tailWord_2853435 prefixEnd_2853435 1465183671362148656139797 := by
  unfold tailWord_2853435
  simp only [CollatzResearch.WordTrace]
  refine ⟨104073324417499797744953759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69382216278333198496635839 104073324417499797744953759)
  ·
    refine ⟨156109986626249696617430639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104073324417499797744953759 156109986626249696617430639)
    ·
      refine ⟨234164979939374544926145959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 156109986626249696617430639 234164979939374544926145959)
      ·
        refine ⟨351247469909061817389218939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 234164979939374544926145959 351247469909061817389218939)
        ·
          refine ⟨526871204863592726083828409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 351247469909061817389218939 526871204863592726083828409)
          ·
            refine ⟨395153403647694544562871307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 526871204863592726083828409 395153403647694544562871307)
            ·
              refine ⟨592730105471541816844306961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 395153403647694544562871307 592730105471541816844306961)
              ·
                refine ⟨444547579103656362633230221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 592730105471541816844306961 444547579103656362633230221)
                ·
                  refine ⟨166705342163871135987461333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 444547579103656362633230221 166705342163871135987461333)
                  ·
                    refine ⟨3907156456965729749706125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 166705342163871135987461333 3907156456965729749706125)
                    ·
                      refine ⟨1465183671362148656139797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3907156456965729749706125 1465183671362148656139797)
                      ·
                        rfl

theorem cell23_2853435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 2, 3, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 2, 3, 7, 3].length) (baseStart_2853435 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2853435 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2853435 prefixEnd_2853435 := by exact prefixLift 2853435
  have htrace : WordTrace (prefixWord ++ tailWord_2853435) baseStart_2853435 baseEnd_2853435 := by
    simpa [prefixWord, tailWord_2853435, baseEnd_2853435] using wordTrace_append hprefix tailTrace_2853435
  have hstable : (prefixWord ++ tailWord_2853435).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2853435).length < 2 ^ (prefixWord ++ tailWord_2853435).sum := by decide
  have hdescent : baseEnd_2853435 < baseStart_2853435 := by decide
  rcases family_descends (prefixWord ++ tailWord_2853435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2853472 : List Nat := [2, 1, 1, 3, 2, 1, 2, 5, 1, 5]
def baseStart_2853472 : Nat := 118140960795 + 2853472 * 2 ^ 59
def prefixEnd_2853472 : Nat := 4983230072969 + 3 ^ 40 * 2853472 * 2
def baseEnd_2853472 : Nat := 488400890048788337125709

theorem tailTrace_2853472 : CollatzResearch.WordTrace tailWord_2853472 prefixEnd_2853472 488400890048788337125709 := by
  unfold tailWord_2853472
  simp only [CollatzResearch.WordTrace]
  refine ⟨52037336959182876532025335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69383115945577168709367113 52037336959182876532025335)
  ·
    refine ⟨78056005438774314798038003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52037336959182876532025335 78056005438774314798038003)
    ·
      refine ⟨117084008158161472197057005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78056005438774314798038003 117084008158161472197057005)
      ·
        refine ⟨43906503059310552073896377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 117084008158161472197057005 43906503059310552073896377)
        ·
          refine ⟨32929877294482914055422283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43906503059310552073896377 32929877294482914055422283)
          ·
            refine ⟨49394815941724371083133425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32929877294482914055422283 49394815941724371083133425)
            ·
              refine ⟨37046111956293278312350069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49394815941724371083133425 37046111956293278312350069)
              ·
                refine ⟨3473072995902494841782819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 37046111956293278312350069 3473072995902494841782819)
                ·
                  refine ⟨5209609493853742262674229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3473072995902494841782819 5209609493853742262674229)
                  ·
                    refine ⟨488400890048788337125709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5209609493853742262674229 488400890048788337125709)
                    ·
                      rfl

theorem cell23_2853472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 2, 5, 1, 5].length) (baseStart_2853472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2853472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2853472 prefixEnd_2853472 := by exact prefixLift 2853472
  have htrace : WordTrace (prefixWord ++ tailWord_2853472) baseStart_2853472 baseEnd_2853472 := by
    simpa [prefixWord, tailWord_2853472, baseEnd_2853472] using wordTrace_append hprefix tailTrace_2853472
  have hstable : (prefixWord ++ tailWord_2853472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2853472).length < 2 ^ (prefixWord ++ tailWord_2853472).sum := by decide
  have hdescent : baseEnd_2853472 < baseStart_2853472 := by decide
  rcases family_descends (prefixWord ++ tailWord_2853472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2853480 : List Nat := [2, 1, 4, 3, 2, 2, 2, 2, 1, 4]
def baseStart_2853480 : Nat := 118140960795 + 2853480 * 2 ^ 59
def prefixEnd_2853480 : Nat := 4983230072969 + 3 ^ 40 * 2853480 * 2
def baseEnd_2853480 : Nat := 488402259330533660025697

theorem tailTrace_2853480 : CollatzResearch.WordTrace tailWord_2853480 prefixEnd_2853480 488402259330533660025697 := by
  unfold tailWord_2853480
  simp only [CollatzResearch.WordTrace]
  refine ⟨52037482851168385215170947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69383310468224513620227929 52037482851168385215170947)
  ·
    refine ⟨78056224276752577822756421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52037482851168385215170947 78056224276752577822756421)
    ·
      refine ⟨14635542051891108341766829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 78056224276752577822756421 14635542051891108341766829)
      ·
        refine ⟨5488328269459165628162561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14635542051891108341766829 5488328269459165628162561)
        ·
          refine ⟨4116246202094374221121921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5488328269459165628162561 4116246202094374221121921)
          ·
            refine ⟨3087184651570780665841441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4116246202094374221121921 3087184651570780665841441)
            ·
              refine ⟨2315388488678085499381081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3087184651570780665841441 2315388488678085499381081)
              ·
                refine ⟨1736541366508564124535811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2315388488678085499381081 1736541366508564124535811)
                ·
                  refine ⟨2604812049762846186803717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1736541366508564124535811 2604812049762846186803717)
                  ·
                    refine ⟨488402259330533660025697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2604812049762846186803717 488402259330533660025697)
                    ·
                      rfl

theorem cell23_2853480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 2, 2, 2, 1, 4].length) (baseStart_2853480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2853480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2853480 prefixEnd_2853480 := by exact prefixLift 2853480
  have htrace : WordTrace (prefixWord ++ tailWord_2853480) baseStart_2853480 baseEnd_2853480 := by
    simpa [prefixWord, tailWord_2853480, baseEnd_2853480] using wordTrace_append hprefix tailTrace_2853480
  have hstable : (prefixWord ++ tailWord_2853480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2853480).length < 2 ^ (prefixWord ++ tailWord_2853480).sum := by decide
  have hdescent : baseEnd_2853480 < baseStart_2853480 := by decide
  rcases family_descends (prefixWord ++ tailWord_2853480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2853529 : List Nat := [1, 2, 1, 2, 1, 2, 5, 3, 1, 2, 3]
def baseStart_2853529 : Nat := 118140960795 + 2853529 * 2 ^ 59
def prefixEnd_2853529 : Nat := 4983230072969 + 3 ^ 40 * 2853529 * 2
def baseEnd_2853529 : Nat := 1465231938543671288364365

theorem tailTrace_2853529 : CollatzResearch.WordTrace tailWord_2853529 prefixEnd_2853529 1465231938543671288364365 := by
  unfold tailWord_2853529
  simp only [CollatzResearch.WordTrace]
  refine ⟨104076752879159251798875641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69384501919439501199250427 104076752879159251798875641)
  ·
    refine ⟨78057564659369438849156731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104076752879159251798875641 78057564659369438849156731)
    ·
      refine ⟨117086346989054158273735097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78057564659369438849156731 117086346989054158273735097)
      ·
        refine ⟨87814760241790618705301323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 117086346989054158273735097 87814760241790618705301323)
        ·
          refine ⟨131722140362685928057951985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87814760241790618705301323 131722140362685928057951985)
          ·
            refine ⟨98791605272014446043463989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 131722140362685928057951985 98791605272014446043463989)
            ·
              refine ⟨9261712994251354316574749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 98791605272014446043463989 9261712994251354316574749)
              ·
                refine ⟨3473142372844257868715531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9261712994251354316574749 3473142372844257868715531)
                ·
                  refine ⟨5209713559266386803073297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3473142372844257868715531 5209713559266386803073297)
                  ·
                    refine ⟨3907285169449790102304973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5209713559266386803073297 3907285169449790102304973)
                    ·
                      refine ⟨1465231938543671288364365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3907285169449790102304973 1465231938543671288364365)
                      ·
                        rfl

theorem cell23_2853529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 5, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 5, 3, 1, 2, 3].length) (baseStart_2853529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2853529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2853529 prefixEnd_2853529 := by exact prefixLift 2853529
  have htrace : WordTrace (prefixWord ++ tailWord_2853529) baseStart_2853529 baseEnd_2853529 := by
    simpa [prefixWord, tailWord_2853529, baseEnd_2853529] using wordTrace_append hprefix tailTrace_2853529
  have hstable : (prefixWord ++ tailWord_2853529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2853529).length < 2 ^ (prefixWord ++ tailWord_2853529).sum := by decide
  have hdescent : baseEnd_2853529 < baseStart_2853529 := by decide
  rcases family_descends (prefixWord ++ tailWord_2853529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2853532 : List Nat := [2, 2, 3, 2, 2, 2, 10]
def baseStart_2853532 : Nat := 118140960795 + 2853532 * 2 ^ 59
def prefixEnd_2853532 : Nat := 4983230072969 + 3 ^ 40 * 2853532 * 2
def baseEnd_2853532 : Nat := 18089302209699194773171

theorem tailTrace_2853532 : CollatzResearch.WordTrace tailWord_2853532 prefixEnd_2853532 18089302209699194773171 := by
  unfold tailWord_2853532
  simp only [CollatzResearch.WordTrace]
  refine ⟨52038431149074191655617425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69384574865432255540823233 52038431149074191655617425)
  ·
    refine ⟨39028823361805643741713069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52038431149074191655617425 39028823361805643741713069)
    ·
      refine ⟨14635808760677116403142401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39028823361805643741713069 14635808760677116403142401)
      ·
        refine ⟨10976856570507837302356801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14635808760677116403142401 10976856570507837302356801)
        ·
          refine ⟨8232642427880877976767601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10976856570507837302356801 8232642427880877976767601)
          ·
            refine ⟨6174481820910658482575701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8232642427880877976767601 6174481820910658482575701)
            ·
              refine ⟨18089302209699194773171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 6174481820910658482575701 18089302209699194773171)
              ·
                rfl

theorem cell23_2853532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 2, 10].length) (baseStart_2853532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2853532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2853532 prefixEnd_2853532 := by exact prefixLift 2853532
  have htrace : WordTrace (prefixWord ++ tailWord_2853532) baseStart_2853532 baseEnd_2853532 := by
    simpa [prefixWord, tailWord_2853532, baseEnd_2853532] using wordTrace_append hprefix tailTrace_2853532
  have hstable : (prefixWord ++ tailWord_2853532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2853532).length < 2 ^ (prefixWord ++ tailWord_2853532).sum := by decide
  have hdescent : baseEnd_2853532 < baseStart_2853532 := by decide
  rcases family_descends (prefixWord ++ tailWord_2853532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2853553 : List Nat := [1, 2, 2, 6, 2, 1, 1, 1, 1, 6]
def baseStart_2853553 : Nat := 118140960795 + 2853553 * 2 ^ 59
def prefixEnd_2853553 : Nat := 4983230072969 + 3 ^ 40 * 2853553 * 2
def baseEnd_2853553 : Nat := 488414754026459731488085

theorem tailTrace_2853553 : CollatzResearch.WordTrace tailWord_2853553 prefixEnd_2853553 488414754026459731488085 := by
  unfold tailWord_2853553
  simp only [CollatzResearch.WordTrace]
  refine ⟨104077628231072303897749313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69385085487381535931832875 104077628231072303897749313)
  ·
    refine ⟨78058221173304227923311985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104077628231072303897749313 78058221173304227923311985)
    ·
      refine ⟨58543665879978170942483989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78058221173304227923311985 58543665879978170942483989)
      ·
        refine ⟨2744234338123976762928937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 58543665879978170942483989 2744234338123976762928937)
        ·
          refine ⟨2058175753592982572196703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2744234338123976762928937 2058175753592982572196703)
          ·
            refine ⟨3087263630389473858295055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2058175753592982572196703 3087263630389473858295055)
            ·
              refine ⟨4630895445584210787442583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3087263630389473858295055 4630895445584210787442583)
              ·
                refine ⟨6946343168376316181163875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4630895445584210787442583 6946343168376316181163875)
                ·
                  refine ⟨10419514752564474271745813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6946343168376316181163875 10419514752564474271745813)
                  ·
                    refine ⟨488414754026459731488085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10419514752564474271745813 488414754026459731488085)
                    ·
                      rfl

theorem cell23_2853553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 2, 1, 1, 1, 1, 6].length) (baseStart_2853553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2853553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2853553 prefixEnd_2853553 := by exact prefixLift 2853553
  have htrace : WordTrace (prefixWord ++ tailWord_2853553) baseStart_2853553 baseEnd_2853553 := by
    simpa [prefixWord, tailWord_2853553, baseEnd_2853553] using wordTrace_append hprefix tailTrace_2853553
  have hstable : (prefixWord ++ tailWord_2853553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2853553).length < 2 ^ (prefixWord ++ tailWord_2853553).sum := by decide
  have hdescent : baseEnd_2853553 < baseStart_2853553 := by decide
  rcases family_descends (prefixWord ++ tailWord_2853553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2853612 : List Nat := [2, 2, 1, 1, 2, 2, 1, 3, 1, 4, 4]
def baseStart_2853612 : Nat := 118140960795 + 2853612 * 2 ^ 59
def prefixEnd_2853612 : Nat := 4983230072969 + 3 ^ 40 * 2853612 * 2
def baseEnd_2853612 : Nat := 1465274557437994463626483

theorem tailTrace_2853612 : CollatzResearch.WordTrace tailWord_2853612 prefixEnd_2853612 1465274557437994463626483 := by
  unfold tailWord_2853612
  simp only [CollatzResearch.WordTrace]
  refine ⟨52039890068929278487073545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69386520091905704649431393 52039890068929278487073545)
  ·
    refine ⟨39029917551696958865305159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52039890068929278487073545 39029917551696958865305159)
    ·
      refine ⟨58544876327545438297957739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39029917551696958865305159 58544876327545438297957739)
      ·
        refine ⟨87817314491318157446936609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58544876327545438297957739 87817314491318157446936609)
        ·
          refine ⟨65862985868488618085202457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 87817314491318157446936609 65862985868488618085202457)
          ·
            refine ⟨49397239401366463563901843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65862985868488618085202457 49397239401366463563901843)
            ·
              refine ⟨74095859102049695345852765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49397239401366463563901843 74095859102049695345852765)
              ·
                refine ⟨27785947163268635754694787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 74095859102049695345852765 27785947163268635754694787)
                ·
                  refine ⟨41678920744902953632042181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27785947163268635754694787 41678920744902953632042181)
                  ·
                    refine ⟨7814797639669303806007909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 41678920744902953632042181 7814797639669303806007909)
                    ·
                      refine ⟨1465274557437994463626483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7814797639669303806007909 1465274557437994463626483)
                      ·
                        rfl

theorem cell23_2853612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 4, 4].length) (baseStart_2853612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2853612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2853612 prefixEnd_2853612 := by exact prefixLift 2853612
  have htrace : WordTrace (prefixWord ++ tailWord_2853612) baseStart_2853612 baseEnd_2853612 := by
    simpa [prefixWord, tailWord_2853612, baseEnd_2853612] using wordTrace_append hprefix tailTrace_2853612
  have hstable : (prefixWord ++ tailWord_2853612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2853612).length < 2 ^ (prefixWord ++ tailWord_2853612).sum := by decide
  have hdescent : baseEnd_2853612 < baseStart_2853612 := by decide
  rcases family_descends (prefixWord ++ tailWord_2853612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2853666 : List Nat := [3, 3, 1, 1, 2, 3, 1, 1, 2, 3, 3]
def baseStart_2853666 : Nat := 118140960795 + 2853666 * 2 ^ 59
def prefixEnd_2853666 : Nat := 4983230072969 + 3 ^ 40 * 2853666 * 2
def baseEnd_2853666 : Nat := 1465302285393337252351235

theorem tailTrace_2853666 : CollatzResearch.WordTrace tailWord_2853666 prefixEnd_2853666 1465302285393337252351235 := by
  unfold tailWord_2853666
  simp only [CollatzResearch.WordTrace]
  refine ⟨26020437419915731049153213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69387833119775282797741901 26020437419915731049153213)
  ·
    refine ⟨9757664032468399143432455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26020437419915731049153213 9757664032468399143432455)
    ·
      refine ⟨14636496048702598715148683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9757664032468399143432455 14636496048702598715148683)
      ·
        refine ⟨21954744073053898072723025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14636496048702598715148683 21954744073053898072723025)
        ·
          refine ⟨16466058054790423554542269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21954744073053898072723025 16466058054790423554542269)
          ·
            refine ⟨6174771770546408832953351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16466058054790423554542269 6174771770546408832953351)
            ·
              refine ⟨9262157655819613249430027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6174771770546408832953351 9262157655819613249430027)
              ·
                refine ⟨13893236483729419874145041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9262157655819613249430027 13893236483729419874145041)
                ·
                  refine ⟨10419927362797064905608781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13893236483729419874145041 10419927362797064905608781)
                  ·
                    refine ⟨3907472761048899339603293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10419927362797064905608781 3907472761048899339603293)
                    ·
                      refine ⟨1465302285393337252351235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3907472761048899339603293 1465302285393337252351235)
                      ·
                        rfl

theorem cell23_2853666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 3, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 3, 1, 1, 2, 3, 3].length) (baseStart_2853666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2853666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2853666 prefixEnd_2853666 := by exact prefixLift 2853666
  have htrace : WordTrace (prefixWord ++ tailWord_2853666) baseStart_2853666 baseEnd_2853666 := by
    simpa [prefixWord, tailWord_2853666, baseEnd_2853666] using wordTrace_append hprefix tailTrace_2853666
  have hstable : (prefixWord ++ tailWord_2853666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2853666).length < 2 ^ (prefixWord ++ tailWord_2853666).sum := by decide
  have hdescent : baseEnd_2853666 < baseStart_2853666 := by decide
  rcases family_descends (prefixWord ++ tailWord_2853666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2853699 : List Nat := [1, 1, 1, 3, 1, 4, 1, 2, 5, 4]
def baseStart_2853699 : Nat := 118140960795 + 2853699 * 2 ^ 59
def prefixEnd_2853699 : Nat := 4983230072969 + 3 ^ 40 * 2853699 * 2
def baseEnd_2853699 : Nat := 488439743418311874412861

theorem tailTrace_2853699 : CollatzResearch.WordTrace tailWord_2853699 prefixEnd_2853699 488439743418311874412861 := by
  unfold tailWord_2853699
  simp only [CollatzResearch.WordTrace]
  refine ⟨104082953288543370832564151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69388635525695580555042767 104082953288543370832564151)
  ·
    refine ⟨156124429932815056248846227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104082953288543370832564151 156124429932815056248846227)
    ·
      refine ⟨234186644899222584373269341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 156124429932815056248846227 234186644899222584373269341)
      ·
        refine ⟨87819991837208469139976003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 234186644899222584373269341 87819991837208469139976003)
        ·
          refine ⟨131729987755812703709964005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87819991837208469139976003 131729987755812703709964005)
          ·
            refine ⟨24699372704214881945618251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 131729987755812703709964005 24699372704214881945618251)
            ·
              refine ⟨37049059056322322918427377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24699372704214881945618251 37049059056322322918427377)
              ·
                refine ⟨27786794292241742188820533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37049059056322322918427377 27786794292241742188820533)
                ·
                  refine ⟨2605011964897663330201925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 27786794292241742188820533 2605011964897663330201925)
                  ·
                    refine ⟨488439743418311874412861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2605011964897663330201925 488439743418311874412861)
                    ·
                      rfl

theorem cell23_2853699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 1, 2, 5, 4].length) (baseStart_2853699 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2853699 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2853699 prefixEnd_2853699 := by exact prefixLift 2853699
  have htrace : WordTrace (prefixWord ++ tailWord_2853699) baseStart_2853699 baseEnd_2853699 := by
    simpa [prefixWord, tailWord_2853699, baseEnd_2853699] using wordTrace_append hprefix tailTrace_2853699
  have hstable : (prefixWord ++ tailWord_2853699).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2853699).length < 2 ^ (prefixWord ++ tailWord_2853699).sum := by decide
  have hdescent : baseEnd_2853699 < baseStart_2853699 := by decide
  rcases family_descends (prefixWord ++ tailWord_2853699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2853756 : List Nat := [2, 2, 2, 1, 1, 1, 1, 4, 5, 1, 3]
def baseStart_2853756 : Nat := 118140960795 + 2853756 * 2 ^ 59
def prefixEnd_2853756 : Nat := 4983230072969 + 3 ^ 40 * 2853756 * 2
def baseEnd_2853756 : Nat := 1465348498652241900225821

theorem tailTrace_2853756 : CollatzResearch.WordTrace tailWord_2853756 prefixEnd_2853756 1465348498652241900225821 := by
  unfold tailWord_2853756
  simp only [CollatzResearch.WordTrace]
  refine ⟨52042516124668434783694561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69390021499557913044926081 52042516124668434783694561)
  ·
    refine ⟨39031887093501326087770921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52042516124668434783694561 39031887093501326087770921)
    ·
      refine ⟨29273915320125994565828191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39031887093501326087770921 29273915320125994565828191)
      ·
        refine ⟨43910872980188991848742287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29273915320125994565828191 43910872980188991848742287)
        ·
          refine ⟨65866309470283487773113431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43910872980188991848742287 65866309470283487773113431)
          ·
            refine ⟨98799464205425231659670147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65866309470283487773113431 98799464205425231659670147)
            ·
              refine ⟨148199196308137847489505221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 98799464205425231659670147 148199196308137847489505221)
              ·
                refine ⟨27787349307775846404282229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 148199196308137847489505221 27787349307775846404282229)
                ·
                  refine ⟨2605063997603985600401459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 27787349307775846404282229 2605063997603985600401459)
                  ·
                    refine ⟨3907595996405978400602189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2605063997603985600401459 3907595996405978400602189)
                    ·
                      refine ⟨1465348498652241900225821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3907595996405978400602189 1465348498652241900225821)
                      ·
                        rfl

theorem cell23_2853756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 4, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 4, 5, 1, 3].length) (baseStart_2853756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2853756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2853756 prefixEnd_2853756 := by exact prefixLift 2853756
  have htrace : WordTrace (prefixWord ++ tailWord_2853756) baseStart_2853756 baseEnd_2853756 := by
    simpa [prefixWord, tailWord_2853756, baseEnd_2853756] using wordTrace_append hprefix tailTrace_2853756
  have hstable : (prefixWord ++ tailWord_2853756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2853756).length < 2 ^ (prefixWord ++ tailWord_2853756).sum := by decide
  have hdescent : baseEnd_2853756 < baseStart_2853756 := by decide
  rcases family_descends (prefixWord ++ tailWord_2853756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2853793 : List Nat := [1, 2, 3, 4, 1, 1, 3, 2, 1, 5]
def baseStart_2853793 : Nat := 118140960795 + 2853793 * 2 ^ 59
def prefixEnd_2853793 : Nat := 4983230072969 + 3 ^ 40 * 2853793 * 2
def baseEnd_2853793 : Nat := 488455832478819418487717

theorem tailTrace_2853793 : CollatzResearch.WordTrace tailWord_2853793 prefixEnd_2853793 488455832478819418487717 := by
  unfold tailWord_2853793
  simp only [CollatzResearch.WordTrace]
  refine ⟨104086381750202824886486033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69390921166801883257657355 104086381750202824886486033)
  ·
    refine ⟨78064786312652118664864525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104086381750202824886486033 78064786312652118664864525)
    ·
      refine ⟨29274294867244544499324197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 78064786312652118664864525 29274294867244544499324197)
      ·
        refine ⟨5488930287608352093623287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 29274294867244544499324197 5488930287608352093623287)
        ·
          refine ⟨8233395431412528140434931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5488930287608352093623287 8233395431412528140434931)
          ·
            refine ⟨12350093147118792210652397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8233395431412528140434931 12350093147118792210652397)
            ·
              refine ⟨4631284930169547078994649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12350093147118792210652397 4631284930169547078994649)
              ·
                refine ⟨3473463697627160309245987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4631284930169547078994649 3473463697627160309245987)
                ·
                  refine ⟨5210195546440740463868981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3473463697627160309245987 5210195546440740463868981)
                  ·
                    refine ⟨488455832478819418487717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5210195546440740463868981 488455832478819418487717)
                    ·
                      rfl

theorem cell23_2853793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 3, 2, 1, 5].length) (baseStart_2853793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2853793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2853793 prefixEnd_2853793 := by exact prefixLift 2853793
  have htrace : WordTrace (prefixWord ++ tailWord_2853793) baseStart_2853793 baseEnd_2853793 := by
    simpa [prefixWord, tailWord_2853793, baseEnd_2853793] using wordTrace_append hprefix tailTrace_2853793
  have hstable : (prefixWord ++ tailWord_2853793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2853793).length < 2 ^ (prefixWord ++ tailWord_2853793).sum := by decide
  have hdescent : baseEnd_2853793 < baseStart_2853793 := by decide
  rcases family_descends (prefixWord ++ tailWord_2853793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2853796 : List Nat := [2, 3, 1, 2, 1, 2, 3, 1, 3, 1, 4]
def baseStart_2853796 : Nat := 118140960795 + 2853796 * 2 ^ 59
def prefixEnd_2853796 : Nat := 4983230072969 + 3 ^ 40 * 2853796 * 2
def baseEnd_2853796 : Nat := 1465369037878421743725637

theorem tailTrace_2853796 : CollatzResearch.WordTrace tailWord_2853796 prefixEnd_2853796 1465369037878421743725637 := by
  unfold tailWord_2853796
  simp only [CollatzResearch.WordTrace]
  refine ⟨52043245584595978199422621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69390994112794637599230161 52043245584595978199422621)
  ·
    refine ⟨19516217094223491824783483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52043245584595978199422621 19516217094223491824783483)
    ·
      refine ⟨29274325641335237737175225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19516217094223491824783483 29274325641335237737175225)
      ·
        refine ⟨21955744231001428302881419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29274325641335237737175225 21955744231001428302881419)
        ·
          refine ⟨32933616346502142454322129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21955744231001428302881419 32933616346502142454322129)
          ·
            refine ⟨24700212259876606840741597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32933616346502142454322129 24700212259876606840741597)
            ·
              refine ⟨9262579597453727565278099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24700212259876606840741597 9262579597453727565278099)
              ·
                refine ⟨13893869396180591347917149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9262579597453727565278099 13893869396180591347917149)
                ·
                  refine ⟨5210201023567721755468931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13893869396180591347917149 5210201023567721755468931)
                  ·
                    refine ⟨7815301535351582633203397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5210201023567721755468931 7815301535351582633203397)
                    ·
                      refine ⟨1465369037878421743725637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7815301535351582633203397 1465369037878421743725637)
                      ·
                        rfl

theorem cell23_2853796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 3, 1, 3, 1, 4].length) (baseStart_2853796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2853796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2853796 prefixEnd_2853796 := by exact prefixLift 2853796
  have htrace : WordTrace (prefixWord ++ tailWord_2853796) baseStart_2853796 baseEnd_2853796 := by
    simpa [prefixWord, tailWord_2853796, baseEnd_2853796] using wordTrace_append hprefix tailTrace_2853796
  have hstable : (prefixWord ++ tailWord_2853796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2853796).length < 2 ^ (prefixWord ++ tailWord_2853796).sum := by decide
  have hdescent : baseEnd_2853796 < baseStart_2853796 := by decide
  rcases family_descends (prefixWord ++ tailWord_2853796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2853816 : List Nat := [2, 1, 2, 1, 2, 4, 3, 1, 1, 1, 5]
def baseStart_2853816 : Nat := 118140960795 + 2853816 * 2 ^ 59
def prefixEnd_2853816 : Nat := 4983230072969 + 3 ^ 40 * 2853816 * 2
def baseEnd_2853816 : Nat := 1465379307491511665475545

theorem tailTrace_2853816 : CollatzResearch.WordTrace tailWord_2853816 prefixEnd_2853816 1465379307491511665475545 := by
  unfold tailWord_2853816
  simp only [CollatzResearch.WordTrace]
  refine ⟨52043610314559749907286651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69391480419412999876382201 52043610314559749907286651)
  ·
    refine ⟨78065415471839624860929977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52043610314559749907286651 78065415471839624860929977)
    ·
      refine ⟨58549061603879718645697483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78065415471839624860929977 58549061603879718645697483)
      ·
        refine ⟨87823592405819577968546225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58549061603879718645697483 87823592405819577968546225)
        ·
          refine ⟨65867694304364683476409669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 87823592405819577968546225 65867694304364683476409669)
          ·
            refine ⟨12350192682068378151826813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 65867694304364683476409669 12350192682068378151826813)
            ·
              refine ⟨4631322255775641806935055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12350192682068378151826813 4631322255775641806935055)
              ·
                refine ⟨6946983383663462710402583, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4631322255775641806935055 6946983383663462710402583)
                ·
                  refine ⟨10420475075495194065603875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6946983383663462710402583 10420475075495194065603875)
                  ·
                    refine ⟨15630712613242791098405813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10420475075495194065603875 15630712613242791098405813)
                    ·
                      refine ⟨1465379307491511665475545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15630712613242791098405813 1465379307491511665475545)
                      ·
                        rfl

theorem cell23_2853816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 3, 1, 1, 1, 5].length) (baseStart_2853816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2853816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2853816 prefixEnd_2853816 := by exact prefixLift 2853816
  have htrace : WordTrace (prefixWord ++ tailWord_2853816) baseStart_2853816 baseEnd_2853816 := by
    simpa [prefixWord, tailWord_2853816, baseEnd_2853816] using wordTrace_append hprefix tailTrace_2853816
  have hstable : (prefixWord ++ tailWord_2853816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2853816).length < 2 ^ (prefixWord ++ tailWord_2853816).sum := by decide
  have hdescent : baseEnd_2853816 < baseStart_2853816 := by decide
  rcases family_descends (prefixWord ++ tailWord_2853816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2853853 : List Nat := [1, 4, 3, 1, 2, 2, 3, 7]
def baseStart_2853853 : Nat := 118140960795 + 2853853 * 2 ^ 59
def prefixEnd_2853853 : Nat := 4983230072969 + 3 ^ 40 * 2853853 * 2
def baseEnd_2853853 : Nat := 54274011343545482248625

theorem tailTrace_2853853 : CollatzResearch.WordTrace tailWord_2853853 prefixEnd_2853853 54274011343545482248625 := by
  unfold tailWord_2853853
  simp only [CollatzResearch.WordTrace]
  refine ⟨104088570129985455133670213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69392380086656970089113475 104088570129985455133670213)
  ·
    refine ⟨19516606899372272837563165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 104088570129985455133670213 19516606899372272837563165)
    ·
      refine ⟨7318727587264602314086187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19516606899372272837563165 7318727587264602314086187)
      ·
        refine ⟨10978091380896903471129281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7318727587264602314086187 10978091380896903471129281)
        ·
          refine ⟨8233568535672677603346961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10978091380896903471129281 8233568535672677603346961)
          ·
            refine ⟨6175176401754508202510221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8233568535672677603346961 6175176401754508202510221)
            ·
              refine ⟨2315691150657940575941333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6175176401754508202510221 2315691150657940575941333)
              ·
                refine ⟨54274011343545482248625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2315691150657940575941333 54274011343545482248625)
                ·
                  rfl

theorem cell23_2853853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 2, 3, 7].length) (baseStart_2853853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2853853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2853853 prefixEnd_2853853 := by exact prefixLift 2853853
  have htrace : WordTrace (prefixWord ++ tailWord_2853853) baseStart_2853853 baseEnd_2853853 := by
    simpa [prefixWord, tailWord_2853853, baseEnd_2853853] using wordTrace_append hprefix tailTrace_2853853
  have hstable : (prefixWord ++ tailWord_2853853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2853853).length < 2 ^ (prefixWord ++ tailWord_2853853).sum := by decide
  have hdescent : baseEnd_2853853 < baseStart_2853853 := by decide
  rcases family_descends (prefixWord ++ tailWord_2853853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2853863 : List Nat := [1, 1, 5, 2, 2, 1, 2, 2, 1, 3, 3]
def baseStart_2853863 : Nat := 118140960795 + 2853863 * 2 ^ 59
def prefixEnd_2853863 : Nat := 4983230072969 + 3 ^ 40 * 2853863 * 2
def baseEnd_2853863 : Nat := 1465403441082272981587829

theorem tailTrace_2853863 : CollatzResearch.WordTrace tailWord_2853863 prefixEnd_2853863 1465403441082272981587829 := by
  unfold tailWord_2853863
  simp only [CollatzResearch.WordTrace]
  refine ⟨104088934859949226841534243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69392623239966151227689495 104088934859949226841534243)
  ·
    refine ⟨156133402289923840262301365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104088934859949226841534243 156133402289923840262301365)
    ·
      refine ⟨14637506464680360024590753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 156133402289923840262301365 14637506464680360024590753)
      ·
        refine ⟨10978129848510270018443065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14637506464680360024590753 10978129848510270018443065)
        ·
          refine ⟨8233597386382702513832299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10978129848510270018443065 8233597386382702513832299)
          ·
            refine ⟨12350396079574053770748449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8233597386382702513832299 12350396079574053770748449)
            ·
              refine ⟨9262797059680540328061337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12350396079574053770748449 9262797059680540328061337)
              ·
                refine ⟨6947097794760405246046003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9262797059680540328061337 6947097794760405246046003)
                ·
                  refine ⟨10420646692140607869069005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6947097794760405246046003 10420646692140607869069005)
                  ·
                    refine ⟨3907742509552727950900877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10420646692140607869069005 3907742509552727950900877)
                    ·
                      refine ⟨1465403441082272981587829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3907742509552727950900877 1465403441082272981587829)
                      ·
                        rfl

theorem cell23_2853863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 2, 2, 1, 3, 3].length) (baseStart_2853863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2853863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2853863 prefixEnd_2853863 := by exact prefixLift 2853863
  have htrace : WordTrace (prefixWord ++ tailWord_2853863) baseStart_2853863 baseEnd_2853863 := by
    simpa [prefixWord, tailWord_2853863, baseEnd_2853863] using wordTrace_append hprefix tailTrace_2853863
  have hstable : (prefixWord ++ tailWord_2853863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2853863).length < 2 ^ (prefixWord ++ tailWord_2853863).sum := by decide
  have hdescent : baseEnd_2853863 < baseStart_2853863 := by decide
  rcases family_descends (prefixWord ++ tailWord_2853863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2853874 : List Nat := [3, 2, 1, 5, 2, 1, 1, 2, 2, 4]
def baseStart_2853874 : Nat := 118140960795 + 2853874 * 2 ^ 59
def prefixEnd_2853874 : Nat := 4983230072969 + 3 ^ 40 * 2853874 * 2
def baseEnd_2853874 : Nat := 488469696456490812850093

theorem tailTrace_2853874 : CollatzResearch.WordTrace tailWord_2853874 prefixEnd_2853874 488469696456490812850093 := by
  unfold tailWord_2853874
  simp only [CollatzResearch.WordTrace]
  refine ⟨26022334015727343930046169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69392890708606250480123117 26022334015727343930046169)
  ·
    refine ⟨19516750511795507947534627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26022334015727343930046169 19516750511795507947534627)
    ·
      refine ⟨29275125767693261921301941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19516750511795507947534627 29275125767693261921301941)
      ·
        refine ⟨2744543040721243305122057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 29275125767693261921301941 2744543040721243305122057)
        ·
          refine ⟨2058407280540932478841543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2744543040721243305122057 2058407280540932478841543)
          ·
            refine ⟨3087610920811398718262315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2058407280540932478841543 3087610920811398718262315)
            ·
              refine ⟨4631416381217098077393473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3087610920811398718262315 4631416381217098077393473)
              ·
                refine ⟨3473562285912823558045105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4631416381217098077393473 3473562285912823558045105)
                ·
                  refine ⟨2605171714434617668533829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3473562285912823558045105 2605171714434617668533829)
                  ·
                    refine ⟨488469696456490812850093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2605171714434617668533829 488469696456490812850093)
                    ·
                      rfl

theorem cell23_2853874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 2, 1, 1, 2, 2, 4].length) (baseStart_2853874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2853874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2853874 prefixEnd_2853874 := by exact prefixLift 2853874
  have htrace : WordTrace (prefixWord ++ tailWord_2853874) baseStart_2853874 baseEnd_2853874 := by
    simpa [prefixWord, tailWord_2853874, baseEnd_2853874] using wordTrace_append hprefix tailTrace_2853874
  have hstable : (prefixWord ++ tailWord_2853874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2853874).length < 2 ^ (prefixWord ++ tailWord_2853874).sum := by decide
  have hdescent : baseEnd_2853874 < baseStart_2853874 := by decide
  rcases family_descends (prefixWord ++ tailWord_2853874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2853896 : List Nat := [2, 1, 3, 2, 1, 3, 2, 1, 2, 6]
def baseStart_2853896 : Nat := 118140960795 + 2853896 * 2 ^ 59
def prefixEnd_2853896 : Nat := 4983230072969 + 3 ^ 40 * 2853896 * 2
def baseEnd_2853896 : Nat := 488473461981290450825059

theorem tailTrace_2853896 : CollatzResearch.WordTrace tailWord_2853896 prefixEnd_2853896 488473461981290450825059 := by
  unfold tailWord_2853896
  simp only [CollatzResearch.WordTrace]
  refine ⟨52045069234414836738742771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69393425645886448984990361 52045069234414836738742771)
  ·
    refine ⟨78067603851622255108114157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52045069234414836738742771 78067603851622255108114157)
    ·
      refine ⟨29275351444358345665542809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 78067603851622255108114157 29275351444358345665542809)
      ·
        refine ⟨21956513583268759249157107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29275351444358345665542809 21956513583268759249157107)
        ·
          refine ⟨32934770374903138873735661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21956513583268759249157107 32934770374903138873735661)
          ·
            refine ⟨12350538890588677077650873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32934770374903138873735661 12350538890588677077650873)
            ·
              refine ⟨9262904167941507808238155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12350538890588677077650873 9262904167941507808238155)
              ·
                refine ⟨13894356251912261712357233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9262904167941507808238155 13894356251912261712357233)
                ·
                  refine ⟨10420767188934196284267925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13894356251912261712357233 10420767188934196284267925)
                  ·
                    refine ⟨488473461981290450825059, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10420767188934196284267925 488473461981290450825059)
                    ·
                      rfl

theorem cell23_2853896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 2, 1, 2, 6].length) (baseStart_2853896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2853896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2853896 prefixEnd_2853896 := by exact prefixLift 2853896
  have htrace : WordTrace (prefixWord ++ tailWord_2853896) baseStart_2853896 baseEnd_2853896 := by
    simpa [prefixWord, tailWord_2853896, baseEnd_2853896] using wordTrace_append hprefix tailTrace_2853896
  have hstable : (prefixWord ++ tailWord_2853896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2853896).length < 2 ^ (prefixWord ++ tailWord_2853896).sum := by decide
  have hdescent : baseEnd_2853896 < baseStart_2853896 := by decide
  rcases family_descends (prefixWord ++ tailWord_2853896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2853966 : List Nat := [4, 1, 1, 1, 1, 3, 1, 2, 1, 1, 7]
def baseStart_2853966 : Nat := 118140960795 + 2853966 * 2 ^ 59
def prefixEnd_2853966 : Nat := 4983230072969 + 3 ^ 40 * 2853966 * 2
def baseEnd_2853966 : Nat := 1465456329589686078599855

theorem tailTrace_2853966 : CollatzResearch.WordTrace tailWord_2853966 prefixEnd_2853966 1465456329589686078599855 := by
  unfold tailWord_2853966
  simp only [CollatzResearch.WordTrace]
  refine ⟨13011586447322009429066719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 69395127719050716955022501 13011586447322009429066719)
  ·
    refine ⟨19517379670983014143600079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13011586447322009429066719 19517379670983014143600079)
    ·
      refine ⟨29276069506474521215400119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19517379670983014143600079 29276069506474521215400119)
      ·
        refine ⟨43914104259711781823100179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29276069506474521215400119 43914104259711781823100179)
        ·
          refine ⟨65871156389567672734650269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43914104259711781823100179 65871156389567672734650269)
          ·
            refine ⟨24701683646087877275493851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 65871156389567672734650269 24701683646087877275493851)
            ·
              refine ⟨37052525469131815913240777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24701683646087877275493851 37052525469131815913240777)
              ·
                refine ⟨27789394101848861934930583, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37052525469131815913240777 27789394101848861934930583)
                ·
                  refine ⟨41684091152773292902395875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27789394101848861934930583 41684091152773292902395875)
                  ·
                    refine ⟨62526136729159939353593813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 41684091152773292902395875 62526136729159939353593813)
                    ·
                      refine ⟨1465456329589686078599855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 62526136729159939353593813 1465456329589686078599855)
                      ·
                        rfl

theorem cell23_2853966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 1, 2, 1, 1, 7].length) (baseStart_2853966 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2853966 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2853966 prefixEnd_2853966 := by exact prefixLift 2853966
  have htrace : WordTrace (prefixWord ++ tailWord_2853966) baseStart_2853966 baseEnd_2853966 := by
    simpa [prefixWord, tailWord_2853966, baseEnd_2853966] using wordTrace_append hprefix tailTrace_2853966
  have hstable : (prefixWord ++ tailWord_2853966).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2853966).length < 2 ^ (prefixWord ++ tailWord_2853966).sum := by decide
  have hdescent : baseEnd_2853966 < baseStart_2853966 := by decide
  rcases family_descends (prefixWord ++ tailWord_2853966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2853973 : List Nat := [1, 3, 2, 2, 1, 2, 4, 1, 2, 5]
def baseStart_2853973 : Nat := 118140960795 + 2853973 * 2 ^ 59
def prefixEnd_2853973 : Nat := 4983230072969 + 3 ^ 40 * 2853973 * 2
def baseEnd_2853973 : Nat := 488486641318089183737441

theorem tailTrace_2853973 : CollatzResearch.WordTrace tailWord_2853973 prefixEnd_2853973 488486641318089183737441 := by
  unfold tailWord_2853973
  simp only [CollatzResearch.WordTrace]
  refine ⟨104092946889550715628038573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69395297926367143752025715 104092946889550715628038573)
  ·
    refine ⟨39034855083581518360514465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 104092946889550715628038573 39034855083581518360514465)
    ·
      refine ⟨29276141312686138770385849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39034855083581518360514465 29276141312686138770385849)
      ·
        refine ⟨21957105984514604077789387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29276141312686138770385849 21957105984514604077789387)
        ·
          refine ⟨32935658976771906116684081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21957105984514604077789387 32935658976771906116684081)
          ·
            refine ⟨24701744232578929587513061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32935658976771906116684081 24701744232578929587513061)
            ·
              refine ⟨4631577043608549297658699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24701744232578929587513061 4631577043608549297658699)
              ·
                refine ⟨6947365565412823946488049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4631577043608549297658699 6947365565412823946488049)
                ·
                  refine ⟨5210524174059617959866037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6947365565412823946488049 5210524174059617959866037)
                  ·
                    refine ⟨488486641318089183737441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5210524174059617959866037 488486641318089183737441)
                    ·
                      rfl

theorem cell23_2853973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 4, 1, 2, 5].length) (baseStart_2853973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2853973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2853973 prefixEnd_2853973 := by exact prefixLift 2853973
  have htrace : WordTrace (prefixWord ++ tailWord_2853973) baseStart_2853973 baseEnd_2853973 := by
    simpa [prefixWord, tailWord_2853973, baseEnd_2853973] using wordTrace_append hprefix tailTrace_2853973
  have hstable : (prefixWord ++ tailWord_2853973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2853973).length < 2 ^ (prefixWord ++ tailWord_2853973).sum := by decide
  have hdescent : baseEnd_2853973 < baseStart_2853973 := by decide
  rcases family_descends (prefixWord ++ tailWord_2853973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2853993 : List Nat := [1, 2, 1, 1, 1, 6, 2, 2, 2, 1, 4]
def baseStart_2853993 : Nat := 118140960795 + 2853993 * 2 ^ 59
def prefixEnd_2853993 : Nat := 4983230072969 + 3 ^ 40 * 2853993 * 2
def baseEnd_2853993 : Nat := 1465470193567357472962231

theorem tailTrace_2853993 : CollatzResearch.WordTrace tailWord_2853993 prefixEnd_2853993 1465470193567357472962231 := by
  unfold tailWord_2853993
  simp only [CollatzResearch.WordTrace]
  refine ⟨104093676349478259043766633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69395784232985506029177755 104093676349478259043766633)
  ·
    refine ⟨78070257262108694282824975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104093676349478259043766633 78070257262108694282824975)
    ·
      refine ⟨117105385893163041424237463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78070257262108694282824975 117105385893163041424237463)
      ·
        refine ⟨175658078839744562136356195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117105385893163041424237463 175658078839744562136356195)
        ·
          refine ⟨263487118259616843204534293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 175658078839744562136356195 263487118259616843204534293)
          ·
            refine ⟨12350958668419539525212545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 263487118259616843204534293 12350958668419539525212545)
            ·
              refine ⟨9263219001314654643909409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12350958668419539525212545 9263219001314654643909409)
              ·
                refine ⟨6947414250985990982932057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9263219001314654643909409 6947414250985990982932057)
                ·
                  refine ⟨5210560688239493237199043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6947414250985990982932057 5210560688239493237199043)
                  ·
                    refine ⟨7815841032359239855798565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5210560688239493237199043 7815841032359239855798565)
                    ·
                      refine ⟨1465470193567357472962231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7815841032359239855798565 1465470193567357472962231)
                      ·
                        rfl

theorem cell23_2853993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 2, 2, 2, 1, 4].length) (baseStart_2853993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2853993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2853993 prefixEnd_2853993 := by exact prefixLift 2853993
  have htrace : WordTrace (prefixWord ++ tailWord_2853993) baseStart_2853993 baseEnd_2853993 := by
    simpa [prefixWord, tailWord_2853993, baseEnd_2853993] using wordTrace_append hprefix tailTrace_2853993
  have hstable : (prefixWord ++ tailWord_2853993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2853993).length < 2 ^ (prefixWord ++ tailWord_2853993).sum := by decide
  have hdescent : baseEnd_2853993 < baseStart_2853993 := by decide
  rcases family_descends (prefixWord ++ tailWord_2853993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2853996 : List Nat := [2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 5]
def baseStart_2853996 : Nat := 118140960795 + 2853996 * 2 ^ 59
def prefixEnd_2853996 : Nat := 4983230072969 + 3 ^ 40 * 2853996 * 2
def baseEnd_2853996 : Nat := 1465471734009320961224717

theorem tailTrace_2853996 : CollatzResearch.WordTrace tailWord_2853996 prefixEnd_2853996 1465471734009320961224717 := by
  unfold tailWord_2853996
  simp only [CollatzResearch.WordTrace]
  refine ⟨52046892884233695278062921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69395857178978260370750561 52046892884233695278062921)
  ·
    refine ⟨39035169663175271458547191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52046892884233695278062921 39035169663175271458547191)
    ·
      refine ⟨58552754494762907187820787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39035169663175271458547191 58552754494762907187820787)
      ·
        refine ⟨87829131742144360781731181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58552754494762907187820787 87829131742144360781731181)
        ·
          refine ⟨32935924403304135293149193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 87829131742144360781731181 32935924403304135293149193)
          ·
            refine ⟨24701943302478101469861895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32935924403304135293149193 24701943302478101469861895)
            ·
              refine ⟨37052914953717152204792843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24701943302478101469861895 37052914953717152204792843)
              ·
                refine ⟨55579372430575728307189265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37052914953717152204792843 55579372430575728307189265)
                ·
                  refine ⟨41684529322931796230391949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 55579372430575728307189265 41684529322931796230391949)
                  ·
                    refine ⟨15631698496099423586396981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 41684529322931796230391949 15631698496099423586396981)
                    ·
                      refine ⟨1465471734009320961224717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15631698496099423586396981 1465471734009320961224717)
                      ·
                        rfl

theorem cell23_2853996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 5].length) (baseStart_2853996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2853996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2853996 prefixEnd_2853996 := by exact prefixLift 2853996
  have htrace : WordTrace (prefixWord ++ tailWord_2853996) baseStart_2853996 baseEnd_2853996 := by
    simpa [prefixWord, tailWord_2853996, baseEnd_2853996] using wordTrace_append hprefix tailTrace_2853996
  have hstable : (prefixWord ++ tailWord_2853996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2853996).length < 2 ^ (prefixWord ++ tailWord_2853996).sum := by decide
  have hdescent : baseEnd_2853996 < baseStart_2853996 := by decide
  rcases family_descends (prefixWord ++ tailWord_2853996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2854013 : List Nat := [1, 4, 1, 1, 3, 1, 2, 2, 1, 4, 3]
def baseStart_2854013 : Nat := 118140960795 + 2854013 * 2 ^ 59
def prefixEnd_2854013 : Nat := 4983230072969 + 3 ^ 40 * 2854013 * 2
def baseEnd_2854013 : Nat := 1465480463180447394712139

theorem tailTrace_2854013 : CollatzResearch.WordTrace tailWord_2854013 prefixEnd_2854013 1465480463180447394712139 := by
  unfold tailWord_2854013
  simp only [CollatzResearch.WordTrace]
  refine ⟨104094405809405802459494693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69396270539603868306329795 104094405809405802459494693)
  ·
    refine ⟨19517701089263587961155255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 104094405809405802459494693 19517701089263587961155255)
    ·
      refine ⟨29276551633895381941732883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19517701089263587961155255 29276551633895381941732883)
      ·
        refine ⟨43914827450843072912599325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29276551633895381941732883 43914827450843072912599325)
        ·
          refine ⟨16468060294066152342224747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43914827450843072912599325 16468060294066152342224747)
          ·
            refine ⟨24702090441099228513337121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16468060294066152342224747 24702090441099228513337121)
            ·
              refine ⟨18526567830824421385002841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24702090441099228513337121 18526567830824421385002841)
              ·
                refine ⟨13894925873118316038752131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18526567830824421385002841 13894925873118316038752131)
                ·
                  refine ⟨20842388809677474058128197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13894925873118316038752131 20842388809677474058128197)
                  ·
                    refine ⟨3907947901814526385899037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20842388809677474058128197 3907947901814526385899037)
                    ·
                      refine ⟨1465480463180447394712139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3907947901814526385899037 1465480463180447394712139)
                      ·
                        rfl

theorem cell23_2854013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 2, 2, 1, 4, 3].length) (baseStart_2854013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2854013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2854013 prefixEnd_2854013 := by exact prefixLift 2854013
  have htrace : WordTrace (prefixWord ++ tailWord_2854013) baseStart_2854013 baseEnd_2854013 := by
    simpa [prefixWord, tailWord_2854013, baseEnd_2854013] using wordTrace_append hprefix tailTrace_2854013
  have hstable : (prefixWord ++ tailWord_2854013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2854013).length < 2 ^ (prefixWord ++ tailWord_2854013).sum := by decide
  have hdescent : baseEnd_2854013 < baseStart_2854013 := by decide
  rcases family_descends (prefixWord ++ tailWord_2854013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2854020 : List Nat := [2, 3, 2, 1, 2, 3, 1, 2, 3, 4]
def baseStart_2854020 : Nat := 118140960795 + 2854020 * 2 ^ 59
def prefixEnd_2854020 : Nat := 4983230072969 + 3 ^ 40 * 2854020 * 2
def baseEnd_2854020 : Nat := 488494685848342955774869

theorem tailTrace_2854020 : CollatzResearch.WordTrace tailWord_2854020 prefixEnd_2854020 488494685848342955774869 := by
  unfold tailWord_2854020
  simp only [CollatzResearch.WordTrace]
  refine ⟨52047330560190221327499757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69396440746920295103333009 52047330560190221327499757)
  ·
    refine ⟨19517748960071332997812409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52047330560190221327499757 19517748960071332997812409)
    ·
      refine ⟨14638311720053499748359307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19517748960071332997812409 14638311720053499748359307)
      ·
        refine ⟨21957467580080249622538961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14638311720053499748359307 21957467580080249622538961)
        ·
          refine ⟨16468100685060187216904221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21957467580080249622538961 16468100685060187216904221)
          ·
            refine ⟨6175537756897570206339083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16468100685060187216904221 6175537756897570206339083)
            ·
              refine ⟨9263306635346355309508625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6175537756897570206339083 9263306635346355309508625)
              ·
                refine ⟨6947479976509766482131469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9263306635346355309508625 6947479976509766482131469)
                ·
                  refine ⟨2605304991191162430799301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6947479976509766482131469 2605304991191162430799301)
                  ·
                    refine ⟨488494685848342955774869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2605304991191162430799301 488494685848342955774869)
                    ·
                      rfl

theorem cell23_2854020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 3, 1, 2, 3, 4].length) (baseStart_2854020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2854020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2854020 prefixEnd_2854020 := by exact prefixLift 2854020
  have htrace : WordTrace (prefixWord ++ tailWord_2854020) baseStart_2854020 baseEnd_2854020 := by
    simpa [prefixWord, tailWord_2854020, baseEnd_2854020] using wordTrace_append hprefix tailTrace_2854020
  have hstable : (prefixWord ++ tailWord_2854020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2854020).length < 2 ^ (prefixWord ++ tailWord_2854020).sum := by decide
  have hdescent : baseEnd_2854020 < baseStart_2854020 := by decide
  rcases family_descends (prefixWord ++ tailWord_2854020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2854030 : List Nat := [4, 1, 1, 3, 2, 2, 1, 1, 1, 4, 3]
def baseStart_2854030 : Nat := 118140960795 + 2854030 * 2 ^ 59
def prefixEnd_2854030 : Nat := 4983230072969 + 3 ^ 40 * 2854030 * 2
def baseEnd_2854030 : Nat := 1465489192351573828199561

theorem tailTrace_2854030 : CollatzResearch.WordTrace tailWord_2854030 prefixEnd_2854030 1465489192351573828199561 := by
  unfold tailWord_2854030
  simp only [CollatzResearch.WordTrace]
  refine ⟨13011878231293026795357943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 69396683900229476241909029 13011878231293026795357943)
  ·
    refine ⟨19517817346939540193036915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13011878231293026795357943 19517817346939540193036915)
    ·
      refine ⟨29276726020409310289555373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19517817346939540193036915 29276726020409310289555373)
      ·
        refine ⟨10978772257653491358583265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29276726020409310289555373 10978772257653491358583265)
        ·
          refine ⟨8234079193240118518937449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10978772257653491358583265 8234079193240118518937449)
          ·
            refine ⟨6175559394930088889203087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8234079193240118518937449 6175559394930088889203087)
            ·
              refine ⟨9263339092395133333804631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6175559394930088889203087 9263339092395133333804631)
              ·
                refine ⟨13895008638592700000706947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9263339092395133333804631 13895008638592700000706947)
                ·
                  refine ⟨20842512957889050001060421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13895008638592700000706947 20842512957889050001060421)
                  ·
                    refine ⟨3907971179604196875198829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20842512957889050001060421 3907971179604196875198829)
                    ·
                      refine ⟨1465489192351573828199561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3907971179604196875198829 1465489192351573828199561)
                      ·
                        rfl

theorem cell23_2854030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 2, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 2, 1, 1, 1, 4, 3].length) (baseStart_2854030 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2854030 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2854030 prefixEnd_2854030 := by exact prefixLift 2854030
  have htrace : WordTrace (prefixWord ++ tailWord_2854030) baseStart_2854030 baseEnd_2854030 := by
    simpa [prefixWord, tailWord_2854030, baseEnd_2854030] using wordTrace_append hprefix tailTrace_2854030
  have hstable : (prefixWord ++ tailWord_2854030).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2854030).length < 2 ^ (prefixWord ++ tailWord_2854030).sum := by decide
  have hdescent : baseEnd_2854030 < baseStart_2854030 := by decide
  rcases family_descends (prefixWord ++ tailWord_2854030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2854050 : List Nat := [3, 3, 1, 3, 2, 1, 1, 1, 8]
def baseStart_2854050 : Nat := 118140960795 + 2854050 * 2 ^ 59
def prefixEnd_2854050 : Nat := 4983230072969 + 3 ^ 40 * 2854050 * 2
def baseEnd_2854050 : Nat := 162833273551629305549941

theorem tailTrace_2854050 : CollatzResearch.WordTrace tailWord_2854050 prefixEnd_2854050 162833273551629305549941 := by
  unfold tailWord_2854050
  simp only [CollatzResearch.WordTrace]
  refine ⟨26023938827567939444647901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69397170206847838519061069 26023938827567939444647901)
  ·
    refine ⟨9758977060337977291742963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26023938827567939444647901 9758977060337977291742963)
    ·
      refine ⟨14638465590506965937614445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9758977060337977291742963 14638465590506965937614445)
      ·
        refine ⟨5489424596440112226605417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14638465590506965937614445 5489424596440112226605417)
        ·
          refine ⟨4117068447330084169954063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5489424596440112226605417 4117068447330084169954063)
          ·
            refine ⟨6175602670995126254931095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4117068447330084169954063 6175602670995126254931095)
            ·
              refine ⟨9263404006492689382396643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6175602670995126254931095 9263404006492689382396643)
              ·
                refine ⟨13895106009739034073594965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9263404006492689382396643 13895106009739034073594965)
                ·
                  refine ⟨162833273551629305549941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 13895106009739034073594965 162833273551629305549941)
                  ·
                    rfl

theorem cell23_2854050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 1, 1, 1, 8].length) (baseStart_2854050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2854050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2854050 prefixEnd_2854050 := by exact prefixLift 2854050
  have htrace : WordTrace (prefixWord ++ tailWord_2854050) baseStart_2854050 baseEnd_2854050 := by
    simpa [prefixWord, tailWord_2854050, baseEnd_2854050] using wordTrace_append hprefix tailTrace_2854050
  have hstable : (prefixWord ++ tailWord_2854050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2854050).length < 2 ^ (prefixWord ++ tailWord_2854050).sum := by decide
  have hdescent : baseEnd_2854050 < baseStart_2854050 := by decide
  rcases family_descends (prefixWord ++ tailWord_2854050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2854103 : List Nat := [1, 1, 3, 2, 1, 2, 3, 3, 1, 1, 5]
def baseStart_2854103 : Nat := 118140960795 + 2854103 * 2 ^ 59
def prefixEnd_2854103 : Nat := 4983230072969 + 3 ^ 40 * 2854103 * 2
def baseEnd_2854103 : Nat := 1465526676439352042586725

theorem tailTrace_2854103 : CollatzResearch.WordTrace tailWord_2854103 prefixEnd_2854103 1465526676439352042586725 := by
  unfold tailWord_2854103
  simp only [CollatzResearch.WordTrace]
  refine ⟨104097688379079747830270963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69398458919386498553513975 104097688379079747830270963)
  ·
    refine ⟨156146532568619621745406445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104097688379079747830270963 156146532568619621745406445)
    ·
      refine ⟨58554949713232358154527417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 156146532568619621745406445 58554949713232358154527417)
      ·
        refine ⟨43916212284924268615895563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58554949713232358154527417 43916212284924268615895563)
        ·
          refine ⟨65874318427386402923843345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43916212284924268615895563 65874318427386402923843345)
          ·
            refine ⟨49405738820539802192882509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65874318427386402923843345 49405738820539802192882509)
            ·
              refine ⟨18527152057702425822330941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 49405738820539802192882509 18527152057702425822330941)
              ·
                refine ⟨6947682021638409683374103, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18527152057702425822330941 6947682021638409683374103)
                ·
                  refine ⟨10421523032457614525061155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6947682021638409683374103 10421523032457614525061155)
                  ·
                    refine ⟨15632284548686421787591733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10421523032457614525061155 15632284548686421787591733)
                    ·
                      refine ⟨1465526676439352042586725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15632284548686421787591733 1465526676439352042586725)
                      ·
                        rfl

theorem cell23_2854103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 3, 3, 1, 1, 5].length) (baseStart_2854103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2854103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2854103 prefixEnd_2854103 := by exact prefixLift 2854103
  have htrace : WordTrace (prefixWord ++ tailWord_2854103) baseStart_2854103 baseEnd_2854103 := by
    simpa [prefixWord, tailWord_2854103, baseEnd_2854103] using wordTrace_append hprefix tailTrace_2854103
  have hstable : (prefixWord ++ tailWord_2854103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2854103).length < 2 ^ (prefixWord ++ tailWord_2854103).sum := by decide
  have hdescent : baseEnd_2854103 < baseStart_2854103 := by decide
  rcases family_descends (prefixWord ++ tailWord_2854103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2854113 : List Nat := [1, 2, 3, 1, 3, 2, 1, 2, 1, 1, 6]
def baseStart_2854113 : Nat := 118140960795 + 2854113 * 2 ^ 59
def prefixEnd_2854113 : Nat := 4983230072969 + 3 ^ 40 * 2854113 * 2
def baseEnd_2854113 : Nat := 1465531811245897003461679

theorem tailTrace_2854113 : CollatzResearch.WordTrace tailWord_2854113 prefixEnd_2854113 1465531811245897003461679 := by
  unfold tailWord_2854113
  simp only [CollatzResearch.WordTrace]
  refine ⟨104098053109043519538134993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69398702072695679692089995 104098053109043519538134993)
  ·
    refine ⟨78073539831782639653601245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104098053109043519538134993 78073539831782639653601245)
    ·
      refine ⟨29277577436918489870100467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 78073539831782639653601245 29277577436918489870100467)
      ·
        refine ⟨43916366155377734805150701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29277577436918489870100467 43916366155377734805150701)
        ·
          refine ⟨16468637308266650551931513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43916366155377734805150701 16468637308266650551931513)
          ·
            refine ⟨12351477981199987913948635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16468637308266650551931513 12351477981199987913948635)
            ·
              refine ⟨18527216971799981870922953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12351477981199987913948635 18527216971799981870922953)
              ·
                refine ⟨13895412728849986403192215, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18527216971799981870922953 13895412728849986403192215)
                ·
                  refine ⟨20843119093274979604788323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13895412728849986403192215 20843119093274979604788323)
                  ·
                    refine ⟨31264678639912469407182485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20843119093274979604788323 31264678639912469407182485)
                    ·
                      refine ⟨1465531811245897003461679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 31264678639912469407182485 1465531811245897003461679)
                      ·
                        rfl

theorem cell23_2854113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 1, 2, 1, 1, 6].length) (baseStart_2854113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2854113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2854113 prefixEnd_2854113 := by exact prefixLift 2854113
  have htrace : WordTrace (prefixWord ++ tailWord_2854113) baseStart_2854113 baseEnd_2854113 := by
    simpa [prefixWord, tailWord_2854113, baseEnd_2854113] using wordTrace_append hprefix tailTrace_2854113
  have hstable : (prefixWord ++ tailWord_2854113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2854113).length < 2 ^ (prefixWord ++ tailWord_2854113).sum := by decide
  have hdescent : baseEnd_2854113 < baseStart_2854113 := by decide
  rcases family_descends (prefixWord ++ tailWord_2854113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2854120 : List Nat := [2, 1, 4, 1, 2, 1, 2, 2, 3, 2, 3]
def baseStart_2854120 : Nat := 118140960795 + 2854120 * 2 ^ 59
def prefixEnd_2854120 : Nat := 4983230072969 + 3 ^ 40 * 2854120 * 2
def baseEnd_2854120 : Nat := 1465535405610478476074147

theorem tailTrace_2854120 : CollatzResearch.WordTrace tailWord_2854120 prefixEnd_2854120 1465535405610478476074147 := by
  unfold tailWord_2854120
  simp only [CollatzResearch.WordTrace]
  refine ⟨52049154210009079866819907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69398872280012106489093209 52049154210009079866819907)
  ·
    refine ⟨78073731315013619800229861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52049154210009079866819907 78073731315013619800229861)
    ·
      refine ⟨14638824621565053712543099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 78073731315013619800229861 14638824621565053712543099)
      ·
        refine ⟨21958236932347580568814649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14638824621565053712543099 21958236932347580568814649)
        ·
          refine ⟨16468677699260685426610987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21958236932347580568814649 16468677699260685426610987)
          ·
            refine ⟨24703016548891028139916481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16468677699260685426610987 24703016548891028139916481)
            ·
              refine ⟨18527262411668271104937361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24703016548891028139916481 18527262411668271104937361)
              ·
                refine ⟨13895446808751203328703021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18527262411668271104937361 13895446808751203328703021)
                ·
                  refine ⟨5210792553281701248263633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13895446808751203328703021 5210792553281701248263633)
                  ·
                    refine ⟨3908094414961275936197725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5210792553281701248263633 3908094414961275936197725)
                    ·
                      refine ⟨1465535405610478476074147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3908094414961275936197725 1465535405610478476074147)
                      ·
                        rfl

theorem cell23_2854120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 2, 2, 3, 2, 3].length) (baseStart_2854120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2854120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2854120 prefixEnd_2854120 := by exact prefixLift 2854120
  have htrace : WordTrace (prefixWord ++ tailWord_2854120) baseStart_2854120 baseEnd_2854120 := by
    simpa [prefixWord, tailWord_2854120, baseEnd_2854120] using wordTrace_append hprefix tailTrace_2854120
  have hstable : (prefixWord ++ tailWord_2854120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2854120).length < 2 ^ (prefixWord ++ tailWord_2854120).sum := by decide
  have hdescent : baseEnd_2854120 < baseStart_2854120 := by decide
  rcases family_descends (prefixWord ++ tailWord_2854120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2854123 : List Nat := [1, 1, 1, 1, 2, 7, 2, 8]
def baseStart_2854123 : Nat := 118140960795 + 2854123 * 2 ^ 59
def prefixEnd_2854123 : Nat := 4983230072969 + 3 ^ 40 * 2854123 * 2
def baseEnd_2854123 : Nat := 54279146150090443123579

theorem tailTrace_2854123 : CollatzResearch.WordTrace tailWord_2854123 prefixEnd_2854123 54279146150090443123579 := by
  unfold tailWord_2854123
  simp only [CollatzResearch.WordTrace]
  refine ⟨104098417839007291245999023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69398945226004860830666015 104098417839007291245999023)
  ·
    refine ⟨156147626758510936868998535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104098417839007291245999023 156147626758510936868998535)
    ·
      refine ⟨234221440137766405303497803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 156147626758510936868998535 234221440137766405303497803)
      ·
        refine ⟨351332160206649607955246705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 234221440137766405303497803 351332160206649607955246705)
        ·
          refine ⟨263499120154987205966435029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 351332160206649607955246705 263499120154987205966435029)
          ·
            refine ⟨6175760628632512639838321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 263499120154987205966435029 6175760628632512639838321)
            ·
              refine ⟨4631820471474384479878741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6175760628632512639838321 4631820471474384479878741)
              ·
                refine ⟨54279146150090443123579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4631820471474384479878741 54279146150090443123579)
                ·
                  rfl

theorem cell23_2854123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 7, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 7, 2, 8].length) (baseStart_2854123 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2854123 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2854123 prefixEnd_2854123 := by exact prefixLift 2854123
  have htrace : WordTrace (prefixWord ++ tailWord_2854123) baseStart_2854123 baseEnd_2854123 := by
    simpa [prefixWord, tailWord_2854123, baseEnd_2854123] using wordTrace_append hprefix tailTrace_2854123
  have hstable : (prefixWord ++ tailWord_2854123).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2854123).length < 2 ^ (prefixWord ++ tailWord_2854123).sum := by decide
  have hdescent : baseEnd_2854123 < baseStart_2854123 := by decide
  rcases family_descends (prefixWord ++ tailWord_2854123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2854127 : List Nat := [1, 1, 2, 1, 7, 1, 1, 3, 2, 4]
def baseStart_2854127 : Nat := 118140960795 + 2854127 * 2 ^ 59
def prefixEnd_2854127 : Nat := 4983230072969 + 3 ^ 40 * 2854127 * 2
def baseEnd_2854127 : Nat := 488512999991686649562205

theorem tailTrace_2854127 : CollatzResearch.WordTrace tailWord_2854127 prefixEnd_2854127 488512999991686649562205 := by
  unfold tailWord_2854127
  simp only [CollatzResearch.WordTrace]
  refine ⟨104098563730992799929144635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69399042487328533286096423 104098563730992799929144635)
  ·
    refine ⟨156147845596489199893716953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104098563730992799929144635 156147845596489199893716953)
    ·
      refine ⟨117110884197366899920287715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 156147845596489199893716953 117110884197366899920287715)
      ·
        refine ⟨175666326296050349880431573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117110884197366899920287715 175666326296050349880431573)
        ·
          refine ⟨4117179522563680075322615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 175666326296050349880431573 4117179522563680075322615)
          ·
            refine ⟨6175769283845520112983923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4117179522563680075322615 6175769283845520112983923)
            ·
              refine ⟨9263653925768280169475885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6175769283845520112983923 9263653925768280169475885)
              ·
                refine ⟨3473870222163105063553457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9263653925768280169475885 3473870222163105063553457)
                ·
                  refine ⟨2605402666622328797665093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3473870222163105063553457 2605402666622328797665093)
                  ·
                    refine ⟨488512999991686649562205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2605402666622328797665093 488512999991686649562205)
                    ·
                      rfl

theorem cell23_2854127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 1, 1, 3, 2, 4].length) (baseStart_2854127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2854127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2854127 prefixEnd_2854127 := by exact prefixLift 2854127
  have htrace : WordTrace (prefixWord ++ tailWord_2854127) baseStart_2854127 baseEnd_2854127 := by
    simpa [prefixWord, tailWord_2854127, baseEnd_2854127] using wordTrace_append hprefix tailTrace_2854127
  have hstable : (prefixWord ++ tailWord_2854127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2854127).length < 2 ^ (prefixWord ++ tailWord_2854127).sum := by decide
  have hdescent : baseEnd_2854127 < baseStart_2854127 := by decide
  rcases family_descends (prefixWord ++ tailWord_2854127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2854162 : List Nat := [3, 2, 4, 2, 2, 1, 2, 2, 1, 1, 3]
def baseStart_2854162 : Nat := 118140960795 + 2854162 * 2 ^ 59
def prefixEnd_2854162 : Nat := 4983230072969 + 3 ^ 40 * 2854162 * 2
def baseEnd_2854162 : Nat := 1465556971797967311748955

theorem tailTrace_2854162 : CollatzResearch.WordTrace tailWord_2854162 prefixEnd_2854162 1465556971797967311748955 := by
  unfold tailWord_2854162
  simp only [CollatzResearch.WordTrace]
  refine ⟨26024960071466500226667185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69399893523910667271112493 26024960071466500226667185)
  ·
    refine ⟨19518720053599875170000389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26024960071466500226667185 19518720053599875170000389)
    ·
      refine ⟨3659760010049976594375073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19518720053599875170000389 3659760010049976594375073)
      ·
        refine ⟨2744820007537482445781305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3659760010049976594375073 2744820007537482445781305)
        ·
          refine ⟨2058615005653111834335979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2744820007537482445781305 2058615005653111834335979)
          ·
            refine ⟨3087922508479667751503969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2058615005653111834335979 3087922508479667751503969)
            ·
              refine ⟨2315941881359750813627977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3087922508479667751503969 2315941881359750813627977)
              ·
                refine ⟨1736956411019813110220983, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2315941881359750813627977 1736956411019813110220983)
                ·
                  refine ⟨2605434616529719665331475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1736956411019813110220983 2605434616529719665331475)
                  ·
                    refine ⟨3908151924794579497997213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2605434616529719665331475 3908151924794579497997213)
                    ·
                      refine ⟨1465556971797967311748955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3908151924794579497997213 1465556971797967311748955)
                      ·
                        rfl

theorem cell23_2854162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 2, 1, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 2, 1, 2, 2, 1, 1, 3].length) (baseStart_2854162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2854162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2854162 prefixEnd_2854162 := by exact prefixLift 2854162
  have htrace : WordTrace (prefixWord ++ tailWord_2854162) baseStart_2854162 baseEnd_2854162 := by
    simpa [prefixWord, tailWord_2854162, baseEnd_2854162] using wordTrace_append hprefix tailTrace_2854162
  have hstable : (prefixWord ++ tailWord_2854162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2854162).length < 2 ^ (prefixWord ++ tailWord_2854162).sum := by decide
  have hdescent : baseEnd_2854162 < baseStart_2854162 := by decide
  rcases family_descends (prefixWord ++ tailWord_2854162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2854168 : List Nat := [2, 1, 2, 3, 1, 5, 2, 2, 1, 2, 2]
def baseStart_2854168 : Nat := 118140960795 + 2854168 * 2 ^ 59
def prefixEnd_2854168 : Nat := 4983230072969 + 3 ^ 40 * 2854168 * 2
def baseEnd_2854168 : Nat := 1465560052681894288273927

theorem tailTrace_2854168 : CollatzResearch.WordTrace tailWord_2854168 prefixEnd_2854168 1465560052681894288273927 := by
  unfold tailWord_2854168
  simp only [CollatzResearch.WordTrace]
  refine ⟨52050029561922131965693579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69400039415896175954258105 52050029561922131965693579)
  ·
    refine ⟨78075044342883197948540369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52050029561922131965693579 78075044342883197948540369)
    ·
      refine ⟨58556283257162398461405277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78075044342883197948540369 58556283257162398461405277)
      ·
        refine ⟨21958606221435899423026979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 58556283257162398461405277 21958606221435899423026979)
        ·
          refine ⟨32937909332153849134540469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21958606221435899423026979 32937909332153849134540469)
          ·
            refine ⟨3087928999889423356363169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 32937909332153849134540469 3087928999889423356363169)
            ·
              refine ⟨2315946749917067517272377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3087928999889423356363169 2315946749917067517272377)
              ·
                refine ⟨1736960062437800637954283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2315946749917067517272377 1736960062437800637954283)
                ·
                  refine ⟨2605440093656700956931425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1736960062437800637954283 2605440093656700956931425)
                  ·
                    refine ⟨1954080070242525717698569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2605440093656700956931425 1954080070242525717698569)
                    ·
                      refine ⟨1465560052681894288273927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1954080070242525717698569 1465560052681894288273927)
                      ·
                        rfl

theorem cell23_2854168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 5, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 5, 2, 2, 1, 2, 2].length) (baseStart_2854168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2854168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2854168 prefixEnd_2854168 := by exact prefixLift 2854168
  have htrace : WordTrace (prefixWord ++ tailWord_2854168) baseStart_2854168 baseEnd_2854168 := by
    simpa [prefixWord, tailWord_2854168, baseEnd_2854168] using wordTrace_append hprefix tailTrace_2854168
  have hstable : (prefixWord ++ tailWord_2854168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2854168).length < 2 ^ (prefixWord ++ tailWord_2854168).sum := by decide
  have hdescent : baseEnd_2854168 < baseStart_2854168 := by decide
  rcases family_descends (prefixWord ++ tailWord_2854168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2854174 : List Nat := [4, 3, 2, 1, 2, 2, 1, 8]
def baseStart_2854174 : Nat := 118140960795 + 2854174 * 2 ^ 59
def prefixEnd_2854174 : Nat := 4983230072969 + 3 ^ 40 * 2854174 * 2
def baseEnd_2854174 : Nat := 54280116057993380177737

theorem tailTrace_2854174 : CollatzResearch.WordTrace tailWord_2854174 prefixEnd_2854174 54280116057993380177737 := by
  unfold tailWord_2854174
  simp only [CollatzResearch.WordTrace]
  refine ⟨13012534745227815869513197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 69400185307881684637403717 13012534745227815869513197)
  ·
    refine ⟨4879700529460430951067449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13012534745227815869513197 4879700529460430951067449)
    ·
      refine ⟨3659775397095323213300587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4879700529460430951067449 3659775397095323213300587)
      ·
        refine ⟨5489663095642984819950881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3659775397095323213300587 5489663095642984819950881)
        ·
          refine ⟨4117247321732238614963161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5489663095642984819950881 4117247321732238614963161)
          ·
            refine ⟨3087935491299178961222371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4117247321732238614963161 3087935491299178961222371)
            ·
              refine ⟨4631903236948768441833557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3087935491299178961222371 4631903236948768441833557)
              ·
                refine ⟨54280116057993380177737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4631903236948768441833557 54280116057993380177737)
                ·
                  rfl

theorem cell23_2854174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 2, 1, 8].length) (baseStart_2854174 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2854174 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2854174 prefixEnd_2854174 := by exact prefixLift 2854174
  have htrace : WordTrace (prefixWord ++ tailWord_2854174) baseStart_2854174 baseEnd_2854174 := by
    simpa [prefixWord, tailWord_2854174, baseEnd_2854174] using wordTrace_append hprefix tailTrace_2854174
  have hstable : (prefixWord ++ tailWord_2854174).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2854174).length < 2 ^ (prefixWord ++ tailWord_2854174).sum := by decide
  have hdescent : baseEnd_2854174 < baseStart_2854174 := by decide
  rcases family_descends (prefixWord ++ tailWord_2854174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2854184 : List Nat := [2, 1, 5, 1, 2, 1, 2, 3, 2, 1, 3]
def baseStart_2854184 : Nat := 118140960795 + 2854184 * 2 ^ 59
def prefixEnd_2854184 : Nat := 4983230072969 + 3 ^ 40 * 2854184 * 2
def baseEnd_2854184 : Nat := 1465568268372366225673853

theorem tailTrace_2854184 : CollatzResearch.WordTrace tailWord_2854184 prefixEnd_2854184 1465568268372366225673853 := by
  unfold tailWord_2854184
  simp only [CollatzResearch.WordTrace]
  refine ⟨52050321345893149331984803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69400428461190865775979737 52050321345893149331984803)
  ·
    refine ⟨78075482018839723997977205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52050321345893149331984803 78075482018839723997977205)
    ·
      refine ⟨7319576439266224124810363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 78075482018839723997977205 7319576439266224124810363)
      ·
        refine ⟨10979364658899336187215545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7319576439266224124810363 10979364658899336187215545)
        ·
          refine ⟨8234523494174502140411659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10979364658899336187215545 8234523494174502140411659)
          ·
            refine ⟨12351785241261753210617489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8234523494174502140411659 12351785241261753210617489)
            ·
              refine ⟨9263838930946314907963117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12351785241261753210617489 9263838930946314907963117)
              ·
                refine ⟨3473939599104868090486169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9263838930946314907963117 3473939599104868090486169)
                ·
                  refine ⟨2605454699328651067864627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3473939599104868090486169 2605454699328651067864627)
                  ·
                    refine ⟨3908182048992976601796941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2605454699328651067864627 3908182048992976601796941)
                    ·
                      refine ⟨1465568268372366225673853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3908182048992976601796941 1465568268372366225673853)
                      ·
                        rfl

theorem cell23_2854184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 2, 3, 2, 1, 3].length) (baseStart_2854184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2854184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2854184 prefixEnd_2854184 := by exact prefixLift 2854184
  have htrace : WordTrace (prefixWord ++ tailWord_2854184) baseStart_2854184 baseEnd_2854184 := by
    simpa [prefixWord, tailWord_2854184, baseEnd_2854184] using wordTrace_append hprefix tailTrace_2854184
  have hstable : (prefixWord ++ tailWord_2854184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2854184).length < 2 ^ (prefixWord ++ tailWord_2854184).sum := by decide
  have hdescent : baseEnd_2854184 < baseStart_2854184 := by decide
  rcases family_descends (prefixWord ++ tailWord_2854184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2854207 : List Nat := [1, 1, 2, 2, 4, 2, 2, 2, 1, 4, 2]
def baseStart_2854207 : Nat := 118140960795 + 2854207 * 2 ^ 59
def prefixEnd_2854207 : Nat := 4983230072969 + 3 ^ 40 * 2854207 * 2
def baseEnd_2854207 : Nat := 1465580078427419635686247

theorem tailTrace_2854207 : CollatzResearch.WordTrace tailWord_2854207 prefixEnd_2854207 1465580078427419635686247 := by
  unfold tailWord_2854207
  simp only [CollatzResearch.WordTrace]
  refine ⟨104101481570702973592056875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69400987713801982394704583 104101481570702973592056875)
  ·
    refine ⟨156152222356054460388085313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104101481570702973592056875 156152222356054460388085313)
    ·
      refine ⟨117114166767040845291063985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 156152222356054460388085313 117114166767040845291063985)
      ·
        refine ⟨87835625075280633968297989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 117114166767040845291063985 87835625075280633968297989)
        ·
          refine ⟨16469179701615118869055873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 87835625075280633968297989 16469179701615118869055873)
          ·
            refine ⟨12351884776211339151791905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16469179701615118869055873 12351884776211339151791905)
            ·
              refine ⟨9263913582158504363843929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12351884776211339151791905 9263913582158504363843929)
              ·
                refine ⟨6947935186618878272882947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9263913582158504363843929 6947935186618878272882947)
                ·
                  refine ⟨10421902779928317409324421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6947935186618878272882947 10421902779928317409324421)
                  ·
                    refine ⟨1954106771236559514248329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10421902779928317409324421 1954106771236559514248329)
                    ·
                      refine ⟨1465580078427419635686247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1954106771236559514248329 1465580078427419635686247)
                      ·
                        rfl

theorem cell23_2854207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 2, 2, 1, 4, 2].length) (baseStart_2854207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2854207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2854207 prefixEnd_2854207 := by exact prefixLift 2854207
  have htrace : WordTrace (prefixWord ++ tailWord_2854207) baseStart_2854207 baseEnd_2854207 := by
    simpa [prefixWord, tailWord_2854207, baseEnd_2854207] using wordTrace_append hprefix tailTrace_2854207
  have hstable : (prefixWord ++ tailWord_2854207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2854207).length < 2 ^ (prefixWord ++ tailWord_2854207).sum := by decide
  have hdescent : baseEnd_2854207 < baseStart_2854207 := by decide
  rcases family_descends (prefixWord ++ tailWord_2854207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2854220 : List Nat := [2, 2, 1, 3, 2, 2, 1, 2, 2, 2, 4]
def baseStart_2854220 : Nat := 118140960795 + 2854220 * 2 ^ 59
def prefixEnd_2854220 : Nat := 4983230072969 + 3 ^ 40 * 2854220 * 2
def baseEnd_2854220 : Nat := 1465586753675928084823687

theorem tailTrace_2854220 : CollatzResearch.WordTrace tailWord_2854220 prefixEnd_2854220 1465586753675928084823687 := by
  unfold tailWord_2854220
  simp only [CollatzResearch.WordTrace]
  refine ⟨52050977859827938406140057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69401303813103917874853409 52050977859827938406140057)
  ·
    refine ⟨39038233394870953804605043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52050977859827938406140057 39038233394870953804605043)
    ·
      refine ⟨58557350092306430706907565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39038233394870953804605043 58557350092306430706907565)
      ·
        refine ⟨21959006284614911515090337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 58557350092306430706907565 21959006284614911515090337)
        ·
          refine ⟨16469254713461183636317753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21959006284614911515090337 16469254713461183636317753)
          ·
            refine ⟨12351941035095887727238315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16469254713461183636317753 12351941035095887727238315)
            ·
              refine ⟨18527911552643831590857473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12351941035095887727238315 18527911552643831590857473)
              ·
                refine ⟨13895933664482873693143105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18527911552643831590857473 13895933664482873693143105)
                ·
                  refine ⟨10421950248362155269857329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13895933664482873693143105 10421950248362155269857329)
                  ·
                    refine ⟨7816462686271616452392997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10421950248362155269857329 7816462686271616452392997)
                    ·
                      refine ⟨1465586753675928084823687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7816462686271616452392997 1465586753675928084823687)
                      ·
                        rfl

theorem cell23_2854220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 1, 2, 2, 2, 4].length) (baseStart_2854220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2854220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2854220 prefixEnd_2854220 := by exact prefixLift 2854220
  have htrace : WordTrace (prefixWord ++ tailWord_2854220) baseStart_2854220 baseEnd_2854220 := by
    simpa [prefixWord, tailWord_2854220, baseEnd_2854220] using wordTrace_append hprefix tailTrace_2854220
  have hstable : (prefixWord ++ tailWord_2854220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2854220).length < 2 ^ (prefixWord ++ tailWord_2854220).sum := by decide
  have hdescent : baseEnd_2854220 < baseStart_2854220 := by decide
  rcases family_descends (prefixWord ++ tailWord_2854220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2854367 : List Nat := [1, 1, 2, 3, 3, 1, 2, 4, 1, 5]
def baseStart_2854367 : Nat := 118140960795 + 2854367 * 2 ^ 59
def prefixEnd_2854367 : Nat := 4983230072969 + 3 ^ 40 * 2854367 * 2
def baseEnd_2854367 : Nat := 488554078444046336561837

theorem tailTrace_2854367 : CollatzResearch.WordTrace tailWord_2854367 prefixEnd_2854367 488554078444046336561837 := by
  unfold tailWord_2854367
  simp only [CollatzResearch.WordTrace]
  refine ⟨104107317250123320917881355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69404878166748880611920903 104107317250123320917881355)
  ·
    refine ⟨156160975875184981376822033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104107317250123320917881355 156160975875184981376822033)
    ·
      refine ⟨117120731906388736032616525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 156160975875184981376822033 117120731906388736032616525)
      ·
        refine ⟨43920274464895776012231197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 117120731906388736032616525 43920274464895776012231197)
        ·
          refine ⟨16470102924335916004586699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43920274464895776012231197 16470102924335916004586699)
          ·
            refine ⟨24705154386503874006880049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16470102924335916004586699 24705154386503874006880049)
            ·
              refine ⟨18528865789877905505160037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24705154386503874006880049 18528865789877905505160037)
              ·
                refine ⟨3474162335602107282217507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18528865789877905505160037 3474162335602107282217507)
                ·
                  refine ⟨5211243503403160923326261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3474162335602107282217507 5211243503403160923326261)
                  ·
                    refine ⟨488554078444046336561837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5211243503403160923326261 488554078444046336561837)
                    ·
                      rfl

theorem cell23_2854367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 2, 4, 1, 5].length) (baseStart_2854367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2854367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2854367 prefixEnd_2854367 := by exact prefixLift 2854367
  have htrace : WordTrace (prefixWord ++ tailWord_2854367) baseStart_2854367 baseEnd_2854367 := by
    simpa [prefixWord, tailWord_2854367, baseEnd_2854367] using wordTrace_append hprefix tailTrace_2854367
  have hstable : (prefixWord ++ tailWord_2854367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2854367).length < 2 ^ (prefixWord ++ tailWord_2854367).sum := by decide
  have hdescent : baseEnd_2854367 < baseStart_2854367 := by decide
  rcases family_descends (prefixWord ++ tailWord_2854367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2854380 : List Nat := [2, 2, 1, 1, 2, 1, 2, 3, 3, 6]
def baseStart_2854380 : Nat := 118140960795 + 2854380 * 2 ^ 59
def prefixEnd_2854380 : Nat := 4983230072969 + 3 ^ 40 * 2854380 * 2
def baseEnd_2854380 : Nat := 488556303526882486274317

theorem tailTrace_2854380 : CollatzResearch.WordTrace tailWord_2854380 prefixEnd_2854380 488556303526882486274317 := by
  unfold tailWord_2854380
  simp only [CollatzResearch.WordTrace]
  refine ⟨52053895699538112069052297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69405194266050816092069729 52053895699538112069052297)
  ·
    refine ⟨39040421774653584051789223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52053895699538112069052297 39040421774653584051789223)
    ·
      refine ⟨58560632661980376077683835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39040421774653584051789223 58560632661980376077683835)
      ·
        refine ⟨87840948992970564116525753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58560632661980376077683835 87840948992970564116525753)
        ·
          refine ⟨65880711744727923087394315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 87840948992970564116525753 65880711744727923087394315)
          ·
            refine ⟨98821067617091884631091473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65880711744727923087394315 98821067617091884631091473)
            ·
              refine ⟨74115800712818913473318605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 98821067617091884631091473 74115800712818913473318605)
              ·
                refine ⟨27793425267307092552494477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 74115800712818913473318605 27793425267307092552494477)
                ·
                  refine ⟨10422534475240159707185429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27793425267307092552494477 10422534475240159707185429)
                  ·
                    refine ⟨488556303526882486274317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10422534475240159707185429 488556303526882486274317)
                    ·
                      rfl

theorem cell23_2854380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 6].length) (baseStart_2854380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2854380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2854380 prefixEnd_2854380 := by exact prefixLift 2854380
  have htrace : WordTrace (prefixWord ++ tailWord_2854380) baseStart_2854380 baseEnd_2854380 := by
    simpa [prefixWord, tailWord_2854380, baseEnd_2854380] using wordTrace_append hprefix tailTrace_2854380
  have hstable : (prefixWord ++ tailWord_2854380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2854380).length < 2 ^ (prefixWord ++ tailWord_2854380).sum := by decide
  have hdescent : baseEnd_2854380 < baseStart_2854380 := by decide
  rcases family_descends (prefixWord ++ tailWord_2854380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2854384 : List Nat := [2, 1, 1, 1, 3, 4, 4, 1, 1, 5]
def baseStart_2854384 : Nat := 118140960795 + 2854384 * 2 ^ 59
def prefixEnd_2854384 : Nat := 4983230072969 + 3 ^ 40 * 2854384 * 2
def baseEnd_2854384 : Nat := 488556988167755147724311

theorem tailTrace_2854384 : CollatzResearch.WordTrace tailWord_2854384 prefixEnd_2854384 488556988167755147724311 := by
  unfold tailWord_2854384
  simp only [CollatzResearch.WordTrace]
  refine ⟨52053968645530866410625103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69405291527374488547500137 52053968645530866410625103)
  ·
    refine ⟨78080952968296299615937655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52053968645530866410625103 78080952968296299615937655)
    ·
      refine ⟨117121429452444449423906483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78080952968296299615937655 117121429452444449423906483)
      ·
        refine ⟨175682144178666674135859725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117121429452444449423906483 175682144178666674135859725)
        ·
          refine ⟨65880804067000002800947397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 175682144178666674135859725 65880804067000002800947397)
          ·
            refine ⟨12352650762562500525177637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 65880804067000002800947397 12352650762562500525177637)
            ·
              refine ⟨2316122017980468848470807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12352650762562500525177637 2316122017980468848470807)
              ·
                refine ⟨3474183026970703272706211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2316122017980468848470807 3474183026970703272706211)
                ·
                  refine ⟨5211274540456054909059317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3474183026970703272706211 5211274540456054909059317)
                  ·
                    refine ⟨488556988167755147724311, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5211274540456054909059317 488556988167755147724311)
                    ·
                      rfl

theorem cell23_2854384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 4, 1, 1, 5].length) (baseStart_2854384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2854384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2854384 prefixEnd_2854384 := by exact prefixLift 2854384
  have htrace : WordTrace (prefixWord ++ tailWord_2854384) baseStart_2854384 baseEnd_2854384 := by
    simpa [prefixWord, tailWord_2854384, baseEnd_2854384] using wordTrace_append hprefix tailTrace_2854384
  have hstable : (prefixWord ++ tailWord_2854384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2854384).length < 2 ^ (prefixWord ++ tailWord_2854384).sum := by decide
  have hdescent : baseEnd_2854384 < baseStart_2854384 := by decide
  rcases family_descends (prefixWord ++ tailWord_2854384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2854400 : List Nat := [2, 1, 1, 2, 1, 1, 1, 1, 1, 8, 4]
def baseStart_2854400 : Nat := 118140960795 + 2854400 * 2 ^ 59
def prefixEnd_2854400 : Nat := 4983230072969 + 3 ^ 40 * 2854400 * 2
def baseEnd_2854400 : Nat := 1465679180193737380572859

theorem tailTrace_2854400 : CollatzResearch.WordTrace tailWord_2854400 prefixEnd_2854400 1465679180193737380572859 := by
  unfold tailWord_2854400
  simp only [CollatzResearch.WordTrace]
  refine ⟨52054260429501883776916327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69405680572669178369221769 52054260429501883776916327)
  ·
    refine ⟨78081390644252825665374491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52054260429501883776916327 78081390644252825665374491)
    ·
      refine ⟨117122085966379238498061737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78081390644252825665374491 117122085966379238498061737)
      ·
        refine ⟨87841564474784428873546303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 117122085966379238498061737 87841564474784428873546303)
        ·
          refine ⟨131762346712176643310319455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87841564474784428873546303 131762346712176643310319455)
          ·
            refine ⟨197643520068264964965479183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 131762346712176643310319455 197643520068264964965479183)
            ·
              refine ⟨296465280102397447448218775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 197643520068264964965479183 296465280102397447448218775)
              ·
                refine ⟨444697920153596171172328163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 296465280102397447448218775 444697920153596171172328163)
                ·
                  refine ⟨667046880230394256758492245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 444697920153596171172328163 667046880230394256758492245)
                  ·
                    refine ⟨7816955627699932696388581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 667046880230394256758492245 7816955627699932696388581)
                    ·
                      refine ⟨1465679180193737380572859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7816955627699932696388581 1465679180193737380572859)
                      ·
                        rfl

theorem cell23_2854400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 8, 4].length) (baseStart_2854400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2854400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2854400 prefixEnd_2854400 := by exact prefixLift 2854400
  have htrace : WordTrace (prefixWord ++ tailWord_2854400) baseStart_2854400 baseEnd_2854400 := by
    simpa [prefixWord, tailWord_2854400, baseEnd_2854400] using wordTrace_append hprefix tailTrace_2854400
  have hstable : (prefixWord ++ tailWord_2854400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2854400).length < 2 ^ (prefixWord ++ tailWord_2854400).sum := by decide
  have hdescent : baseEnd_2854400 < baseStart_2854400 := by decide
  rcases family_descends (prefixWord ++ tailWord_2854400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2854407 : List Nat := [1, 1, 4, 3, 2, 1, 1, 1, 3, 1, 5]
def baseStart_2854407 : Nat := 118140960795 + 2854407 * 2 ^ 59
def prefixEnd_2854407 : Nat := 4983230072969 + 3 ^ 40 * 2854407 * 2
def baseEnd_2854407 : Nat := 1465682774558318853185327

theorem tailTrace_2854407 : CollatzResearch.WordTrace tailWord_2854407 prefixEnd_2854407 1465682774558318853185327 := by
  unfold tailWord_2854407
  simp only [CollatzResearch.WordTrace]
  refine ⟨104108776169978407749337475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69405850779985605166224983 104108776169978407749337475)
  ·
    refine ⟨156163164254967611624006213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104108776169978407749337475 156163164254967611624006213)
    ·
      refine ⟨29280593297806427179501165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 156163164254967611624006213 29280593297806427179501165)
      ·
        refine ⟨10980222486677410192312937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29280593297806427179501165 10980222486677410192312937)
        ·
          refine ⟨8235166865008057644234703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10980222486677410192312937 8235166865008057644234703)
          ·
            refine ⟨12352750297512086466352055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8235166865008057644234703 12352750297512086466352055)
            ·
              refine ⟨18529125446268129699528083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12352750297512086466352055 18529125446268129699528083)
              ·
                refine ⟨27793688169402194549292125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18529125446268129699528083 27793688169402194549292125)
                ·
                  refine ⟨10422633063525822955984547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27793688169402194549292125 10422633063525822955984547)
                  ·
                    refine ⟨15633949595288734433976821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10422633063525822955984547 15633949595288734433976821)
                    ·
                      refine ⟨1465682774558318853185327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15633949595288734433976821 1465682774558318853185327)
                      ·
                        rfl

theorem cell23_2854407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 1, 1, 3, 1, 5].length) (baseStart_2854407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2854407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2854407 prefixEnd_2854407 := by exact prefixLift 2854407
  have htrace : WordTrace (prefixWord ++ tailWord_2854407) baseStart_2854407 baseEnd_2854407 := by
    simpa [prefixWord, tailWord_2854407, baseEnd_2854407] using wordTrace_append hprefix tailTrace_2854407
  have hstable : (prefixWord ++ tailWord_2854407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2854407).length < 2 ^ (prefixWord ++ tailWord_2854407).sum := by decide
  have hdescent : baseEnd_2854407 < baseStart_2854407 := by decide
  rcases family_descends (prefixWord ++ tailWord_2854407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2854421 : List Nat := [1, 3, 2, 1, 3, 2, 2, 2, 3, 2, 2]
def baseStart_2854421 : Nat := 118140960795 + 2854421 * 2 ^ 59
def prefixEnd_2854421 : Nat := 4983230072969 + 3 ^ 40 * 2854421 * 2
def baseEnd_2854421 : Nat := 1465689963287481798410263

theorem tailTrace_2854421 : CollatzResearch.WordTrace tailWord_2854421 prefixEnd_2854421 1465689963287481798410263 := by
  unfold tailWord_2854421
  simp only [CollatzResearch.WordTrace]
  refine ⟨104109286791927688140347117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69406191194618458760231411 104109286791927688140347117)
  ·
    refine ⟨39040982546972883052630169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 104109286791927688140347117 39040982546972883052630169)
    ·
      refine ⟨29280736910229662289472627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39040982546972883052630169 29280736910229662289472627)
      ·
        refine ⟨43921105365344493434208941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29280736910229662289472627 43921105365344493434208941)
        ·
          refine ⟨16470414512004185037828353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43921105365344493434208941 16470414512004185037828353)
          ·
            refine ⟨12352810884003138778371265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16470414512004185037828353 12352810884003138778371265)
            ·
              refine ⟨9264608163002354083778449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12352810884003138778371265 9264608163002354083778449)
              ·
                refine ⟨6948456122251765562833837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9264608163002354083778449 6948456122251765562833837)
                ·
                  refine ⟨2605671045844412086062689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6948456122251765562833837 2605671045844412086062689)
                  ·
                    refine ⟨1954253284383309064547017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2605671045844412086062689 1954253284383309064547017)
                    ·
                      refine ⟨1465689963287481798410263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1954253284383309064547017 1465689963287481798410263)
                      ·
                        rfl

theorem cell23_2854421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 2, 2, 3, 2, 2].length) (baseStart_2854421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2854421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2854421 prefixEnd_2854421 := by exact prefixLift 2854421
  have htrace : WordTrace (prefixWord ++ tailWord_2854421) baseStart_2854421 baseEnd_2854421 := by
    simpa [prefixWord, tailWord_2854421, baseEnd_2854421] using wordTrace_append hprefix tailTrace_2854421
  have hstable : (prefixWord ++ tailWord_2854421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2854421).length < 2 ^ (prefixWord ++ tailWord_2854421).sum := by decide
  have hdescent : baseEnd_2854421 < baseStart_2854421 := by decide
  rcases family_descends (prefixWord ++ tailWord_2854421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2854437 : List Nat := [1, 3, 1, 2, 2, 1, 1, 3, 3, 3, 3]
def baseStart_2854437 : Nat := 118140960795 + 2854437 * 2 ^ 59
def prefixEnd_2854437 : Nat := 4983230072969 + 3 ^ 40 * 2854437 * 2
def baseEnd_2854437 : Nat := 1465698178977953735810189

theorem tailTrace_2854437 : CollatzResearch.WordTrace tailWord_2854437 prefixEnd_2854437 1465698178977953735810189 := by
  unfold tailWord_2854437
  simp only [CollatzResearch.WordTrace]
  refine ⟨104109870359869722872929565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69406580239913148581953043 104109870359869722872929565)
  ·
    refine ⟨39041201384951146077348587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 104109870359869722872929565 39041201384951146077348587)
    ·
      refine ⟨58561802077426719116022881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39041201384951146077348587 58561802077426719116022881)
      ·
        refine ⟨43921351558070039337017161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58561802077426719116022881 43921351558070039337017161)
        ·
          refine ⟨32941013668552529502762871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43921351558070039337017161 32941013668552529502762871)
          ·
            refine ⟨49411520502828794254144307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32941013668552529502762871 49411520502828794254144307)
            ·
              refine ⟨74117280754243191381216461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49411520502828794254144307 74117280754243191381216461)
              ·
                refine ⟨27793980282841196767956173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 74117280754243191381216461 27793980282841196767956173)
                ·
                  refine ⟨10422742606065448787983565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27793980282841196767956173 10422742606065448787983565)
                  ·
                    refine ⟨3908528477274543295493837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10422742606065448787983565 3908528477274543295493837)
                    ·
                      refine ⟨1465698178977953735810189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3908528477274543295493837 1465698178977953735810189)
                      ·
                        rfl

theorem cell23_2854437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 3, 3, 3, 3].length) (baseStart_2854437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2854437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2854437 prefixEnd_2854437 := by exact prefixLift 2854437
  have htrace : WordTrace (prefixWord ++ tailWord_2854437) baseStart_2854437 baseEnd_2854437 := by
    simpa [prefixWord, tailWord_2854437, baseEnd_2854437] using wordTrace_append hprefix tailTrace_2854437
  have hstable : (prefixWord ++ tailWord_2854437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2854437).length < 2 ^ (prefixWord ++ tailWord_2854437).sum := by decide
  have hdescent : baseEnd_2854437 < baseStart_2854437 := by decide
  rcases family_descends (prefixWord ++ tailWord_2854437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2854455 : List Nat := [1, 1, 3, 1, 2, 5, 3, 2, 1, 2, 2]
def baseStart_2854455 : Nat := 118140960795 + 2854455 * 2 ^ 59
def prefixEnd_2854455 : Nat := 4983230072969 + 3 ^ 40 * 2854455 * 2
def baseEnd_2854455 : Nat := 1465707421629734665385107

theorem tailTrace_2854455 : CollatzResearch.WordTrace tailWord_2854455 prefixEnd_2854455 1465707421629734665385107 := by
  unfold tailWord_2854455
  simp only [CollatzResearch.WordTrace]
  refine ⟨104110526873804511947084819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69407017915869674631389879 104110526873804511947084819)
  ·
    refine ⟨156165790310706767920627229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104110526873804511947084819 156165790310706767920627229)
    ·
      refine ⟨58562171366515037970235211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 156165790310706767920627229 58562171366515037970235211)
      ·
        refine ⟨87843257049772556955352817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58562171366515037970235211 87843257049772556955352817)
        ·
          refine ⟨65882442787329417716514613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 87843257049772556955352817 65882442787329417716514613)
          ·
            refine ⟨6176479011312132910923245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 65882442787329417716514613 6176479011312132910923245)
            ·
              refine ⟨2316179629242049841596217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6176479011312132910923245 2316179629242049841596217)
              ·
                refine ⟨1737134721931537381197163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2316179629242049841596217 1737134721931537381197163)
                ·
                  refine ⟨2605702082897306071795745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1737134721931537381197163 2605702082897306071795745)
                  ·
                    refine ⟨1954276562172979553846809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2605702082897306071795745 1954276562172979553846809)
                    ·
                      refine ⟨1465707421629734665385107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1954276562172979553846809 1465707421629734665385107)
                      ·
                        rfl

theorem cell23_2854455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 5, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 5, 3, 2, 1, 2, 2].length) (baseStart_2854455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2854455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2854455 prefixEnd_2854455 := by exact prefixLift 2854455
  have htrace : WordTrace (prefixWord ++ tailWord_2854455) baseStart_2854455 baseEnd_2854455 := by
    simpa [prefixWord, tailWord_2854455, baseEnd_2854455] using wordTrace_append hprefix tailTrace_2854455
  have hstable : (prefixWord ++ tailWord_2854455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2854455).length < 2 ^ (prefixWord ++ tailWord_2854455).sum := by decide
  have hdescent : baseEnd_2854455 < baseStart_2854455 := by decide
  rcases family_descends (prefixWord ++ tailWord_2854455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2854464 : List Nat := [2, 1, 1, 2, 2, 2, 1, 4, 3, 3, 2]
def baseStart_2854464 : Nat := 118140960795 + 2854464 * 2 ^ 59
def prefixEnd_2854464 : Nat := 4983230072969 + 3 ^ 40 * 2854464 * 2
def baseEnd_2854464 : Nat := 1465712042955625130172565

theorem tailTrace_2854464 : CollatzResearch.WordTrace tailWord_2854464 prefixEnd_2854464 1465712042955625130172565 := by
  unfold tailWord_2854464
  simp only [CollatzResearch.WordTrace]
  refine ⟨52055427565385953242081223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69407236753847937656108297 52055427565385953242081223)
  ·
    refine ⟨78083141348078929863121835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52055427565385953242081223 78083141348078929863121835)
    ·
      refine ⟨117124712022118394794682753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78083141348078929863121835 117124712022118394794682753)
      ·
        refine ⟨87843534016588796096012065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 117124712022118394794682753 87843534016588796096012065)
        ·
          refine ⟨65882650512441597072009049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 87843534016588796096012065 65882650512441597072009049)
          ·
            refine ⟨49411987884331197804006787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65882650512441597072009049 49411987884331197804006787)
            ·
              refine ⟨74117981826496796706010181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49411987884331197804006787 74117981826496796706010181)
              ·
                refine ⟨13897121592468149382376909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 74117981826496796706010181 13897121592468149382376909)
                ·
                  refine ⟨5211420597175556018391341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13897121592468149382376909 5211420597175556018391341)
                  ·
                    refine ⟨1954282723940833506896753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5211420597175556018391341 1954282723940833506896753)
                    ·
                      refine ⟨1465712042955625130172565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1954282723940833506896753 1465712042955625130172565)
                      ·
                        rfl

theorem cell23_2854464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 4, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 4, 3, 3, 2].length) (baseStart_2854464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2854464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2854464 prefixEnd_2854464 := by exact prefixLift 2854464
  have htrace : WordTrace (prefixWord ++ tailWord_2854464) baseStart_2854464 baseEnd_2854464 := by
    simpa [prefixWord, tailWord_2854464, baseEnd_2854464] using wordTrace_append hprefix tailTrace_2854464
  have hstable : (prefixWord ++ tailWord_2854464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2854464).length < 2 ^ (prefixWord ++ tailWord_2854464).sum := by decide
  have hdescent : baseEnd_2854464 < baseStart_2854464 := by decide
  rcases family_descends (prefixWord ++ tailWord_2854464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2854497 : List Nat := [1, 2, 3, 1, 1, 3, 1, 3, 2, 1, 5]
def baseStart_2854497 : Nat := 118140960795 + 2854497 * 2 ^ 59
def prefixEnd_2854497 : Nat := 4983230072969 + 3 ^ 40 * 2854497 * 2
def baseEnd_2854497 : Nat := 1465728987817223501059913

theorem tailTrace_2854497 : CollatzResearch.WordTrace tailWord_2854497 prefixEnd_2854497 1465728987817223501059913 := by
  unfold tailWord_2854497
  simp only [CollatzResearch.WordTrace]
  refine ⟨104112058739652353120113745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69408039159768235413409163 104112058739652353120113745)
  ·
    refine ⟨78084044054739264840085309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104112058739652353120113745 78084044054739264840085309)
    ·
      refine ⟨29281516520527224315031991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 78084044054739264840085309 29281516520527224315031991)
      ·
        refine ⟨43922274780790836472547987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29281516520527224315031991 43922274780790836472547987)
        ·
          refine ⟨65883412171186254708821981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43922274780790836472547987 65883412171186254708821981)
          ·
            refine ⟨24706279564194845515808243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 65883412171186254708821981 24706279564194845515808243)
            ·
              refine ⟨37059419346292268273712365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24706279564194845515808243 37059419346292268273712365)
              ·
                refine ⟨13897282254859600602642137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37059419346292268273712365 13897282254859600602642137)
                ·
                  refine ⟨10422961691144700451981603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13897282254859600602642137 10422961691144700451981603)
                  ·
                    refine ⟨15634442536717050677972405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10422961691144700451981603 15634442536717050677972405)
                    ·
                      refine ⟨1465728987817223501059913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15634442536717050677972405 1465728987817223501059913)
                      ·
                        rfl

theorem cell23_2854497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 1, 3, 2, 1, 5].length) (baseStart_2854497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2854497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2854497 prefixEnd_2854497 := by exact prefixLift 2854497
  have htrace : WordTrace (prefixWord ++ tailWord_2854497) baseStart_2854497 baseEnd_2854497 := by
    simpa [prefixWord, tailWord_2854497, baseEnd_2854497] using wordTrace_append hprefix tailTrace_2854497
  have hstable : (prefixWord ++ tailWord_2854497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2854497).length < 2 ^ (prefixWord ++ tailWord_2854497).sum := by decide
  have hdescent : baseEnd_2854497 < baseStart_2854497 := by decide
  rcases family_descends (prefixWord ++ tailWord_2854497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2854514 : List Nat := [3, 2, 1, 2, 3, 1, 1, 1, 2, 4, 3]
def baseStart_2854514 : Nat := 118140960795 + 2854514 * 2 ^ 59
def prefixEnd_2854514 : Nat := 4983230072969 + 3 ^ 40 * 2854514 * 2
def baseEnd_2854514 : Nat := 1465737716988349934547335

theorem tailTrace_2854514 : CollatzResearch.WordTrace tailWord_2854514 prefixEnd_2854514 1465737716988349934547335 := by
  unfold tailWord_2854514
  simp only [CollatzResearch.WordTrace]
  refine ⟨26028169695147691255870649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69408452520393843348988397 26028169695147691255870649)
  ·
    refine ⟨19521127271360768441902987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26028169695147691255870649 19521127271360768441902987)
    ·
      refine ⟨29281690907041152662854481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19521127271360768441902987 29281690907041152662854481)
      ·
        refine ⟨21961268180280864497140861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29281690907041152662854481 21961268180280864497140861)
        ·
          refine ⟨8235475567605324186427823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21961268180280864497140861 8235475567605324186427823)
          ·
            refine ⟨12353213351407986279641735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8235475567605324186427823 12353213351407986279641735)
            ·
              refine ⟨18529820027111979419462603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12353213351407986279641735 18529820027111979419462603)
              ·
                refine ⟨27794730040667969129193905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18529820027111979419462603 27794730040667969129193905)
                ·
                  refine ⟨20846047530500976846895429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27794730040667969129193905 20846047530500976846895429)
                  ·
                    refine ⟨3908633911968933158792893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20846047530500976846895429 3908633911968933158792893)
                    ·
                      refine ⟨1465737716988349934547335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3908633911968933158792893 1465737716988349934547335)
                      ·
                        rfl

theorem cell23_2854514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 1, 1, 2, 4, 3].length) (baseStart_2854514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2854514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2854514 prefixEnd_2854514 := by exact prefixLift 2854514
  have htrace : WordTrace (prefixWord ++ tailWord_2854514) baseStart_2854514 baseEnd_2854514 := by
    simpa [prefixWord, tailWord_2854514, baseEnd_2854514] using wordTrace_append hprefix tailTrace_2854514
  have hstable : (prefixWord ++ tailWord_2854514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2854514).length < 2 ^ (prefixWord ++ tailWord_2854514).sum := by decide
  have hdescent : baseEnd_2854514 < baseStart_2854514 := by decide
  rcases family_descends (prefixWord ++ tailWord_2854514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2854551 : List Nat := [1, 1, 3, 3, 2, 3, 2, 3, 5]
def baseStart_2854551 : Nat := 118140960795 + 2854551 * 2 ^ 59
def prefixEnd_2854551 : Nat := 4983230072969 + 3 ^ 40 * 2854551 * 2
def baseEnd_2854551 : Nat := 162861857308062921087185

theorem tailTrace_2854551 : CollatzResearch.WordTrace tailWord_2854551 prefixEnd_2854551 162861857308062921087185 := by
  unfold tailWord_2854551
  simp only [CollatzResearch.WordTrace]
  refine ⟨104114028281456720342579507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69409352187637813561719671 104114028281456720342579507)
  ·
    refine ⟨156171042422185080513869261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104114028281456720342579507 156171042422185080513869261)
    ·
      refine ⟨58564140908319405192700973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 156171042422185080513869261 58564140908319405192700973)
      ·
        refine ⟨21961552840619776947262865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 58564140908319405192700973 21961552840619776947262865)
        ·
          refine ⟨16471164630464832710447149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21961552840619776947262865 16471164630464832710447149)
          ·
            refine ⟨6176686736424312266417681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16471164630464832710447149 6176686736424312266417681)
            ·
              refine ⟨4632515052318234199813261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6176686736424312266417681 4632515052318234199813261)
              ·
                refine ⟨1737193144619337824929973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4632515052318234199813261 1737193144619337824929973)
                ·
                  refine ⟨162861857308062921087185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1737193144619337824929973 162861857308062921087185)
                  ·
                    rfl

theorem cell23_2854551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 3, 2, 3, 5].length) (baseStart_2854551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2854551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2854551 prefixEnd_2854551 := by exact prefixLift 2854551
  have htrace : WordTrace (prefixWord ++ tailWord_2854551) baseStart_2854551 baseEnd_2854551 := by
    simpa [prefixWord, tailWord_2854551, baseEnd_2854551] using wordTrace_append hprefix tailTrace_2854551
  have hstable : (prefixWord ++ tailWord_2854551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2854551).length < 2 ^ (prefixWord ++ tailWord_2854551).sum := by decide
  have hdescent : baseEnd_2854551 < baseStart_2854551 := by decide
  rcases family_descends (prefixWord ++ tailWord_2854551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2854597 : List Nat := [1, 3, 1, 1, 1, 1, 2, 2, 4, 1, 6]
def baseStart_2854597 : Nat := 118140960795 + 2854597 * 2 ^ 59
def prefixEnd_2854597 : Nat := 4983230072969 + 3 ^ 40 * 2854597 * 2
def baseEnd_2854597 : Nat := 1465780335882673109809453

theorem tailTrace_2854597 : CollatzResearch.WordTrace tailWord_2854597 prefixEnd_2854597 1465780335882673109809453 := by
  unfold tailWord_2854597
  simp only [CollatzResearch.WordTrace]
  refine ⟨104115706039290070198754045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69410470692860046799169363 104115706039290070198754045)
  ·
    refine ⟨39043389764733776324532767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 104115706039290070198754045 39043389764733776324532767)
    ·
      refine ⟨58565084647100664486799151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39043389764733776324532767 58565084647100664486799151)
      ·
        refine ⟨87847626970650996730198727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58565084647100664486799151 87847626970650996730198727)
        ·
          refine ⟨131771440455976495095298091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87847626970650996730198727 131771440455976495095298091)
          ·
            refine ⟨197657160683964742642947137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 131771440455976495095298091 197657160683964742642947137)
            ·
              refine ⟨148242870512973556982210353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 197657160683964742642947137 148242870512973556982210353)
              ·
                refine ⟨111182152884730167736657765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 148242870512973556982210353 111182152884730167736657765)
                ·
                  refine ⟨20846653665886906450623331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 111182152884730167736657765 20846653665886906450623331)
                  ·
                    refine ⟨31269980498830359675934997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20846653665886906450623331 31269980498830359675934997)
                    ·
                      refine ⟨1465780335882673109809453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 31269980498830359675934997 1465780335882673109809453)
                      ·
                        rfl

theorem cell23_2854597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 2, 4, 1, 6].length) (baseStart_2854597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2854597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2854597 prefixEnd_2854597 := by exact prefixLift 2854597
  have htrace : WordTrace (prefixWord ++ tailWord_2854597) baseStart_2854597 baseEnd_2854597 := by
    simpa [prefixWord, tailWord_2854597, baseEnd_2854597] using wordTrace_append hprefix tailTrace_2854597
  have hstable : (prefixWord ++ tailWord_2854597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2854597).length < 2 ^ (prefixWord ++ tailWord_2854597).sum := by decide
  have hdescent : baseEnd_2854597 < baseStart_2854597 := by decide
  rcases family_descends (prefixWord ++ tailWord_2854597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2854598 : List Nat := [6, 1, 2, 1, 1, 1, 2, 1, 1, 7]
def baseStart_2854598 : Nat := 118140960795 + 2854598 * 2 ^ 59
def prefixEnd_2854598 : Nat := 4983230072969 + 3 ^ 40 * 2854598 * 2
def baseEnd_2854598 : Nat := 488593616454442535298983

theorem tailTrace_2854598 : CollatzResearch.WordTrace tailWord_2854598 prefixEnd_2854598 488593616454442535298983 := by
  unfold tailWord_2854598
  simp only [CollatzResearch.WordTrace]
  refine ⟨3253616953508951480298139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 69410495008190964913026965 3253616953508951480298139)
  ·
    refine ⟨4880425430263427220447209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3253616953508951480298139 4880425430263427220447209)
    ·
      refine ⟨3660319072697570415335407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4880425430263427220447209 3660319072697570415335407)
      ·
        refine ⟨5490478609046355623003111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3660319072697570415335407 5490478609046355623003111)
        ·
          refine ⟨8235717913569533434504667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5490478609046355623003111 8235717913569533434504667)
          ·
            refine ⟨12353576870354300151757001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8235717913569533434504667 12353576870354300151757001)
            ·
              refine ⟨9265182652765725113817751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12353576870354300151757001 9265182652765725113817751)
              ·
                refine ⟨13897773979148587670726627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9265182652765725113817751 13897773979148587670726627)
                ·
                  refine ⟨20846660968722881506089941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13897773979148587670726627 20846660968722881506089941)
                  ·
                    refine ⟨488593616454442535298983, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 20846660968722881506089941 488593616454442535298983)
                    ·
                      rfl

theorem cell23_2854598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 2, 1, 1, 7].length) (baseStart_2854598 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2854598 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2854598 prefixEnd_2854598 := by exact prefixLift 2854598
  have htrace : WordTrace (prefixWord ++ tailWord_2854598) baseStart_2854598 baseEnd_2854598 := by
    simpa [prefixWord, tailWord_2854598, baseEnd_2854598] using wordTrace_append hprefix tailTrace_2854598
  have hstable : (prefixWord ++ tailWord_2854598).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2854598).length < 2 ^ (prefixWord ++ tailWord_2854598).sum := by decide
  have hdescent : baseEnd_2854598 < baseStart_2854598 := by decide
  rcases family_descends (prefixWord ++ tailWord_2854598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2854641 : List Nat := [1, 2, 2, 2, 2, 3, 4, 1, 6]
def baseStart_2854641 : Nat := 118140960795 + 2854641 * 2 ^ 59
def prefixEnd_2854641 : Nat := 4983230072969 + 3 ^ 40 * 2854641 * 2
def baseEnd_2854641 : Nat := 162866992114607881962139

theorem tailTrace_2854641 : CollatzResearch.WordTrace tailWord_2854641 prefixEnd_2854641 162866992114607881962139 := by
  unfold tailWord_2854641
  simp only [CollatzResearch.WordTrace]
  refine ⟨104117310851130665713355777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69411540567420443808903851 104117310851130665713355777)
  ·
    refine ⟨78087983138347999285016833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104117310851130665713355777 78087983138347999285016833)
    ·
      refine ⟨58565987353760999463762625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78087983138347999285016833 58565987353760999463762625)
      ·
        refine ⟨43924490515320749597821969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58565987353760999463762625 43924490515320749597821969)
        ·
          refine ⟨32943367886490562198366477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43924490515320749597821969 32943367886490562198366477)
          ·
            refine ⟨12353762957433960824387429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32943367886490562198366477 12353762957433960824387429)
            ·
              refine ⟨2316330554518867654572643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12353762957433960824387429 2316330554518867654572643)
              ·
                refine ⟨3474495831778301481858965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2316330554518867654572643 3474495831778301481858965)
                ·
                  refine ⟨162866992114607881962139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3474495831778301481858965 162866992114607881962139)
                  ·
                    rfl

theorem cell23_2854641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 4, 1, 6].length) (baseStart_2854641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2854641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2854641 prefixEnd_2854641 := by exact prefixLift 2854641
  have htrace : WordTrace (prefixWord ++ tailWord_2854641) baseStart_2854641 baseEnd_2854641 := by
    simpa [prefixWord, tailWord_2854641, baseEnd_2854641] using wordTrace_append hprefix tailTrace_2854641
  have hstable : (prefixWord ++ tailWord_2854641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2854641).length < 2 ^ (prefixWord ++ tailWord_2854641).sum := by decide
  have hdescent : baseEnd_2854641 < baseStart_2854641 := by decide
  rcases family_descends (prefixWord ++ tailWord_2854641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2854684 : List Nat := [2, 2, 3, 1, 1, 2, 1, 2, 3, 6]
def baseStart_2854684 : Nat := 118140960795 + 2854684 * 2 ^ 59
def prefixEnd_2854684 : Nat := 4983230072969 + 3 ^ 40 * 2854684 * 2
def baseEnd_2854684 : Nat := 488608336233204756473851

theorem tailTrace_2854684 : CollatzResearch.WordTrace tailWord_2854684 prefixEnd_2854684 488608336233204756473851 := by
  unfold tailWord_2854684
  simp only [CollatzResearch.WordTrace]
  refine ⟨52059439594987442028585553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69412586126649922704780737 52059439594987442028585553)
  ·
    refine ⟨39044579696240581521439165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52059439594987442028585553 39044579696240581521439165)
    ·
      refine ⟨14641717386090218070539687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39044579696240581521439165 14641717386090218070539687)
      ·
        refine ⟨21962576079135327105809531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14641717386090218070539687 21962576079135327105809531)
        ·
          refine ⟨32943864118702990658714297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21962576079135327105809531 32943864118702990658714297)
          ·
            refine ⟨24707898089027242994035723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32943864118702990658714297 24707898089027242994035723)
            ·
              refine ⟨37061847133540864491053585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24707898089027242994035723 37061847133540864491053585)
              ·
                refine ⟨27796385350155648368290189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37061847133540864491053585 27796385350155648368290189)
                ·
                  refine ⟨10423644506308368138108821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27796385350155648368290189 10423644506308368138108821)
                  ·
                    refine ⟨488608336233204756473851, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10423644506308368138108821 488608336233204756473851)
                    ·
                      rfl

theorem cell23_2854684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 1, 2, 3, 6].length) (baseStart_2854684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2854684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2854684 prefixEnd_2854684 := by exact prefixLift 2854684
  have htrace : WordTrace (prefixWord ++ tailWord_2854684) baseStart_2854684 baseEnd_2854684 := by
    simpa [prefixWord, tailWord_2854684, baseEnd_2854684] using wordTrace_append hprefix tailTrace_2854684
  have hstable : (prefixWord ++ tailWord_2854684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2854684).length < 2 ^ (prefixWord ++ tailWord_2854684).sum := by decide
  have hdescent : baseEnd_2854684 < baseStart_2854684 := by decide
  rcases family_descends (prefixWord ++ tailWord_2854684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2854708 : List Nat := [2, 5, 1, 1, 2, 1, 2, 1, 3, 1, 4]
def baseStart_2854708 : Nat := 118140960795 + 2854708 * 2 ^ 59
def prefixEnd_2854708 : Nat := 4983230072969 + 3 ^ 40 * 2854708 * 2
def baseEnd_2854708 : Nat := 1465837332235322175521443

theorem tailTrace_2854708 : CollatzResearch.WordTrace tailWord_2854708 prefixEnd_2854708 1465837332235322175521443 := by
  unfold tailWord_2854708
  simp only [CollatzResearch.WordTrace]
  refine ⟨52059877270943968078022389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69413169694591957437363185 52059877270943968078022389)
  ·
    refine ⟨4880613494150997007314599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 52059877270943968078022389 4880613494150997007314599)
    ·
      refine ⟨7320920241226495510971899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4880613494150997007314599 7320920241226495510971899)
      ·
        refine ⟨10981380361839743266457849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7320920241226495510971899 10981380361839743266457849)
        ·
          refine ⟨8236035271379807449843387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10981380361839743266457849 8236035271379807449843387)
          ·
            refine ⟨12354052907069711174765081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8236035271379807449843387 12354052907069711174765081)
            ·
              refine ⟨9265539680302283381073811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12354052907069711174765081 9265539680302283381073811)
              ·
                refine ⟨13898309520453425071610717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9265539680302283381073811 13898309520453425071610717)
                ·
                  refine ⟨5211866070170034401854019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13898309520453425071610717 5211866070170034401854019)
                  ·
                    refine ⟨7817799105255051602781029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5211866070170034401854019 7817799105255051602781029)
                    ·
                      refine ⟨1465837332235322175521443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7817799105255051602781029 1465837332235322175521443)
                      ·
                        rfl

theorem cell23_2854708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 2, 1, 3, 1, 4].length) (baseStart_2854708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2854708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2854708 prefixEnd_2854708 := by exact prefixLift 2854708
  have htrace : WordTrace (prefixWord ++ tailWord_2854708) baseStart_2854708 baseEnd_2854708 := by
    simpa [prefixWord, tailWord_2854708, baseEnd_2854708] using wordTrace_append hprefix tailTrace_2854708
  have hstable : (prefixWord ++ tailWord_2854708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2854708).length < 2 ^ (prefixWord ++ tailWord_2854708).sum := by decide
  have hdescent : baseEnd_2854708 < baseStart_2854708 := by decide
  rcases family_descends (prefixWord ++ tailWord_2854708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2854728 : List Nat := [2, 1, 3, 1, 1, 5, 1, 3, 1, 2, 3]
def baseStart_2854728 : Nat := 118140960795 + 2854728 * 2 ^ 59
def prefixEnd_2854728 : Nat := 4983230072969 + 3 ^ 40 * 2854728 * 2
def baseEnd_2854728 : Nat := 1465847601848412097271351

theorem tailTrace_2854728 : CollatzResearch.WordTrace tailWord_2854728 prefixEnd_2854728 1465847601848412097271351 := by
  unfold tailWord_2854728
  simp only [CollatzResearch.WordTrace]
  refine ⟨52060242000907739785886419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69413656001210319714515225 52060242000907739785886419)
  ·
    refine ⟨78090363001361609678829629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52060242000907739785886419 78090363001361609678829629)
    ·
      refine ⟨29283886125510603629561111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 78090363001361609678829629 29283886125510603629561111)
      ·
        refine ⟨43925829188265905444341667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29283886125510603629561111 43925829188265905444341667)
        ·
          refine ⟨65888743782398858166512501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43925829188265905444341667 65888743782398858166512501)
          ·
            refine ⟨6177069729599892953110547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 65888743782398858166512501 6177069729599892953110547)
            ·
              refine ⟨9265604594399839429665821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6177069729599892953110547 9265604594399839429665821)
              ·
                refine ⟨3474601722899939786124683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9265604594399839429665821 3474601722899939786124683)
                ·
                  refine ⟨5211902584349909679187025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3474601722899939786124683 5211902584349909679187025)
                  ·
                    refine ⟨3908926938262432259390269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5211902584349909679187025 3908926938262432259390269)
                    ·
                      refine ⟨1465847601848412097271351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3908926938262432259390269 1465847601848412097271351)
                      ·
                        rfl

theorem cell23_2854728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 5, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 5, 1, 3, 1, 2, 3].length) (baseStart_2854728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2854728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2854728 prefixEnd_2854728 := by exact prefixLift 2854728
  have htrace : WordTrace (prefixWord ++ tailWord_2854728) baseStart_2854728 baseEnd_2854728 := by
    simpa [prefixWord, tailWord_2854728, baseEnd_2854728] using wordTrace_append hprefix tailTrace_2854728
  have hstable : (prefixWord ++ tailWord_2854728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2854728).length < 2 ^ (prefixWord ++ tailWord_2854728).sum := by decide
  have hdescent : baseEnd_2854728 < baseStart_2854728 := by decide
  rcases family_descends (prefixWord ++ tailWord_2854728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2854734 : List Nat := [4, 1, 1, 1, 1, 1, 1, 1, 4, 2, 6]
def baseStart_2854734 : Nat := 118140960795 + 2854734 * 2 ^ 59
def prefixEnd_2854734 : Nat := 4983230072969 + 3 ^ 40 * 2854734 * 2
def baseEnd_2854734 : Nat := 1465850682732339073796323

theorem tailTrace_2854734 : CollatzResearch.WordTrace tailWord_2854734 prefixEnd_2854734 1465850682732339073796323 := by
  unfold tailWord_2854734
  simp only [CollatzResearch.WordTrace]
  refine ⟨13015087854974217824561407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 69413801893195828397660837 13015087854974217824561407)
  ·
    refine ⟨19522631782461326736842111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13015087854974217824561407 19522631782461326736842111)
    ·
      refine ⟨29283947673691990105263167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19522631782461326736842111 29283947673691990105263167)
      ·
        refine ⟨43925921510537985157894751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29283947673691990105263167 43925921510537985157894751)
        ·
          refine ⟨65888882265806977736842127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43925921510537985157894751 65888882265806977736842127)
          ·
            refine ⟨98833323398710466605263191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65888882265806977736842127 98833323398710466605263191)
            ·
              refine ⟨148249985098065699907894787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 98833323398710466605263191 148249985098065699907894787)
              ·
                refine ⟨222374977647098549861842181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 148249985098065699907894787 222374977647098549861842181)
                ·
                  refine ⟨41695308308830978099095409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 222374977647098549861842181 41695308308830978099095409)
                  ·
                    refine ⟨31271481231623233574321557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 41695308308830978099095409 31271481231623233574321557)
                    ·
                      refine ⟨1465850682732339073796323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 31271481231623233574321557 1465850682732339073796323)
                      ·
                        rfl

theorem cell23_2854734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 1, 4, 2, 6].length) (baseStart_2854734 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2854734 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2854734 prefixEnd_2854734 := by exact prefixLift 2854734
  have htrace : WordTrace (prefixWord ++ tailWord_2854734) baseStart_2854734 baseEnd_2854734 := by
    simpa [prefixWord, tailWord_2854734, baseEnd_2854734] using wordTrace_append hprefix tailTrace_2854734
  have hstable : (prefixWord ++ tailWord_2854734).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2854734).length < 2 ^ (prefixWord ++ tailWord_2854734).sum := by decide
  have hdescent : baseEnd_2854734 < baseStart_2854734 := by decide
  rcases family_descends (prefixWord ++ tailWord_2854734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2854755 : List Nat := [1, 1, 1, 5, 5, 1, 1, 1, 1, 2, 4]
def baseStart_2854755 : Nat := 118140960795 + 2854755 * 2 ^ 59
def prefixEnd_2854755 : Nat := 4983230072969 + 3 ^ 40 * 2854755 * 2
def baseEnd_2854755 : Nat := 1465861465826083491633727

theorem tailTrace_2854755 : CollatzResearch.WordTrace tailWord_2854755 prefixEnd_2854755 1465861465826083491633727 := by
  unfold tailWord_2854755
  simp only [CollatzResearch.WordTrace]
  refine ⟨104121468772717663183005719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69414312515145108788670479 104121468772717663183005719)
  ·
    refine ⟨156182203159076494774508579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104121468772717663183005719 156182203159076494774508579)
    ·
      refine ⟨234273304738614742161762869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 156182203159076494774508579 234273304738614742161762869)
      ·
        refine ⟨21963122319245132077665269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 234273304738614742161762869 21963122319245132077665269)
        ·
          refine ⟨2059042717429231132281119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 21963122319245132077665269 2059042717429231132281119)
          ·
            refine ⟨3088564076143846698421679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2059042717429231132281119 3088564076143846698421679)
            ·
              refine ⟨4632846114215770047632519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3088564076143846698421679 4632846114215770047632519)
              ·
                refine ⟨6949269171323655071448779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4632846114215770047632519 6949269171323655071448779)
                ·
                  refine ⟨10423903756985482607173169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6949269171323655071448779 10423903756985482607173169)
                  ·
                    refine ⟨7817927817739111955379877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10423903756985482607173169 7817927817739111955379877)
                    ·
                      refine ⟨1465861465826083491633727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7817927817739111955379877 1465861465826083491633727)
                      ·
                        rfl

theorem cell23_2854755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 5, 1, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 5, 1, 1, 1, 1, 2, 4].length) (baseStart_2854755 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2854755 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2854755 prefixEnd_2854755 := by exact prefixLift 2854755
  have htrace : WordTrace (prefixWord ++ tailWord_2854755) baseStart_2854755 baseEnd_2854755 := by
    simpa [prefixWord, tailWord_2854755, baseEnd_2854755] using wordTrace_append hprefix tailTrace_2854755
  have hstable : (prefixWord ++ tailWord_2854755).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2854755).length < 2 ^ (prefixWord ++ tailWord_2854755).sum := by decide
  have hdescent : baseEnd_2854755 < baseStart_2854755 := by decide
  rcases family_descends (prefixWord ++ tailWord_2854755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2854762 : List Nat := [3, 1, 3, 4, 1, 1, 2, 2, 1, 2, 3]
def baseStart_2854762 : Nat := 118140960795 + 2854762 * 2 ^ 59
def prefixEnd_2854762 : Nat := 4983230072969 + 3 ^ 40 * 2854762 * 2
def baseEnd_2854762 : Nat := 1465865060190664964246195

theorem tailTrace_2854762 : CollatzResearch.WordTrace tailWord_2854762 prefixEnd_2854762 1465865060190664964246195 := by
  unfold tailWord_2854762
  simp only [CollatzResearch.WordTrace]
  refine ⟨26030431020923075844627635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69414482722461535585673693 26030431020923075844627635)
  ·
    refine ⟨39045646531384613766941453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26030431020923075844627635 39045646531384613766941453)
    ·
      refine ⟨14642117449269230162603045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39045646531384613766941453 14642117449269230162603045)
      ·
        refine ⟨2745397021737980655488071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14642117449269230162603045 2745397021737980655488071)
        ·
          refine ⟨4118095532606970983232107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2745397021737980655488071 4118095532606970983232107)
          ·
            refine ⟨6177143298910456474848161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4118095532606970983232107 6177143298910456474848161)
            ·
              refine ⟨4632857474182842356136121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6177143298910456474848161 4632857474182842356136121)
              ·
                refine ⟨3474643105637131767102091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4632857474182842356136121 3474643105637131767102091)
                ·
                  refine ⟨5211964658455697650653137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3474643105637131767102091 5211964658455697650653137)
                  ·
                    refine ⟨3908973493841773237989853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5211964658455697650653137 3908973493841773237989853)
                    ·
                      refine ⟨1465865060190664964246195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3908973493841773237989853 1465865060190664964246195)
                      ·
                        rfl

theorem cell23_2854762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 1, 2, 2, 1, 2, 3].length) (baseStart_2854762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2854762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2854762 prefixEnd_2854762 := by exact prefixLift 2854762
  have htrace : WordTrace (prefixWord ++ tailWord_2854762) baseStart_2854762 baseEnd_2854762 := by
    simpa [prefixWord, tailWord_2854762, baseEnd_2854762] using wordTrace_append hprefix tailTrace_2854762
  have hstable : (prefixWord ++ tailWord_2854762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2854762).length < 2 ^ (prefixWord ++ tailWord_2854762).sum := by decide
  have hdescent : baseEnd_2854762 < baseStart_2854762 := by decide
  rcases family_descends (prefixWord ++ tailWord_2854762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2854836 : List Nat := [2, 5, 2, 1, 2, 1, 3, 1, 1, 3, 2]
def baseStart_2854836 : Nat := 118140960795 + 2854836 * 2 ^ 59
def prefixEnd_2854836 : Nat := 4983230072969 + 3 ^ 40 * 2854836 * 2
def baseEnd_2854836 : Nat := 1465903057759097674720855

theorem tailTrace_2854836 : CollatzResearch.WordTrace tailWord_2854836 prefixEnd_2854836 1465903057759097674720855 := by
  unfold tailWord_2854836
  simp only [CollatzResearch.WordTrace]
  refine ⟨52062211542712107008352181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69416282056949476011136241 52062211542712107008352181)
  ·
    refine ⟨4880832332129260032033017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 52062211542712107008352181 4880832332129260032033017)
    ·
      refine ⟨3660624249096945024024763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4880832332129260032033017 3660624249096945024024763)
      ·
        refine ⟨5490936373645417536037145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3660624249096945024024763 5490936373645417536037145)
        ·
          refine ⟨4118202280234063152027859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5490936373645417536037145 4118202280234063152027859)
          ·
            refine ⟨6177303420351094728041789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4118202280234063152027859 6177303420351094728041789)
            ·
              refine ⟨2316488782631660523015671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6177303420351094728041789 2316488782631660523015671)
              ·
                refine ⟨3474733173947490784523507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2316488782631660523015671 3474733173947490784523507)
                ·
                  refine ⟨5212099760921236176785261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3474733173947490784523507 5212099760921236176785261)
                  ·
                    refine ⟨1954537410345463566294473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5212099760921236176785261 1954537410345463566294473)
                    ·
                      refine ⟨1465903057759097674720855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1954537410345463566294473 1465903057759097674720855)
                      ·
                        rfl

theorem cell23_2854836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 1, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 1, 3, 1, 1, 3, 2].length) (baseStart_2854836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2854836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2854836 prefixEnd_2854836 := by exact prefixLift 2854836
  have htrace : WordTrace (prefixWord ++ tailWord_2854836) baseStart_2854836 baseEnd_2854836 := by
    simpa [prefixWord, tailWord_2854836, baseEnd_2854836] using wordTrace_append hprefix tailTrace_2854836
  have hstable : (prefixWord ++ tailWord_2854836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2854836).length < 2 ^ (prefixWord ++ tailWord_2854836).sum := by decide
  have hdescent : baseEnd_2854836 < baseStart_2854836 := by decide
  rcases family_descends (prefixWord ++ tailWord_2854836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2854858 : List Nat := [3, 1, 2, 1, 2, 1, 3, 1, 2, 5, 2]
def baseStart_2854858 : Nat := 118140960795 + 2854858 * 2 ^ 59
def prefixEnd_2854858 : Nat := 4983230072969 + 3 ^ 40 * 2854858 * 2
def baseEnd_2854858 : Nat := 1465914354333496588645753

theorem tailTrace_2854858 : CollatzResearch.WordTrace tailWord_2854858 prefixEnd_2854858 1465914354333496588645753 := by
  unfold tailWord_2854858
  simp only [CollatzResearch.WordTrace]
  refine ⟨26031306372836127943501307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69416816994229674516003485 26031306372836127943501307)
  ·
    refine ⟨39046959559254191915251961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26031306372836127943501307 39046959559254191915251961)
    ·
      refine ⟨29285219669440643936438971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39046959559254191915251961 29285219669440643936438971)
      ·
        refine ⟨43927829504160965904658457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29285219669440643936438971 43927829504160965904658457)
        ·
          refine ⟨32945872128120724428493843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43927829504160965904658457 32945872128120724428493843)
          ·
            refine ⟨49418808192181086642740765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32945872128120724428493843 49418808192181086642740765)
            ·
              refine ⟨18532053072067907491027787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 49418808192181086642740765 18532053072067907491027787)
              ·
                refine ⟨27798079608101861236541681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18532053072067907491027787 27798079608101861236541681)
                ·
                  refine ⟨20848559706076395927406261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27798079608101861236541681 20848559706076395927406261)
                  ·
                    refine ⟨1954552472444662118194337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 20848559706076395927406261 1954552472444662118194337)
                    ·
                      refine ⟨1465914354333496588645753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1954552472444662118194337 1465914354333496588645753)
                      ·
                        rfl

theorem cell23_2854858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 3, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 3, 1, 2, 5, 2].length) (baseStart_2854858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2854858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2854858 prefixEnd_2854858 := by exact prefixLift 2854858
  have htrace : WordTrace (prefixWord ++ tailWord_2854858) baseStart_2854858 baseEnd_2854858 := by
    simpa [prefixWord, tailWord_2854858, baseEnd_2854858] using wordTrace_append hprefix tailTrace_2854858
  have hstable : (prefixWord ++ tailWord_2854858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2854858).length < 2 ^ (prefixWord ++ tailWord_2854858).sum := by decide
  have hdescent : baseEnd_2854858 < baseStart_2854858 := by decide
  rcases family_descends (prefixWord ++ tailWord_2854858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2854871 : List Nat := [1, 1, 3, 2, 1, 1, 4, 2, 1, 3, 4]
def baseStart_2854871 : Nat := 118140960795 + 2854871 * 2 ^ 59
def prefixEnd_2854871 : Nat := 4983230072969 + 3 ^ 40 * 2854871 * 2
def baseEnd_2854871 : Nat := 1465921029582005037783193

theorem tailTrace_2854871 : CollatzResearch.WordTrace tailWord_2854871 prefixEnd_2854871 1465921029582005037783193 := by
  unfold tailWord_2854871
  simp only [CollatzResearch.WordTrace]
  refine ⟨104125699640297414994228467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69417133093531609996152311 104125699640297414994228467)
  ·
    refine ⟨156188549460446122491342701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104125699640297414994228467 156188549460446122491342701)
    ·
      refine ⟨58570706047667295934253513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 156188549460446122491342701 58570706047667295934253513)
      ·
        refine ⟨43928029535750471950690135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58570706047667295934253513 43928029535750471950690135)
        ·
          refine ⟨65892044303625707926035203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43928029535750471950690135 65892044303625707926035203)
          ·
            refine ⟨98838066455438561889052805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65892044303625707926035203 98838066455438561889052805)
            ·
              refine ⟨18532137460394730354197401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 98838066455438561889052805 18532137460394730354197401)
              ·
                refine ⟨13899103095296047765648051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18532137460394730354197401 13899103095296047765648051)
                ·
                  refine ⟨20848654642944071648472077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13899103095296047765648051 20848654642944071648472077)
                  ·
                    refine ⟨7818245491104026868177029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20848654642944071648472077 7818245491104026868177029)
                    ·
                      refine ⟨1465921029582005037783193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7818245491104026868177029 1465921029582005037783193)
                      ·
                        rfl

theorem cell23_2854871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 4, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 4, 2, 1, 3, 4].length) (baseStart_2854871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2854871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2854871 prefixEnd_2854871 := by exact prefixLift 2854871
  have htrace : WordTrace (prefixWord ++ tailWord_2854871) baseStart_2854871 baseEnd_2854871 := by
    simpa [prefixWord, tailWord_2854871, baseEnd_2854871] using wordTrace_append hprefix tailTrace_2854871
  have hstable : (prefixWord ++ tailWord_2854871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2854871).length < 2 ^ (prefixWord ++ tailWord_2854871).sum := by decide
  have hdescent : baseEnd_2854871 < baseStart_2854871 := by decide
  rcases family_descends (prefixWord ++ tailWord_2854871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2854888 : List Nat := [2, 1, 4, 1, 1, 1, 1, 1, 3, 6, 2]
def baseStart_2854888 : Nat := 118140960795 + 2854888 * 2 ^ 59
def prefixEnd_2854888 : Nat := 4983230072969 + 3 ^ 40 * 2854888 * 2
def baseEnd_2854888 : Nat := 1465929758753131471270615

theorem tailTrace_2854888 : CollatzResearch.WordTrace tailWord_2854888 prefixEnd_2854888 1465929758753131471270615 := by
  unfold tailWord_2854888
  simp only [CollatzResearch.WordTrace]
  refine ⟨52063159840617913448798659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69417546454157217931731545 52063159840617913448798659)
  ·
    refine ⟨78094739760926870173197989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52063159840617913448798659 78094739760926870173197989)
    ·
      refine ⟨14642763705173788157474623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 78094739760926870173197989 14642763705173788157474623)
      ·
        refine ⟨21964145557760682236211935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14642763705173788157474623 21964145557760682236211935)
        ·
          refine ⟨32946218336641023354317903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21964145557760682236211935 32946218336641023354317903)
          ·
            refine ⟨49419327504961535031476855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32946218336641023354317903 49419327504961535031476855)
            ·
              refine ⟨74128991257442302547215283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49419327504961535031476855 74128991257442302547215283)
              ·
                refine ⟨111193486886163453820822925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 74128991257442302547215283 111193486886163453820822925)
                ·
                  refine ⟨41697557582311295182808597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 111193486886163453820822925 41697557582311295182808597)
                  ·
                    refine ⟨1954573011670841961694153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 41697557582311295182808597 1954573011670841961694153)
                    ·
                      refine ⟨1465929758753131471270615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1954573011670841961694153 1465929758753131471270615)
                      ·
                        rfl

theorem cell23_2854888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 1, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 1, 3, 6, 2].length) (baseStart_2854888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2854888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2854888 prefixEnd_2854888 := by exact prefixLift 2854888
  have htrace : WordTrace (prefixWord ++ tailWord_2854888) baseStart_2854888 baseEnd_2854888 := by
    simpa [prefixWord, tailWord_2854888, baseEnd_2854888] using wordTrace_append hprefix tailTrace_2854888
  have hstable : (prefixWord ++ tailWord_2854888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2854888).length < 2 ^ (prefixWord ++ tailWord_2854888).sum := by decide
  have hdescent : baseEnd_2854888 < baseStart_2854888 := by decide
  rcases family_descends (prefixWord ++ tailWord_2854888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2854908 : List Nat := [2, 2, 2, 1, 2, 2, 2, 1, 4, 2, 3]
def baseStart_2854908 : Nat := 118140960795 + 2854908 * 2 ^ 59
def prefixEnd_2854908 : Nat := 4983230072969 + 3 ^ 40 * 2854908 * 2
def baseEnd_2854908 : Nat := 1465940028366221393020523

theorem tailTrace_2854908 : CollatzResearch.WordTrace tailWord_2854908 prefixEnd_2854908 1465940028366221393020523 := by
  unfold tailWord_2854908
  simp only [CollatzResearch.WordTrace]
  refine ⟨52063524570581685156662689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69418032760775580208883585 52063524570581685156662689)
  ·
    refine ⟨39047643427936263867497017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52063524570581685156662689 39047643427936263867497017)
    ·
      refine ⟨29285732570952197900622763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39047643427936263867497017 29285732570952197900622763)
      ·
        refine ⟨43928598856428296850934145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29285732570952197900622763 43928598856428296850934145)
        ·
          refine ⟨32946449142321222638200609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43928598856428296850934145 32946449142321222638200609)
          ·
            refine ⟨24709836856740916978650457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32946449142321222638200609 24709836856740916978650457)
            ·
              refine ⟨18532377642555687733987843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24709836856740916978650457 18532377642555687733987843)
              ·
                refine ⟨27798566463833531600981765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18532377642555687733987843 27798566463833531600981765)
                ·
                  refine ⟨5212231211968787175184081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27798566463833531600981765 5212231211968787175184081)
                  ·
                    refine ⟨3909173408976590381388061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5212231211968787175184081 3909173408976590381388061)
                    ·
                      refine ⟨1465940028366221393020523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3909173408976590381388061 1465940028366221393020523)
                      ·
                        rfl

theorem cell23_2854908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 2, 1, 4, 2, 3].length) (baseStart_2854908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2854908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2854908 prefixEnd_2854908 := by exact prefixLift 2854908
  have htrace : WordTrace (prefixWord ++ tailWord_2854908) baseStart_2854908 baseEnd_2854908 := by
    simpa [prefixWord, tailWord_2854908, baseEnd_2854908] using wordTrace_append hprefix tailTrace_2854908
  have hstable : (prefixWord ++ tailWord_2854908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2854908).length < 2 ^ (prefixWord ++ tailWord_2854908).sum := by decide
  have hdescent : baseEnd_2854908 < baseStart_2854908 := by decide
  rcases family_descends (prefixWord ++ tailWord_2854908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2854965 : List Nat := [1, 3, 3, 1, 1, 1, 3, 1, 4, 3, 2]
def baseStart_2854965 : Nat := 118140960795 + 2854965 * 2 ^ 59
def prefixEnd_2854965 : Nat := 4983230072969 + 3 ^ 40 * 2854965 * 2
def baseEnd_2854965 : Nat := 1465969296763527670007761

theorem tailTrace_2854965 : CollatzResearch.WordTrace tailWord_2854965 prefixEnd_2854965 1465969296763527670007761 := by
  unfold tailWord_2854965
  simp only [CollatzResearch.WordTrace]
  refine ⟨104129128101956869048150349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69419418734637912698766899 104129128101956869048150349)
  ·
    refine ⟨39048423038233825893056381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 104129128101956869048150349 39048423038233825893056381)
    ·
      refine ⟨14643158639337684709896143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39048423038233825893056381 14643158639337684709896143)
      ·
        refine ⟨21964737959006527064844215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14643158639337684709896143 21964737959006527064844215)
        ·
          refine ⟨32947106938509790597266323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21964737959006527064844215 32947106938509790597266323)
          ·
            refine ⟨49420660407764685895899485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32947106938509790597266323 49420660407764685895899485)
            ·
              refine ⟨18532747652911757210962307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 49420660407764685895899485 18532747652911757210962307)
              ·
                refine ⟨27799121479367635816443461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18532747652911757210962307 27799121479367635816443461)
                ·
                  refine ⟨5212335277381431715583149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27799121479367635816443461 5212335277381431715583149)
                  ·
                    refine ⟨1954625729018036893343681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5212335277381431715583149 1954625729018036893343681)
                    ·
                      refine ⟨1465969296763527670007761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1954625729018036893343681 1465969296763527670007761)
                      ·
                        rfl

theorem cell23_2854965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 3, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 3, 1, 4, 3, 2].length) (baseStart_2854965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2854965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2854965 prefixEnd_2854965 := by exact prefixLift 2854965
  have htrace : WordTrace (prefixWord ++ tailWord_2854965) baseStart_2854965 baseEnd_2854965 := by
    simpa [prefixWord, tailWord_2854965, baseEnd_2854965] using wordTrace_append hprefix tailTrace_2854965
  have hstable : (prefixWord ++ tailWord_2854965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2854965).length < 2 ^ (prefixWord ++ tailWord_2854965).sum := by decide
  have hdescent : baseEnd_2854965 < baseStart_2854965 := by decide
  rcases family_descends (prefixWord ++ tailWord_2854965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2854971 : List Nat := [1, 1, 1, 1, 1, 2, 1, 6, 3, 6]
def baseStart_2854971 : Nat := 118140960795 + 2854971 * 2 ^ 59
def prefixEnd_2854971 : Nat := 4983230072969 + 3 ^ 40 * 2854971 * 2
def baseEnd_2854971 : Nat := 488657459215818215510911

theorem tailTrace_2854971 : CollatzResearch.WordTrace tailWord_2854971 prefixEnd_2854971 488657459215818215510911 := by
  unfold tailWord_2854971
  simp only [CollatzResearch.WordTrace]
  refine ⟨104129346939935132072868767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69419564626623421381912511 104129346939935132072868767)
  ·
    refine ⟨156194020409902698109303151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104129346939935132072868767 156194020409902698109303151)
    ·
      refine ⟨234291030614854047163954727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 156194020409902698109303151 234291030614854047163954727)
      ·
        refine ⟨351436545922281070745932091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 234291030614854047163954727 351436545922281070745932091)
        ·
          refine ⟨527154818883421606118898137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 351436545922281070745932091 527154818883421606118898137)
          ·
            refine ⟨395366114162566204589173603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 527154818883421606118898137 395366114162566204589173603)
            ·
              refine ⟨593049171243849306883760405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 395366114162566204589173603 593049171243849306883760405)
              ·
                refine ⟨27799179902055436260176269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 593049171243849306883760405 27799179902055436260176269)
                ·
                  refine ⟨10424692463270788597566101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27799179902055436260176269 10424692463270788597566101)
                  ·
                    refine ⟨488657459215818215510911, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10424692463270788597566101 488657459215818215510911)
                    ·
                      rfl

theorem cell23_2854971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 6, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 6, 3, 6].length) (baseStart_2854971 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2854971 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2854971 prefixEnd_2854971 := by exact prefixLift 2854971
  have htrace : WordTrace (prefixWord ++ tailWord_2854971) baseStart_2854971 baseEnd_2854971 := by
    simpa [prefixWord, tailWord_2854971, baseEnd_2854971] using wordTrace_append hprefix tailTrace_2854971
  have hstable : (prefixWord ++ tailWord_2854971).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2854971).length < 2 ^ (prefixWord ++ tailWord_2854971).sum := by decide
  have hdescent : baseEnd_2854971 < baseStart_2854971 := by decide
  rcases family_descends (prefixWord ++ tailWord_2854971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2855001 : List Nat := [1, 2, 1, 2, 2, 1, 3, 11]
def baseStart_2855001 : Nat := 118140960795 + 2855001 * 2 ^ 59
def prefixEnd_2855001 : Nat := 4983230072969 + 3 ^ 40 * 2855001 * 2
def baseEnd_2855001 : Nat := 54295843780262575153985

theorem tailTrace_2855001 : CollatzResearch.WordTrace tailWord_2855001 prefixEnd_2855001 54295843780262575153985 := by
  unfold tailWord_2855001
  simp only [CollatzResearch.WordTrace]
  refine ⟨104130441129826447196460857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69420294086550964797640571 104130441129826447196460857)
  ·
    refine ⟨78097830847369835397345643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104130441129826447196460857 78097830847369835397345643)
    ·
      refine ⟨117146746271054753096018465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78097830847369835397345643 117146746271054753096018465)
      ·
        refine ⟨87860059703291064822013849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 117146746271054753096018465 87860059703291064822013849)
        ·
          refine ⟨65895044777468298616510387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 87860059703291064822013849 65895044777468298616510387)
          ·
            refine ⟨98842567166202447924765581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65895044777468298616510387 98842567166202447924765581)
            ·
              refine ⟨37065962687325917971787093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 98842567166202447924765581 37065962687325917971787093)
              ·
                refine ⟨54295843780262575153985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 37065962687325917971787093 54295843780262575153985)
                ·
                  rfl

theorem cell23_2855001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 3, 11].length) (baseStart_2855001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2855001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2855001 prefixEnd_2855001 := by exact prefixLift 2855001
  have htrace : WordTrace (prefixWord ++ tailWord_2855001) baseStart_2855001 baseEnd_2855001 := by
    simpa [prefixWord, tailWord_2855001, baseEnd_2855001] using wordTrace_append hprefix tailTrace_2855001
  have hstable : (prefixWord ++ tailWord_2855001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2855001).length < 2 ^ (prefixWord ++ tailWord_2855001).sum := by decide
  have hdescent : baseEnd_2855001 < baseStart_2855001 := by decide
  rcases family_descends (prefixWord ++ tailWord_2855001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2855005 : List Nat := [1, 4, 4, 1, 1, 1, 1, 1, 3, 6]
def baseStart_2855005 : Nat := 118140960795 + 2855005 * 2 ^ 59
def prefixEnd_2855005 : Nat := 4983230072969 + 3 ^ 40 * 2855005 * 2
def baseEnd_2855005 : Nat := 488663278663235837835859

theorem tailTrace_2855005 : CollatzResearch.WordTrace tailWord_2855005 prefixEnd_2855005 488663278663235837835859 := by
  unfold tailWord_2855005
  simp only [CollatzResearch.WordTrace]
  refine ⟨104130587021811955879606469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69420391347874637253070979 104130587021811955879606469)
  ·
    refine ⟨19524485066589741727426213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 104130587021811955879606469 19524485066589741727426213)
    ·
      refine ⟨3660840949985576573892415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19524485066589741727426213 3660840949985576573892415)
      ·
        refine ⟨5491261424978364860838623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3660840949985576573892415 5491261424978364860838623)
        ·
          refine ⟨8236892137467547291257935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5491261424978364860838623 8236892137467547291257935)
          ·
            refine ⟨12355338206201320936886903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8236892137467547291257935 12355338206201320936886903)
            ·
              refine ⟨18533007309301981405330355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12355338206201320936886903 18533007309301981405330355)
              ·
                refine ⟨27799510963952972107995533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18533007309301981405330355 27799510963952972107995533)
                ·
                  refine ⟨10424816611482364540498325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27799510963952972107995533 10424816611482364540498325)
                  ·
                    refine ⟨488663278663235837835859, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10424816611482364540498325 488663278663235837835859)
                    ·
                      rfl

theorem cell23_2855005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 1, 1, 3, 6].length) (baseStart_2855005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2855005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2855005 prefixEnd_2855005 := by exact prefixLift 2855005
  have htrace : WordTrace (prefixWord ++ tailWord_2855005) baseStart_2855005 baseEnd_2855005 := by
    simpa [prefixWord, tailWord_2855005, baseEnd_2855005] using wordTrace_append hprefix tailTrace_2855005
  have hstable : (prefixWord ++ tailWord_2855005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2855005).length < 2 ^ (prefixWord ++ tailWord_2855005).sum := by decide
  have hdescent : baseEnd_2855005 < baseStart_2855005 := by decide
  rcases family_descends (prefixWord ++ tailWord_2855005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2855008 : List Nat := [2, 1, 1, 3, 2, 3, 1, 1, 3, 2, 4]
def baseStart_2855008 : Nat := 118140960795 + 2855008 * 2 ^ 59
def prefixEnd_2855008 : Nat := 4983230072969 + 3 ^ 40 * 2855008 * 2
def baseEnd_2855008 : Nat := 1465991376431671001770063

theorem tailTrace_2855008 : CollatzResearch.WordTrace tailWord_2855008 prefixEnd_2855008 1465991376431671001770063 := by
  unfold tailWord_2855008
  simp only [CollatzResearch.WordTrace]
  refine ⟨52065348220400543695982839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69420464293867391594643785 52065348220400543695982839)
  ·
    refine ⟨78098022330600815543974259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52065348220400543695982839 78098022330600815543974259)
    ·
      refine ⟨117147033495901223315961389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78098022330600815543974259 117147033495901223315961389)
      ·
        refine ⟨43930137560962958743485521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 117147033495901223315961389 43930137560962958743485521)
        ·
          refine ⟨32947603170722219057614141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43930137560962958743485521 32947603170722219057614141)
          ·
            refine ⟨12355351189020832146605303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32947603170722219057614141 12355351189020832146605303)
            ·
              refine ⟨18533026783531248219907955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12355351189020832146605303 18533026783531248219907955)
              ·
                refine ⟨27799540175296872329861933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18533026783531248219907955 27799540175296872329861933)
                ·
                  refine ⟨10424827565736327123698225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27799540175296872329861933 10424827565736327123698225)
                  ·
                    refine ⟨7818620674302245342773669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10424827565736327123698225 7818620674302245342773669)
                    ·
                      refine ⟨1465991376431671001770063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7818620674302245342773669 1465991376431671001770063)
                      ·
                        rfl

theorem cell23_2855008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 1, 1, 3, 2, 4].length) (baseStart_2855008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2855008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2855008 prefixEnd_2855008 := by exact prefixLift 2855008
  have htrace : WordTrace (prefixWord ++ tailWord_2855008) baseStart_2855008 baseEnd_2855008 := by
    simpa [prefixWord, tailWord_2855008, baseEnd_2855008] using wordTrace_append hprefix tailTrace_2855008
  have hstable : (prefixWord ++ tailWord_2855008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2855008).length < 2 ^ (prefixWord ++ tailWord_2855008).sum := by decide
  have hdescent : baseEnd_2855008 < baseStart_2855008 := by decide
  rcases family_descends (prefixWord ++ tailWord_2855008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2855018 : List Nat := [3, 1, 3, 2, 3, 11]
def baseStart_2855018 : Nat := 118140960795 + 2855018 * 2 ^ 59
def prefixEnd_2855018 : Nat := 4983230072969 + 3 ^ 40 * 2855018 * 2
def baseEnd_2855018 : Nat := 6032907453655209722819

theorem tailTrace_2855018 : CollatzResearch.WordTrace tailWord_2855018 prefixEnd_2855018 6032907453655209722819 := by
  unfold tailWord_2855018
  simp only [CollatzResearch.WordTrace]
  refine ⟨26032765292691214774957427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69420707447176572733219805 26032765292691214774957427)
  ·
    refine ⟨39049147939036822162436141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26032765292691214774957427 39049147939036822162436141)
    ·
      refine ⟨14643430477138808310913553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39049147939036822162436141 14643430477138808310913553)
      ·
        refine ⟨10982572857854106233185165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14643430477138808310913553 10982572857854106233185165)
        ·
          refine ⟨4118464821695289837444437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10982572857854106233185165 4118464821695289837444437)
          ·
            refine ⟨6032907453655209722819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 4118464821695289837444437 6032907453655209722819)
            ·
              rfl

theorem cell23_2855018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 11].length) (baseStart_2855018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2855018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2855018 prefixEnd_2855018 := by exact prefixLift 2855018
  have htrace : WordTrace (prefixWord ++ tailWord_2855018) baseStart_2855018 baseEnd_2855018 := by
    simpa [prefixWord, tailWord_2855018, baseEnd_2855018] using wordTrace_append hprefix tailTrace_2855018
  have hstable : (prefixWord ++ tailWord_2855018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2855018).length < 2 ^ (prefixWord ++ tailWord_2855018).sum := by decide
  have hdescent : baseEnd_2855018 < baseStart_2855018 := by decide
  rcases family_descends (prefixWord ++ tailWord_2855018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2855022 : List Nat := [4, 1, 2, 2, 1, 1, 4, 2, 2, 4]
def baseStart_2855022 : Nat := 118140960795 + 2855022 * 2 ^ 59
def prefixEnd_2855022 : Nat := 4983230072969 + 3 ^ 40 * 2855022 * 2
def baseEnd_2855022 : Nat := 488666188386944648998333

theorem tailTrace_2855022 : CollatzResearch.WordTrace tailWord_2855022 prefixEnd_2855022 488666188386944648998333 := by
  unfold tailWord_2855022
  simp only [CollatzResearch.WordTrace]
  refine ⟨13016400882843795972871915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 69420804708500245188650213 13016400882843795972871915)
  ·
    refine ⟨19524601324265693959307873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13016400882843795972871915 19524601324265693959307873)
    ·
      refine ⟨14643450993199270469480905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19524601324265693959307873 14643450993199270469480905)
      ·
        refine ⟨10982588244899452852110679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14643450993199270469480905 10982588244899452852110679)
        ·
          refine ⟨16473882367349179278166019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10982588244899452852110679 16473882367349179278166019)
          ·
            refine ⟨24710823551023768917249029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16473882367349179278166019 24710823551023768917249029)
            ·
              refine ⟨4633279415816956671984193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24710823551023768917249029 4633279415816956671984193)
              ·
                refine ⟨3474959561862717503988145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4633279415816956671984193 3474959561862717503988145)
                ·
                  refine ⟨2606219671397038127991109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3474959561862717503988145 2606219671397038127991109)
                  ·
                    refine ⟨488666188386944648998333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2606219671397038127991109 488666188386944648998333)
                    ·
                      rfl

theorem cell23_2855022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 4, 2, 2, 4].length) (baseStart_2855022 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2855022 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2855022 prefixEnd_2855022 := by exact prefixLift 2855022
  have htrace : WordTrace (prefixWord ++ tailWord_2855022) baseStart_2855022 baseEnd_2855022 := by
    simpa [prefixWord, tailWord_2855022, baseEnd_2855022] using wordTrace_append hprefix tailTrace_2855022
  have hstable : (prefixWord ++ tailWord_2855022).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2855022).length < 2 ^ (prefixWord ++ tailWord_2855022).sum := by decide
  have hdescent : baseEnd_2855022 < baseStart_2855022 := by decide
  rcases family_descends (prefixWord ++ tailWord_2855022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2855045 : List Nat := [1, 3, 1, 1, 5, 1, 1, 3, 1, 3, 3]
def baseStart_2855045 : Nat := 118140960795 + 2855045 * 2 ^ 59
def prefixEnd_2855045 : Nat := 4983230072969 + 3 ^ 40 * 2855045 * 2
def baseEnd_2855045 : Nat := 1466010375215887357007393

theorem tailTrace_2855045 : CollatzResearch.WordTrace tailWord_2855045 prefixEnd_2855045 1466010375215887357007393 := by
  unfold tailWord_2855045
  simp only [CollatzResearch.WordTrace]
  refine ⟨104132045941667042711062589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69421363961111361807375059 104132045941667042711062589)
  ·
    refine ⟨39049517228125141016648471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 104132045941667042711062589 39049517228125141016648471)
    ·
      refine ⟨58574275842187711524972707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39049517228125141016648471 58574275842187711524972707)
      ·
        refine ⟨87861413763281567287459061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58574275842187711524972707 87861413763281567287459061)
        ·
          refine ⟨8237007540307646933199287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 87861413763281567287459061 8237007540307646933199287)
          ·
            refine ⟨12355511310461470399798931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8237007540307646933199287 12355511310461470399798931)
            ·
              refine ⟨18533266965692205599698397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12355511310461470399798931 18533266965692205599698397)
              ·
                refine ⟨6949975112134577099886899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18533266965692205599698397 6949975112134577099886899)
                ·
                  refine ⟨10424962668201865649830349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6949975112134577099886899 10424962668201865649830349)
                  ·
                    refine ⟨3909361000575699618686381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10424962668201865649830349 3909361000575699618686381)
                    ·
                      refine ⟨1466010375215887357007393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3909361000575699618686381 1466010375215887357007393)
                      ·
                        rfl

theorem cell23_2855045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 1, 3, 1, 3, 3].length) (baseStart_2855045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2855045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2855045 prefixEnd_2855045 := by exact prefixLift 2855045
  have htrace : WordTrace (prefixWord ++ tailWord_2855045) baseStart_2855045 baseEnd_2855045 := by
    simpa [prefixWord, tailWord_2855045, baseEnd_2855045] using wordTrace_append hprefix tailTrace_2855045
  have hstable : (prefixWord ++ tailWord_2855045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2855045).length < 2 ^ (prefixWord ++ tailWord_2855045).sum := by decide
  have hdescent : baseEnd_2855045 < baseStart_2855045 := by decide
  rcases family_descends (prefixWord ++ tailWord_2855045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2855066 : List Nat := [3, 1, 1, 5, 2, 2, 2, 1, 1, 2, 3]
def baseStart_2855066 : Nat := 118140960795 + 2855066 * 2 ^ 59
def prefixEnd_2855066 : Nat := 4983230072969 + 3 ^ 40 * 2855066 * 2
def baseEnd_2855066 : Nat := 1466021158309631774844797

theorem tailTrace_2855066 : CollatzResearch.WordTrace tailWord_2855066 prefixEnd_2855066 1466021158309631774844797 := by
  unfold tailWord_2855066
  simp only [CollatzResearch.WordTrace]
  refine ⟨26033202968647740824394263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69421874583060642198384701 26033202968647740824394263)
  ·
    refine ⟨39049804452971611236591395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26033202968647740824394263 39049804452971611236591395)
    ·
      refine ⟨58574706679457416854887093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39049804452971611236591395 58574706679457416854887093)
      ·
        refine ⟨5491378751199132830145665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 58574706679457416854887093 5491378751199132830145665)
        ·
          refine ⟨4118534063399349622609249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5491378751199132830145665 4118534063399349622609249)
          ·
            refine ⟨3088900547549512216956937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4118534063399349622609249 3088900547549512216956937)
            ·
              refine ⟨2316675410662134162717703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3088900547549512216956937 2316675410662134162717703)
              ·
                refine ⟨3475013115993201244076555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2316675410662134162717703 3475013115993201244076555)
                ·
                  refine ⟨5212519673989801866114833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3475013115993201244076555 5212519673989801866114833)
                  ·
                    refine ⟨3909389755492351399586125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5212519673989801866114833 3909389755492351399586125)
                    ·
                      refine ⟨1466021158309631774844797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3909389755492351399586125 1466021158309631774844797)
                      ·
                        rfl

theorem cell23_2855066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 2, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 2, 2, 1, 1, 2, 3].length) (baseStart_2855066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2855066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2855066 prefixEnd_2855066 := by exact prefixLift 2855066
  have htrace : WordTrace (prefixWord ++ tailWord_2855066) baseStart_2855066 baseEnd_2855066 := by
    simpa [prefixWord, tailWord_2855066, baseEnd_2855066] using wordTrace_append hprefix tailTrace_2855066
  have hstable : (prefixWord ++ tailWord_2855066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2855066).length < 2 ^ (prefixWord ++ tailWord_2855066).sum := by decide
  have hdescent : baseEnd_2855066 < baseStart_2855066 := by decide
  rcases family_descends (prefixWord ++ tailWord_2855066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2855079 : List Nat := [1, 1, 6, 2, 2, 1, 1, 1, 4, 1, 3]
def baseStart_2855079 : Nat := 118140960795 + 2855079 * 2 ^ 59
def prefixEnd_2855079 : Nat := 4983230072969 + 3 ^ 40 * 2855079 * 2
def baseEnd_2855079 : Nat := 1466027833558140223982237

theorem tailTrace_2855079 : CollatzResearch.WordTrace tailWord_2855079 prefixEnd_2855079 1466027833558140223982237 := by
  unfold tailWord_2855079
  simp only [CollatzResearch.WordTrace]
  refine ⟨104133286023543866517800291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69422190682362577678533527 104133286023543866517800291)
  ·
    refine ⟨156199929035315799776700437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104133286023543866517800291 156199929035315799776700437)
    ·
      refine ⟨7321871673530428114532833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 156199929035315799776700437 7321871673530428114532833)
      ·
        refine ⟨5491403755147821085899625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7321871673530428114532833 5491403755147821085899625)
        ·
          refine ⟨4118552816360865814424719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5491403755147821085899625 4118552816360865814424719)
          ·
            refine ⟨6177829224541298721637079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4118552816360865814424719 6177829224541298721637079)
            ·
              refine ⟨9266743836811948082455619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6177829224541298721637079 9266743836811948082455619)
              ·
                refine ⟨13900115755217922123683429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9266743836811948082455619 13900115755217922123683429)
                ·
                  refine ⟨2606271704103360398190643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13900115755217922123683429 2606271704103360398190643)
                  ·
                    refine ⟨3909407556155040597285965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2606271704103360398190643 3909407556155040597285965)
                    ·
                      refine ⟨1466027833558140223982237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3909407556155040597285965 1466027833558140223982237)
                      ·
                        rfl

theorem cell23_2855079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 1, 1, 1, 4, 1, 3].length) (baseStart_2855079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2855079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2855079 prefixEnd_2855079 := by exact prefixLift 2855079
  have htrace : WordTrace (prefixWord ++ tailWord_2855079) baseStart_2855079 baseEnd_2855079 := by
    simpa [prefixWord, tailWord_2855079, baseEnd_2855079] using wordTrace_append hprefix tailTrace_2855079
  have hstable : (prefixWord ++ tailWord_2855079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2855079).length < 2 ^ (prefixWord ++ tailWord_2855079).sum := by decide
  have hdescent : baseEnd_2855079 < baseStart_2855079 := by decide
  rcases family_descends (prefixWord ++ tailWord_2855079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2855145 : List Nat := [1, 2, 1, 1, 1, 2, 2, 3, 1, 7, 2]
def baseStart_2855145 : Nat := 118140960795 + 2855145 * 2 ^ 59
def prefixEnd_2855145 : Nat := 4983230072969 + 3 ^ 40 * 2855145 * 2
def baseEnd_2855145 : Nat := 1466061723281336965756933

theorem tailTrace_2855145 : CollatzResearch.WordTrace tailWord_2855145 prefixEnd_2855145 1466061723281336965756933 := by
  unfold tailWord_2855145
  simp only [CollatzResearch.WordTrace]
  refine ⟨104135693241304759789702889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69423795494203173193135259 104135693241304759789702889)
  ·
    refine ⟨78101769930978569842277167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104135693241304759789702889 78101769930978569842277167)
    ·
      refine ⟨117152654896467854763415751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78101769930978569842277167 117152654896467854763415751)
      ·
        refine ⟨175728982344701782145123627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117152654896467854763415751 175728982344701782145123627)
        ·
          refine ⟨263593473517052673217685441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 175728982344701782145123627 263593473517052673217685441)
          ·
            refine ⟨197695105137789504913264081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 263593473517052673217685441 197695105137789504913264081)
            ·
              refine ⟨148271328853342128684948061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 197695105137789504913264081 148271328853342128684948061)
              ·
                refine ⟨55601748320003298256855523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 148271328853342128684948061 55601748320003298256855523)
                ·
                  refine ⟨83402622480004947385283285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 55601748320003298256855523 83402622480004947385283285)
                  ·
                    refine ⟨1954748964375115954342577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 83402622480004947385283285 1954748964375115954342577)
                    ·
                      refine ⟨1466061723281336965756933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1954748964375115954342577 1466061723281336965756933)
                      ·
                        rfl

theorem cell23_2855145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 3, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 3, 1, 7, 2].length) (baseStart_2855145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2855145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2855145 prefixEnd_2855145 := by exact prefixLift 2855145
  have htrace : WordTrace (prefixWord ++ tailWord_2855145) baseStart_2855145 baseEnd_2855145 := by
    simpa [prefixWord, tailWord_2855145, baseEnd_2855145] using wordTrace_append hprefix tailTrace_2855145
  have hstable : (prefixWord ++ tailWord_2855145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2855145).length < 2 ^ (prefixWord ++ tailWord_2855145).sum := by decide
  have hdescent : baseEnd_2855145 < baseStart_2855145 := by decide
  rcases family_descends (prefixWord ++ tailWord_2855145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2855168 : List Nat := [2, 1, 1, 2, 1, 1, 4, 1, 2, 8]
def baseStart_2855168 : Nat := 118140960795 + 2855168 * 2 ^ 59
def prefixEnd_2855168 : Nat := 4983230072969 + 3 ^ 40 * 2855168 * 2
def baseEnd_2855168 : Nat := 488691177778796791923109

theorem tailTrace_2855168 : CollatzResearch.WordTrace tailWord_2855168 prefixEnd_2855168 488691177778796791923109 := by
  unfold tailWord_2855168
  simp only [CollatzResearch.WordTrace]
  refine ⟨52068266060110717358895079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69424354746814289811860105 52068266060110717358895079)
  ·
    refine ⟨78102399090166076038342619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52068266060110717358895079 78102399090166076038342619)
    ·
      refine ⟨117153598635249114057513929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78102399090166076038342619 117153598635249114057513929)
      ·
        refine ⟨87865198976436835543135447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 117153598635249114057513929 87865198976436835543135447)
        ·
          refine ⟨131797798464655253314703171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87865198976436835543135447 131797798464655253314703171)
          ·
            refine ⟨197696697696982879972054757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 131797798464655253314703171 197696697696982879972054757)
            ·
              refine ⟨37068130818184289994760267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 197696697696982879972054757 37068130818184289994760267)
              ·
                refine ⟨55602196227276434992140401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37068130818184289994760267 55602196227276434992140401)
                ·
                  refine ⟨41701647170457326244105301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 55602196227276434992140401 41701647170457326244105301)
                  ·
                    refine ⟨488691177778796791923109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 41701647170457326244105301 488691177778796791923109)
                    ·
                      rfl

theorem cell23_2855168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 1, 2, 8].length) (baseStart_2855168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2855168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2855168 prefixEnd_2855168 := by exact prefixLift 2855168
  have htrace : WordTrace (prefixWord ++ tailWord_2855168) baseStart_2855168 baseEnd_2855168 := by
    simpa [prefixWord, tailWord_2855168, baseEnd_2855168] using wordTrace_append hprefix tailTrace_2855168
  have hstable : (prefixWord ++ tailWord_2855168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2855168).length < 2 ^ (prefixWord ++ tailWord_2855168).sum := by decide
  have hdescent : baseEnd_2855168 < baseStart_2855168 := by decide
  rcases family_descends (prefixWord ++ tailWord_2855168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2855192 : List Nat := [2, 1, 2, 3, 1, 2, 2, 2, 2, 4, 2]
def baseStart_2855192 : Nat := 118140960795 + 2855192 * 2 ^ 59
def prefixEnd_2855192 : Nat := 4983230072969 + 3 ^ 40 * 2855192 * 2
def baseEnd_2855192 : Nat := 1466085856872098281869217

theorem tailTrace_2855192 : CollatzResearch.WordTrace tailWord_2855192 prefixEnd_2855192 1466085856872098281869217 := by
  unfold tailWord_2855192
  simp only [CollatzResearch.WordTrace]
  refine ⟨52068703736067243408331915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69424938314756324544442553 52068703736067243408331915)
  ·
    refine ⟨78103055604100865112497873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52068703736067243408331915 78103055604100865112497873)
    ·
      refine ⟨58577291703075648834373405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78103055604100865112497873 58577291703075648834373405)
      ·
        refine ⟨21966484388653368312890027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 58577291703075648834373405 21966484388653368312890027)
        ·
          refine ⟨32949726582980052469335041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21966484388653368312890027 32949726582980052469335041)
          ·
            refine ⟨24712294937235039352001281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32949726582980052469335041 24712294937235039352001281)
            ·
              refine ⟨18534221202926279514000961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24712294937235039352001281 18534221202926279514000961)
              ·
                refine ⟨13900665902194709635500721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18534221202926279514000961 13900665902194709635500721)
                ·
                  refine ⟨10425499426646032226625541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13900665902194709635500721 10425499426646032226625541)
                  ·
                    refine ⟨1954781142496131042492289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10425499426646032226625541 1954781142496131042492289)
                    ·
                      refine ⟨1466085856872098281869217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1954781142496131042492289 1466085856872098281869217)
                      ·
                        rfl

theorem cell23_2855192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 2, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 2, 2, 2, 4, 2].length) (baseStart_2855192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2855192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2855192 prefixEnd_2855192 := by exact prefixLift 2855192
  have htrace : WordTrace (prefixWord ++ tailWord_2855192) baseStart_2855192 baseEnd_2855192 := by
    simpa [prefixWord, tailWord_2855192, baseEnd_2855192] using wordTrace_append hprefix tailTrace_2855192
  have hstable : (prefixWord ++ tailWord_2855192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2855192).length < 2 ^ (prefixWord ++ tailWord_2855192).sum := by decide
  have hdescent : baseEnd_2855192 < baseStart_2855192 := by decide
  rcases family_descends (prefixWord ++ tailWord_2855192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2855215 : List Nat := [1, 1, 2, 1, 2, 1, 6, 3, 6]
def baseStart_2855215 : Nat := 118140960795 + 2855215 * 2 ^ 59
def prefixEnd_2855215 : Nat := 4983230072969 + 3 ^ 40 * 2855215 * 2
def baseEnd_2855215 : Nat := 162899740769683521320179

theorem tailTrace_2855215 : CollatzResearch.WordTrace tailWord_2855215 prefixEnd_2855215 162899740769683521320179 := by
  unfold tailWord_2855215
  simp only [CollatzResearch.WordTrace]
  refine ⟨104138246351051161744751099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69425497567367441163167399 104138246351051161744751099)
  ·
    refine ⟨156207369526576742617126649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104138246351051161744751099 156207369526576742617126649)
    ·
      refine ⟨117155527144932556962844987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 156207369526576742617126649 117155527144932556962844987)
      ·
        refine ⟨175733290717398835444267481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117155527144932556962844987 175733290717398835444267481)
        ·
          refine ⟨131799968038049126583200611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 175733290717398835444267481 131799968038049126583200611)
          ·
            refine ⟨197699952057073689874800917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 131799968038049126583200611 197699952057073689874800917)
            ·
              refine ⟨9267185252675329212881293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 197699952057073689874800917 9267185252675329212881293)
              ·
                refine ⟨3475194469753248454830485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9267185252675329212881293 3475194469753248454830485)
                ·
                  refine ⟨162899740769683521320179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3475194469753248454830485 162899740769683521320179)
                  ·
                    rfl

theorem cell23_2855215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 6, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 6, 3, 6].length) (baseStart_2855215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2855215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2855215 prefixEnd_2855215 := by exact prefixLift 2855215
  have htrace : WordTrace (prefixWord ++ tailWord_2855215) baseStart_2855215 baseEnd_2855215 := by
    simpa [prefixWord, tailWord_2855215, baseEnd_2855215] using wordTrace_append hprefix tailTrace_2855215
  have hstable : (prefixWord ++ tailWord_2855215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2855215).length < 2 ^ (prefixWord ++ tailWord_2855215).sum := by decide
  have hdescent : baseEnd_2855215 < baseStart_2855215 := by decide
  rcases family_descends (prefixWord ++ tailWord_2855215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2855293 : List Nat := [1, 4, 1, 1, 2, 5, 1, 3, 1, 1, 3]
def baseStart_2855293 : Nat := 118140960795 + 2855293 * 2 ^ 59
def prefixEnd_2855293 : Nat := 4983230072969 + 3 ^ 40 * 2855293 * 2
def baseEnd_2855293 : Nat := 1466137718418202386706253

theorem tailTrace_2855293 : CollatzResearch.WordTrace tailWord_2855293 prefixEnd_2855293 1466137718418202386706253 := by
  unfold tailWord_2855293
  simp only [CollatzResearch.WordTrace]
  refine ⟨104141091244768581066090533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69427394163179054044060355 104141091244768581066090533)
  ·
    refine ⟨19526454608394108949891975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 104141091244768581066090533 19526454608394108949891975)
    ·
      refine ⟨29289681912591163424837963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19526454608394108949891975 29289681912591163424837963)
      ·
        refine ⟨43934522868886745137256945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29289681912591163424837963 43934522868886745137256945)
        ·
          refine ⟨32950892151665058852942709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43934522868886745137256945 32950892151665058852942709)
          ·
            refine ⟨3089146139218599267463379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 32950892151665058852942709 3089146139218599267463379)
            ·
              refine ⟨4633719208827898901195069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3089146139218599267463379 4633719208827898901195069)
              ·
                refine ⟨1737644703310462087948151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4633719208827898901195069 1737644703310462087948151)
                ·
                  refine ⟨2606467054965693131922227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1737644703310462087948151 2606467054965693131922227)
                  ·
                    refine ⟨3909700582448539697883341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2606467054965693131922227 3909700582448539697883341)
                    ·
                      refine ⟨1466137718418202386706253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3909700582448539697883341 1466137718418202386706253)
                      ·
                        rfl

theorem cell23_2855293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 5, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 5, 1, 3, 1, 1, 3].length) (baseStart_2855293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2855293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2855293 prefixEnd_2855293 := by exact prefixLift 2855293
  have htrace : WordTrace (prefixWord ++ tailWord_2855293) baseStart_2855293 baseEnd_2855293 := by
    simpa [prefixWord, tailWord_2855293, baseEnd_2855293] using wordTrace_append hprefix tailTrace_2855293
  have hstable : (prefixWord ++ tailWord_2855293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2855293).length < 2 ^ (prefixWord ++ tailWord_2855293).sum := by decide
  have hdescent : baseEnd_2855293 < baseStart_2855293 := by decide
  rcases family_descends (prefixWord ++ tailWord_2855293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2855305 : List Nat := [1, 2, 1, 1, 6, 1, 11]
def baseStart_2855305 : Nat := 118140960795 + 2855305 * 2 ^ 59
def prefixEnd_2855305 : Nat := 4983230072969 + 3 ^ 40 * 2855305 * 2
def baseEnd_2855305 : Nat := 18100541730692053577237

theorem tailTrace_2855305 : CollatzResearch.WordTrace tailWord_2855305 prefixEnd_2855305 18100541730692053577237 := by
  unfold tailWord_2855305
  simp only [CollatzResearch.WordTrace]
  refine ⟨104141528920725107115527369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69427685947150071410351579 104141528920725107115527369)
  ·
    refine ⟨78106146690543830336645527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104141528920725107115527369 78106146690543830336645527)
    ·
      refine ⟨117159220035815745504968291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78106146690543830336645527 117159220035815745504968291)
      ·
        refine ⟨175738830053723618257452437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117159220035815745504968291 175738830053723618257452437)
        ·
          refine ⟨8237757658768294605818083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 175738830053723618257452437 8237757658768294605818083)
          ·
            refine ⟨12356636488152441908727125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8237757658768294605818083 12356636488152441908727125)
            ·
              refine ⟨18100541730692053577237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 12356636488152441908727125 18100541730692053577237)
              ·
                rfl

theorem cell23_2855305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 11].length) (baseStart_2855305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2855305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2855305 prefixEnd_2855305 := by exact prefixLift 2855305
  have htrace : WordTrace (prefixWord ++ tailWord_2855305) baseStart_2855305 baseEnd_2855305 := by
    simpa [prefixWord, tailWord_2855305, baseEnd_2855305] using wordTrace_append hprefix tailTrace_2855305
  have hstable : (prefixWord ++ tailWord_2855305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2855305).length < 2 ^ (prefixWord ++ tailWord_2855305).sum := by decide
  have hdescent : baseEnd_2855305 < baseStart_2855305 := by decide
  rcases family_descends (prefixWord ++ tailWord_2855305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2855310 : List Nat := [4, 1, 1, 4, 1, 2, 3, 2, 1, 1, 3]
def baseStart_2855310 : Nat := 118140960795 + 2855310 * 2 ^ 59
def prefixEnd_2855310 : Nat := 4983230072969 + 3 ^ 40 * 2855310 * 2
def baseEnd_2855310 : Nat := 1466146447589328820193675

theorem tailTrace_2855310 : CollatzResearch.WordTrace tailWord_2855310 prefixEnd_2855310 1466146447589328820193675 := by
  unfold tailWord_2855310
  simp only [CollatzResearch.WordTrace]
  refine ⟨13017713910713374121182423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 69427807523804661979639589 13017713910713374121182423)
  ·
    refine ⟨19526570866070061181773635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13017713910713374121182423 19526570866070061181773635)
    ·
      refine ⟨29289856299105091772660453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19526570866070061181773635 29289856299105091772660453)
      ·
        refine ⟨5491848056082204707373835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 29289856299105091772660453 5491848056082204707373835)
        ·
          refine ⟨8237772084123307061060753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5491848056082204707373835 8237772084123307061060753)
          ·
            refine ⟨6178329063092480295795565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8237772084123307061060753 6178329063092480295795565)
            ·
              refine ⟨2316873398659680110923337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6178329063092480295795565 2316873398659680110923337)
              ·
                refine ⟨1737655048994760083192503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2316873398659680110923337 1737655048994760083192503)
                ·
                  refine ⟨2606482573492140124788755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1737655048994760083192503 2606482573492140124788755)
                  ·
                    refine ⟨3909723860238210187183133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2606482573492140124788755 3909723860238210187183133)
                    ·
                      refine ⟨1466146447589328820193675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3909723860238210187183133 1466146447589328820193675)
                      ·
                        rfl

theorem cell23_2855310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 2, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 2, 3, 2, 1, 1, 3].length) (baseStart_2855310 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2855310 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2855310 prefixEnd_2855310 := by exact prefixLift 2855310
  have htrace : WordTrace (prefixWord ++ tailWord_2855310) baseStart_2855310 baseEnd_2855310 := by
    simpa [prefixWord, tailWord_2855310, baseEnd_2855310] using wordTrace_append hprefix tailTrace_2855310
  have hstable : (prefixWord ++ tailWord_2855310).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2855310).length < 2 ^ (prefixWord ++ tailWord_2855310).sum := by decide
  have hdescent : baseEnd_2855310 < baseStart_2855310 := by decide
  rcases family_descends (prefixWord ++ tailWord_2855310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2855322 : List Nat := [3, 1, 1, 4, 1, 3, 2, 8]
def baseStart_2855322 : Nat := 118140960795 + 2855322 * 2 ^ 59
def prefixEnd_2855322 : Nat := 4983230072969 + 3 ^ 40 * 2855322 * 2
def baseEnd_2855322 : Nat := 54301948494710473083097

theorem tailTrace_2855322 : CollatzResearch.WordTrace tailWord_2855322 prefixEnd_2855322 54301948494710473083097 := by
  unfold tailWord_2855322
  simp only [CollatzResearch.WordTrace]
  refine ⟨26035537240415879754724055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69428099307775679345930813 26035537240415879754724055)
  ·
    refine ⟨39053305860623819632086083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26035537240415879754724055 39053305860623819632086083)
    ·
      refine ⟨58579958790935729448129125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39053305860623819632086083 58579958790935729448129125)
      ·
        refine ⟨10983742273300449271524211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 58579958790935729448129125 10983742273300449271524211)
        ·
          refine ⟨16475613409950673907286317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10983742273300449271524211 16475613409950673907286317)
          ·
            refine ⟨6178355028731502715232369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16475613409950673907286317 6178355028731502715232369)
            ·
              refine ⟨4633766271548627036424277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6178355028731502715232369 4633766271548627036424277)
              ·
                refine ⟨54301948494710473083097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4633766271548627036424277 54301948494710473083097)
                ·
                  rfl

theorem cell23_2855322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 3, 2, 8].length) (baseStart_2855322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2855322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2855322 prefixEnd_2855322 := by exact prefixLift 2855322
  have htrace : WordTrace (prefixWord ++ tailWord_2855322) baseStart_2855322 baseEnd_2855322 := by
    simpa [prefixWord, tailWord_2855322, baseEnd_2855322] using wordTrace_append hprefix tailTrace_2855322
  have hstable : (prefixWord ++ tailWord_2855322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2855322).length < 2 ^ (prefixWord ++ tailWord_2855322).sum := by decide
  have hdescent : baseEnd_2855322 < baseStart_2855322 := by decide
  rcases family_descends (prefixWord ++ tailWord_2855322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2855336 : List Nat := [2, 1, 6, 1, 1, 2, 1, 1, 3, 2, 3]
def baseStart_2855336 : Nat := 118140960795 + 2855336 * 2 ^ 59
def prefixEnd_2855336 : Nat := 4983230072969 + 3 ^ 40 * 2855336 * 2
def baseEnd_2855336 : Nat := 1466159798086345718468555

theorem tailTrace_2855336 : CollatzResearch.WordTrace tailWord_2855336 prefixEnd_2855336 1466159798086345718468555 := by
  unfold tailWord_2855336
  simp only [CollatzResearch.WordTrace]
  refine ⟨52071329791806399704952931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69428439722408532939937241 52071329791806399704952931)
  ·
    refine ⟨78106994687709599557429397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52071329791806399704952931 78106994687709599557429397)
    ·
      refine ⟨3661265375986387479254503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 78106994687709599557429397 3661265375986387479254503)
      ·
        refine ⟨5491898063979581218881755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3661265375986387479254503 5491898063979581218881755)
        ·
          refine ⟨8237847095969371828322633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5491898063979581218881755 8237847095969371828322633)
          ·
            refine ⟨6178385321977028871241975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8237847095969371828322633 6178385321977028871241975)
            ·
              refine ⟨9267577982965543306862963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6178385321977028871241975 9267577982965543306862963)
              ·
                refine ⟨13901366974448314960294445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9267577982965543306862963 13901366974448314960294445)
                ·
                  refine ⟨5213012615418118110110417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13901366974448314960294445 5213012615418118110110417)
                  ·
                    refine ⟨3909759461563588582582813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5213012615418118110110417 3909759461563588582582813)
                    ·
                      refine ⟨1466159798086345718468555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3909759461563588582582813 1466159798086345718468555)
                      ·
                        rfl

theorem cell23_2855336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 2, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 2, 1, 1, 3, 2, 3].length) (baseStart_2855336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2855336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2855336 prefixEnd_2855336 := by exact prefixLift 2855336
  have htrace : WordTrace (prefixWord ++ tailWord_2855336) baseStart_2855336 baseEnd_2855336 := by
    simpa [prefixWord, tailWord_2855336, baseEnd_2855336] using wordTrace_append hprefix tailTrace_2855336
  have hstable : (prefixWord ++ tailWord_2855336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2855336).length < 2 ^ (prefixWord ++ tailWord_2855336).sum := by decide
  have hdescent : baseEnd_2855336 < baseStart_2855336 := by decide
  rcases family_descends (prefixWord ++ tailWord_2855336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2855361 : List Nat := [1, 2, 7, 1, 2, 1, 2, 2, 1, 1, 3]
def baseStart_2855361 : Nat := 118140960795 + 2855361 * 2 ^ 59
def prefixEnd_2855361 : Nat := 4983230072969 + 3 ^ 40 * 2855361 * 2
def baseEnd_2855361 : Nat := 1466172635102708120655941

theorem tailTrace_2855361 : CollatzResearch.WordTrace tailWord_2855361 prefixEnd_2855361 1466172635102708120655941 := by
  unfold tailWord_2855361
  simp only [CollatzResearch.WordTrace]
  refine ⟨104143571408522228679565937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69429047605681485786377291 104143571408522228679565937)
  ·
    refine ⟨78107678556391671509674453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104143571408522228679565937 78107678556391671509674453)
    ·
      refine ⟨1830648716165429801007995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 78107678556391671509674453 1830648716165429801007995)
      ·
        refine ⟨2745973074248144701511993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1830648716165429801007995 2745973074248144701511993)
        ·
          refine ⟨2059479805686108526133995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2745973074248144701511993 2059479805686108526133995)
          ·
            refine ⟨3089219708529162789200993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2059479805686108526133995 3089219708529162789200993)
            ·
              refine ⟨2316914781396872091900745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3089219708529162789200993 2316914781396872091900745)
              ·
                refine ⟨1737686086047654068925559, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2316914781396872091900745 1737686086047654068925559)
                ·
                  refine ⟨2606529129071481103388339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1737686086047654068925559 2606529129071481103388339)
                  ·
                    refine ⟨3909793693607221655082509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2606529129071481103388339 3909793693607221655082509)
                    ·
                      refine ⟨1466172635102708120655941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3909793693607221655082509 1466172635102708120655941)
                      ·
                        rfl

theorem cell23_2855361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 2, 1, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 2, 1, 2, 2, 1, 1, 3].length) (baseStart_2855361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2855361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2855361 prefixEnd_2855361 := by exact prefixLift 2855361
  have htrace : WordTrace (prefixWord ++ tailWord_2855361) baseStart_2855361 baseEnd_2855361 := by
    simpa [prefixWord, tailWord_2855361, baseEnd_2855361] using wordTrace_append hprefix tailTrace_2855361
  have hstable : (prefixWord ++ tailWord_2855361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2855361).length < 2 ^ (prefixWord ++ tailWord_2855361).sum := by decide
  have hdescent : baseEnd_2855361 < baseStart_2855361 := by decide
  rcases family_descends (prefixWord ++ tailWord_2855361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2855365 : List Nat := [1, 3, 1, 1, 1, 1, 1, 1, 5, 8]
def baseStart_2855365 : Nat := 118140960795 + 2855365 * 2 ^ 59
def prefixEnd_2855365 : Nat := 4983230072969 + 3 ^ 40 * 2855365 * 2
def baseEnd_2855365 : Nat := 488724896341775368335307

theorem tailTrace_2855365 : CollatzResearch.WordTrace tailWord_2855365 prefixEnd_2855365 488724896341775368335307 := by
  unfold tailWord_2855365
  simp only [CollatzResearch.WordTrace]
  refine ⟨104143717300507737362711549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69429144867005158241807699 104143717300507737362711549)
  ·
    refine ⟨39053893987690401511016831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 104143717300507737362711549 39053893987690401511016831)
    ·
      refine ⟨58580840981535602266525247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39053893987690401511016831 58580840981535602266525247)
      ·
        refine ⟨87871261472303403399787871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58580840981535602266525247 87871261472303403399787871)
        ·
          refine ⟨131806892208455105099681807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87871261472303403399787871 131806892208455105099681807)
          ·
            refine ⟨197710338312682657649522711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 131806892208455105099681807 197710338312682657649522711)
            ·
              refine ⟨296565507469023986474284067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 197710338312682657649522711 296565507469023986474284067)
              ·
                refine ⟨444848261203535979711426101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 296565507469023986474284067 444848261203535979711426101)
                ·
                  refine ⟨41704524487831498097946197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 444848261203535979711426101 41704524487831498097946197)
                  ·
                    refine ⟨488724896341775368335307, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 41704524487831498097946197 488724896341775368335307)
                    ·
                      rfl

theorem cell23_2855365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 1, 5, 8].length) (baseStart_2855365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2855365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2855365 prefixEnd_2855365 := by exact prefixLift 2855365
  have htrace : WordTrace (prefixWord ++ tailWord_2855365) baseStart_2855365 baseEnd_2855365 := by
    simpa [prefixWord, tailWord_2855365, baseEnd_2855365] using wordTrace_append hprefix tailTrace_2855365
  have hstable : (prefixWord ++ tailWord_2855365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2855365).length < 2 ^ (prefixWord ++ tailWord_2855365).sum := by decide
  have hdescent : baseEnd_2855365 < baseStart_2855365 := by decide
  rcases family_descends (prefixWord ++ tailWord_2855365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2855392 : List Nat := [2, 1, 1, 3, 1, 1, 3, 2, 2, 4, 3]
def baseStart_2855392 : Nat := 118140960795 + 2855392 * 2 ^ 59
def prefixEnd_2855392 : Nat := 4983230072969 + 3 ^ 40 * 2855392 * 2
def baseEnd_2855392 : Nat := 1466188553002997499368297

theorem tailTrace_2855392 : CollatzResearch.WordTrace tailWord_2855392 prefixEnd_2855392 1466188553002997499368297 := by
  unfold tailWord_2855392
  simp only [CollatzResearch.WordTrace]
  refine ⟨52072351035704960486972215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69429801380939947315962953 52072351035704960486972215)
  ·
    refine ⟨78108526553557440730458323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52072351035704960486972215 78108526553557440730458323)
    ·
      refine ⟨117162789830336161095687485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78108526553557440730458323 117162789830336161095687485)
      ·
        refine ⟨43936046186376060410882807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 117162789830336161095687485 43936046186376060410882807)
        ·
          refine ⟨65904069279564090616324211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43936046186376060410882807 65904069279564090616324211)
          ·
            refine ⟨98856103919346135924486317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65904069279564090616324211 98856103919346135924486317)
            ·
              refine ⟨37071038969754800971682369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 98856103919346135924486317 37071038969754800971682369)
              ·
                refine ⟨27803279227316100728761777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37071038969754800971682369 27803279227316100728761777)
                ·
                  refine ⟨20852459420487075546571333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27803279227316100728761777 20852459420487075546571333)
                  ·
                    refine ⟨3909836141341326664982125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20852459420487075546571333 3909836141341326664982125)
                    ·
                      refine ⟨1466188553002997499368297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3909836141341326664982125 1466188553002997499368297)
                      ·
                        rfl

theorem cell23_2855392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 3, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 3, 2, 2, 4, 3].length) (baseStart_2855392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2855392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2855392 prefixEnd_2855392 := by exact prefixLift 2855392
  have htrace : WordTrace (prefixWord ++ tailWord_2855392) baseStart_2855392 baseEnd_2855392 := by
    simpa [prefixWord, tailWord_2855392, baseEnd_2855392] using wordTrace_append hprefix tailTrace_2855392
  have hstable : (prefixWord ++ tailWord_2855392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2855392).length < 2 ^ (prefixWord ++ tailWord_2855392).sum := by decide
  have hdescent : baseEnd_2855392 < baseStart_2855392 := by decide
  rcases family_descends (prefixWord ++ tailWord_2855392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2855406 : List Nat := [4, 1, 2, 1, 2, 2, 2, 2, 1, 4, 2]
def baseStart_2855406 : Nat := 118140960795 + 2855406 * 2 ^ 59
def prefixEnd_2855406 : Nat := 4983230072969 + 3 ^ 40 * 2855406 * 2
def baseEnd_2855406 : Nat := 1466195741732160444593233

theorem tailTrace_2855406 : CollatzResearch.WordTrace tailWord_2855406 prefixEnd_2855406 1466195741732160444593233 := by
  unfold tailWord_2855406
  simp only [CollatzResearch.WordTrace]
  refine ⟨13018151586669900170619259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 69430141795572800909969381 13018151586669900170619259)
  ·
    refine ⟨19527227380004850255928889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13018151586669900170619259 19527227380004850255928889)
    ·
      refine ⟨14645420535003637691946667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19527227380004850255928889 14645420535003637691946667)
      ·
        refine ⟨21968130802505456537920001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14645420535003637691946667 21968130802505456537920001)
        ·
          refine ⟨16476098101879092403440001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21968130802505456537920001 16476098101879092403440001)
          ·
            refine ⟨12357073576409319302580001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16476098101879092403440001 12357073576409319302580001)
            ·
              refine ⟨9267805182306989476935001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12357073576409319302580001 9267805182306989476935001)
              ·
                refine ⟨6950853886730242107701251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9267805182306989476935001 6950853886730242107701251)
                ·
                  refine ⟨10426280830095363161551877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6950853886730242107701251 10426280830095363161551877)
                  ·
                    refine ⟨1954927655642880592790977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10426280830095363161551877 1954927655642880592790977)
                    ·
                      refine ⟨1466195741732160444593233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1954927655642880592790977 1466195741732160444593233)
                      ·
                        rfl

theorem cell23_2855406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 2, 2, 1, 4, 2].length) (baseStart_2855406 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2855406 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2855406 prefixEnd_2855406 := by exact prefixLift 2855406
  have htrace : WordTrace (prefixWord ++ tailWord_2855406) baseStart_2855406 baseEnd_2855406 := by
    simpa [prefixWord, tailWord_2855406, baseEnd_2855406] using wordTrace_append hprefix tailTrace_2855406
  have hstable : (prefixWord ++ tailWord_2855406).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2855406).length < 2 ^ (prefixWord ++ tailWord_2855406).sum := by decide
  have hdescent : baseEnd_2855406 < baseStart_2855406 := by decide
  rcases family_descends (prefixWord ++ tailWord_2855406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2855429 : List Nat := [1, 3, 1, 1, 2, 2, 4, 4, 5]
def baseStart_2855429 : Nat := 118140960795 + 2855429 * 2 ^ 59
def prefixEnd_2855429 : Nat := 4983230072969 + 3 ^ 40 * 2855429 * 2
def baseEnd_2855429 : Nat := 162911950198579317178403

theorem tailTrace_2855429 : CollatzResearch.WordTrace tailWord_2855429 prefixEnd_2855429 162911950198579317178403 := by
  unfold tailWord_2855429
  simp only [CollatzResearch.WordTrace]
  refine ⟨104146051572275876293041341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69430701048183917528694227 104146051572275876293041341)
  ·
    refine ⟨39054769339603453609890503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 104146051572275876293041341 39054769339603453609890503)
    ·
      refine ⟨58582154009405180414835755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39054769339603453609890503 58582154009405180414835755)
      ·
        refine ⟨87873231014107770622253633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58582154009405180414835755 87873231014107770622253633)
        ·
          refine ⟨65904923260580827966690225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 87873231014107770622253633 65904923260580827966690225)
          ·
            refine ⟨49428692445435620975017669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65904923260580827966690225 49428692445435620975017669)
            ·
              refine ⟨9267879833519178932815813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 49428692445435620975017669 9267879833519178932815813)
              ·
                refine ⟨1737727468784846049902965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9267879833519178932815813 1737727468784846049902965)
                ·
                  refine ⟨162911950198579317178403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1737727468784846049902965 162911950198579317178403)
                  ·
                    rfl

theorem cell23_2855429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 4, 4, 5].length) (baseStart_2855429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2855429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2855429 prefixEnd_2855429 := by exact prefixLift 2855429
  have htrace : WordTrace (prefixWord ++ tailWord_2855429) baseStart_2855429 baseEnd_2855429 := by
    simpa [prefixWord, tailWord_2855429, baseEnd_2855429] using wordTrace_append hprefix tailTrace_2855429
  have hstable : (prefixWord ++ tailWord_2855429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2855429).length < 2 ^ (prefixWord ++ tailWord_2855429).sum := by decide
  have hdescent : baseEnd_2855429 < baseStart_2855429 := by decide
  rcases family_descends (prefixWord ++ tailWord_2855429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2855479 : List Nat := [1, 1, 3, 1, 2, 3, 3, 2, 2, 1, 4]
def baseStart_2855479 : Nat := 118140960795 + 2855479 * 2 ^ 59
def prefixEnd_2855479 : Nat := 4983230072969 + 3 ^ 40 * 2855479 * 2
def baseEnd_2855479 : Nat := 1466233225819938658980397

theorem tailTrace_2855479 : CollatzResearch.WordTrace tailWord_2855479 prefixEnd_2855479 1466233225819938658980397 := by
  unfold tailWord_2855479
  simp only [CollatzResearch.WordTrace]
  refine ⟨104147875222094734832361491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69431916814729823221574327 104147875222094734832361491)
  ·
    refine ⟨156221812833142102248542237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104147875222094734832361491 156221812833142102248542237)
    ·
      refine ⟨58583179812428288343203339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 156221812833142102248542237 58583179812428288343203339)
      ·
        refine ⟨87874769718642432514805009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58583179812428288343203339 87874769718642432514805009)
        ·
          refine ⟨65906077288981824386103757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 87874769718642432514805009 65906077288981824386103757)
          ·
            refine ⟨24714778983368184144788909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 65906077288981824386103757 24714778983368184144788909)
            ·
              refine ⟨9268042118763069054295841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24714778983368184144788909 9268042118763069054295841)
              ·
                refine ⟨6951031589072301790721881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9268042118763069054295841 6951031589072301790721881)
                ·
                  refine ⟨5213273691804226343041411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6951031589072301790721881 5213273691804226343041411)
                  ·
                    refine ⟨7819910537706339514562117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5213273691804226343041411 7819910537706339514562117)
                    ·
                      refine ⟨1466233225819938658980397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7819910537706339514562117 1466233225819938658980397)
                      ·
                        rfl

theorem cell23_2855479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 3, 2, 2, 1, 4].length) (baseStart_2855479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2855479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2855479 prefixEnd_2855479 := by exact prefixLift 2855479
  have htrace : WordTrace (prefixWord ++ tailWord_2855479) baseStart_2855479 baseEnd_2855479 := by
    simpa [prefixWord, tailWord_2855479, baseEnd_2855479] using wordTrace_append hprefix tailTrace_2855479
  have hstable : (prefixWord ++ tailWord_2855479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2855479).length < 2 ^ (prefixWord ++ tailWord_2855479).sum := by decide
  have hdescent : baseEnd_2855479 < baseStart_2855479 := by decide
  rcases family_descends (prefixWord ++ tailWord_2855479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2855536 : List Nat := [2, 1, 1, 1, 7, 1, 2, 2, 6]
def baseStart_2855536 : Nat := 118140960795 + 2855536 * 2 ^ 59
def prefixEnd_2855536 : Nat := 4983230072969 + 3 ^ 40 * 2855536 * 2
def baseEnd_2855536 : Nat := 162918054913027215107515

theorem tailTrace_2855536 : CollatzResearch.WordTrace tailWord_2855536 prefixEnd_2855536 162918054913027215107515 := by
  unfold tailWord_2855536
  simp only [CollatzResearch.WordTrace]
  refine ⟨52074977091444116783593231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69433302788592155711457641 52074977091444116783593231)
  ·
    refine ⟨78112465637166175175389847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52074977091444116783593231 78112465637166175175389847)
    ·
      refine ⟨117168698455749262763084771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78112465637166175175389847 117168698455749262763084771)
      ·
        refine ⟨175753047683623894144627157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117168698455749262763084771 175753047683623894144627157)
        ·
          refine ⟨4119212055084935019014699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 175753047683623894144627157 4119212055084935019014699)
          ·
            refine ⟨6178818082627402528522049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4119212055084935019014699 6178818082627402528522049)
            ·
              refine ⟨4634113561970551896391537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6178818082627402528522049 4634113561970551896391537)
              ·
                refine ⟨3475585171477913922293653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4634113561970551896391537 3475585171477913922293653)
                ·
                  refine ⟨162918054913027215107515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3475585171477913922293653 162918054913027215107515)
                  ·
                    rfl

theorem cell23_2855536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 1, 2, 2, 6].length) (baseStart_2855536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2855536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2855536 prefixEnd_2855536 := by exact prefixLift 2855536
  have htrace : WordTrace (prefixWord ++ tailWord_2855536) baseStart_2855536 baseEnd_2855536 := by
    simpa [prefixWord, tailWord_2855536, baseEnd_2855536] using wordTrace_append hprefix tailTrace_2855536
  have hstable : (prefixWord ++ tailWord_2855536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2855536).length < 2 ^ (prefixWord ++ tailWord_2855536).sum := by decide
  have hdescent : baseEnd_2855536 < baseStart_2855536 := by decide
  rcases family_descends (prefixWord ++ tailWord_2855536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2855566 : List Nat := [4, 1, 1, 3, 1, 1, 2, 4, 1, 5]
def baseStart_2855566 : Nat := 118140960795 + 2855566 * 2 ^ 59
def prefixEnd_2855566 : Nat := 4983230072969 + 3 ^ 40 * 2855566 * 2
def baseEnd_2855566 : Nat := 488759299545626606197499

theorem tailTrace_2855566 : CollatzResearch.WordTrace tailWord_2855566 prefixEnd_2855566 488759299545626606197499 := by
  unfold tailWord_2855566
  simp only [CollatzResearch.WordTrace]
  refine ⟨13018881046597443586347319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 69434032248519699127185701 13018881046597443586347319)
  ·
    refine ⟨19528321569896165379520979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13018881046597443586347319 19528321569896165379520979)
    ·
      refine ⟨29292482354844248069281469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19528321569896165379520979 29292482354844248069281469)
      ·
        refine ⟨10984680883066593025980551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29292482354844248069281469 10984680883066593025980551)
        ·
          refine ⟨16477021324599889538970827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10984680883066593025980551 16477021324599889538970827)
          ·
            refine ⟨24715531986899834308456241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16477021324599889538970827 24715531986899834308456241)
            ·
              refine ⟨18536648990174875731342181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24715531986899834308456241 18536648990174875731342181)
              ·
                refine ⟨3475621685657789199626659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18536648990174875731342181 3475621685657789199626659)
                ·
                  refine ⟨5213432528486683799439989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3475621685657789199626659 5213432528486683799439989)
                  ·
                    refine ⟨488759299545626606197499, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5213432528486683799439989 488759299545626606197499)
                    ·
                      rfl

theorem cell23_2855566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 2, 4, 1, 5].length) (baseStart_2855566 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2855566 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2855566 prefixEnd_2855566 := by exact prefixLift 2855566
  have htrace : WordTrace (prefixWord ++ tailWord_2855566) baseStart_2855566 baseEnd_2855566 := by
    simpa [prefixWord, tailWord_2855566, baseEnd_2855566] using wordTrace_append hprefix tailTrace_2855566
  have hstable : (prefixWord ++ tailWord_2855566).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2855566).length < 2 ^ (prefixWord ++ tailWord_2855566).sum := by decide
  have hdescent : baseEnd_2855566 < baseStart_2855566 := by decide
  rcases family_descends (prefixWord ++ tailWord_2855566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2855580 : List Nat := [2, 2, 3, 2, 2, 1, 1, 5, 1, 1, 3]
def baseStart_2855580 : Nat := 118140960795 + 2855580 * 2 ^ 59
def prefixEnd_2855580 : Nat := 4983230072969 + 3 ^ 40 * 2855580 * 2
def baseEnd_2855580 : Nat := 1466285087366042763817433

theorem tailTrace_2855580 : CollatzResearch.WordTrace tailWord_2855580 prefixEnd_2855580 1466285087366042763817433 := by
  unfold tailWord_2855580
  simp only [CollatzResearch.WordTrace]
  refine ⟨52075779497364414540894097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69434372663152552721192129 52075779497364414540894097)
  ·
    refine ⟨39056834623023310905670573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52075779497364414540894097 39056834623023310905670573)
    ·
      refine ⟨14646312983633741589626465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39056834623023310905670573 14646312983633741589626465)
      ·
        refine ⟨10984734737725306192219849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14646312983633741589626465 10984734737725306192219849)
        ·
          refine ⟨8238551053293979644164887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10984734737725306192219849 8238551053293979644164887)
          ·
            refine ⟨12357826579940969466247331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8238551053293979644164887 12357826579940969466247331)
            ·
              refine ⟨18536739869911454199370997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12357826579940969466247331 18536739869911454199370997)
              ·
                refine ⟨1737819362804198831191031, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 18536739869911454199370997 1737819362804198831191031)
                ·
                  refine ⟨2606729044206298246786547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1737819362804198831191031 2606729044206298246786547)
                  ·
                    refine ⟨3910093566309447370179821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2606729044206298246786547 3910093566309447370179821)
                    ·
                      refine ⟨1466285087366042763817433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3910093566309447370179821 1466285087366042763817433)
                      ·
                        rfl

theorem cell23_2855580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 1, 5, 1, 1, 3].length) (baseStart_2855580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2855580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2855580 prefixEnd_2855580 := by exact prefixLift 2855580
  have htrace : WordTrace (prefixWord ++ tailWord_2855580) baseStart_2855580 baseEnd_2855580 := by
    simpa [prefixWord, tailWord_2855580, baseEnd_2855580] using wordTrace_append hprefix tailTrace_2855580
  have hstable : (prefixWord ++ tailWord_2855580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2855580).length < 2 ^ (prefixWord ++ tailWord_2855580).sum := by decide
  have hdescent : baseEnd_2855580 < baseStart_2855580 := by decide
  rcases family_descends (prefixWord ++ tailWord_2855580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2855589 : List Nat := [1, 3, 1, 2, 1, 2, 1, 5, 1, 1, 5]
def baseStart_2855589 : Nat := 118140960795 + 2855589 * 2 ^ 59
def prefixEnd_2855589 : Nat := 4983230072969 + 3 ^ 40 * 2855589 * 2
def baseEnd_2855589 : Nat := 1466289708691933228604891

theorem tailTrace_2855589 : CollatzResearch.WordTrace tailWord_2855589 prefixEnd_2855589 1466289708691933228604891 := by
  unfold tailWord_2855589
  simp only [CollatzResearch.WordTrace]
  refine ⟨104151887251696223618865821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69434591501130815745910547 104151887251696223618865821)
  ·
    refine ⟨39056957719386083857074683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 104151887251696223618865821 39056957719386083857074683)
    ·
      refine ⟨58585436579079125785612025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39056957719386083857074683 58585436579079125785612025)
      ·
        refine ⟨43939077434309344339209019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58585436579079125785612025 43939077434309344339209019)
        ·
          refine ⟨65908616151464016508813529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43939077434309344339209019 65908616151464016508813529)
          ·
            refine ⟨49431462113598012381610147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65908616151464016508813529 49431462113598012381610147)
            ·
              refine ⟨74147193170397018572415221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49431462113598012381610147 74147193170397018572415221)
              ·
                refine ⟨6951299359724720491163927, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 74147193170397018572415221 6951299359724720491163927)
                ·
                  refine ⟨10426949039587080736745891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6951299359724720491163927 10426949039587080736745891)
                  ·
                    refine ⟨15640423559380621105118837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10426949039587080736745891 15640423559380621105118837)
                    ·
                      refine ⟨1466289708691933228604891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15640423559380621105118837 1466289708691933228604891)
                      ·
                        rfl

theorem cell23_2855589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 5, 1, 1, 5].length) (baseStart_2855589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2855589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2855589 prefixEnd_2855589 := by exact prefixLift 2855589
  have htrace : WordTrace (prefixWord ++ tailWord_2855589) baseStart_2855589 baseEnd_2855589 := by
    simpa [prefixWord, tailWord_2855589, baseEnd_2855589] using wordTrace_append hprefix tailTrace_2855589
  have hstable : (prefixWord ++ tailWord_2855589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2855589).length < 2 ^ (prefixWord ++ tailWord_2855589).sum := by decide
  have hdescent : baseEnd_2855589 < baseStart_2855589 := by decide
  rcases family_descends (prefixWord ++ tailWord_2855589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2855603 : List Nat := [1, 1, 1, 2, 3, 4, 1, 3, 3, 2, 2]
def baseStart_2855603 : Nat := 118140960795 + 2855603 * 2 ^ 59
def prefixEnd_2855603 : Nat := 4983230072969 + 3 ^ 40 * 2855603 * 2
def baseEnd_2855603 : Nat := 1466296897421096173829827

theorem tailTrace_2855603 : CollatzResearch.WordTrace tailWord_2855603 prefixEnd_2855603 1466296897421096173829827 := by
  unfold tailWord_2855603
  simp only [CollatzResearch.WordTrace]
  refine ⟨104152397873645504009875463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69434931915763669339916975 104152397873645504009875463)
  ·
    refine ⟨156228596810468256014813195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104152397873645504009875463 156228596810468256014813195)
    ·
      refine ⟨234342895215702384022219793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 156228596810468256014813195 234342895215702384022219793)
      ·
        refine ⟨175757171411776788016664845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 234342895215702384022219793 175757171411776788016664845)
        ·
          refine ⟨65908939279416295506249317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 175757171411776788016664845 65908939279416295506249317)
          ·
            refine ⟨12357926114890555407421747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 65908939279416295506249317 12357926114890555407421747)
            ·
              refine ⟨18536889172335833111132621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12357926114890555407421747 18536889172335833111132621)
              ·
                refine ⟨6951333439625937416674733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18536889172335833111132621 6951333439625937416674733)
                ·
                  refine ⟨2606750039859726531253025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6951333439625937416674733 2606750039859726531253025)
                  ·
                    refine ⟨1955062529894794898439769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2606750039859726531253025 1955062529894794898439769)
                    ·
                      refine ⟨1466296897421096173829827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1955062529894794898439769 1466296897421096173829827)
                      ·
                        rfl

theorem cell23_2855603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 1, 3, 3, 2, 2].length) (baseStart_2855603 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2855603 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2855603 prefixEnd_2855603 := by exact prefixLift 2855603
  have htrace : WordTrace (prefixWord ++ tailWord_2855603) baseStart_2855603 baseEnd_2855603 := by
    simpa [prefixWord, tailWord_2855603, baseEnd_2855603] using wordTrace_append hprefix tailTrace_2855603
  have hstable : (prefixWord ++ tailWord_2855603).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2855603).length < 2 ^ (prefixWord ++ tailWord_2855603).sum := by decide
  have hdescent : baseEnd_2855603 < baseStart_2855603 := by decide
  rcases family_descends (prefixWord ++ tailWord_2855603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2855616 : List Nat := [2, 1, 1, 2, 4, 2, 3, 1, 1, 2, 4]
def baseStart_2855616 : Nat := 118140960795 + 2855616 * 2 ^ 59
def prefixEnd_2855616 : Nat := 4983230072969 + 3 ^ 40 * 2855616 * 2
def baseEnd_2855616 : Nat := 1466303572669604622967267

theorem tailTrace_2855616 : CollatzResearch.WordTrace tailWord_2855616 prefixEnd_2855616 1466303572669604622967267 := by
  unfold tailWord_2855616
  simp only [CollatzResearch.WordTrace]
  refine ⟨52076436011299203615049351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69435248015065604820065801 52076436011299203615049351)
  ·
    refine ⟨78114654016948805422574027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52076436011299203615049351 78114654016948805422574027)
    ·
      refine ⟨117171981025423208133861041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78114654016948805422574027 117171981025423208133861041)
      ·
        refine ⟨87878985769067406100395781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 117171981025423208133861041 87878985769067406100395781)
        ·
          refine ⟨16477309831700138643824209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 87878985769067406100395781 16477309831700138643824209)
          ·
            refine ⟨12357982373775103982868157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16477309831700138643824209 12357982373775103982868157)
            ·
              refine ⟨4634243390165663993575559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12357982373775103982868157 4634243390165663993575559)
              ·
                refine ⟨6951365085248495990363339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4634243390165663993575559 6951365085248495990363339)
                ·
                  refine ⟨10427047627872743985545009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6951365085248495990363339 10427047627872743985545009)
                  ·
                    refine ⟨7820285720904557989158757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10427047627872743985545009 7820285720904557989158757)
                    ·
                      refine ⟨1466303572669604622967267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7820285720904557989158757 1466303572669604622967267)
                      ·
                        rfl

theorem cell23_2855616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 3, 1, 1, 2, 4].length) (baseStart_2855616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2855616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2855616 prefixEnd_2855616 := by exact prefixLift 2855616
  have htrace : WordTrace (prefixWord ++ tailWord_2855616) baseStart_2855616 baseEnd_2855616 := by
    simpa [prefixWord, tailWord_2855616, baseEnd_2855616] using wordTrace_append hprefix tailTrace_2855616
  have hstable : (prefixWord ++ tailWord_2855616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2855616).length < 2 ^ (prefixWord ++ tailWord_2855616).sum := by decide
  have hdescent : baseEnd_2855616 < baseStart_2855616 := by decide
  rcases family_descends (prefixWord ++ tailWord_2855616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2855620 : List Nat := [2, 3, 3, 1, 1, 2, 2, 2, 3, 2, 2]
def baseStart_2855620 : Nat := 118140960795 + 2855620 * 2 ^ 59
def prefixEnd_2855620 : Nat := 4983230072969 + 3 ^ 40 * 2855620 * 2
def baseEnd_2855620 : Nat := 1466305626592222607317249

theorem tailTrace_2855620 : CollatzResearch.WordTrace tailWord_2855620 prefixEnd_2855620 1466305626592222607317249 := by
  unfold tailWord_2855620
  simp only [CollatzResearch.WordTrace]
  refine ⟨52076508957291957956622157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69435345276389277275496209 52076508957291957956622157)
  ·
    refine ⟨19528690858984484233733309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52076508957291957956622157 19528690858984484233733309)
    ·
      refine ⟨7323259072119181587649991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19528690858984484233733309 7323259072119181587649991)
      ·
        refine ⟨10984888608178772381474987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7323259072119181587649991 10984888608178772381474987)
        ·
          refine ⟨16477332912268158572212481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10984888608178772381474987 16477332912268158572212481)
          ·
            refine ⟨12357999684201118929159361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16477332912268158572212481 12357999684201118929159361)
            ·
              refine ⟨9268499763150839196869521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12357999684201118929159361 9268499763150839196869521)
              ·
                refine ⟨6951374822363129397652141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9268499763150839196869521 6951374822363129397652141)
                ·
                  refine ⟨2606765558386173524119553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6951374822363129397652141 2606765558386173524119553)
                  ·
                    refine ⟨1955074168789630143089665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2606765558386173524119553 1955074168789630143089665)
                    ·
                      refine ⟨1466305626592222607317249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1955074168789630143089665 1466305626592222607317249)
                      ·
                        rfl

theorem cell23_2855620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 2, 2, 3, 2, 2].length) (baseStart_2855620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2855620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2855620 prefixEnd_2855620 := by exact prefixLift 2855620
  have htrace : WordTrace (prefixWord ++ tailWord_2855620) baseStart_2855620 baseEnd_2855620 := by
    simpa [prefixWord, tailWord_2855620, baseEnd_2855620] using wordTrace_append hprefix tailTrace_2855620
  have hstable : (prefixWord ++ tailWord_2855620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2855620).length < 2 ^ (prefixWord ++ tailWord_2855620).sum := by decide
  have hdescent : baseEnd_2855620 < baseStart_2855620 := by decide
  rcases family_descends (prefixWord ++ tailWord_2855620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2855626 : List Nat := [3, 1, 2, 1, 4, 1, 4, 7]
def baseStart_2855626 : Nat := 118140960795 + 2855626 * 2 ^ 59
def prefixEnd_2855626 : Nat := 4983230072969 + 3 ^ 40 * 2855626 * 2
def baseEnd_2855626 : Nat := 54307729906524058660823

theorem tailTrace_2855626 : CollatzResearch.WordTrace tailWord_2855626 prefixEnd_2855626 54307729906524058660823 := by
  unfold tailWord_2855626
  simp only [CollatzResearch.WordTrace]
  refine ⟨26038309188140544734490683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69435491168374785958641821 26038309188140544734490683)
  ·
    refine ⟨39057463782210817101736025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26038309188140544734490683 39057463782210817101736025)
    ·
      refine ⟨29293097836658112826302019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39057463782210817101736025 29293097836658112826302019)
      ·
        refine ⟨43939646754987169239453029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29293097836658112826302019 43939646754987169239453029)
        ·
          refine ⟨8238683766560094232397443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 43939646754987169239453029 8238683766560094232397443)
          ·
            refine ⟨12358025649840141348596165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8238683766560094232397443 12358025649840141348596165)
            ·
              refine ⟨2317129809345026502861781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12358025649840141348596165 2317129809345026502861781)
              ·
                refine ⟨54307729906524058660823, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2317129809345026502861781 54307729906524058660823)
                ·
                  rfl

theorem cell23_2855626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 4, 7].length) (baseStart_2855626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2855626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2855626 prefixEnd_2855626 := by exact prefixLift 2855626
  have htrace : WordTrace (prefixWord ++ tailWord_2855626) baseStart_2855626 baseEnd_2855626 := by
    simpa [prefixWord, tailWord_2855626, baseEnd_2855626] using wordTrace_append hprefix tailTrace_2855626
  have hstable : (prefixWord ++ tailWord_2855626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2855626).length < 2 ^ (prefixWord ++ tailWord_2855626).sum := by decide
  have hdescent : baseEnd_2855626 < baseStart_2855626 := by decide
  rcases family_descends (prefixWord ++ tailWord_2855626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2855653 : List Nat := [1, 3, 1, 4, 1, 2, 2, 1, 4, 1, 3]
def baseStart_2855653 : Nat := 118140960795 + 2855653 * 2 ^ 59
def prefixEnd_2855653 : Nat := 4983230072969 + 3 ^ 40 * 2855653 * 2
def baseEnd_2855653 : Nat := 1466322571453820978204597

theorem tailTrace_2855653 : CollatzResearch.WordTrace tailWord_2855653 prefixEnd_2855653 1466322571453820978204597 := by
  unfold tailWord_2855653
  simp only [CollatzResearch.WordTrace]
  refine ⟨104154221523464362549195613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69436147682309575032797075 104154221523464362549195613)
  ·
    refine ⟨39057833071299135955948355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 104154221523464362549195613 39057833071299135955948355)
    ·
      refine ⟨58586749606948703933922533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39057833071299135955948355 58586749606948703933922533)
      ·
        refine ⟨10985015551302881987610475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 58586749606948703933922533 10985015551302881987610475)
        ·
          refine ⟨16477523326954322981415713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10985015551302881987610475 16477523326954322981415713)
          ·
            refine ⟨12358142495215742236061785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16477523326954322981415713 12358142495215742236061785)
            ·
              refine ⟨9268606871411806677046339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12358142495215742236061785 9268606871411806677046339)
              ·
                refine ⟨13902910307117710015569509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9268606871411806677046339 13902910307117710015569509)
                ·
                  refine ⟨2606795682584570627919283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13902910307117710015569509 2606795682584570627919283)
                  ·
                    refine ⟨3910193523876855941878925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2606795682584570627919283 3910193523876855941878925)
                    ·
                      refine ⟨1466322571453820978204597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3910193523876855941878925 1466322571453820978204597)
                      ·
                        rfl

theorem cell23_2855653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 2, 1, 4, 1, 3].length) (baseStart_2855653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2855653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2855653 prefixEnd_2855653 := by exact prefixLift 2855653
  have htrace : WordTrace (prefixWord ++ tailWord_2855653) baseStart_2855653 baseEnd_2855653 := by
    simpa [prefixWord, tailWord_2855653, baseEnd_2855653] using wordTrace_append hprefix tailTrace_2855653
  have hstable : (prefixWord ++ tailWord_2855653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2855653).length < 2 ^ (prefixWord ++ tailWord_2855653).sum := by decide
  have hdescent : baseEnd_2855653 < baseStart_2855653 := by decide
  rcases family_descends (prefixWord ++ tailWord_2855653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2855659 : List Nat := [1, 1, 1, 1, 2, 4, 1, 3, 2, 3, 4]
def baseStart_2855659 : Nat := 118140960795 + 2855659 * 2 ^ 59
def prefixEnd_2855659 : Nat := 4983230072969 + 3 ^ 40 * 2855659 * 2
def baseEnd_2855659 : Nat := 1466325652337747954729569

theorem tailTrace_2855659 : CollatzResearch.WordTrace tailWord_2855659 prefixEnd_2855659 1466325652337747954729569 := by
  unfold tailWord_2855659
  simp only [CollatzResearch.WordTrace]
  refine ⟨104154440361442625573914031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69436293574295083715942687 104154440361442625573914031)
  ·
    refine ⟨156231660542163938360871047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104154440361442625573914031 156231660542163938360871047)
    ·
      refine ⟨234347490813245907541306571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 156231660542163938360871047 234347490813245907541306571)
      ·
        refine ⟨351521236219868861311959857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 234347490813245907541306571 351521236219868861311959857)
        ·
          refine ⟨263640927164901645983969893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 351521236219868861311959857 263640927164901645983969893)
          ·
            refine ⟨49432673843419058621994355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 263640927164901645983969893 49432673843419058621994355)
            ·
              refine ⟨74149010765128587932991533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49432673843419058621994355 74149010765128587932991533)
              ·
                refine ⟨27805879036923220474871825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 74149010765128587932991533 27805879036923220474871825)
                ·
                  refine ⟨20854409277692415356153869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27805879036923220474871825 20854409277692415356153869)
                  ·
                    refine ⟨7820403479134655758557701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20854409277692415356153869 7820403479134655758557701)
                    ·
                      refine ⟨1466325652337747954729569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7820403479134655758557701 1466325652337747954729569)
                      ·
                        rfl

theorem cell23_2855659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 3, 2, 3, 4].length) (baseStart_2855659 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2855659 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2855659 prefixEnd_2855659 := by exact prefixLift 2855659
  have htrace : WordTrace (prefixWord ++ tailWord_2855659) baseStart_2855659 baseEnd_2855659 := by
    simpa [prefixWord, tailWord_2855659, baseEnd_2855659] using wordTrace_append hprefix tailTrace_2855659
  have hstable : (prefixWord ++ tailWord_2855659).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2855659).length < 2 ^ (prefixWord ++ tailWord_2855659).sum := by decide
  have hdescent : baseEnd_2855659 < baseStart_2855659 := by decide
  rcases family_descends (prefixWord ++ tailWord_2855659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2855670 : List Nat := [5, 1, 1, 1, 1, 2, 3, 3, 2, 1, 3]
def baseStart_2855670 : Nat := 118140960795 + 2855670 * 2 ^ 59
def prefixEnd_2855670 : Nat := 4983230072969 + 3 ^ 40 * 2855670 * 2
def baseEnd_2855670 : Nat := 1466331300624947411692019

theorem tailTrace_2855670 : CollatzResearch.WordTrace tailWord_2855670 prefixEnd_2855670 1466331300624947411692019 := by
  unfold tailWord_2855670
  simp only [CollatzResearch.WordTrace]
  refine ⟨6509677597775173403285279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 69436561042935182968376309 6509677597775173403285279)
  ·
    refine ⟨9764516396662760104927919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6509677597775173403285279 9764516396662760104927919)
    ·
      refine ⟨14646774594994140157391879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9764516396662760104927919 14646774594994140157391879)
      ·
        refine ⟨21970161892491210236087819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14646774594994140157391879 21970161892491210236087819)
        ·
          refine ⟨32955242838736815354131729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21970161892491210236087819 32955242838736815354131729)
          ·
            refine ⟨24716432129052611515598797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32955242838736815354131729 24716432129052611515598797)
            ·
              refine ⟨9268662048394729318349549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24716432129052611515598797 9268662048394729318349549)
              ·
                refine ⟨3475748268148023494381081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9268662048394729318349549 3475748268148023494381081)
                ·
                  refine ⟨2606811201111017620785811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3475748268148023494381081 2606811201111017620785811)
                  ·
                    refine ⟨3910216801666526431178717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2606811201111017620785811 3910216801666526431178717)
                    ·
                      refine ⟨1466331300624947411692019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3910216801666526431178717 1466331300624947411692019)
                      ·
                        rfl

theorem cell23_2855670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 3, 3, 2, 1, 3].length) (baseStart_2855670 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2855670 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2855670 prefixEnd_2855670 := by exact prefixLift 2855670
  have htrace : WordTrace (prefixWord ++ tailWord_2855670) baseStart_2855670 baseEnd_2855670 := by
    simpa [prefixWord, tailWord_2855670, baseEnd_2855670] using wordTrace_append hprefix tailTrace_2855670
  have hstable : (prefixWord ++ tailWord_2855670).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2855670).length < 2 ^ (prefixWord ++ tailWord_2855670).sum := by decide
  have hdescent : baseEnd_2855670 < baseStart_2855670 := by decide
  rcases family_descends (prefixWord ++ tailWord_2855670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2855706 : List Nat := [3, 1, 1, 3, 2, 1, 2, 2, 2, 2, 4]
def baseStart_2855706 : Nat := 118140960795 + 2855706 * 2 ^ 59
def prefixEnd_2855706 : Nat := 4983230072969 + 3 ^ 40 * 2855706 * 2
def baseEnd_2855706 : Nat := 1466349785928509270841853

theorem tailTrace_2855706 : CollatzResearch.WordTrace tailWord_2855706 prefixEnd_2855706 1466349785928509270841853 := by
  unfold tailWord_2855706
  simp only [CollatzResearch.WordTrace]
  refine ⟨26039038648068088150218743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69437436394848235067249981 26039038648068088150218743)
  ·
    refine ⟨39058557972102132225328115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26039038648068088150218743 39058557972102132225328115)
    ·
      refine ⟨58587836958153198337992173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39058557972102132225328115 58587836958153198337992173)
      ·
        refine ⟨21970438859307449376747065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 58587836958153198337992173 21970438859307449376747065)
        ·
          refine ⟨16477829144480587032560299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21970438859307449376747065 16477829144480587032560299)
          ·
            refine ⟨24716743716720880548840449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16477829144480587032560299 24716743716720880548840449)
            ·
              refine ⟨18537557787540660411630337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24716743716720880548840449 18537557787540660411630337)
              ·
                refine ⟨13903168340655495308722753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18537557787540660411630337 13903168340655495308722753)
                ·
                  refine ⟨10427376255491621481542065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13903168340655495308722753 10427376255491621481542065)
                  ·
                    refine ⟨7820532191618716111156549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10427376255491621481542065 7820532191618716111156549)
                    ·
                      refine ⟨1466349785928509270841853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7820532191618716111156549 1466349785928509270841853)
                      ·
                        rfl

theorem cell23_2855706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 2, 2, 2, 2, 4].length) (baseStart_2855706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2855706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2855706 prefixEnd_2855706 := by exact prefixLift 2855706
  have htrace : WordTrace (prefixWord ++ tailWord_2855706) baseStart_2855706 baseEnd_2855706 := by
    simpa [prefixWord, tailWord_2855706, baseEnd_2855706] using wordTrace_append hprefix tailTrace_2855706
  have hstable : (prefixWord ++ tailWord_2855706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2855706).length < 2 ^ (prefixWord ++ tailWord_2855706).sum := by decide
  have hdescent : baseEnd_2855706 < baseStart_2855706 := by decide
  rcases family_descends (prefixWord ++ tailWord_2855706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2855739 : List Nat := [1, 1, 1, 1, 1, 2, 1, 1, 1, 8, 5]
def baseStart_2855739 : Nat := 118140960795 + 2855739 * 2 ^ 59
def prefixEnd_2855739 : Nat := 4983230072969 + 3 ^ 40 * 2855739 * 2
def baseEnd_2855739 : Nat := 1466366730790107641729201

theorem tailTrace_2855739 : CollatzResearch.WordTrace tailWord_2855739 prefixEnd_2855739 1466366730790107641729201 := by
  unfold tailWord_2855739
  simp only [CollatzResearch.WordTrace]
  refine ⟨104157358201152799236826271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69438238800768532824550847 104157358201152799236826271)
  ·
    refine ⟨156236037301729198855239407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104157358201152799236826271 156236037301729198855239407)
    ·
      refine ⟨234354055952593798282859111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 156236037301729198855239407 234354055952593798282859111)
      ·
        refine ⟨351531083928890697424288667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 234354055952593798282859111 351531083928890697424288667)
        ·
          refine ⟨527296625893336046136433001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 351531083928890697424288667 527296625893336046136433001)
          ·
            refine ⟨395472469420002034602324751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 527296625893336046136433001 395472469420002034602324751)
            ·
              refine ⟨593208704130003051903487127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 395472469420002034602324751 593208704130003051903487127)
              ·
                refine ⟨889813056195004577855230691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 593208704130003051903487127 889813056195004577855230691)
                ·
                  refine ⟨1334719584292506866782846037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 889813056195004577855230691 1334719584292506866782846037)
                  ·
                    refine ⟨15641245128427814845111477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 1334719584292506866782846037 15641245128427814845111477)
                    ·
                      refine ⟨1466366730790107641729201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15641245128427814845111477 1466366730790107641729201)
                      ·
                        rfl

theorem cell23_2855739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 8, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 8, 5].length) (baseStart_2855739 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2855739 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2855739 prefixEnd_2855739 := by exact prefixLift 2855739
  have htrace : WordTrace (prefixWord ++ tailWord_2855739) baseStart_2855739 baseEnd_2855739 := by
    simpa [prefixWord, tailWord_2855739, baseEnd_2855739] using wordTrace_append hprefix tailTrace_2855739
  have hstable : (prefixWord ++ tailWord_2855739).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2855739).length < 2 ^ (prefixWord ++ tailWord_2855739).sum := by decide
  have hdescent : baseEnd_2855739 < baseStart_2855739 := by decide
  rcases family_descends (prefixWord ++ tailWord_2855739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2855748 : List Nat := [2, 3, 4, 2, 2, 1, 2, 1, 1, 3, 2]
def baseStart_2855748 : Nat := 118140960795 + 2855748 * 2 ^ 59
def prefixEnd_2855748 : Nat := 4983230072969 + 3 ^ 40 * 2855748 * 2
def baseEnd_2855748 : Nat := 1466371352115998106516661

theorem tailTrace_2855748 : CollatzResearch.WordTrace tailWord_2855748 prefixEnd_2855748 1466371352115998106516661 := by
  unfold tailWord_2855748
  simp only [CollatzResearch.WordTrace]
  refine ⟨52078843229060096886951949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69438457638746795849269265 52078843229060096886951949)
  ·
    refine ⟨19529566210897536332606981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52078843229060096886951949 19529566210897536332606981)
    ·
      refine ⟨3661793664543288062363809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19529566210897536332606981 3661793664543288062363809)
      ·
        refine ⟨2746345248407466046772857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3661793664543288062363809 2746345248407466046772857)
        ·
          refine ⟨2059758936305599535079643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2746345248407466046772857 2059758936305599535079643)
          ·
            refine ⟨3089638404458399302619465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2059758936305599535079643 3089638404458399302619465)
            ·
              refine ⟨2317228803343799476964599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3089638404458399302619465 2317228803343799476964599)
              ·
                refine ⟨3475843205015699215446899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2317228803343799476964599 3475843205015699215446899)
                ·
                  refine ⟨5213764807523548823170349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3475843205015699215446899 5213764807523548823170349)
                  ·
                    refine ⟨1955161802821330808688881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5213764807523548823170349 1955161802821330808688881)
                    ·
                      refine ⟨1466371352115998106516661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1955161802821330808688881 1466371352115998106516661)
                      ·
                        rfl

theorem cell23_2855748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 2, 1, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 2, 1, 2, 1, 1, 3, 2].length) (baseStart_2855748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2855748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2855748 prefixEnd_2855748 := by exact prefixLift 2855748
  have htrace : WordTrace (prefixWord ++ tailWord_2855748) baseStart_2855748 baseEnd_2855748 := by
    simpa [prefixWord, tailWord_2855748, baseEnd_2855748] using wordTrace_append hprefix tailTrace_2855748
  have hstable : (prefixWord ++ tailWord_2855748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2855748).length < 2 ^ (prefixWord ++ tailWord_2855748).sum := by decide
  have hdescent : baseEnd_2855748 < baseStart_2855748 := by decide
  rcases family_descends (prefixWord ++ tailWord_2855748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2855759 : List Nat := [1, 1, 2, 1, 1, 2, 1, 1, 3, 10]
def baseStart_2855759 : Nat := 118140960795 + 2855759 * 2 ^ 59
def prefixEnd_2855759 : Nat := 4983230072969 + 3 ^ 40 * 2855759 * 2
def baseEnd_2855759 : Nat := 488792333467732521159703

theorem tailTrace_2855759 : CollatzResearch.WordTrace tailWord_2855759 prefixEnd_2855759 488792333467732521159703 := by
  unfold tailWord_2855759
  simp only [CollatzResearch.WordTrace]
  refine ⟨104158087661080342652554331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69438725107386895101702887 104158087661080342652554331)
  ·
    refine ⟨156237131491620513978831497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104158087661080342652554331 156237131491620513978831497)
    ·
      refine ⟨117177848618715385484123623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 156237131491620513978831497 117177848618715385484123623)
      ·
        refine ⟨175766772928073078226185435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117177848618715385484123623 175766772928073078226185435)
        ·
          refine ⟨263650159392109617339278153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 175766772928073078226185435 263650159392109617339278153)
          ·
            refine ⟨197737619544082213004458615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 263650159392109617339278153 197737619544082213004458615)
            ·
              refine ⟨296606429316123319506687923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 197737619544082213004458615 296606429316123319506687923)
              ·
                refine ⟨444909643974184979260031885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 296606429316123319506687923 444909643974184979260031885)
                ·
                  refine ⟨166841116490319367222511957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 444909643974184979260031885 166841116490319367222511957)
                  ·
                    refine ⟨488792333467732521159703, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 166841116490319367222511957 488792333467732521159703)
                    ·
                      rfl

theorem cell23_2855759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 1, 3, 10].length) (baseStart_2855759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2855759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2855759 prefixEnd_2855759 := by exact prefixLift 2855759
  have htrace : WordTrace (prefixWord ++ tailWord_2855759) baseStart_2855759 baseEnd_2855759 := by
    simpa [prefixWord, tailWord_2855759, baseEnd_2855759] using wordTrace_append hprefix tailTrace_2855759
  have hstable : (prefixWord ++ tailWord_2855759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2855759).length < 2 ^ (prefixWord ++ tailWord_2855759).sum := by decide
  have hdescent : baseEnd_2855759 < baseStart_2855759 := by decide
  rcases family_descends (prefixWord ++ tailWord_2855759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2855793 : List Nat := [1, 2, 2, 2, 1, 4, 2, 2, 3, 4]
def baseStart_2855793 : Nat := 118140960795 + 2855793 * 2 ^ 59
def prefixEnd_2855793 : Nat := 4983230072969 + 3 ^ 40 * 2855793 * 2
def baseEnd_2855793 : Nat := 488798152915150143484651

theorem tailTrace_2855793 : CollatzResearch.WordTrace tailWord_2855793 prefixEnd_2855793 488798152915150143484651 := by
  unfold tailWord_2855793
  simp only [CollatzResearch.WordTrace]
  refine ⟨104159327742957166459292033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69439551828638110972861355 104159327742957166459292033)
  ·
    refine ⟨78119495807217874844469025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104159327742957166459292033 78119495807217874844469025)
    ·
      refine ⟨58589621855413406133351769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78119495807217874844469025 58589621855413406133351769)
      ·
        refine ⟨43942216391560054600013827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58589621855413406133351769 43942216391560054600013827)
        ·
          refine ⟨65913324587340081900020741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43942216391560054600013827 65913324587340081900020741)
          ·
            refine ⟨12358748360126265356253889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 65913324587340081900020741 12358748360126265356253889)
            ·
              refine ⟨9269061270094699017190417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12358748360126265356253889 9269061270094699017190417)
              ·
                refine ⟨6951795952571024262892813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9269061270094699017190417 6951795952571024262892813)
                ·
                  refine ⟨2606923482214134098584805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6951795952571024262892813 2606923482214134098584805)
                  ·
                    refine ⟨488798152915150143484651, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2606923482214134098584805 488798152915150143484651)
                    ·
                      rfl

theorem cell23_2855793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 2, 2, 3, 4].length) (baseStart_2855793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2855793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2855793 prefixEnd_2855793 := by exact prefixLift 2855793
  have htrace : WordTrace (prefixWord ++ tailWord_2855793) baseStart_2855793 baseEnd_2855793 := by
    simpa [prefixWord, tailWord_2855793, baseEnd_2855793] using wordTrace_append hprefix tailTrace_2855793
  have hstable : (prefixWord ++ tailWord_2855793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2855793).length < 2 ^ (prefixWord ++ tailWord_2855793).sum := by decide
  have hdescent : baseEnd_2855793 < baseStart_2855793 := by decide
  rcases family_descends (prefixWord ++ tailWord_2855793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2855843 : List Nat := [1, 1, 1, 4, 1, 2, 2, 1, 3, 5, 2]
def baseStart_2855843 : Nat := 118140960795 + 2855843 * 2 ^ 59
def prefixEnd_2855843 : Nat := 4983230072969 + 3 ^ 40 * 2855843 * 2
def baseEnd_2855843 : Nat := 1466420132778175234828723

theorem tailTrace_2855843 : CollatzResearch.WordTrace tailWord_2855843 prefixEnd_2855843 1466420132778175234828723 := by
  unfold tailWord_2855843
  simp only [CollatzResearch.WordTrace]
  refine ⟨104161151392776024998612183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69440767595184016665741455 104161151392776024998612183)
  ·
    refine ⟨156241727089164037497918275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104161151392776024998612183 156241727089164037497918275)
    ·
      refine ⟨234362590633746056246877413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 156241727089164037497918275 234362590633746056246877413)
      ·
        refine ⟨43942985743827385546289515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 234362590633746056246877413 43942985743827385546289515)
        ·
          refine ⟨65914478615741078319434273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43942985743827385546289515 65914478615741078319434273)
          ·
            refine ⟨49435858961805808739575705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65914478615741078319434273 49435858961805808739575705)
            ·
              refine ⟨37076894221354356554681779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49435858961805808739575705 37076894221354356554681779)
              ·
                refine ⟨55615341332031534832022669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37076894221354356554681779 55615341332031534832022669)
                ·
                  refine ⟨20855752999511825562008501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 55615341332031534832022669 20855752999511825562008501)
                  ·
                    refine ⟨1955226843704233646438297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 20855752999511825562008501 1955226843704233646438297)
                    ·
                      refine ⟨1466420132778175234828723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1955226843704233646438297 1466420132778175234828723)
                      ·
                        rfl

theorem cell23_2855843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 2, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 2, 1, 3, 5, 2].length) (baseStart_2855843 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2855843 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2855843 prefixEnd_2855843 := by exact prefixLift 2855843
  have htrace : WordTrace (prefixWord ++ tailWord_2855843) baseStart_2855843 baseEnd_2855843 := by
    simpa [prefixWord, tailWord_2855843, baseEnd_2855843] using wordTrace_append hprefix tailTrace_2855843
  have hstable : (prefixWord ++ tailWord_2855843).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2855843).length < 2 ^ (prefixWord ++ tailWord_2855843).sum := by decide
  have hdescent : baseEnd_2855843 < baseStart_2855843 := by decide
  rcases family_descends (prefixWord ++ tailWord_2855843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2855890 : List Nat := [3, 2, 2, 3, 1, 1, 1, 2, 3, 1, 4]
def baseStart_2855890 : Nat := 118140960795 + 2855890 * 2 ^ 59
def prefixEnd_2855890 : Nat := 4983230072969 + 3 ^ 40 * 2855890 * 2
def baseEnd_2855890 : Nat := 1466444266368936550941007

theorem tailTrace_2855890 : CollatzResearch.WordTrace tailWord_2855890 prefixEnd_2855890 1466444266368936550941007 := by
  unfold tailWord_2855890
  simp only [CollatzResearch.WordTrace]
  refine ⟨26040716405901438006393281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69441910415737168017048749 26040716405901438006393281)
  ·
    refine ⟨19530537304426078504794961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26040716405901438006393281 19530537304426078504794961)
    ·
      refine ⟨14647902978319558878596221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19530537304426078504794961 14647902978319558878596221)
      ·
        refine ⟨5492963616869834579473583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14647902978319558878596221 5492963616869834579473583)
        ·
          refine ⟨8239445425304751869210375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5492963616869834579473583 8239445425304751869210375)
          ·
            refine ⟨12359168137957127803815563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8239445425304751869210375 12359168137957127803815563)
            ·
              refine ⟨18538752206935691705723345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12359168137957127803815563 18538752206935691705723345)
              ·
                refine ⟨13904064155201768779292509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18538752206935691705723345 13904064155201768779292509)
                ·
                  refine ⟨5214024058200663292234691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13904064155201768779292509 5214024058200663292234691)
                  ·
                    refine ⟨7821036087300994938352037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5214024058200663292234691 7821036087300994938352037)
                    ·
                      refine ⟨1466444266368936550941007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7821036087300994938352037 1466444266368936550941007)
                      ·
                        rfl

theorem cell23_2855890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 1, 2, 3, 1, 4].length) (baseStart_2855890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2855890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2855890 prefixEnd_2855890 := by exact prefixLift 2855890
  have htrace : WordTrace (prefixWord ++ tailWord_2855890) baseStart_2855890 baseEnd_2855890 := by
    simpa [prefixWord, tailWord_2855890, baseEnd_2855890] using wordTrace_append hprefix tailTrace_2855890
  have hstable : (prefixWord ++ tailWord_2855890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2855890).length < 2 ^ (prefixWord ++ tailWord_2855890).sum := by decide
  have hdescent : baseEnd_2855890 < baseStart_2855890 := by decide
  rcases family_descends (prefixWord ++ tailWord_2855890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2855907 : List Nat := [1, 1, 1, 6, 1, 1, 3, 2, 3, 2, 2]
def baseStart_2855907 : Nat := 118140960795 + 2855907 * 2 ^ 59
def prefixEnd_2855907 : Nat := 4983230072969 + 3 ^ 40 * 2855907 * 2
def baseEnd_2855907 : Nat := 1466452995540062984428429

theorem tailTrace_2855907 : CollatzResearch.WordTrace tailWord_2855907 prefixEnd_2855907 1466452995540062984428429 := by
  unfold tailWord_2855907
  simp only [CollatzResearch.WordTrace]
  refine ⟨104163485664544163928941975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69442323776362775952627983 104163485664544163928941975)
  ·
    refine ⟨156245228496816245893412963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104163485664544163928941975 156245228496816245893412963)
    ·
      refine ⟨234367842745224368840119445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 156245228496816245893412963 234367842745224368840119445)
      ·
        refine ⟨10985992628682392289380599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 234367842745224368840119445 10985992628682392289380599)
        ·
          refine ⟨16478988943023588434070899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10985992628682392289380599 16478988943023588434070899)
          ·
            refine ⟨24718483414535382651106349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16478988943023588434070899 24718483414535382651106349)
            ·
              refine ⟨9269431280450768494164881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24718483414535382651106349 9269431280450768494164881)
              ·
                refine ⟨6952073460338076370623661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9269431280450768494164881 6952073460338076370623661)
                ·
                  refine ⟨2607027547626778638983873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6952073460338076370623661 2607027547626778638983873)
                  ·
                    refine ⟨1955270660720083979237905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2607027547626778638983873 1955270660720083979237905)
                    ·
                      refine ⟨1466452995540062984428429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1955270660720083979237905 1466452995540062984428429)
                      ·
                        rfl

theorem cell23_2855907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 3, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 3, 2, 3, 2, 2].length) (baseStart_2855907 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2855907 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2855907 prefixEnd_2855907 := by exact prefixLift 2855907
  have htrace : WordTrace (prefixWord ++ tailWord_2855907) baseStart_2855907 baseEnd_2855907 := by
    simpa [prefixWord, tailWord_2855907, baseEnd_2855907] using wordTrace_append hprefix tailTrace_2855907
  have hstable : (prefixWord ++ tailWord_2855907).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2855907).length < 2 ^ (prefixWord ++ tailWord_2855907).sum := by decide
  have hdescent : baseEnd_2855907 < baseStart_2855907 := by decide
  rcases family_descends (prefixWord ++ tailWord_2855907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2855954 : List Nat := [3, 2, 5, 1, 1, 1, 1, 1, 1, 1, 6]
def baseStart_2855954 : Nat := 118140960795 + 2855954 * 2 ^ 59
def prefixEnd_2855954 : Nat := 4983230072969 + 3 ^ 40 * 2855954 * 2
def baseEnd_2855954 : Nat := 1466477129130824300540713

theorem tailTrace_2855954 : CollatzResearch.WordTrace tailWord_2855954 prefixEnd_2855954 1466477129130824300540713 := by
  unfold tailWord_2855954
  simp only [CollatzResearch.WordTrace]
  refine ⟨26041299973843472738975729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69443466596915927303935277 26041299973843472738975729)
  ·
    refine ⟨19530974980382604554231797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26041299973843472738975729 19530974980382604554231797)
    ·
      refine ⟨1831028904410869176959231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 19530974980382604554231797 1831028904410869176959231)
      ·
        refine ⟨2746543356616303765438847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1831028904410869176959231 2746543356616303765438847)
        ·
          refine ⟨4119815034924455648158271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2746543356616303765438847 4119815034924455648158271)
          ·
            refine ⟨6179722552386683472237407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4119815034924455648158271 6179722552386683472237407)
            ·
              refine ⟨9269583828580025208356111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6179722552386683472237407 9269583828580025208356111)
              ·
                refine ⟨13904375742870037812534167, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9269583828580025208356111 13904375742870037812534167)
                ·
                  refine ⟨20856563614305056718801251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13904375742870037812534167 20856563614305056718801251)
                  ·
                    refine ⟨31284845421457585078201877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20856563614305056718801251 31284845421457585078201877)
                    ·
                      refine ⟨1466477129130824300540713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 31284845421457585078201877 1466477129130824300540713)
                      ·
                        rfl

theorem cell23_2855954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 1, 1, 1, 1, 1, 6].length) (baseStart_2855954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2855954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2855954 prefixEnd_2855954 := by exact prefixLift 2855954
  have htrace : WordTrace (prefixWord ++ tailWord_2855954) baseStart_2855954 baseEnd_2855954 := by
    simpa [prefixWord, tailWord_2855954, baseEnd_2855954] using wordTrace_append hprefix tailTrace_2855954
  have hstable : (prefixWord ++ tailWord_2855954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2855954).length < 2 ^ (prefixWord ++ tailWord_2855954).sum := by decide
  have hdescent : baseEnd_2855954 < baseStart_2855954 := by decide
  rcases family_descends (prefixWord ++ tailWord_2855954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2855957 : List Nat := [1, 3, 2, 1, 4, 3, 1, 1, 1, 3, 3]
def baseStart_2855957 : Nat := 118140960795 + 2855957 * 2 ^ 59
def prefixEnd_2855957 : Nat := 4983230072969 + 3 ^ 40 * 2855957 * 2
def baseEnd_2855957 : Nat := 1466478669572787788803199

theorem tailTrace_2855957 : CollatzResearch.WordTrace tailWord_2855957 prefixEnd_2855957 1466478669572787788803199 := by
  unfold tailWord_2855957
  simp only [CollatzResearch.WordTrace]
  refine ⟨104165309314363022468262125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69443539542908681645508083 104165309314363022468262125)
  ·
    refine ⟨39061990992886133425598297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 104165309314363022468262125 39061990992886133425598297)
    ·
      refine ⟨29296493244664600069198723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39061990992886133425598297 29296493244664600069198723)
      ·
        refine ⟨43944739866996900103798085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29296493244664600069198723 43944739866996900103798085)
        ·
          refine ⟨8239638725061918769462141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 43944739866996900103798085 8239638725061918769462141)
          ·
            refine ⟨3089864521898219538548303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8239638725061918769462141 3089864521898219538548303)
            ·
              refine ⟨4634796782847329307822455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3089864521898219538548303 4634796782847329307822455)
              ·
                refine ⟨6952195174270993961733683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4634796782847329307822455 6952195174270993961733683)
                ·
                  refine ⟨10428292761406490942600525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6952195174270993961733683 10428292761406490942600525)
                  ·
                    refine ⟨3910609785527434103475197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10428292761406490942600525 3910609785527434103475197)
                    ·
                      refine ⟨1466478669572787788803199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3910609785527434103475197 1466478669572787788803199)
                      ·
                        rfl

theorem cell23_2855957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 3, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 3, 1, 1, 1, 3, 3].length) (baseStart_2855957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2855957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2855957 prefixEnd_2855957 := by exact prefixLift 2855957
  have htrace : WordTrace (prefixWord ++ tailWord_2855957) baseStart_2855957 baseEnd_2855957 := by
    simpa [prefixWord, tailWord_2855957, baseEnd_2855957] using wordTrace_append hprefix tailTrace_2855957
  have hstable : (prefixWord ++ tailWord_2855957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2855957).length < 2 ^ (prefixWord ++ tailWord_2855957).sum := by decide
  have hdescent : baseEnd_2855957 < baseStart_2855957 := by decide
  rcases family_descends (prefixWord ++ tailWord_2855957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2855967 : List Nat := [1, 1, 2, 4, 1, 3, 1, 4, 1, 3, 2]
def baseStart_2855967 : Nat := 118140960795 + 2855967 * 2 ^ 59
def prefixEnd_2855967 : Nat := 4983230072969 + 3 ^ 40 * 2855967 * 2
def baseEnd_2855967 : Nat := 1466483804379332749678153

theorem tailTrace_2855967 : CollatzResearch.WordTrace tailWord_2855967 prefixEnd_2855967 1466483804379332749678153 := by
  unfold tailWord_2855967
  simp only [CollatzResearch.WordTrace]
  refine ⟨104165674044326794176126155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69443782696217862784084103 104165674044326794176126155)
  ·
    refine ⟨156248511066490191264189233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104165674044326794176126155 156248511066490191264189233)
    ·
      refine ⟨117186383299867643448141925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 156248511066490191264189233 117186383299867643448141925)
      ·
        refine ⟨21972446868725183146526611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 117186383299867643448141925 21972446868725183146526611)
        ·
          refine ⟨32958670303087774719789917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21972446868725183146526611 32958670303087774719789917)
          ·
            refine ⟨12359501363657915519921219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32958670303087774719789917 12359501363657915519921219)
            ·
              refine ⟨18539252045486873279881829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12359501363657915519921219 18539252045486873279881829)
              ·
                refine ⟨3476109758528788739977843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18539252045486873279881829 3476109758528788739977843)
                ·
                  refine ⟨5214164637793183109966765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3476109758528788739977843 5214164637793183109966765)
                  ·
                    refine ⟨1955311739172443666237537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5214164637793183109966765 1955311739172443666237537)
                    ·
                      refine ⟨1466483804379332749678153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1955311739172443666237537 1466483804379332749678153)
                      ·
                        rfl

theorem cell23_2855967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 1, 4, 1, 3, 2].length) (baseStart_2855967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2855967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2855967 prefixEnd_2855967 := by exact prefixLift 2855967
  have htrace : WordTrace (prefixWord ++ tailWord_2855967) baseStart_2855967 baseEnd_2855967 := by
    simpa [prefixWord, tailWord_2855967, baseEnd_2855967] using wordTrace_append hprefix tailTrace_2855967
  have hstable : (prefixWord ++ tailWord_2855967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2855967).length < 2 ^ (prefixWord ++ tailWord_2855967).sum := by decide
  have hdescent : baseEnd_2855967 < baseStart_2855967 := by decide
  rcases family_descends (prefixWord ++ tailWord_2855967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2855980 : List Nat := [2, 2, 1, 1, 1, 2, 4, 1, 3, 4, 2]
def baseStart_2855980 : Nat := 118140960795 + 2855980 * 2 ^ 59
def prefixEnd_2855980 : Nat := 4983230072969 + 3 ^ 40 * 2855980 * 2
def baseEnd_2855980 : Nat := 1466490479627841198815593

theorem tailTrace_2855980 : CollatzResearch.WordTrace tailWord_2855980 prefixEnd_2855980 1466490479627841198815593 := by
  unfold tailWord_2855980
  simp only [CollatzResearch.WordTrace]
  refine ⟨52083074096639848698174697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69444098795519798264232929 52083074096639848698174697)
  ·
    refine ⟨39062305572479886523631023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52083074096639848698174697 39062305572479886523631023)
    ·
      refine ⟨58593458358719829785446535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39062305572479886523631023 58593458358719829785446535)
      ·
        refine ⟨87890187538079744678169803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58593458358719829785446535 87890187538079744678169803)
        ·
          refine ⟨131835281307119617017254705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87890187538079744678169803 131835281307119617017254705)
          ·
            refine ⟨98876460980339712762941029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 131835281307119617017254705 98876460980339712762941029)
            ·
              refine ⟨18539336433813696143051443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 98876460980339712762941029 18539336433813696143051443)
              ·
                refine ⟨27809004650720544214577165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18539336433813696143051443 27809004650720544214577165)
                ·
                  refine ⟨10428376744020204080466437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27809004650720544214577165 10428376744020204080466437)
                  ·
                    refine ⟨1955320639503788265087457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10428376744020204080466437 1955320639503788265087457)
                    ·
                      refine ⟨1466490479627841198815593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1955320639503788265087457 1466490479627841198815593)
                      ·
                        rfl

theorem cell23_2855980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 4, 2].length) (baseStart_2855980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2855980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2855980 prefixEnd_2855980 := by exact prefixLift 2855980
  have htrace : WordTrace (prefixWord ++ tailWord_2855980) baseStart_2855980 baseEnd_2855980 := by
    simpa [prefixWord, tailWord_2855980, baseEnd_2855980] using wordTrace_append hprefix tailTrace_2855980
  have hstable : (prefixWord ++ tailWord_2855980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2855980).length < 2 ^ (prefixWord ++ tailWord_2855980).sum := by decide
  have hdescent : baseEnd_2855980 < baseStart_2855980 := by decide
  rcases family_descends (prefixWord ++ tailWord_2855980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2856014 : List Nat := [4, 1, 1, 1, 1, 3, 3, 3, 2, 2, 2]
def baseStart_2856014 : Nat := 118140960795 + 2856014 * 2 ^ 59
def prefixEnd_2856014 : Nat := 4983230072969 + 3 ^ 40 * 2856014 * 2
def baseEnd_2856014 : Nat := 1466507937970094065790437

theorem tailTrace_2856014 : CollatzResearch.WordTrace tailWord_2856014 prefixEnd_2856014 1466507937970094065790437 := by
  unfold tailWord_2856014
  simp only [CollatzResearch.WordTrace]
  refine ⟨13020923534394565150385887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 69444925516771014135391397 13020923534394565150385887)
  ·
    refine ⟨19531385301591847725578831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13020923534394565150385887 19531385301591847725578831)
    ·
      refine ⟨29297077952387771588368247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19531385301591847725578831 29297077952387771588368247)
      ·
        refine ⟨43945616928581657382552371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29297077952387771588368247 43945616928581657382552371)
        ·
          refine ⟨65918425392872486073828557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43945616928581657382552371 65918425392872486073828557)
          ·
            refine ⟨24719409522327182277685709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 65918425392872486073828557 24719409522327182277685709)
            ·
              refine ⟨9269778570872693354132141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24719409522327182277685709 9269778570872693354132141)
              ·
                refine ⟨3476166964077260007799553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9269778570872693354132141 3476166964077260007799553)
                ·
                  refine ⟨2607125223057945005849665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3476166964077260007799553 2607125223057945005849665)
                  ·
                    refine ⟨1955343917293458754387249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2607125223057945005849665 1955343917293458754387249)
                    ·
                      refine ⟨1466507937970094065790437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1955343917293458754387249 1466507937970094065790437)
                      ·
                        rfl

theorem cell23_2856014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 3, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 3, 3, 2, 2, 2].length) (baseStart_2856014 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2856014 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2856014 prefixEnd_2856014 := by exact prefixLift 2856014
  have htrace : WordTrace (prefixWord ++ tailWord_2856014) baseStart_2856014 baseEnd_2856014 := by
    simpa [prefixWord, tailWord_2856014, baseEnd_2856014] using wordTrace_append hprefix tailTrace_2856014
  have hstable : (prefixWord ++ tailWord_2856014).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2856014).length < 2 ^ (prefixWord ++ tailWord_2856014).sum := by decide
  have hdescent : baseEnd_2856014 < baseStart_2856014 := by decide
  rcases family_descends (prefixWord ++ tailWord_2856014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2856033 : List Nat := [1, 2, 3, 1, 1, 2, 2, 3, 1, 7]
def baseStart_2856033 : Nat := 118140960795 + 2856033 * 2 ^ 59
def prefixEnd_2856033 : Nat := 4983230072969 + 3 ^ 40 * 2856033 * 2
def baseEnd_2856033 : Nat := 488839231367509830484283

theorem tailTrace_2856033 : CollatzResearch.WordTrace tailWord_2856033 prefixEnd_2856033 488839231367509830484283 := by
  unfold tailWord_2856033
  simp only [CollatzResearch.WordTrace]
  refine ⟨104168081262087687448028753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69445387508058458298685835 104168081262087687448028753)
  ·
    refine ⟨78126060946565765586021565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104168081262087687448028753 78126060946565765586021565)
    ·
      refine ⟨29297272854962162094758087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 78126060946565765586021565 29297272854962162094758087)
      ·
        refine ⟨43945909282443243142137131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29297272854962162094758087 43945909282443243142137131)
        ·
          refine ⟨65918863923664864713205697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43945909282443243142137131 65918863923664864713205697)
          ·
            refine ⟨49439147942748648534904273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 65918863923664864713205697 49439147942748648534904273)
            ·
              refine ⟨37079360957061486401178205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49439147942748648534904273 37079360957061486401178205)
              ·
                refine ⟨13904760358898057400441827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37079360957061486401178205 13904760358898057400441827)
                ·
                  refine ⟨20857140538347086100662741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13904760358898057400441827 20857140538347086100662741)
                  ·
                    refine ⟨488839231367509830484283, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 20857140538347086100662741 488839231367509830484283)
                    ·
                      rfl

theorem cell23_2856033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 2, 3, 1, 7].length) (baseStart_2856033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2856033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2856033 prefixEnd_2856033 := by exact prefixLift 2856033
  have htrace : WordTrace (prefixWord ++ tailWord_2856033) baseStart_2856033 baseEnd_2856033 := by
    simpa [prefixWord, tailWord_2856033, baseEnd_2856033] using wordTrace_append hprefix tailTrace_2856033
  have hstable : (prefixWord ++ tailWord_2856033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2856033).length < 2 ^ (prefixWord ++ tailWord_2856033).sum := by decide
  have hdescent : baseEnd_2856033 < baseStart_2856033 := by decide
  rcases family_descends (prefixWord ++ tailWord_2856033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2856050 : List Nat := [3, 2, 1, 2, 2, 1, 1, 4, 2, 5]
def baseStart_2856050 : Nat := 118140960795 + 2856050 * 2 ^ 59
def prefixEnd_2856050 : Nat := 4983230072969 + 3 ^ 40 * 2856050 * 2
def baseEnd_2856050 : Nat := 488842141091218641646757

theorem tailTrace_2856050 : CollatzResearch.WordTrace tailWord_2856050 prefixEnd_2856050 488842141091218641646757 := by
  unfold tailWord_2856050
  simp only [CollatzResearch.WordTrace]
  refine ⟨26042175325756524837849401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69445800868684066234265069 26042175325756524837849401)
  ·
    refine ⟨19531631494317393628387051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26042175325756524837849401 19531631494317393628387051)
    ·
      refine ⟨29297447241476090442580577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19531631494317393628387051 29297447241476090442580577)
      ·
        refine ⟨21973085431107067831935433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29297447241476090442580577 21973085431107067831935433)
        ·
          refine ⟨16479814073330300873951575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21973085431107067831935433 16479814073330300873951575)
          ·
            refine ⟨24719721109995451310927363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16479814073330300873951575 24719721109995451310927363)
            ·
              refine ⟨37079581664993176966391045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24719721109995451310927363 37079581664993176966391045)
              ·
                refine ⟨6952421562186220681198321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 37079581664993176966391045 6952421562186220681198321)
                ·
                  refine ⟨5214316171639665510898741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6952421562186220681198321 5214316171639665510898741)
                  ·
                    refine ⟨488842141091218641646757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5214316171639665510898741 488842141091218641646757)
                    ·
                      rfl

theorem cell23_2856050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 1, 4, 2, 5].length) (baseStart_2856050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2856050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2856050 prefixEnd_2856050 := by exact prefixLift 2856050
  have htrace : WordTrace (prefixWord ++ tailWord_2856050) baseStart_2856050 baseEnd_2856050 := by
    simpa [prefixWord, tailWord_2856050, baseEnd_2856050] using wordTrace_append hprefix tailTrace_2856050
  have hstable : (prefixWord ++ tailWord_2856050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2856050).length < 2 ^ (prefixWord ++ tailWord_2856050).sum := by decide
  have hdescent : baseEnd_2856050 < baseStart_2856050 := by decide
  rcases family_descends (prefixWord ++ tailWord_2856050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2856087 : List Nat := [1, 1, 3, 3, 3, 1, 3, 1, 2, 1, 4]
def baseStart_2856087 : Nat := 118140960795 + 2856087 * 2 ^ 59
def prefixEnd_2856087 : Nat := 4983230072969 + 3 ^ 40 * 2856087 * 2
def baseEnd_2856087 : Nat := 1466545422057872280177601

theorem tailTrace_2856087 : CollatzResearch.WordTrace tailWord_2856087 prefixEnd_2856087 1466545422057872280177601 := by
  unfold tailWord_2856087
  simp only [CollatzResearch.WordTrace]
  refine ⟨104170050803892054670494515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69446700535928036446996343 104170050803892054670494515)
  ·
    refine ⟨156255076205838082005741773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104170050803892054670494515 156255076205838082005741773)
    ·
      refine ⟨58595653577189280752153165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 156255076205838082005741773 58595653577189280752153165)
      ·
        refine ⟨21973370091445980282057437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 58595653577189280752153165 21973370091445980282057437)
        ·
          refine ⟨8240013784292242605771539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21973370091445980282057437 8240013784292242605771539)
          ·
            refine ⟨12360020676438363908657309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8240013784292242605771539 12360020676438363908657309)
            ·
              refine ⟨4635007753664386465746491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12360020676438363908657309 4635007753664386465746491)
              ·
                refine ⟨6952511630496579698619737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4635007753664386465746491 6952511630496579698619737)
                ·
                  refine ⟨5214383722872434773964803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6952511630496579698619737 5214383722872434773964803)
                  ·
                    refine ⟨7821575584308652160947205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5214383722872434773964803 7821575584308652160947205)
                    ·
                      refine ⟨1466545422057872280177601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7821575584308652160947205 1466545422057872280177601)
                      ·
                        rfl

theorem cell23_2856087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 3, 1, 2, 1, 4].length) (baseStart_2856087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2856087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2856087 prefixEnd_2856087 := by exact prefixLift 2856087
  have htrace : WordTrace (prefixWord ++ tailWord_2856087) baseStart_2856087 baseEnd_2856087 := by
    simpa [prefixWord, tailWord_2856087, baseEnd_2856087] using wordTrace_append hprefix tailTrace_2856087
  have hstable : (prefixWord ++ tailWord_2856087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2856087).length < 2 ^ (prefixWord ++ tailWord_2856087).sum := by decide
  have hdescent : baseEnd_2856087 < baseStart_2856087 := by decide
  rcases family_descends (prefixWord ++ tailWord_2856087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2856100 : List Nat := [2, 3, 1, 2, 3, 1, 1, 1, 2, 1, 6]
def baseStart_2856100 : Nat := 118140960795 + 2856100 * 2 ^ 59
def prefixEnd_2856100 : Nat := 4983230072969 + 3 ^ 40 * 2856100 * 2
def baseEnd_2856100 : Nat := 1466552097306380729315041

theorem tailTrace_2856100 : CollatzResearch.WordTrace tailWord_2856100 prefixEnd_2856100 1466552097306380729315041 := by
  unfold tailWord_2856100
  simp only [CollatzResearch.WordTrace]
  refine ⟨52085262476422478945358877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69447016635229971927145169 52085262476422478945358877)
  ·
    refine ⟨19531973428658429604509579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52085262476422478945358877 19531973428658429604509579)
    ·
      refine ⟨29297960142987644406764369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19531973428658429604509579 29297960142987644406764369)
      ·
        refine ⟨21973470107240733305073277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29297960142987644406764369 21973470107240733305073277)
        ·
          refine ⟨8240051290215274989402479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21973470107240733305073277 8240051290215274989402479)
          ·
            refine ⟨12360076935322912484103719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8240051290215274989402479 12360076935322912484103719)
            ·
              refine ⟨18540115402984368726155579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12360076935322912484103719 18540115402984368726155579)
              ·
                refine ⟨27810173104476553089233369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18540115402984368726155579 27810173104476553089233369)
                ·
                  refine ⟨20857629828357414816925027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27810173104476553089233369 20857629828357414816925027)
                  ·
                    refine ⟨31286444742536122225387541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20857629828357414816925027 31286444742536122225387541)
                    ·
                      refine ⟨1466552097306380729315041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 31286444742536122225387541 1466552097306380729315041)
                      ·
                        rfl

theorem cell23_2856100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 1, 1, 2, 1, 6].length) (baseStart_2856100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2856100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2856100 prefixEnd_2856100 := by exact prefixLift 2856100
  have htrace : WordTrace (prefixWord ++ tailWord_2856100) baseStart_2856100 baseEnd_2856100 := by
    simpa [prefixWord, tailWord_2856100, baseEnd_2856100] using wordTrace_append hprefix tailTrace_2856100
  have hstable : (prefixWord ++ tailWord_2856100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2856100).length < 2 ^ (prefixWord ++ tailWord_2856100).sum := by decide
  have hdescent : baseEnd_2856100 < baseStart_2856100 := by decide
  rcases family_descends (prefixWord ++ tailWord_2856100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2856114 : List Nat := [3, 2, 1, 1, 1, 4, 2, 4, 1, 4]
def baseStart_2856114 : Nat := 118140960795 + 2856114 * 2 ^ 59
def prefixEnd_2856114 : Nat := 4983230072969 + 3 ^ 40 * 2856114 * 2
def baseEnd_2856114 : Nat := 488853095345181224846659

theorem tailTrace_2856114 : CollatzResearch.WordTrace tailWord_2856114 prefixEnd_2856114 488853095345181224846659 := by
  unfold tailWord_2856114
  simp only [CollatzResearch.WordTrace]
  refine ⟨26042758893698559570431849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69447357049862825521151597 26042758893698559570431849)
  ·
    refine ⟨19532069170273919677823887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26042758893698559570431849 19532069170273919677823887)
    ·
      refine ⟨29298103755410879516735831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19532069170273919677823887 29298103755410879516735831)
      ·
        refine ⟨43947155633116319275103747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29298103755410879516735831 43947155633116319275103747)
        ·
          refine ⟨65920733449674478912655621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43947155633116319275103747 65920733449674478912655621)
          ·
            refine ⟨12360137521813964796122929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 65920733449674478912655621 12360137521813964796122929)
            ·
              refine ⟨9270103141360473597092197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12360137521813964796122929 9270103141360473597092197)
              ·
                refine ⟨1738144339005088799454787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9270103141360473597092197 1738144339005088799454787)
                ·
                  refine ⟨2607216508507633199182181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1738144339005088799454787 2607216508507633199182181)
                  ·
                    refine ⟨488853095345181224846659, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2607216508507633199182181 488853095345181224846659)
                    ·
                      rfl

theorem cell23_2856114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 2, 4, 1, 4].length) (baseStart_2856114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2856114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2856114 prefixEnd_2856114 := by exact prefixLift 2856114
  have htrace : WordTrace (prefixWord ++ tailWord_2856114) baseStart_2856114 baseEnd_2856114 := by
    simpa [prefixWord, tailWord_2856114, baseEnd_2856114] using wordTrace_append hprefix tailTrace_2856114
  have hstable : (prefixWord ++ tailWord_2856114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2856114).length < 2 ^ (prefixWord ++ tailWord_2856114).sum := by decide
  have hdescent : baseEnd_2856114 < baseStart_2856114 := by decide
  rcases family_descends (prefixWord ++ tailWord_2856114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2856123 : List Nat := [1, 1, 1, 1, 1, 2, 4, 1, 2, 9]
def baseStart_2856123 : Nat := 118140960795 + 2856123 * 2 ^ 59
def prefixEnd_2856123 : Nat := 4983230072969 + 3 ^ 40 * 2856123 * 2
def baseEnd_2856123 : Nat := 488854635787144713109145

theorem tailTrace_2856123 : CollatzResearch.WordTrace tailWord_2856123 prefixEnd_2856123 488854635787144713109145 := by
  unfold tailWord_2856123
  simp only [CollatzResearch.WordTrace]
  refine ⟨104171363831761632818805023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69447575887841088545870015 104171363831761632818805023)
  ·
    refine ⟨156257045747642449228207535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104171363831761632818805023 156257045747642449228207535)
    ·
      refine ⟨234385568621463673842311303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 156257045747642449228207535 234385568621463673842311303)
      ·
        refine ⟨351578352932195510763466955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 234385568621463673842311303 351578352932195510763466955)
        ·
          refine ⟨527367529398293266145200433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 351578352932195510763466955 527367529398293266145200433)
          ·
            refine ⟨395525647048719949608900325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 527367529398293266145200433 395525647048719949608900325)
            ·
              refine ⟨74161058821634990551668811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 395525647048719949608900325 74161058821634990551668811)
              ·
                refine ⟨111241588232452485827503217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 74161058821634990551668811 111241588232452485827503217)
                ·
                  refine ⟨83431191174339364370627413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 111241588232452485827503217 83431191174339364370627413)
                  ·
                    refine ⟨488854635787144713109145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 83431191174339364370627413 488854635787144713109145)
                    ·
                      rfl

theorem cell23_2856123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 1, 2, 9].length) (baseStart_2856123 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2856123 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2856123 prefixEnd_2856123 := by exact prefixLift 2856123
  have htrace : WordTrace (prefixWord ++ tailWord_2856123) baseStart_2856123 baseEnd_2856123 := by
    simpa [prefixWord, tailWord_2856123, baseEnd_2856123] using wordTrace_append hprefix tailTrace_2856123
  have hstable : (prefixWord ++ tailWord_2856123).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2856123).length < 2 ^ (prefixWord ++ tailWord_2856123).sum := by decide
  have hdescent : baseEnd_2856123 < baseStart_2856123 := by decide
  rcases family_descends (prefixWord ++ tailWord_2856123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2856197 : List Nat := [1, 3, 1, 1, 2, 1, 5, 1, 3, 2, 3]
def baseStart_2856197 : Nat := 118140960795 + 2856197 * 2 ^ 59
def prefixEnd_2856197 : Nat := 4983230072969 + 3 ^ 40 * 2856197 * 2
def baseEnd_2856197 : Nat := 1466601904929866849802095

theorem tailTrace_2856197 : CollatzResearch.WordTrace tailWord_2856197 prefixEnd_2856197 1466601904929866849802095 := by
  unfold tailWord_2856197
  simp only [CollatzResearch.WordTrace]
  refine ⟨104174062833493543456998845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69449375222329028971332563 104174062833493543456998845)
  ·
    refine ⟨39065273562560078796374567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 104174062833493543456998845 39065273562560078796374567)
    ·
      refine ⟨58597910343840118194561851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39065273562560078796374567 58597910343840118194561851)
      ·
        refine ⟨87896865515760177291842777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58597910343840118194561851 87896865515760177291842777)
        ·
          refine ⟨65922649136820132968882083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 87896865515760177291842777 65922649136820132968882083)
          ·
            refine ⟨98883973705230199453323125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65922649136820132968882083 98883973705230199453323125)
            ·
              refine ⟨9270372534865331198749043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 98883973705230199453323125 9270372534865331198749043)
              ·
                refine ⟨13905558802297996798123565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9270372534865331198749043 13905558802297996798123565)
                ·
                  refine ⟨5214584550861748799296337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13905558802297996798123565 5214584550861748799296337)
                  ·
                    refine ⟨3910938413146311599472253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5214584550861748799296337 3910938413146311599472253)
                    ·
                      refine ⟨1466601904929866849802095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3910938413146311599472253 1466601904929866849802095)
                      ·
                        rfl

theorem cell23_2856197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 5, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 5, 1, 3, 2, 3].length) (baseStart_2856197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2856197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2856197 prefixEnd_2856197 := by exact prefixLift 2856197
  have htrace : WordTrace (prefixWord ++ tailWord_2856197) baseStart_2856197 baseEnd_2856197 := by
    simpa [prefixWord, tailWord_2856197, baseEnd_2856197] using wordTrace_append hprefix tailTrace_2856197
  have hstable : (prefixWord ++ tailWord_2856197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2856197).length < 2 ^ (prefixWord ++ tailWord_2856197).sum := by decide
  have hdescent : baseEnd_2856197 < baseStart_2856197 := by decide
  rcases family_descends (prefixWord ++ tailWord_2856197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2856221 : List Nat := [1, 4, 2, 3, 1, 2, 2, 2, 2, 4]
def baseStart_2856221 : Nat := 118140960795 + 2856221 * 2 ^ 59
def prefixEnd_2856221 : Nat := 4983230072969 + 3 ^ 40 * 2856221 * 2
def baseEnd_2856221 : Nat := 488871409488524918633995

theorem tailTrace_2856221 : CollatzResearch.WordTrace tailWord_2856221 prefixEnd_2856221 488871409488524918633995 := by
  unfold tailWord_2856221
  simp only [CollatzResearch.WordTrace]
  refine ⟨104174938185406595555872517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69449958790271063703915011 104174938185406595555872517)
  ·
    refine ⟨19532800909763736666726097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 104174938185406595555872517 19532800909763736666726097)
    ·
      refine ⟨14649600682322802500044573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19532800909763736666726097 14649600682322802500044573)
      ·
        refine ⟨5493600255871050937516715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14649600682322802500044573 5493600255871050937516715)
        ·
          refine ⟨8240400383806576406275073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5493600255871050937516715 8240400383806576406275073)
          ·
            refine ⟨6180300287854932304706305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8240400383806576406275073 6180300287854932304706305)
            ·
              refine ⟨4635225215891199228529729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6180300287854932304706305 4635225215891199228529729)
              ·
                refine ⟨3476418911918399421397297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4635225215891199228529729 3476418911918399421397297)
                ·
                  refine ⟨2607314183938799566047973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3476418911918399421397297 2607314183938799566047973)
                  ·
                    refine ⟨488871409488524918633995, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2607314183938799566047973 488871409488524918633995)
                    ·
                      rfl

theorem cell23_2856221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 2, 2, 2, 2, 4].length) (baseStart_2856221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2856221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2856221 prefixEnd_2856221 := by exact prefixLift 2856221
  have htrace : WordTrace (prefixWord ++ tailWord_2856221) baseStart_2856221 baseEnd_2856221 := by
    simpa [prefixWord, tailWord_2856221, baseEnd_2856221] using wordTrace_append hprefix tailTrace_2856221
  have hstable : (prefixWord ++ tailWord_2856221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2856221).length < 2 ^ (prefixWord ++ tailWord_2856221).sum := by decide
  have hdescent : baseEnd_2856221 < baseStart_2856221 := by decide
  rcases family_descends (prefixWord ++ tailWord_2856221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2856228 : List Nat := [2, 3, 1, 3, 1, 1, 3, 4, 1, 2, 2]
def baseStart_2856228 : Nat := 118140960795 + 2856228 * 2 ^ 59
def prefixEnd_2856228 : Nat := 4983230072969 + 3 ^ 40 * 2856228 * 2
def baseEnd_2856228 : Nat := 1466617822830156228514453

theorem tailTrace_2856228 : CollatzResearch.WordTrace tailWord_2856228 prefixEnd_2856228 1466617822830156228514453 := by
  unfold tailWord_2856228
  simp only [CollatzResearch.WordTrace]
  refine ⟨52087596748190617875688669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69450128997587490500918225 52087596748190617875688669)
  ·
    refine ⟨19532848780571481703383251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52087596748190617875688669 19532848780571481703383251)
    ·
      refine ⟨29299273170857222555074877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19532848780571481703383251 29299273170857222555074877)
      ·
        refine ⟨10987227439071458458153079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29299273170857222555074877 10987227439071458458153079)
        ·
          refine ⟨16480841158607187687229619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10987227439071458458153079 16480841158607187687229619)
          ·
            refine ⟨24721261737910781530844429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16480841158607187687229619 24721261737910781530844429)
            ·
              refine ⟨9270473151716543074066661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24721261737910781530844429 9270473151716543074066661)
              ·
                refine ⟨1738213715946851826387499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9270473151716543074066661 1738213715946851826387499)
                ·
                  refine ⟨2607320573920277739581249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1738213715946851826387499 2607320573920277739581249)
                  ·
                    refine ⟨1955490430440208304685937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2607320573920277739581249 1955490430440208304685937)
                    ·
                      refine ⟨1466617822830156228514453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1955490430440208304685937 1466617822830156228514453)
                      ·
                        rfl

theorem cell23_2856228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 3, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 3, 4, 1, 2, 2].length) (baseStart_2856228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2856228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2856228 prefixEnd_2856228 := by exact prefixLift 2856228
  have htrace : WordTrace (prefixWord ++ tailWord_2856228) baseStart_2856228 baseEnd_2856228 := by
    simpa [prefixWord, tailWord_2856228, baseEnd_2856228] using wordTrace_append hprefix tailTrace_2856228
  have hstable : (prefixWord ++ tailWord_2856228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2856228).length < 2 ^ (prefixWord ++ tailWord_2856228).sum := by decide
  have hdescent : baseEnd_2856228 < baseStart_2856228 := by decide
  rcases family_descends (prefixWord ++ tailWord_2856228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2856234 : List Nat := [3, 1, 4, 2, 1, 3, 1, 8]
def baseStart_2856234 : Nat := 118140960795 + 2856234 * 2 ^ 59
def prefixEnd_2856234 : Nat := 4983230072969 + 3 ^ 40 * 2856234 * 2
def baseEnd_2856234 : Nat := 54319292730151229816275

theorem tailTrace_2856234 : CollatzResearch.WordTrace tailWord_2856234 prefixEnd_2856234 54319292730151229816275 := by
  unfold tailWord_2856234
  simp only [CollatzResearch.WordTrace]
  refine ⟨26043853083589874694023939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69450274889572999184063837 26043853083589874694023939)
  ·
    refine ⟨39065779625384812041035909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26043853083589874694023939 39065779625384812041035909)
    ·
      refine ⟨7324833679759652257694233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 39065779625384812041035909 7324833679759652257694233)
      ·
        refine ⟨5493625259819739193270675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7324833679759652257694233 5493625259819739193270675)
        ·
          refine ⟨8240437889729608789906013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5493625259819739193270675 8240437889729608789906013)
          ·
            refine ⟨3090164208648603296214755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8240437889729608789906013 3090164208648603296214755)
            ·
              refine ⟨4635246312972904944322133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3090164208648603296214755 4635246312972904944322133)
              ·
                refine ⟨54319292730151229816275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4635246312972904944322133 54319292730151229816275)
                ·
                  rfl

theorem cell23_2856234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 3, 1, 8].length) (baseStart_2856234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2856234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2856234 prefixEnd_2856234 := by exact prefixLift 2856234
  have htrace : WordTrace (prefixWord ++ tailWord_2856234) baseStart_2856234 baseEnd_2856234 := by
    simpa [prefixWord, tailWord_2856234, baseEnd_2856234] using wordTrace_append hprefix tailTrace_2856234
  have hstable : (prefixWord ++ tailWord_2856234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2856234).length < 2 ^ (prefixWord ++ tailWord_2856234).sum := by decide
  have hdescent : baseEnd_2856234 < baseStart_2856234 := by decide
  rcases family_descends (prefixWord ++ tailWord_2856234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2856262 : List Nat := [6, 1, 1, 3, 1, 2, 2, 1, 1, 1, 4]
def baseStart_2856262 : Nat := 118140960795 + 2856262 * 2 ^ 59
def prefixEnd_2856262 : Nat := 4983230072969 + 3 ^ 40 * 2856262 * 2
def baseEnd_2856262 : Nat := 1466635281172409095489297

theorem tailTrace_2856262 : CollatzResearch.WordTrace tailWord_2856262 prefixEnd_2856262 1466635281172409095489297 := by
  unfold tailWord_2856262
  simp only [CollatzResearch.WordTrace]
  refine ⟨3255513549320564361191095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 69450955718838706372076693 3255513549320564361191095)
  ·
    refine ⟨4883270323980846541786643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3255513549320564361191095 4883270323980846541786643)
    ·
      refine ⟨7324905485971269812679965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4883270323980846541786643 7324905485971269812679965)
      ·
        refine ⟨2746839557239226179754987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7324905485971269812679965 2746839557239226179754987)
        ·
          refine ⟨4120259335858839269632481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2746839557239226179754987 4120259335858839269632481)
          ·
            refine ⟨3090194501894129452224361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4120259335858839269632481 3090194501894129452224361)
            ·
              refine ⟨2317645876420597089168271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3090194501894129452224361 2317645876420597089168271)
              ·
                refine ⟨3476468814630895633752407, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2317645876420597089168271 3476468814630895633752407)
                ·
                  refine ⟨5214703221946343450628611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3476468814630895633752407 5214703221946343450628611)
                  ·
                    refine ⟨7822054832919515175942917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5214703221946343450628611 7822054832919515175942917)
                    ·
                      refine ⟨1466635281172409095489297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7822054832919515175942917 1466635281172409095489297)
                      ·
                        rfl

theorem cell23_2856262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 2, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 2, 2, 1, 1, 1, 4].length) (baseStart_2856262 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2856262 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2856262 prefixEnd_2856262 := by exact prefixLift 2856262
  have htrace : WordTrace (prefixWord ++ tailWord_2856262) baseStart_2856262 baseEnd_2856262 := by
    simpa [prefixWord, tailWord_2856262, baseEnd_2856262] using wordTrace_append hprefix tailTrace_2856262
  have hstable : (prefixWord ++ tailWord_2856262).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2856262).length < 2 ^ (prefixWord ++ tailWord_2856262).sum := by decide
  have hdescent : baseEnd_2856262 < baseStart_2856262 := by decide
  rcases family_descends (prefixWord ++ tailWord_2856262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2856267 : List Nat := [1, 1, 1, 1, 3, 1, 1, 2, 2, 8, 2]
def baseStart_2856267 : Nat := 118140960795 + 2856267 * 2 ^ 59
def prefixEnd_2856267 : Nat := 4983230072969 + 3 ^ 40 * 2856267 * 2
def baseEnd_2856267 : Nat := 1466637848575681575926773

theorem tailTrace_2856267 : CollatzResearch.WordTrace tailWord_2856267 prefixEnd_2856267 1466637848575681575926773 := by
  unfold tailWord_2856267
  simp only [CollatzResearch.WordTrace]
  refine ⟨104176615943239945412047055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69451077295493296941364703 104176615943239945412047055)
  ·
    refine ⟨156264923914859918118070583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104176615943239945412047055 156264923914859918118070583)
    ·
      refine ⟨234397385872289877177105875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 156264923914859918118070583 234397385872289877177105875)
      ·
        refine ⟨351596078808434815765658813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 234397385872289877177105875 351596078808434815765658813)
        ·
          refine ⟨131848529553163055912122055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 351596078808434815765658813 131848529553163055912122055)
          ·
            refine ⟨197772794329744583868183083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 131848529553163055912122055 197772794329744583868183083)
            ·
              refine ⟨296659191494616875802274625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 197772794329744583868183083 296659191494616875802274625)
              ·
                refine ⟨222494393620962656851705969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 296659191494616875802274625 222494393620962656851705969)
                ·
                  refine ⟨166870795215721992638779477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 222494393620962656851705969 166870795215721992638779477)
                  ·
                    refine ⟨1955517131434242101235697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 166870795215721992638779477 1955517131434242101235697)
                    ·
                      refine ⟨1466637848575681575926773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1955517131434242101235697 1466637848575681575926773)
                      ·
                        rfl

theorem cell23_2856267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 2, 2, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 2, 2, 8, 2].length) (baseStart_2856267 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2856267 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2856267 prefixEnd_2856267 := by exact prefixLift 2856267
  have htrace : WordTrace (prefixWord ++ tailWord_2856267) baseStart_2856267 baseEnd_2856267 := by
    simpa [prefixWord, tailWord_2856267, baseEnd_2856267] using wordTrace_append hprefix tailTrace_2856267
  have hstable : (prefixWord ++ tailWord_2856267).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2856267).length < 2 ^ (prefixWord ++ tailWord_2856267).sum := by decide
  have hdescent : baseEnd_2856267 < baseStart_2856267 := by decide
  rcases family_descends (prefixWord ++ tailWord_2856267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2856277 : List Nat := [1, 3, 2, 2, 3, 1, 1, 2, 2, 6]
def baseStart_2856277 : Nat := 118140960795 + 2856277 * 2 ^ 59
def prefixEnd_2856277 : Nat := 4983230072969 + 3 ^ 40 * 2856277 * 2
def baseEnd_2856277 : Nat := 488880994460742178933909

theorem tailTrace_2856277 : CollatzResearch.WordTrace tailWord_2856277 prefixEnd_2856277 488880994460742178933909 := by
  unfold tailWord_2856277
  simp only [CollatzResearch.WordTrace]
  refine ⟨104176980673203717119911085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69451320448802478079940723 104176980673203717119911085)
  ·
    refine ⟨39066367752451393919966657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 104176980673203717119911085 39066367752451393919966657)
    ·
      refine ⟨29299775814338545439974993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39066367752451393919966657 29299775814338545439974993)
      ·
        refine ⟨21974831860753909079981245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29299775814338545439974993 21974831860753909079981245)
        ·
          refine ⟨8240561947782715904992967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21974831860753909079981245 8240561947782715904992967)
          ·
            refine ⟨12360842921674073857489451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8240561947782715904992967 12360842921674073857489451)
            ·
              refine ⟨18541264382511110786234177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12360842921674073857489451 18541264382511110786234177)
              ·
                refine ⟨13905948286883333089675633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18541264382511110786234177 13905948286883333089675633)
                ·
                  refine ⟨10429461215162499817256725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13905948286883333089675633 10429461215162499817256725)
                  ·
                    refine ⟨488880994460742178933909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10429461215162499817256725 488880994460742178933909)
                    ·
                      rfl

theorem cell23_2856277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 1, 2, 2, 6].length) (baseStart_2856277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2856277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2856277 prefixEnd_2856277 := by exact prefixLift 2856277
  have htrace : WordTrace (prefixWord ++ tailWord_2856277) baseStart_2856277 baseEnd_2856277 := by
    simpa [prefixWord, tailWord_2856277, baseEnd_2856277] using wordTrace_append hprefix tailTrace_2856277
  have hstable : (prefixWord ++ tailWord_2856277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2856277).length < 2 ^ (prefixWord ++ tailWord_2856277).sum := by decide
  have hdescent : baseEnd_2856277 < baseStart_2856277 := by decide
  rcases family_descends (prefixWord ++ tailWord_2856277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2856301 : List Nat := [1, 5, 1, 1, 1, 3, 3, 1, 1, 4, 2]
def baseStart_2856301 : Nat := 118140960795 + 2856301 * 2 ^ 59
def prefixEnd_2856301 : Nat := 4983230072969 + 3 ^ 40 * 2856301 * 2
def baseEnd_2856301 : Nat := 1466655306917934442901617

theorem tailTrace_2856301 : CollatzResearch.WordTrace tailWord_2856301 prefixEnd_2856301 1466655306917934442901617 := by
  unfold tailWord_2856301
  simp only [CollatzResearch.WordTrace]
  refine ⟨104177856025116769218784757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69451904016744512812523171 104177856025116769218784757)
  ·
    refine ⟨9766674002354697114261071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 104177856025116769218784757 9766674002354697114261071)
    ·
      refine ⟨14650011003532045671391607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9766674002354697114261071 14650011003532045671391607)
      ·
        refine ⟨21975016505298068507087411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14650011003532045671391607 21975016505298068507087411)
        ·
          refine ⟨32962524757947102760631117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21975016505298068507087411 32962524757947102760631117)
          ·
            refine ⟨12360946784230163535236669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32962524757947102760631117 12360946784230163535236669)
            ·
              refine ⟨4635355044086311325713751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12360946784230163535236669 4635355044086311325713751)
              ·
                refine ⟨6953032566129466988570627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4635355044086311325713751 6953032566129466988570627)
                ·
                  refine ⟨10429548849194200482855941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6953032566129466988570627 10429548849194200482855941)
                  ·
                    refine ⟨1955540409223912590535489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10429548849194200482855941 1955540409223912590535489)
                    ·
                      refine ⟨1466655306917934442901617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1955540409223912590535489 1466655306917934442901617)
                      ·
                        rfl

theorem cell23_2856301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 3, 1, 1, 4, 2].length) (baseStart_2856301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2856301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2856301 prefixEnd_2856301 := by exact prefixLift 2856301
  have htrace : WordTrace (prefixWord ++ tailWord_2856301) baseStart_2856301 baseEnd_2856301 := by
    simpa [prefixWord, tailWord_2856301, baseEnd_2856301] using wordTrace_append hprefix tailTrace_2856301
  have hstable : (prefixWord ++ tailWord_2856301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2856301).length < 2 ^ (prefixWord ++ tailWord_2856301).sum := by decide
  have hdescent : baseEnd_2856301 < baseStart_2856301 := by decide
  rcases family_descends (prefixWord ++ tailWord_2856301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2856337 : List Nat := [1, 2, 2, 1, 1, 1, 2, 6, 2, 5]
def baseStart_2856337 : Nat := 118140960795 + 2856337 * 2 ^ 59
def prefixEnd_2856337 : Nat := 4983230072969 + 3 ^ 40 * 2856337 * 2
def baseEnd_2856337 : Nat := 488891264073832100683817

theorem tailTrace_2856337 : CollatzResearch.WordTrace tailWord_2856337 prefixEnd_2856337 488891264073832100683817 := by
  unfold tailWord_2856337
  simp only [CollatzResearch.WordTrace]
  refine ⟨104179169052986347367095265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69452779368657564911396843 104179169052986347367095265)
  ·
    refine ⟨78134376789739760525321449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104179169052986347367095265 78134376789739760525321449)
    ·
      refine ⟨58600782592304820393991087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78134376789739760525321449 58600782592304820393991087)
      ·
        refine ⟨87901173888457230590986631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58600782592304820393991087 87901173888457230590986631)
        ·
          refine ⟨131851760832685845886479947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 87901173888457230590986631 131851760832685845886479947)
          ·
            refine ⟨197777641249028768829719921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 131851760832685845886479947 197777641249028768829719921)
            ·
              refine ⟨148333230936771576622289941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 197777641249028768829719921 148333230936771576622289941)
              ·
                refine ⟨6953120200161167654169841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 148333230936771576622289941 6953120200161167654169841)
                ·
                  refine ⟨5214840150120875740627381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6953120200161167654169841 5214840150120875740627381)
                  ·
                    refine ⟨488891264073832100683817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5214840150120875740627381 488891264073832100683817)
                    ·
                      rfl

theorem cell23_2856337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 5].length) (baseStart_2856337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2856337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2856337 prefixEnd_2856337 := by exact prefixLift 2856337
  have htrace : WordTrace (prefixWord ++ tailWord_2856337) baseStart_2856337 baseEnd_2856337 := by
    simpa [prefixWord, tailWord_2856337, baseEnd_2856337] using wordTrace_append hprefix tailTrace_2856337
  have hstable : (prefixWord ++ tailWord_2856337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2856337).length < 2 ^ (prefixWord ++ tailWord_2856337).sum := by decide
  have hdescent : baseEnd_2856337 < baseStart_2856337 := by decide
  rcases family_descends (prefixWord ++ tailWord_2856337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2856357 : List Nat := [1, 3, 1, 2, 1, 1, 2, 4, 1, 3, 4]
def baseStart_2856357 : Nat := 118140960795 + 2856357 * 2 ^ 59
def prefixEnd_2856357 : Nat := 4983230072969 + 3 ^ 40 * 2856357 * 2
def baseEnd_2856357 : Nat := 1466684061834586223801359

theorem tailTrace_2856357 : CollatzResearch.WordTrace tailWord_2856357 prefixEnd_2856357 1466684061834586223801359 := by
  unfold tailWord_2856357
  simp only [CollatzResearch.WordTrace]
  refine ⟨104179898512913890782823325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69453265675275927188548883 104179898512913890782823325)
  ·
    refine ⟨39067461942342709043558747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 104179898512913890782823325 39067461942342709043558747)
    ·
      refine ⟨58601192913514063565338121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39067461942342709043558747 58601192913514063565338121)
      ·
        refine ⟨43950894685135547674003591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58601192913514063565338121 43950894685135547674003591)
        ·
          refine ⟨65926342027703321511005387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43950894685135547674003591 65926342027703321511005387)
          ·
            refine ⟨98889513041554982266508081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65926342027703321511005387 98889513041554982266508081)
            ·
              refine ⟨74167134781166236699881061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 98889513041554982266508081 74167134781166236699881061)
              ·
                refine ⟨13906337771468669381227699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 74167134781166236699881061 13906337771468669381227699)
                ·
                  refine ⟨20859506657203004071841549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13906337771468669381227699 20859506657203004071841549)
                  ·
                    refine ⟨7822314996451126526940581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20859506657203004071841549 7822314996451126526940581)
                    ·
                      refine ⟨1466684061834586223801359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7822314996451126526940581 1466684061834586223801359)
                      ·
                        rfl

theorem cell23_2856357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 4, 1, 3, 4].length) (baseStart_2856357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2856357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2856357 prefixEnd_2856357 := by exact prefixLift 2856357
  have htrace : WordTrace (prefixWord ++ tailWord_2856357) baseStart_2856357 baseEnd_2856357 := by
    simpa [prefixWord, tailWord_2856357, baseEnd_2856357] using wordTrace_append hprefix tailTrace_2856357
  have hstable : (prefixWord ++ tailWord_2856357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2856357).length < 2 ^ (prefixWord ++ tailWord_2856357).sum := by decide
  have hdescent : baseEnd_2856357 < baseStart_2856357 := by decide
  rcases family_descends (prefixWord ++ tailWord_2856357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2856386 : List Nat := [3, 5, 2, 1, 1, 1, 2, 2, 2, 2, 2]
def baseStart_2856386 : Nat := 118140960795 + 2856386 * 2 ^ 59
def prefixEnd_2856386 : Nat := 4983230072969 + 3 ^ 40 * 2856386 * 2
def baseEnd_2856386 : Nat := 1466698952773566610338727

theorem tailTrace_2856386 : CollatzResearch.WordTrace tailWord_2856386 prefixEnd_2856386 1466698952773566610338727 := by
  unfold tailWord_2856386
  simp only [CollatzResearch.WordTrace]
  refine ⟨26045239057452207183907253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69453970819872552490419341 26045239057452207183907253)
  ·
    refine ⟨2441741161636144423491305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 26045239057452207183907253 2441741161636144423491305)
    ·
      refine ⟨1831305871227108317618479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2441741161636144423491305 1831305871227108317618479)
      ·
        refine ⟨2746958806840662476427719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1831305871227108317618479 2746958806840662476427719)
        ·
          refine ⟨4120438210260993714641579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2746958806840662476427719 4120438210260993714641579)
          ·
            refine ⟨6180657315391490571962369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4120438210260993714641579 6180657315391490571962369)
            ·
              refine ⟨4635492986543617928971777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6180657315391490571962369 4635492986543617928971777)
              ·
                refine ⟨3476619739907713446728833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4635492986543617928971777 3476619739907713446728833)
                ·
                  refine ⟨2607464804930785085046625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3476619739907713446728833 2607464804930785085046625)
                  ·
                    refine ⟨1955598603698088813784969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2607464804930785085046625 1955598603698088813784969)
                    ·
                      refine ⟨1466698952773566610338727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1955598603698088813784969 1466698952773566610338727)
                      ·
                        rfl

theorem cell23_2856386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 1, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 1, 2, 2, 2, 2, 2].length) (baseStart_2856386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2856386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2856386 prefixEnd_2856386 := by exact prefixLift 2856386
  have htrace : WordTrace (prefixWord ++ tailWord_2856386) baseStart_2856386 baseEnd_2856386 := by
    simpa [prefixWord, tailWord_2856386, baseEnd_2856386] using wordTrace_append hprefix tailTrace_2856386
  have hstable : (prefixWord ++ tailWord_2856386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2856386).length < 2 ^ (prefixWord ++ tailWord_2856386).sum := by decide
  have hdescent : baseEnd_2856386 < baseStart_2856386 := by decide
  rcases family_descends (prefixWord ++ tailWord_2856386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2856458 : List Nat := [3, 1, 2, 2, 2, 3, 2, 1, 3, 1, 3]
def baseStart_2856458 : Nat := 118140960795 + 2856458 * 2 ^ 59
def prefixEnd_2856458 : Nat := 4983230072969 + 3 ^ 40 * 2856458 * 2
def baseEnd_2856458 : Nat := 1466735923380690328638395

theorem tailTrace_2856458 : CollatzResearch.WordTrace tailWord_2856458 prefixEnd_2856458 1466735923380690328638395 := by
  unfold tailWord_2856458
  simp only [CollatzResearch.WordTrace]
  refine ⟨26045895571386996258062507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69455721523698656688166685 26045895571386996258062507)
  ·
    refine ⟨39068843357080494387093761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26045895571386996258062507 39068843357080494387093761)
    ·
      refine ⟨29301632517810370790320321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39068843357080494387093761 29301632517810370790320321)
      ·
        refine ⟨21976224388357778092740241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29301632517810370790320321 21976224388357778092740241)
        ·
          refine ⟨16482168291268333569555181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21976224388357778092740241 16482168291268333569555181)
          ·
            refine ⟨6180813109225625088583193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16482168291268333569555181 6180813109225625088583193)
            ·
              refine ⟨4635609831919218816437395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6180813109225625088583193 4635609831919218816437395)
              ·
                refine ⟨6953414747878828224656093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4635609831919218816437395 6953414747878828224656093)
                ·
                  refine ⟨2607530530454560584246035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6953414747878828224656093 2607530530454560584246035)
                  ·
                    refine ⟨3911295795681840876369053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2607530530454560584246035 3911295795681840876369053)
                    ·
                      refine ⟨1466735923380690328638395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3911295795681840876369053 1466735923380690328638395)
                      ·
                        rfl

theorem cell23_2856458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 3, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 3, 2, 1, 3, 1, 3].length) (baseStart_2856458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2856458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2856458 prefixEnd_2856458 := by exact prefixLift 2856458
  have htrace : WordTrace (prefixWord ++ tailWord_2856458) baseStart_2856458 baseEnd_2856458 := by
    simpa [prefixWord, tailWord_2856458, baseEnd_2856458] using wordTrace_append hprefix tailTrace_2856458
  have hstable : (prefixWord ++ tailWord_2856458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2856458).length < 2 ^ (prefixWord ++ tailWord_2856458).sum := by decide
  have hdescent : baseEnd_2856458 < baseStart_2856458 := by decide
  rcases family_descends (prefixWord ++ tailWord_2856458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2856481 : List Nat := [1, 2, 3, 2, 2, 2, 1, 4, 1, 1, 4]
def baseStart_2856481 : Nat := 118140960795 + 2856481 * 2 ^ 59
def prefixEnd_2856481 : Nat := 4983230072969 + 3 ^ 40 * 2856481 * 2
def baseEnd_2856481 : Nat := 1466747733435743738650789

theorem tailTrace_2856481 : CollatzResearch.WordTrace tailWord_2856481 prefixEnd_2856481 1466747733435743738650789 := by
  unfold tailWord_2856481
  simp only [CollatzResearch.WordTrace]
  refine ⟨104184421164464659960337297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69456280776309773306891531 104184421164464659960337297)
  ·
    refine ⟨78138315873348494970252973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104184421164464659960337297 78138315873348494970252973)
    ·
      refine ⟨29301868452505685613844865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 78138315873348494970252973 29301868452505685613844865)
      ·
        refine ⟨21976401339379264210383649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29301868452505685613844865 21976401339379264210383649)
        ·
          refine ⟨16482301004534448157787737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21976401339379264210383649 16482301004534448157787737)
          ·
            refine ⟨12361725753400836118340803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16482301004534448157787737 12361725753400836118340803)
            ·
              refine ⟨18542588630101254177511205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12361725753400836118340803 18542588630101254177511205)
              ·
                refine ⟨3476735368143985158283351, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18542588630101254177511205 3476735368143985158283351)
                ·
                  refine ⟨5215103052215977737425027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3476735368143985158283351 5215103052215977737425027)
                  ·
                    refine ⟨7822654578323966606137541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5215103052215977737425027 7822654578323966606137541)
                    ·
                      refine ⟨1466747733435743738650789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7822654578323966606137541 1466747733435743738650789)
                      ·
                        rfl

theorem cell23_2856481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 1, 4, 1, 1, 4].length) (baseStart_2856481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2856481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2856481 prefixEnd_2856481 := by exact prefixLift 2856481
  have htrace : WordTrace (prefixWord ++ tailWord_2856481) baseStart_2856481 baseEnd_2856481 := by
    simpa [prefixWord, tailWord_2856481, baseEnd_2856481] using wordTrace_append hprefix tailTrace_2856481
  have hstable : (prefixWord ++ tailWord_2856481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2856481).length < 2 ^ (prefixWord ++ tailWord_2856481).sum := by decide
  have hdescent : baseEnd_2856481 < baseStart_2856481 := by decide
  rcases family_descends (prefixWord ++ tailWord_2856481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2856501 : List Nat := [1, 3, 3, 1, 1, 4, 2, 1, 1, 1, 5]
def baseStart_2856501 : Nat := 118140960795 + 2856501 * 2 ^ 59
def prefixEnd_2856501 : Nat := 4983230072969 + 3 ^ 40 * 2856501 * 2
def baseEnd_2856501 : Nat := 1466758003048833660400697

theorem tailTrace_2856501 : CollatzResearch.WordTrace tailWord_2856501 prefixEnd_2856501 1466758003048833660400697 := by
  unfold tailWord_2856501
  simp only [CollatzResearch.WordTrace]
  refine ⟨104185150624392203376065357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69456767082928135584043571 104185150624392203376065357)
  ·
    refine ⟨39069431484147076266024509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 104185150624392203376065357 39069431484147076266024509)
    ·
      refine ⟨14651036806555153599759191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39069431484147076266024509 14651036806555153599759191)
      ·
        refine ⟨21976555209832730399638787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14651036806555153599759191 21976555209832730399638787)
        ·
          refine ⟨32964832814749095599458181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21976555209832730399638787 32964832814749095599458181)
          ·
            refine ⟨6180906152765455424898409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 32964832814749095599458181 6180906152765455424898409)
            ·
              refine ⟨4635679614574091568673807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6180906152765455424898409 4635679614574091568673807)
              ·
                refine ⟨6953519421861137353010711, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4635679614574091568673807 6953519421861137353010711)
                ·
                  refine ⟨10430279132791706029516067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6953519421861137353010711 10430279132791706029516067)
                  ·
                    refine ⟨15645418699187559044274101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10430279132791706029516067 15645418699187559044274101)
                    ·
                      refine ⟨1466758003048833660400697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15645418699187559044274101 1466758003048833660400697)
                      ·
                        rfl

theorem cell23_2856501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 4, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 4, 2, 1, 1, 1, 5].length) (baseStart_2856501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2856501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2856501 prefixEnd_2856501 := by exact prefixLift 2856501
  have htrace : WordTrace (prefixWord ++ tailWord_2856501) baseStart_2856501 baseEnd_2856501 := by
    simpa [prefixWord, tailWord_2856501, baseEnd_2856501] using wordTrace_append hprefix tailTrace_2856501
  have hstable : (prefixWord ++ tailWord_2856501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2856501).length < 2 ^ (prefixWord ++ tailWord_2856501).sum := by decide
  have hdescent : baseEnd_2856501 < baseStart_2856501 := by decide
  rcases family_descends (prefixWord ++ tailWord_2856501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2856504 : List Nat := [2, 1, 2, 1, 4, 4, 9]
def baseStart_2856504 : Nat := 118140960795 + 2856504 * 2 ^ 59
def prefixEnd_2856504 : Nat := 4983230072969 + 3 ^ 40 * 2856504 * 2
def baseEnd_2856504 : Nat := 18108142512232063563743

theorem tailTrace_2856504 : CollatzResearch.WordTrace tailWord_2856504 prefixEnd_2856504 18108142512232063563743 := by
  unfold tailWord_2856504
  simp only [CollatzResearch.WordTrace]
  refine ⟨52092630021690667444212283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69456840028920889925616377 52092630021690667444212283)
  ·
    refine ⟨78138945032536001166318425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52092630021690667444212283 78138945032536001166318425)
    ·
      refine ⟨58604208774402000874738819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78138945032536001166318425 58604208774402000874738819)
      ·
        refine ⟨87906313161603001312108229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58604208774402000874738819 87906313161603001312108229)
        ·
          refine ⟨16482433717800562746020293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 87906313161603001312108229 16482433717800562746020293)
          ·
            refine ⟨3090456322087605514878805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16482433717800562746020293 3090456322087605514878805)
            ·
              refine ⟨18108142512232063563743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 3090456322087605514878805 18108142512232063563743)
              ·
                rfl

theorem cell23_2856504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 4, 9].length) (baseStart_2856504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2856504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2856504 prefixEnd_2856504 := by exact prefixLift 2856504
  have htrace : WordTrace (prefixWord ++ tailWord_2856504) baseStart_2856504 baseEnd_2856504 := by
    simpa [prefixWord, tailWord_2856504, baseEnd_2856504] using wordTrace_append hprefix tailTrace_2856504
  have hstable : (prefixWord ++ tailWord_2856504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2856504).length < 2 ^ (prefixWord ++ tailWord_2856504).sum := by decide
  have hdescent : baseEnd_2856504 < baseStart_2856504 := by decide
  rcases family_descends (prefixWord ++ tailWord_2856504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2856525 : List Nat := [1, 6, 1, 1, 3, 1, 1, 3, 2, 4]
def baseStart_2856525 : Nat := 118140960795 + 2856525 * 2 ^ 59
def prefixEnd_2856525 : Nat := 4983230072969 + 3 ^ 40 * 2856525 * 2
def baseEnd_2856525 : Nat := 488923442194847188833529

theorem tailTrace_2856525 : CollatzResearch.WordTrace tailWord_2856525 prefixEnd_2856525 488923442194847188833529 := by
  unfold tailWord_2856525
  simp only [CollatzResearch.WordTrace]
  refine ⟨104186025976305255474939029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69457350650870170316626019 104186025976305255474939029)
  ·
    refine ⟨4883719967639308850387767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 104186025976305255474939029 4883719967639308850387767)
    ·
      refine ⟨7325579951458963275581651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4883719967639308850387767 7325579951458963275581651)
      ·
        refine ⟨10988369927188444913372477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7325579951458963275581651 10988369927188444913372477)
        ·
          refine ⟨4120638722695666842514679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10988369927188444913372477 4120638722695666842514679)
          ·
            refine ⟨6180958084043500263772019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4120638722695666842514679 6180958084043500263772019)
            ·
              refine ⟨9271437126065250395658029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6180958084043500263772019 9271437126065250395658029)
              ·
                refine ⟨3476788922274468898371761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9271437126065250395658029 3476788922274468898371761)
                ·
                  refine ⟨2607591691705851673778821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3476788922274468898371761 2607591691705851673778821)
                  ·
                    refine ⟨488923442194847188833529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2607591691705851673778821 488923442194847188833529)
                    ·
                      rfl

theorem cell23_2856525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 1, 1, 3, 2, 4].length) (baseStart_2856525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2856525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2856525 prefixEnd_2856525 := by exact prefixLift 2856525
  have htrace : WordTrace (prefixWord ++ tailWord_2856525) baseStart_2856525 baseEnd_2856525 := by
    simpa [prefixWord, tailWord_2856525, baseEnd_2856525] using wordTrace_append hprefix tailTrace_2856525
  have hstable : (prefixWord ++ tailWord_2856525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2856525).length < 2 ^ (prefixWord ++ tailWord_2856525).sum := by decide
  have hdescent : baseEnd_2856525 < baseStart_2856525 := by decide
  rcases family_descends (prefixWord ++ tailWord_2856525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2856565 : List Nat := [1, 3, 4, 2, 1, 1, 1, 4, 2, 1, 3]
def baseStart_2856565 : Nat := 118140960795 + 2856565 * 2 ^ 59
def prefixEnd_2856565 : Nat := 4983230072969 + 3 ^ 40 * 2856565 * 2
def baseEnd_2856565 : Nat := 1466790865810721410000403

theorem tailTrace_2856565 : CollatzResearch.WordTrace tailWord_2856565 prefixEnd_2856565 1466790865810721410000403 := by
  unfold tailWord_2856565
  simp only [CollatzResearch.WordTrace]
  refine ⟨104187484896160342306395149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69458323264106894870930099 104187484896160342306395149)
  ·
    refine ⟨39070306836060128364898181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 104187484896160342306395149 39070306836060128364898181)
    ·
      refine ⟨7325682531761274068418409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 39070306836060128364898181 7325682531761274068418409)
      ·
        refine ⟨5494261898820955551313807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7325682531761274068418409 5494261898820955551313807)
        ·
          refine ⟨8241392848231433326970711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5494261898820955551313807 8241392848231433326970711)
          ·
            refine ⟨12362089272347149990456067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8241392848231433326970711 12362089272347149990456067)
            ·
              refine ⟨18543133908520724985684101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12362089272347149990456067 18543133908520724985684101)
              ·
                refine ⟨3476837607847635934815769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18543133908520724985684101 3476837607847635934815769)
                ·
                  refine ⟨2607628205885726951111827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3476837607847635934815769 2607628205885726951111827)
                  ·
                    refine ⟨3911442308828590426667741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2607628205885726951111827 3911442308828590426667741)
                    ·
                      refine ⟨1466790865810721410000403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3911442308828590426667741 1466790865810721410000403)
                      ·
                        rfl

theorem cell23_2856565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 1, 4, 2, 1, 3].length) (baseStart_2856565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2856565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2856565 prefixEnd_2856565 := by exact prefixLift 2856565
  have htrace : WordTrace (prefixWord ++ tailWord_2856565) baseStart_2856565 baseEnd_2856565 := by
    simpa [prefixWord, tailWord_2856565, baseEnd_2856565] using wordTrace_append hprefix tailTrace_2856565
  have hstable : (prefixWord ++ tailWord_2856565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2856565).length < 2 ^ (prefixWord ++ tailWord_2856565).sum := by decide
  have hdescent : baseEnd_2856565 < baseStart_2856565 := by decide
  rcases family_descends (prefixWord ++ tailWord_2856565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2856566 : List Nat := [5, 1, 1, 2, 2, 3, 2, 2, 1, 2, 2]
def baseStart_2856566 : Nat := 118140960795 + 2856566 * 2 ^ 59
def prefixEnd_2856566 : Nat := 4983230072969 + 3 ^ 40 * 2856566 * 2
def baseEnd_2856566 : Nat := 1466791379291375906087899

theorem tailTrace_2856566 : CollatzResearch.WordTrace tailWord_2856566 prefixEnd_2856566 1466791379291375906087899 := by
  unfold tailWord_2856566
  simp only [CollatzResearch.WordTrace]
  refine ⟨6511720085572294967323847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 69458347579437812984787701 6511720085572294967323847)
  ·
    refine ⟨9767580128358442450985771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6511720085572294967323847 9767580128358442450985771)
    ·
      refine ⟨14651370192537663676478657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9767580128358442450985771 14651370192537663676478657)
      ·
        refine ⟨10988527644403247757358993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14651370192537663676478657 10988527644403247757358993)
        ·
          refine ⟨8241395733302435818019245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10988527644403247757358993 8241395733302435818019245)
          ·
            refine ⟨3090523399988413431757217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8241395733302435818019245 3090523399988413431757217)
            ·
              refine ⟨2317892549991310073817913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3090523399988413431757217 2317892549991310073817913)
              ·
                refine ⟨1738419412493482555363435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2317892549991310073817913 1738419412493482555363435)
                ·
                  refine ⟨2607629118740223833045153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1738419412493482555363435 2607629118740223833045153)
                  ·
                    refine ⟨1955721839055167874783865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2607629118740223833045153 1955721839055167874783865)
                    ·
                      refine ⟨1466791379291375906087899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1955721839055167874783865 1466791379291375906087899)
                      ·
                        rfl

theorem cell23_2856566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 3, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 3, 2, 2, 1, 2, 2].length) (baseStart_2856566 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2856566 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2856566 prefixEnd_2856566 := by exact prefixLift 2856566
  have htrace : WordTrace (prefixWord ++ tailWord_2856566) baseStart_2856566 baseEnd_2856566 := by
    simpa [prefixWord, tailWord_2856566, baseEnd_2856566] using wordTrace_append hprefix tailTrace_2856566
  have hstable : (prefixWord ++ tailWord_2856566).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2856566).length < 2 ^ (prefixWord ++ tailWord_2856566).sum := by decide
  have hdescent : baseEnd_2856566 < baseStart_2856566 := by decide
  rcases family_descends (prefixWord ++ tailWord_2856566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2856571 : List Nat := [1, 1, 1, 1, 1, 4, 3, 2, 3, 4, 2]
def baseStart_2856571 : Nat := 118140960795 + 2856571 * 2 ^ 59
def prefixEnd_2856571 : Nat := 4983230072969 + 3 ^ 40 * 2856571 * 2
def baseEnd_2856571 : Nat := 1466793946694648386525375

theorem tailTrace_2856571 : CollatzResearch.WordTrace tailWord_2856571 prefixEnd_2856571 1466793946694648386525375 := by
  unfold tailWord_2856571
  simp only [CollatzResearch.WordTrace]
  refine ⟨104187703734138605331113567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69458469156092403554075711 104187703734138605331113567)
  ·
    refine ⟨156281555601207907996670351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104187703734138605331113567 156281555601207907996670351)
    ·
      refine ⟨234422333401811861995005527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 156281555601207907996670351 234422333401811861995005527)
      ·
        refine ⟨351633500102717792992508291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 234422333401811861995005527 351633500102717792992508291)
        ·
          refine ⟨527450250154076689488762437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 351633500102717792992508291 527450250154076689488762437)
          ·
            refine ⟨98896921903889379279142957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 527450250154076689488762437 98896921903889379279142957)
            ·
              refine ⟨37086345713958517229678609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 98896921903889379279142957 37086345713958517229678609)
              ·
                refine ⟨27814759285468887922258957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37086345713958517229678609 27814759285468887922258957)
                ·
                  refine ⟨10430534732050832970847109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27814759285468887922258957 10430534732050832970847109)
                  ·
                    refine ⟨1955725262259531182033833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10430534732050832970847109 1955725262259531182033833)
                    ·
                      refine ⟨1466793946694648386525375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1955725262259531182033833 1466793946694648386525375)
                      ·
                        rfl

theorem cell23_2856571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 3, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 3, 2, 3, 4, 2].length) (baseStart_2856571 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2856571 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2856571 prefixEnd_2856571 := by exact prefixLift 2856571
  have htrace : WordTrace (prefixWord ++ tailWord_2856571) baseStart_2856571 baseEnd_2856571 := by
    simpa [prefixWord, tailWord_2856571, baseEnd_2856571] using wordTrace_append hprefix tailTrace_2856571
  have hstable : (prefixWord ++ tailWord_2856571).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2856571).length < 2 ^ (prefixWord ++ tailWord_2856571).sum := by decide
  have hdescent : baseEnd_2856571 < baseStart_2856571 := by decide
  rcases family_descends (prefixWord ++ tailWord_2856571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2856588 : List Nat := [2, 2, 1, 2, 1, 1, 6, 1, 1, 4, 2]
def baseStart_2856588 : Nat := 118140960795 + 2856588 * 2 ^ 59
def prefixEnd_2856588 : Nat := 4983230072969 + 3 ^ 40 * 2856588 * 2
def baseEnd_2856588 : Nat := 1466802675865774820012797

theorem tailTrace_2856588 : CollatzResearch.WordTrace tailWord_2856588 prefixEnd_2856588 1466802675865774820012797 := by
  unfold tailWord_2856588
  simp only [CollatzResearch.WordTrace]
  refine ⟨52094161887538508617241209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69458882516718011489654945 52094161887538508617241209)
  ·
    refine ⟨39070621415653881462930907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52094161887538508617241209 39070621415653881462930907)
    ·
      refine ⟨58605932123480822194396361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39070621415653881462930907 58605932123480822194396361)
      ·
        refine ⟨43954449092610616645797271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58605932123480822194396361 43954449092610616645797271)
        ·
          refine ⟨65931673638915924968695907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43954449092610616645797271 65931673638915924968695907)
          ·
            refine ⟨98897510458373887453043861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65931673638915924968695907 98897510458373887453043861)
            ·
              refine ⟨4635820802736275974361431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 98897510458373887453043861 4635820802736275974361431)
              ·
                refine ⟨6953731204104413961542147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4635820802736275974361431 6953731204104413961542147)
                ·
                  refine ⟨10430596806156620942313221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6953731204104413961542147 10430596806156620942313221)
                  ·
                    refine ⟨1955736901154366426683729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10430596806156620942313221 1955736901154366426683729)
                    ·
                      refine ⟨1466802675865774820012797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1955736901154366426683729 1466802675865774820012797)
                      ·
                        rfl

theorem cell23_2856588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 6, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 6, 1, 1, 4, 2].length) (baseStart_2856588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2856588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2856588 prefixEnd_2856588 := by exact prefixLift 2856588
  have htrace : WordTrace (prefixWord ++ tailWord_2856588) baseStart_2856588 baseEnd_2856588 := by
    simpa [prefixWord, tailWord_2856588, baseEnd_2856588] using wordTrace_append hprefix tailTrace_2856588
  have hstable : (prefixWord ++ tailWord_2856588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2856588).length < 2 ^ (prefixWord ++ tailWord_2856588).sum := by decide
  have hdescent : baseEnd_2856588 < baseStart_2856588 := by decide
  rcases family_descends (prefixWord ++ tailWord_2856588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2856616 : List Nat := [2, 1, 7, 1, 1, 2, 1, 2, 2, 1, 3]
def baseStart_2856616 : Nat := 118140960795 + 2856616 * 2 ^ 59
def prefixEnd_2856616 : Nat := 4983230072969 + 3 ^ 40 * 2856616 * 2
def baseEnd_2856616 : Nat := 1466817053324100710462669

theorem tailTrace_2856616 : CollatzResearch.WordTrace tailWord_2856616 prefixEnd_2856616 1466817053324100710462669 := by
  unfold tailWord_2856616
  simp only [CollatzResearch.WordTrace]
  refine ⟨52094672509487789008250851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69459563345983718677667801 52094672509487789008250851)
  ·
    refine ⟨78142008764231683512376277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52094672509487789008250851 78142008764231683512376277)
    ·
      refine ⟨1831453330411680082321319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 78142008764231683512376277 1831453330411680082321319)
      ·
        refine ⟨2747179995617520123481979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1831453330411680082321319 2747179995617520123481979)
        ·
          refine ⟨4120769993426280185222969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2747179995617520123481979 4120769993426280185222969)
          ·
            refine ⟨3090577495069710138917227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4120769993426280185222969 3090577495069710138917227)
            ·
              refine ⟨4635866242604565208375841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3090577495069710138917227 4635866242604565208375841)
              ·
                refine ⟨3476899681953423906281881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4635866242604565208375841 3476899681953423906281881)
                ·
                  refine ⟨2607674761465067929711411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3476899681953423906281881 2607674761465067929711411)
                  ·
                    refine ⟨3911512142197601894567117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2607674761465067929711411 3911512142197601894567117)
                    ·
                      refine ⟨1466817053324100710462669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3911512142197601894567117 1466817053324100710462669)
                      ·
                        rfl

theorem cell23_2856616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 2, 1, 2, 2, 1, 3].length) (baseStart_2856616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2856616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2856616 prefixEnd_2856616 := by exact prefixLift 2856616
  have htrace : WordTrace (prefixWord ++ tailWord_2856616) baseStart_2856616 baseEnd_2856616 := by
    simpa [prefixWord, tailWord_2856616, baseEnd_2856616] using wordTrace_append hprefix tailTrace_2856616
  have hstable : (prefixWord ++ tailWord_2856616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2856616).length < 2 ^ (prefixWord ++ tailWord_2856616).sum := by decide
  have hdescent : baseEnd_2856616 < baseStart_2856616 := by decide
  rcases family_descends (prefixWord ++ tailWord_2856616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2856638 : List Nat := [4, 2, 1, 1, 2, 2, 2, 1, 2, 3, 3]
def baseStart_2856638 : Nat := 118140960795 + 2856638 * 2 ^ 59
def prefixEnd_2856638 : Nat := 4983230072969 + 3 ^ 40 * 2856638 * 2
def baseEnd_2856638 : Nat := 1466828349898499624387567

theorem tailTrace_2856638 : CollatzResearch.WordTrace tailWord_2856638 prefixEnd_2856638 1466828349898499624387567 := by
  unfold tailWord_2856638
  simp only [CollatzResearch.WordTrace]
  refine ⟨13023768428111984471725321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 69460098283263917182535045 13023768428111984471725321)
  ·
    refine ⟨9767826321083988353793991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13023768428111984471725321 9767826321083988353793991)
    ·
      refine ⟨14651739481625982530690987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9767826321083988353793991 14651739481625982530690987)
      ·
        refine ⟨21977609222438973796036481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14651739481625982530690987 21977609222438973796036481)
        ·
          refine ⟨16483206916829230347027361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21977609222438973796036481 16483206916829230347027361)
          ·
            refine ⟨12362405187621922760270521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16483206916829230347027361 12362405187621922760270521)
            ·
              refine ⟨9271803890716442070202891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12362405187621922760270521 9271803890716442070202891)
              ·
                refine ⟨13907705836074663105304337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9271803890716442070202891 13907705836074663105304337)
                ·
                  refine ⟨10430779377055997328978253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13907705836074663105304337 10430779377055997328978253)
                  ·
                    refine ⟨3911542266395998998366845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10430779377055997328978253 3911542266395998998366845)
                    ·
                      refine ⟨1466828349898499624387567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3911542266395998998366845 1466828349898499624387567)
                      ·
                        rfl

theorem cell23_2856638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 2, 1, 2, 3, 3].length) (baseStart_2856638 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2856638 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2856638 prefixEnd_2856638 := by exact prefixLift 2856638
  have htrace : WordTrace (prefixWord ++ tailWord_2856638) baseStart_2856638 baseEnd_2856638 := by
    simpa [prefixWord, tailWord_2856638, baseEnd_2856638] using wordTrace_append hprefix tailTrace_2856638
  have hstable : (prefixWord ++ tailWord_2856638).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2856638).length < 2 ^ (prefixWord ++ tailWord_2856638).sum := by decide
  have hdescent : baseEnd_2856638 < baseStart_2856638 := by decide
  rcases family_descends (prefixWord ++ tailWord_2856638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2856778 : List Nat := [3, 1, 2, 1, 1, 1, 4, 2, 4, 4]
def baseStart_2856778 : Nat := 118140960795 + 2856778 * 2 ^ 59
def prefixEnd_2856778 : Nat := 4983230072969 + 3 ^ 40 * 2856778 * 2
def baseEnd_2856778 : Nat := 488966745730043025545641

theorem tailTrace_2856778 : CollatzResearch.WordTrace tailWord_2856778 prefixEnd_2856778 488966745730043025545641 := by
  unfold tailWord_2856778
  simp only [CollatzResearch.WordTrace]
  refine ⟨26048813411097169920974747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69463502429592453122599325 26048813411097169920974747)
  ·
    refine ⟨39073220116645754881462121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26048813411097169920974747 39073220116645754881462121)
    ·
      refine ⟨29304915087484316161096591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39073220116645754881462121 29304915087484316161096591)
      ·
        refine ⟨43957372631226474241644887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29304915087484316161096591 43957372631226474241644887)
        ·
          refine ⟨65936058946839711362467331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43957372631226474241644887 65936058946839711362467331)
          ·
            refine ⟨98904088420259567043700997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65936058946839711362467331 98904088420259567043700997)
            ·
              refine ⟨18544516578798668820693937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 98904088420259567043700997 18544516578798668820693937)
              ·
                refine ⟨13908387434099001615520453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18544516578798668820693937 13908387434099001615520453)
                ·
                  refine ⟨2607822643893562802910085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13908387434099001615520453 2607822643893562802910085)
                  ·
                    refine ⟨488966745730043025545641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2607822643893562802910085 488966745730043025545641)
                    ·
                      rfl

theorem cell23_2856778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 4, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 4, 2, 4, 4].length) (baseStart_2856778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2856778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2856778 prefixEnd_2856778 := by exact prefixLift 2856778
  have htrace : WordTrace (prefixWord ++ tailWord_2856778) baseStart_2856778 baseEnd_2856778 := by
    simpa [prefixWord, tailWord_2856778, baseEnd_2856778] using wordTrace_append hprefix tailTrace_2856778
  have hstable : (prefixWord ++ tailWord_2856778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2856778).length < 2 ^ (prefixWord ++ tailWord_2856778).sum := by decide
  have hdescent : baseEnd_2856778 < baseStart_2856778 := by decide
  rcases family_descends (prefixWord ++ tailWord_2856778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2856785 : List Nat := [1, 2, 2, 1, 5, 2, 1, 3, 1, 1, 4]
def baseStart_2856785 : Nat := 118140960795 + 2856785 * 2 ^ 59
def prefixEnd_2856785 : Nat := 4983230072969 + 3 ^ 40 * 2856785 * 2
def baseEnd_2856785 : Nat := 1466903831554710549249391

theorem tailTrace_2856785 : CollatzResearch.WordTrace tailWord_2856785 prefixEnd_2856785 1466903831554710549249391 := by
  unfold tailWord_2856785
  simp only [CollatzResearch.WordTrace]
  refine ⟨104195508955363319879403809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69463672636908879919602539 104195508955363319879403809)
  ·
    refine ⟨78146631716522489909552857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104195508955363319879403809 78146631716522489909552857)
    ·
      refine ⟨58609973787391867432164643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78146631716522489909552857 58609973787391867432164643)
      ·
        refine ⟨87914960681087801148246965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58609973787391867432164643 87914960681087801148246965)
        ·
          refine ⟨8242027563851981357648153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 87914960681087801148246965 8242027563851981357648153)
          ·
            refine ⟨6181520672888986018236115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8242027563851981357648153 6181520672888986018236115)
            ·
              refine ⟨9272281009333479027354173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6181520672888986018236115 9272281009333479027354173)
              ·
                refine ⟨3477105378500054635257815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9272281009333479027354173 3477105378500054635257815)
                ·
                  refine ⟨5215658067750081952886723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3477105378500054635257815 5215658067750081952886723)
                  ·
                    refine ⟨7823487101625122929330085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5215658067750081952886723 7823487101625122929330085)
                    ·
                      refine ⟨1466903831554710549249391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7823487101625122929330085 1466903831554710549249391)
                      ·
                        rfl

theorem cell23_2856785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 2, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 2, 1, 3, 1, 1, 4].length) (baseStart_2856785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2856785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2856785 prefixEnd_2856785 := by exact prefixLift 2856785
  have htrace : WordTrace (prefixWord ++ tailWord_2856785) baseStart_2856785 baseEnd_2856785 := by
    simpa [prefixWord, tailWord_2856785, baseEnd_2856785] using wordTrace_append hprefix tailTrace_2856785
  have hstable : (prefixWord ++ tailWord_2856785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2856785).length < 2 ^ (prefixWord ++ tailWord_2856785).sum := by decide
  have hdescent : baseEnd_2856785 < baseStart_2856785 := by decide
  rcases family_descends (prefixWord ++ tailWord_2856785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2856812 : List Nat := [2, 2, 1, 1, 4, 3, 3, 1, 2, 4]
def baseStart_2856812 : Nat := 118140960795 + 2856812 * 2 ^ 59
def prefixEnd_2856812 : Nat := 4983230072969 + 3 ^ 40 * 2856812 * 2
def baseEnd_2856812 : Nat := 488972565177460647870589

theorem tailTrace_2856812 : CollatzResearch.WordTrace tailWord_2856812 prefixEnd_2856812 488972565177460647870589 := by
  unfold tailWord_2856812
  simp only [CollatzResearch.WordTrace]
  refine ⟨52098246863132751745318345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69464329150843668993757793 52098246863132751745318345)
  ·
    refine ⟨39073685147349563808988759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52098246863132751745318345 39073685147349563808988759)
    ·
      refine ⟨58610527721024345713483139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39073685147349563808988759 58610527721024345713483139)
      ·
        refine ⟨87915791581536518570224709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58610527721024345713483139 87915791581536518570224709)
        ·
          refine ⟨16484210921538097231917133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 87915791581536518570224709 16484210921538097231917133)
          ·
            refine ⟨6181579095576786461968925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16484210921538097231917133 6181579095576786461968925)
            ·
              refine ⟨2318092160841294923238347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6181579095576786461968925 2318092160841294923238347)
              ·
                refine ⟨3477138241261942384857521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2318092160841294923238347 3477138241261942384857521)
                ·
                  refine ⟨2607853680946456788643141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3477138241261942384857521 2607853680946456788643141)
                  ·
                    refine ⟨488972565177460647870589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2607853680946456788643141 488972565177460647870589)
                    ·
                      rfl

theorem cell23_2856812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 2, 4].length) (baseStart_2856812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2856812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2856812 prefixEnd_2856812 := by exact prefixLift 2856812
  have htrace : WordTrace (prefixWord ++ tailWord_2856812) baseStart_2856812 baseEnd_2856812 := by
    simpa [prefixWord, tailWord_2856812, baseEnd_2856812] using wordTrace_append hprefix tailTrace_2856812
  have hstable : (prefixWord ++ tailWord_2856812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2856812).length < 2 ^ (prefixWord ++ tailWord_2856812).sum := by decide
  have hdescent : baseEnd_2856812 < baseStart_2856812 := by decide
  rcases family_descends (prefixWord ++ tailWord_2856812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2856835 : List Nat := [1, 1, 1, 3, 4, 2, 1, 2, 4, 1, 3]
def baseStart_2856835 : Nat := 118140960795 + 2856835 * 2 ^ 59
def prefixEnd_2856835 : Nat := 4983230072969 + 3 ^ 40 * 2856835 * 2
def baseEnd_2856835 : Nat := 1466929505587435353624161

theorem tailTrace_2856835 : CollatzResearch.WordTrace tailWord_2856835 prefixEnd_2856835 1466929505587435353624161 := by
  unfold tailWord_2856835
  simp only [CollatzResearch.WordTrace]
  refine ⟨104197332605182178418723959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69464888403454785612482639 104197332605182178418723959)
  ·
    refine ⟨156295998907773267628085939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104197332605182178418723959 156295998907773267628085939)
    ·
      refine ⟨234443998361659901442128909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 156295998907773267628085939 234443998361659901442128909)
      ·
        refine ⟨87916499385622463040798341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 234443998361659901442128909 87916499385622463040798341)
        ·
          refine ⟨16484343634804211820149689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 87916499385622463040798341 16484343634804211820149689)
          ·
            refine ⟨12363257726103158865112267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16484343634804211820149689 12363257726103158865112267)
            ·
              refine ⟨18544886589154738297668401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12363257726103158865112267 18544886589154738297668401)
              ·
                refine ⟨13908664941866053723251301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18544886589154738297668401 13908664941866053723251301)
                ·
                  refine ⟨2607874676599885073109619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13908664941866053723251301 2607874676599885073109619)
                  ·
                    refine ⟨3911812014899827609664429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2607874676599885073109619 3911812014899827609664429)
                    ·
                      refine ⟨1466929505587435353624161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3911812014899827609664429 1466929505587435353624161)
                      ·
                        rfl

theorem cell23_2856835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 1, 2, 4, 1, 3].length) (baseStart_2856835 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2856835 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2856835 prefixEnd_2856835 := by exact prefixLift 2856835
  have htrace : WordTrace (prefixWord ++ tailWord_2856835) baseStart_2856835 baseEnd_2856835 := by
    simpa [prefixWord, tailWord_2856835, baseEnd_2856835] using wordTrace_append hprefix tailTrace_2856835
  have hstable : (prefixWord ++ tailWord_2856835).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2856835).length < 2 ^ (prefixWord ++ tailWord_2856835).sum := by decide
  have hdescent : baseEnd_2856835 < baseStart_2856835 := by decide
  rcases family_descends (prefixWord ++ tailWord_2856835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2856852 : List Nat := [2, 4, 2, 1, 1, 2, 2, 1, 4, 1, 3]
def baseStart_2856852 : Nat := 118140960795 + 2856852 * 2 ^ 59
def prefixEnd_2856852 : Nat := 4983230072969 + 3 ^ 40 * 2856852 * 2
def baseEnd_2856852 : Nat := 1466938234758561787111583

theorem tailTrace_2856852 : CollatzResearch.WordTrace tailWord_2856852 prefixEnd_2856852 1466938234758561787111583 := by
  unfold tailWord_2856852
  simp only [CollatzResearch.WordTrace]
  refine ⟨52098976323060295161046405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69465301764080393548061873 52098976323060295161046405)
  ·
    refine ⟨9768558060573805342696201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 52098976323060295161046405 9768558060573805342696201)
    ·
      refine ⟨7326418545430354007022151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9768558060573805342696201 7326418545430354007022151)
      ·
        refine ⟨10989627818145531010533227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7326418545430354007022151 10989627818145531010533227)
        ·
          refine ⟨16484441727218296515799841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10989627818145531010533227 16484441727218296515799841)
          ·
            refine ⟨12363331295413722386849881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16484441727218296515799841 12363331295413722386849881)
            ·
              refine ⟨9272498471560291790137411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12363331295413722386849881 9272498471560291790137411)
              ·
                refine ⟨13908747707340437685206117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9272498471560291790137411 13908747707340437685206117)
                ·
                  refine ⟨2607890195126332065976147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13908747707340437685206117 2607890195126332065976147)
                  ·
                    refine ⟨3911835292689498098964221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2607890195126332065976147 3911835292689498098964221)
                    ·
                      refine ⟨1466938234758561787111583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3911835292689498098964221 1466938234758561787111583)
                      ·
                        rfl

theorem cell23_2856852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 2, 1, 4, 1, 3].length) (baseStart_2856852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2856852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2856852 prefixEnd_2856852 := by exact prefixLift 2856852
  have htrace : WordTrace (prefixWord ++ tailWord_2856852) baseStart_2856852 baseEnd_2856852 := by
    simpa [prefixWord, tailWord_2856852, baseEnd_2856852] using wordTrace_append hprefix tailTrace_2856852
  have hstable : (prefixWord ++ tailWord_2856852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2856852).length < 2 ^ (prefixWord ++ tailWord_2856852).sum := by decide
  have hdescent : baseEnd_2856852 < baseStart_2856852 := by decide
  rcases family_descends (prefixWord ++ tailWord_2856852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2856928 : List Nat := [2, 1, 1, 3, 1, 1, 1, 4, 4, 5]
def baseStart_2856928 : Nat := 118140960795 + 2856928 * 2 ^ 59
def prefixEnd_2856928 : Nat := 4983230072969 + 3 ^ 40 * 2856928 * 2
def baseEnd_2856928 : Nat := 488992419762767829920411

theorem tailTrace_2856928 : CollatzResearch.WordTrace tailWord_2856928 prefixEnd_2856928 488992419762767829920411 := by
  unfold tailWord_2856928
  simp only [CollatzResearch.WordTrace]
  refine ⟨52100362296922627650929719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69467149729230170201239625 52100362296922627650929719)
  ·
    refine ⟨78150543445383941476394579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52100362296922627650929719 78150543445383941476394579)
    ·
      refine ⟨117225815168075912214591869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78150543445383941476394579 117225815168075912214591869)
      ·
        refine ⟨43959680688028467080471951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 117225815168075912214591869 43959680688028467080471951)
        ·
          refine ⟨65939521032042700620707927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43959680688028467080471951 65939521032042700620707927)
          ·
            refine ⟨98909281548064050931061891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65939521032042700620707927 98909281548064050931061891)
            ·
              refine ⟨148363922322096076396592837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 98909281548064050931061891 148363922322096076396592837)
              ·
                refine ⟨27818235435393014324361157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 148363922322096076396592837 27818235435393014324361157)
                ·
                  refine ⟨5215919144136190185817717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27818235435393014324361157 5215919144136190185817717)
                  ·
                    refine ⟨488992419762767829920411, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5215919144136190185817717 488992419762767829920411)
                    ·
                      rfl

theorem cell23_2856928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 4, 4, 5].length) (baseStart_2856928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2856928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2856928 prefixEnd_2856928 := by exact prefixLift 2856928
  have htrace : WordTrace (prefixWord ++ tailWord_2856928) baseStart_2856928 baseEnd_2856928 := by
    simpa [prefixWord, tailWord_2856928, baseEnd_2856928] using wordTrace_append hprefix tailTrace_2856928
  have hstable : (prefixWord ++ tailWord_2856928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2856928).length < 2 ^ (prefixWord ++ tailWord_2856928).sum := by decide
  have hdescent : baseEnd_2856928 < baseStart_2856928 := by decide
  rcases family_descends (prefixWord ++ tailWord_2856928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2856945 : List Nat := [1, 2, 2, 2, 5, 1, 1, 1, 1, 7]
def baseStart_2856945 : Nat := 118140960795 + 2856945 * 2 ^ 59
def prefixEnd_2856945 : Nat := 4983230072969 + 3 ^ 40 * 2856945 * 2
def baseEnd_2856945 : Nat := 488995329486476641082885

theorem tailTrace_2856945 : CollatzResearch.WordTrace tailWord_2856945 prefixEnd_2856945 488995329486476641082885 := by
  unfold tailWord_2856945
  simp only [CollatzResearch.WordTrace]
  refine ⟨104201344634783667205228289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69467563089855778136818859 104201344634783667205228289)
  ·
    refine ⟨78151008476087750403921217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104201344634783667205228289 78151008476087750403921217)
    ·
      refine ⟨58613256357065812802940913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78151008476087750403921217 58613256357065812802940913)
      ·
        refine ⟨43959942267799359602205685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58613256357065812802940913 43959942267799359602205685)
        ·
          refine ⟨4121244587606189962706783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 43959942267799359602205685 4121244587606189962706783)
          ·
            refine ⟨6181866881409284944060175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4121244587606189962706783 6181866881409284944060175)
            ·
              refine ⟨9272800322113927416090263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6181866881409284944060175 9272800322113927416090263)
              ·
                refine ⟨13909200483170891124135395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9272800322113927416090263 13909200483170891124135395)
                ·
                  refine ⟨20863800724756336686203093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13909200483170891124135395 20863800724756336686203093)
                  ·
                    refine ⟨488995329486476641082885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 20863800724756336686203093 488995329486476641082885)
                    ·
                      rfl

theorem cell23_2856945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 1, 1, 1, 1, 7].length) (baseStart_2856945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2856945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2856945 prefixEnd_2856945 := by exact prefixLift 2856945
  have htrace : WordTrace (prefixWord ++ tailWord_2856945) baseStart_2856945 baseEnd_2856945 := by
    simpa [prefixWord, tailWord_2856945, baseEnd_2856945] using wordTrace_append hprefix tailTrace_2856945
  have hstable : (prefixWord ++ tailWord_2856945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2856945).length < 2 ^ (prefixWord ++ tailWord_2856945).sum := by decide
  have hdescent : baseEnd_2856945 < baseStart_2856945 := by decide
  rcases family_descends (prefixWord ++ tailWord_2856945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2857002 : List Nat := [3, 1, 4, 1, 2, 1, 2, 1, 1, 4, 3]
def baseStart_2857002 : Nat := 118140960795 + 2857002 * 2 ^ 59
def prefixEnd_2857002 : Nat := 4983230072969 + 3 ^ 40 * 2857002 * 2
def baseEnd_2857002 : Nat := 1467015256856736200235893

theorem tailTrace_2857002 : CollatzResearch.WordTrace tailWord_2857002 prefixEnd_2857002 1467015256856736200235893 := by
  unfold tailWord_2857002
  simp only [CollatzResearch.WordTrace]
  refine ⟨26050855898894291485013315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69468949063718110626702173 26050855898894291485013315)
  ·
    refine ⟨39076283848341437227519973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26050855898894291485013315 39076283848341437227519973)
    ·
      refine ⟨7326803221564019480159995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 39076283848341437227519973 7326803221564019480159995)
      ·
        refine ⟨10990204832346029220239993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7326803221564019480159995 10990204832346029220239993)
        ·
          refine ⟨8242653624259521915179995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10990204832346029220239993 8242653624259521915179995)
          ·
            refine ⟨12363980436389282872769993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8242653624259521915179995 12363980436389282872769993)
            ·
              refine ⟨9272985327291962154577495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12363980436389282872769993 9272985327291962154577495)
              ·
                refine ⟨13909477990937943231866243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9272985327291962154577495 13909477990937943231866243)
                ·
                  refine ⟨20864216986406914847799365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13909477990937943231866243 20864216986406914847799365)
                  ·
                    refine ⟨3912040684951296533962381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20864216986406914847799365 3912040684951296533962381)
                    ·
                      refine ⟨1467015256856736200235893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3912040684951296533962381 1467015256856736200235893)
                      ·
                        rfl

theorem cell23_2857002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 2, 1, 1, 4, 3].length) (baseStart_2857002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2857002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2857002 prefixEnd_2857002 := by exact prefixLift 2857002
  have htrace : WordTrace (prefixWord ++ tailWord_2857002) baseStart_2857002 baseEnd_2857002 := by
    simpa [prefixWord, tailWord_2857002, baseEnd_2857002] using wordTrace_append hprefix tailTrace_2857002
  have hstable : (prefixWord ++ tailWord_2857002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2857002).length < 2 ^ (prefixWord ++ tailWord_2857002).sum := by decide
  have hdescent : baseEnd_2857002 < baseStart_2857002 := by decide
  rcases family_descends (prefixWord ++ tailWord_2857002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2857009 : List Nat := [1, 2, 2, 3, 1, 3, 3, 3, 1, 4]
def baseStart_2857009 : Nat := 118140960795 + 2857009 * 2 ^ 59
def prefixEnd_2857009 : Nat := 4983230072969 + 3 ^ 40 * 2857009 * 2
def baseEnd_2857009 : Nat := 489006283740439224282787

theorem tailTrace_2857009 : CollatzResearch.WordTrace tailWord_2857009 prefixEnd_2857009 489006283740439224282787 := by
  unfold tailWord_2857009
  simp only [CollatzResearch.WordTrace]
  refine ⟨104203678906551806135558081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69469119271034537423705387 104203678906551806135558081)
  ·
    refine ⟨78152759179913854601668561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104203678906551806135558081 78152759179913854601668561)
    ·
      refine ⟨58614569384935390951251421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78152759179913854601668561 58614569384935390951251421)
      ·
        refine ⟨21980463519350771606719283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 58614569384935390951251421 21980463519350771606719283)
        ·
          refine ⟨32970695279026157410078925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21980463519350771606719283 32970695279026157410078925)
          ·
            refine ⟨12364010729634809028779597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32970695279026157410078925 12364010729634809028779597)
            ·
              refine ⟨4636504023613053385792349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12364010729634809028779597 4636504023613053385792349)
              ·
                refine ⟨1738689008854895019672131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4636504023613053385792349 1738689008854895019672131)
                ·
                  refine ⟨2608033513282342529508197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1738689008854895019672131 2608033513282342529508197)
                  ·
                    refine ⟨489006283740439224282787, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2608033513282342529508197 489006283740439224282787)
                    ·
                      rfl

theorem cell23_2857009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 3, 3, 1, 4].length) (baseStart_2857009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2857009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2857009 prefixEnd_2857009 := by exact prefixLift 2857009
  have htrace : WordTrace (prefixWord ++ tailWord_2857009) baseStart_2857009 baseEnd_2857009 := by
    simpa [prefixWord, tailWord_2857009, baseEnd_2857009] using wordTrace_append hprefix tailTrace_2857009
  have hstable : (prefixWord ++ tailWord_2857009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2857009).length < 2 ^ (prefixWord ++ tailWord_2857009).sum := by decide
  have hdescent : baseEnd_2857009 < baseStart_2857009 := by decide
  rcases family_descends (prefixWord ++ tailWord_2857009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2857032 : List Nat := [2, 1, 3, 1, 1, 1, 2, 5, 3, 1, 3]
def baseStart_2857032 : Nat := 118140960795 + 2857032 * 2 ^ 59
def prefixEnd_2857032 : Nat := 4983230072969 + 3 ^ 40 * 2857032 * 2
def baseEnd_2857032 : Nat := 1467030661276371082860755

theorem tailTrace_2857032 : CollatzResearch.WordTrace tailWord_2857032 prefixEnd_2857032 1467030661276371082860755 := by
  unfold tailWord_2857032
  simp only [CollatzResearch.WordTrace]
  refine ⟨52102258892734240531822675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69469678523645654042430233 52102258892734240531822675)
  ·
    refine ⟨78153388339101360797734013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52102258892734240531822675 78153388339101360797734013)
    ·
      refine ⟨29307520627163010299150255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 78153388339101360797734013 29307520627163010299150255)
      ·
        refine ⟨43961280940744515448725383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29307520627163010299150255 43961280940744515448725383)
        ·
          refine ⟨65941921411116773173088075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43961280940744515448725383 65941921411116773173088075)
          ·
            refine ⟨98912882116675159759632113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 65941921411116773173088075 98912882116675159759632113)
            ·
              refine ⟨74184661587506369819724085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 98912882116675159759632113 74184661587506369819724085)
              ·
                refine ⟨6954812023828722170599133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 74184661587506369819724085 6954812023828722170599133)
                ·
                  refine ⟨2608054508935770813974675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6954812023828722170599133 2608054508935770813974675)
                  ·
                    refine ⟨3912081763403656220962013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2608054508935770813974675 3912081763403656220962013)
                    ·
                      refine ⟨1467030661276371082860755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3912081763403656220962013 1467030661276371082860755)
                      ·
                        rfl

theorem cell23_2857032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 5, 3, 1, 3].length) (baseStart_2857032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2857032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2857032 prefixEnd_2857032 := by exact prefixLift 2857032
  have htrace : WordTrace (prefixWord ++ tailWord_2857032) baseStart_2857032 baseEnd_2857032 := by
    simpa [prefixWord, tailWord_2857032, baseEnd_2857032] using wordTrace_append hprefix tailTrace_2857032
  have hstable : (prefixWord ++ tailWord_2857032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2857032).length < 2 ^ (prefixWord ++ tailWord_2857032).sum := by decide
  have hdescent : baseEnd_2857032 < baseStart_2857032 := by decide
  rcases family_descends (prefixWord ++ tailWord_2857032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2857052 : List Nat := [2, 2, 4, 1, 1, 3, 1, 1, 3, 5]
def baseStart_2857052 : Nat := 118140960795 + 2857052 * 2 ^ 59
def prefixEnd_2857052 : Nat := 4983230072969 + 3 ^ 40 * 2857052 * 2
def baseEnd_2857052 : Nat := 489013643629820334870221

theorem tailTrace_2857052 : CollatzResearch.WordTrace tailWord_2857052 prefixEnd_2857052 489013643629820334870221 := by
  unfold tailWord_2857052
  simp only [CollatzResearch.WordTrace]
  refine ⟨52102623622698012239686705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69470164830264016319582273 52102623622698012239686705)
  ·
    refine ⟨39076967717023509179765029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52102623622698012239686705 39076967717023509179765029)
    ·
      refine ⟨7326931446941907971205943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 39076967717023509179765029 7326931446941907971205943)
      ·
        refine ⟨10990397170412861956808915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7326931446941907971205943 10990397170412861956808915)
        ·
          refine ⟨16485595755619292935213373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10990397170412861956808915 16485595755619292935213373)
          ·
            refine ⟨6182098408357234850705015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16485595755619292935213373 6182098408357234850705015)
            ·
              refine ⟨9273147612535852276057523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6182098408357234850705015 9273147612535852276057523)
              ·
                refine ⟨13909721418803778414086285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9273147612535852276057523 13909721418803778414086285)
                ·
                  refine ⟨5216145532051416905282357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13909721418803778414086285 5216145532051416905282357)
                  ·
                    refine ⟨489013643629820334870221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5216145532051416905282357 489013643629820334870221)
                    ·
                      rfl

theorem cell23_2857052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 3, 1, 1, 3, 5].length) (baseStart_2857052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2857052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2857052 prefixEnd_2857052 := by exact prefixLift 2857052
  have htrace : WordTrace (prefixWord ++ tailWord_2857052) baseStart_2857052 baseEnd_2857052 := by
    simpa [prefixWord, tailWord_2857052, baseEnd_2857052] using wordTrace_append hprefix tailTrace_2857052
  have hstable : (prefixWord ++ tailWord_2857052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2857052).length < 2 ^ (prefixWord ++ tailWord_2857052).sum := by decide
  have hdescent : baseEnd_2857052 < baseStart_2857052 := by decide
  rcases family_descends (prefixWord ++ tailWord_2857052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2857065 : List Nat := [1, 2, 1, 1, 1, 5, 3, 2, 1, 6]
def baseStart_2857065 : Nat := 118140960795 + 2857065 * 2 ^ 59
def prefixEnd_2857065 : Nat := 4983230072969 + 3 ^ 40 * 2857065 * 2
def baseEnd_2857065 : Nat := 489015868712656484582701

theorem tailTrace_2857065 : CollatzResearch.WordTrace tailWord_2857065 prefixEnd_2857065 489015868712656484582701 := by
  unfold tailWord_2857065
  simp only [CollatzResearch.WordTrace]
  refine ⟨104205721394348927699596649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69470480929565951799731099 104205721394348927699596649)
  ·
    refine ⟨78154291045761695774697487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104205721394348927699596649 78154291045761695774697487)
    ·
      refine ⟨117231436568642543662046231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78154291045761695774697487 117231436568642543662046231)
      ·
        refine ⟨175847154852963815493069347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 117231436568642543662046231 175847154852963815493069347)
        ·
          refine ⟨263770732279445723239604021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 175847154852963815493069347 263770732279445723239604021)
          ·
            refine ⟨24728506151198036553712877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 263770732279445723239604021 24728506151198036553712877)
            ·
              refine ⟨9273189806699263707642329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24728506151198036553712877 9273189806699263707642329)
              ·
                refine ⟨6954892355024447780731747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9273189806699263707642329 6954892355024447780731747)
                ·
                  refine ⟨10432338532536671671097621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6954892355024447780731747 10432338532536671671097621)
                  ·
                    refine ⟨489015868712656484582701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10432338532536671671097621 489015868712656484582701)
                    ·
                      rfl

theorem cell23_2857065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 3, 2, 1, 6].length) (baseStart_2857065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2857065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2857065 prefixEnd_2857065 := by exact prefixLift 2857065
  have htrace : WordTrace (prefixWord ++ tailWord_2857065) baseStart_2857065 baseEnd_2857065 := by
    simpa [prefixWord, tailWord_2857065, baseEnd_2857065] using wordTrace_append hprefix tailTrace_2857065
  have hstable : (prefixWord ++ tailWord_2857065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2857065).length < 2 ^ (prefixWord ++ tailWord_2857065).sum := by decide
  have hdescent : baseEnd_2857065 < baseStart_2857065 := by decide
  rcases family_descends (prefixWord ++ tailWord_2857065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2857069 : List Nat := [1, 5, 1, 1, 2, 1, 5, 1, 1, 5]
def baseStart_2857069 : Nat := 118140960795 + 2857069 * 2 ^ 59
def prefixEnd_2857069 : Nat := 4983230072969 + 3 ^ 40 * 2857069 * 2
def baseEnd_2857069 : Nat := 489016553353529146032695

theorem tailTrace_2857069 : CollatzResearch.WordTrace tailWord_2857069 prefixEnd_2857069 489016553353529146032695 := by
  unfold tailWord_2857069
  simp only [CollatzResearch.WordTrace]
  refine ⟨104205867286334436382742261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69470578190889624255161507 104205867286334436382742261)
  ·
    refine ⟨9769300058093853410882087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 104205867286334436382742261 9769300058093853410882087)
    ·
      refine ⟨14653950087140780116323131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9769300058093853410882087 14653950087140780116323131)
      ·
        refine ⟨21980925130711170174484697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14653950087140780116323131 21980925130711170174484697)
        ·
          refine ⟨16485693848033377630863523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21980925130711170174484697 16485693848033377630863523)
          ·
            refine ⟨24728540772050066446295285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16485693848033377630863523 24728540772050066446295285)
            ·
              refine ⟨2318300697379693729340183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 24728540772050066446295285 2318300697379693729340183)
              ·
                refine ⟨3477451046069540594010275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2318300697379693729340183 3477451046069540594010275)
                ·
                  refine ⟨5216176569104310891015413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3477451046069540594010275 5216176569104310891015413)
                  ·
                    refine ⟨489016553353529146032695, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5216176569104310891015413 489016553353529146032695)
                    ·
                      rfl

theorem cell23_2857069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 5, 1, 1, 5].length) (baseStart_2857069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2857069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2857069 prefixEnd_2857069 := by exact prefixLift 2857069
  have htrace : WordTrace (prefixWord ++ tailWord_2857069) baseStart_2857069 baseEnd_2857069 := by
    simpa [prefixWord, tailWord_2857069, baseEnd_2857069] using wordTrace_append hprefix tailTrace_2857069
  have hstable : (prefixWord ++ tailWord_2857069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2857069).length < 2 ^ (prefixWord ++ tailWord_2857069).sum := by decide
  have hdescent : baseEnd_2857069 < baseStart_2857069 := by decide
  rcases family_descends (prefixWord ++ tailWord_2857069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2857092 : List Nat := [2, 3, 2, 1, 2, 1, 1, 1, 5, 2, 3]
def baseStart_2857092 : Nat := 118140960795 + 2857092 * 2 ^ 59
def prefixEnd_2857092 : Nat := 4983230072969 + 3 ^ 40 * 2857092 * 2
def baseEnd_2857092 : Nat := 1467061470115640848110479

theorem tailTrace_2857092 : CollatzResearch.WordTrace tailWord_2857092 prefixEnd_2857092 1467061470115640848110479 := by
  unfold tailWord_2857092
  simp only [CollatzResearch.WordTrace]
  refine ⟨52103353082625555655414765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69471137443500740873886353 52103353082625555655414765)
  ·
    refine ⟨19538757405984583370780537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52103353082625555655414765 19538757405984583370780537)
    ·
      refine ⟨14654068054488437528085403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19538757405984583370780537 14654068054488437528085403)
      ·
        refine ⟨21981102081732656292128105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14654068054488437528085403 21981102081732656292128105)
        ·
          refine ⟨16485826561299492219096079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21981102081732656292128105 16485826561299492219096079)
          ·
            refine ⟨24728739841949238328644119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16485826561299492219096079 24728739841949238328644119)
            ·
              refine ⟨37093109762923857492966179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24728739841949238328644119 37093109762923857492966179)
              ·
                refine ⟨55639664644385786239449269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37093109762923857492966179 55639664644385786239449269)
                ·
                  refine ⟨5216218560411167459948369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 55639664644385786239449269 5216218560411167459948369)
                  ·
                    refine ⟨3912163920308375594961277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5216218560411167459948369 3912163920308375594961277)
                    ·
                      refine ⟨1467061470115640848110479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3912163920308375594961277 1467061470115640848110479)
                      ·
                        rfl

theorem cell23_2857092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 1, 1, 5, 2, 3].length) (baseStart_2857092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2857092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2857092 prefixEnd_2857092 := by exact prefixLift 2857092
  have htrace : WordTrace (prefixWord ++ tailWord_2857092) baseStart_2857092 baseEnd_2857092 := by
    simpa [prefixWord, tailWord_2857092, baseEnd_2857092] using wordTrace_append hprefix tailTrace_2857092
  have hstable : (prefixWord ++ tailWord_2857092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2857092).length < 2 ^ (prefixWord ++ tailWord_2857092).sum := by decide
  have hdescent : baseEnd_2857092 < baseStart_2857092 := by decide
  rcases family_descends (prefixWord ++ tailWord_2857092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2857095 : List Nat := [1, 1, 4, 2, 1, 1, 5, 8]
def baseStart_2857095 : Nat := 118140960795 + 2857095 * 2 ^ 59
def prefixEnd_2857095 : Nat := 4983230072969 + 3 ^ 40 * 2857095 * 2
def baseEnd_2857095 : Nat := 54335667057689049495295

theorem tailTrace_2857095 : CollatzResearch.WordTrace tailWord_2857095 prefixEnd_2857095 54335667057689049495295 := by
  unfold tailWord_2857095
  simp only [CollatzResearch.WordTrace]
  refine ⟨104206815584240242823188739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69471210389493495215459159 104206815584240242823188739)
  ·
    refine ⟨156310223376360364234783109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104206815584240242823188739 156310223376360364234783109)
    ·
      refine ⟨29308166883067568294021833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 156310223376360364234783109 29308166883067568294021833)
      ·
        refine ⟨21981125162300676220516375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29308166883067568294021833 21981125162300676220516375)
        ·
          refine ⟨32971687743451014330774563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21981125162300676220516375 32971687743451014330774563)
          ·
            refine ⟨49457531615176521496161845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32971687743451014330774563 49457531615176521496161845)
            ·
              refine ⟨4636643588922798890265173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 49457531615176521496161845 4636643588922798890265173)
              ·
                refine ⟨54335667057689049495295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4636643588922798890265173 54335667057689049495295)
                ·
                  rfl

theorem cell23_2857095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 5, 8].length) (baseStart_2857095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2857095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2857095 prefixEnd_2857095 := by exact prefixLift 2857095
  have htrace : WordTrace (prefixWord ++ tailWord_2857095) baseStart_2857095 baseEnd_2857095 := by
    simpa [prefixWord, tailWord_2857095, baseEnd_2857095] using wordTrace_append hprefix tailTrace_2857095
  have hstable : (prefixWord ++ tailWord_2857095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2857095).length < 2 ^ (prefixWord ++ tailWord_2857095).sum := by decide
  have hdescent : baseEnd_2857095 < baseStart_2857095 := by decide
  rcases family_descends (prefixWord ++ tailWord_2857095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2857106 : List Nat := [3, 2, 3, 1, 1, 1, 3, 2, 3, 2, 2]
def baseStart_2857106 : Nat := 118140960795 + 2857106 * 2 ^ 59
def prefixEnd_2857106 : Nat := 4983230072969 + 3 ^ 40 * 2857106 * 2
def baseEnd_2857106 : Nat := 1467068658844803793335415

theorem tailTrace_2857106 : CollatzResearch.WordTrace tailWord_2857106 prefixEnd_2857106 1467068658844803793335415 := by
  unfold tailWord_2857106
  simp only [CollatzResearch.WordTrace]
  refine ⟨26051804196800097925459793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 69471477858133594467892781 26051804196800097925459793)
  ·
    refine ⟨19538853147600073444094845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26051804196800097925459793 19538853147600073444094845)
    ·
      refine ⟨7327069930350027541535567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19538853147600073444094845 7327069930350027541535567)
      ·
        refine ⟨10990604895525041312303351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7327069930350027541535567 10990604895525041312303351)
        ·
          refine ⟨16485907343287561968455027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10990604895525041312303351 16485907343287561968455027)
          ·
            refine ⟨24728861014931342952682541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16485907343287561968455027 24728861014931342952682541)
            ·
              refine ⟨9273322880599253607255953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24728861014931342952682541 9273322880599253607255953)
              ·
                refine ⟨6954992160449440205441965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9273322880599253607255953 6954992160449440205441965)
                ·
                  refine ⟨2608122060168540077040737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6954992160449440205441965 2608122060168540077040737)
                  ·
                    refine ⟨1956091545126405057780553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2608122060168540077040737 1956091545126405057780553)
                    ·
                      refine ⟨1467068658844803793335415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1956091545126405057780553 1467068658844803793335415)
                      ·
                        rfl

theorem cell23_2857106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 3, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 3, 2, 3, 2, 2].length) (baseStart_2857106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2857106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2857106 prefixEnd_2857106 := by exact prefixLift 2857106
  have htrace : WordTrace (prefixWord ++ tailWord_2857106) baseStart_2857106 baseEnd_2857106 := by
    simpa [prefixWord, tailWord_2857106, baseEnd_2857106] using wordTrace_append hprefix tailTrace_2857106
  have hstable : (prefixWord ++ tailWord_2857106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2857106).length < 2 ^ (prefixWord ++ tailWord_2857106).sum := by decide
  have hdescent : baseEnd_2857106 < baseStart_2857106 := by decide
  rcases family_descends (prefixWord ++ tailWord_2857106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2857153 : List Nat := [1, 2, 6, 1, 3, 1, 1, 1, 1, 2, 4]
def baseStart_2857153 : Nat := 118140960795 + 2857153 * 2 ^ 59
def prefixEnd_2857153 : Nat := 4983230072969 + 3 ^ 40 * 2857153 * 2
def baseEnd_2857153 : Nat := 1467092792435565109447699

theorem tailTrace_2857153 : CollatzResearch.WordTrace tailWord_2857153 prefixEnd_2857153 1467092792435565109447699 := by
  unfold tailWord_2857153
  simp only [CollatzResearch.WordTrace]
  refine ⟨104208931018030118728800113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69472620678686745819200075 104208931018030118728800113)
  ·
    refine ⟨78156698263522589046600085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 104208931018030118728800113 78156698263522589046600085)
    ·
      refine ⟨3663595231102621361559379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 78156698263522589046600085 3663595231102621361559379)
      ·
        refine ⟨5495392846653932042339069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3663595231102621361559379 5495392846653932042339069)
        ·
          refine ⟨2060772317495224515877151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5495392846653932042339069 2060772317495224515877151)
          ·
            refine ⟨3091158476242836773815727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2060772317495224515877151 3091158476242836773815727)
            ·
              refine ⟨4636737714364255160723591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3091158476242836773815727 4636737714364255160723591)
              ·
                refine ⟨6955106571546382741085387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4636737714364255160723591 6955106571546382741085387)
                ·
                  refine ⟨10432659857319574111628081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6955106571546382741085387 10432659857319574111628081)
                  ·
                    refine ⟨7824494892989680583721061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10432659857319574111628081 7824494892989680583721061)
                    ·
                      refine ⟨1467092792435565109447699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7824494892989680583721061 1467092792435565109447699)
                      ·
                        rfl

theorem cell23_2857153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 3, 1, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 3, 1, 1, 1, 1, 2, 4].length) (baseStart_2857153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2857153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2857153 prefixEnd_2857153 := by exact prefixLift 2857153
  have htrace : WordTrace (prefixWord ++ tailWord_2857153) baseStart_2857153 baseEnd_2857153 := by
    simpa [prefixWord, tailWord_2857153, baseEnd_2857153] using wordTrace_append hprefix tailTrace_2857153
  have hstable : (prefixWord ++ tailWord_2857153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2857153).length < 2 ^ (prefixWord ++ tailWord_2857153).sum := by decide
  have hdescent : baseEnd_2857153 < baseStart_2857153 := by decide
  rcases family_descends (prefixWord ++ tailWord_2857153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2857156 : List Nat := [2, 3, 3, 1, 2, 3, 1, 1, 1, 3, 3]
def baseStart_2857156 : Nat := 118140960795 + 2857156 * 2 ^ 59
def prefixEnd_2857156 : Nat := 4983230072969 + 3 ^ 40 * 2857156 * 2
def baseEnd_2857156 : Nat := 1467094332877528597710185

theorem tailTrace_2857156 : CollatzResearch.WordTrace tailWord_2857156 prefixEnd_2857156 1467094332877528597710185 := by
  unfold tailWord_2857156
  simp only [CollatzResearch.WordTrace]
  refine ⟨52104520218509625120579661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69472693624679500160772881 52104520218509625120579661)
  ·
    refine ⟨19539195081941109420217373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52104520218509625120579661 19539195081941109420217373)
    ·
      refine ⟨7327198155727916032581515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19539195081941109420217373 7327198155727916032581515)
      ·
        refine ⟨10990797233591874048872273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7327198155727916032581515 10990797233591874048872273)
        ·
          refine ⟨8243097925193905536654205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10990797233591874048872273 8243097925193905536654205)
          ·
            refine ⟨3091161721947714576245327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8243097925193905536654205 3091161721947714576245327)
            ·
              refine ⟨4636742582921571864367991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3091161721947714576245327 4636742582921571864367991)
              ·
                refine ⟨6955113874382357796551987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4636742582921571864367991 6955113874382357796551987)
                ·
                  refine ⟨10432670811573536694827981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6955113874382357796551987 10432670811573536694827981)
                  ·
                    refine ⟨3912251554340076260560493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10432670811573536694827981 3912251554340076260560493)
                    ·
                      refine ⟨1467094332877528597710185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3912251554340076260560493 1467094332877528597710185)
                      ·
                        rfl

theorem cell23_2857156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 3, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 3, 1, 1, 1, 3, 3].length) (baseStart_2857156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2857156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2857156 prefixEnd_2857156 := by exact prefixLift 2857156
  have htrace : WordTrace (prefixWord ++ tailWord_2857156) baseStart_2857156 baseEnd_2857156 := by
    simpa [prefixWord, tailWord_2857156, baseEnd_2857156] using wordTrace_append hprefix tailTrace_2857156
  have hstable : (prefixWord ++ tailWord_2857156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2857156).length < 2 ^ (prefixWord ++ tailWord_2857156).sum := by decide
  have hdescent : baseEnd_2857156 < baseStart_2857156 := by decide
  rcases family_descends (prefixWord ++ tailWord_2857156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2857166 : List Nat := [4, 1, 1, 1, 4, 1, 1, 4, 1, 3, 2]
def baseStart_2857166 : Nat := 118140960795 + 2857166 * 2 ^ 59
def prefixEnd_2857166 : Nat := 4983230072969 + 3 ^ 40 * 2857166 * 2
def baseEnd_2857166 : Nat := 1467099467684073558585139

theorem tailTrace_2857166 : CollatzResearch.WordTrace tailWord_2857166 prefixEnd_2857166 1467099467684073558585139 := by
  unfold tailWord_2857166
  simp only [CollatzResearch.WordTrace]
  refine ⟨13026175645872877743627919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 69472936777988681299348901 13026175645872877743627919)
  ·
    refine ⟨19539263468809316615441879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13026175645872877743627919 19539263468809316615441879)
    ·
      refine ⟨29308895203213974923162819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19539263468809316615441879 29308895203213974923162819)
      ·
        refine ⟨43963342804820962384744229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29308895203213974923162819 43963342804820962384744229)
        ·
          refine ⟨8243126775903930447139543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 43963342804820962384744229 8243126775903930447139543)
          ·
            refine ⟨12364690163855895670709315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8243126775903930447139543 12364690163855895670709315)
            ·
              refine ⟨18547035245783843506063973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12364690163855895670709315 18547035245783843506063973)
              ·
                refine ⟨3477569108584470657386995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18547035245783843506063973 3477569108584470657386995)
                ·
                  refine ⟨5216353662876705986080493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3477569108584470657386995 5216353662876705986080493)
                  ·
                    refine ⟨1956132623578764744780185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5216353662876705986080493 1956132623578764744780185)
                    ·
                      refine ⟨1467099467684073558585139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1956132623578764744780185 1467099467684073558585139)
                      ·
                        rfl

theorem cell23_2857166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 1, 4, 1, 3, 2].length) (baseStart_2857166 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2857166 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2857166 prefixEnd_2857166 := by exact prefixLift 2857166
  have htrace : WordTrace (prefixWord ++ tailWord_2857166) baseStart_2857166 baseEnd_2857166 := by
    simpa [prefixWord, tailWord_2857166, baseEnd_2857166] using wordTrace_append hprefix tailTrace_2857166
  have hstable : (prefixWord ++ tailWord_2857166).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2857166).length < 2 ^ (prefixWord ++ tailWord_2857166).sum := by decide
  have hdescent : baseEnd_2857166 < baseStart_2857166 := by decide
  rcases family_descends (prefixWord ++ tailWord_2857166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2857179 : List Nat := [1, 1, 1, 1, 1, 1, 1, 8, 4, 2, 2]
def baseStart_2857179 : Nat := 118140960795 + 2857179 * 2 ^ 59
def prefixEnd_2857179 : Nat := 4983230072969 + 3 ^ 40 * 2857179 * 2
def baseEnd_2857179 : Nat := 1467106142932582007722579

theorem tailTrace_2857179 : CollatzResearch.WordTrace tailWord_2857179 prefixEnd_2857179 1467106142932582007722579 := by
  unfold tailWord_2857179
  simp only [CollatzResearch.WordTrace]
  refine ⟨104209879315935925169246591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69473252877290616779497727 104209879315935925169246591)
  ·
    refine ⟨156314818973903887753869887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104209879315935925169246591 156314818973903887753869887)
    ·
      refine ⟨234472228460855831630804831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 156314818973903887753869887 234472228460855831630804831)
      ·
        refine ⟨351708342691283747446207247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 234472228460855831630804831 351708342691283747446207247)
        ·
          refine ⟨527562514036925621169310871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 351708342691283747446207247 527562514036925621169310871)
          ·
            refine ⟨791343771055388431753966307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 527562514036925621169310871 791343771055388431753966307)
            ·
              refine ⟨1187015656583082647630949461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 791343771055388431753966307 1187015656583082647630949461)
              ·
                refine ⟨13910339725582999776925189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1187015656583082647630949461 13910339725582999776925189)
                ·
                  refine ⟨2608188698546812458173473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13910339725582999776925189 2608188698546812458173473)
                  ·
                    refine ⟨1956141523910109343630105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2608188698546812458173473 1956141523910109343630105)
                    ·
                      refine ⟨1467106142932582007722579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1956141523910109343630105 1467106142932582007722579)
                      ·
                        rfl

theorem cell23_2857179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 8, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 8, 4, 2, 2].length) (baseStart_2857179 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2857179 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2857179 prefixEnd_2857179 := by exact prefixLift 2857179
  have htrace : WordTrace (prefixWord ++ tailWord_2857179) baseStart_2857179 baseEnd_2857179 := by
    simpa [prefixWord, tailWord_2857179, baseEnd_2857179] using wordTrace_append hprefix tailTrace_2857179
  have hstable : (prefixWord ++ tailWord_2857179).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2857179).length < 2 ^ (prefixWord ++ tailWord_2857179).sum := by decide
  have hdescent : baseEnd_2857179 < baseStart_2857179 := by decide
  rcases family_descends (prefixWord ++ tailWord_2857179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2857195 : List Nat := [1, 1, 1, 1, 2, 5, 1, 1, 1, 2, 7]
def baseStart_2857195 : Nat := 118140960795 + 2857195 * 2 ^ 59
def prefixEnd_2857195 : Nat := 4983230072969 + 3 ^ 40 * 2857195 * 2
def baseEnd_2857195 : Nat := 1467114358623053945122505

theorem tailTrace_2857195 : CollatzResearch.WordTrace tailWord_2857195 prefixEnd_2857195 1467114358623053945122505 := by
  unfold tailWord_2857195
  simp only [CollatzResearch.WordTrace]
  refine ⟨104210462883877959901829039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69473641922585306601219359 104210462883877959901829039)
  ·
    refine ⟨156315694325816939852743559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104210462883877959901829039 156315694325816939852743559)
    ·
      refine ⟨234473541488725409779115339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 156315694325816939852743559 234473541488725409779115339)
      ·
        refine ⟨351710312233088114668673009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 234473541488725409779115339 351710312233088114668673009)
        ·
          refine ⟨263782734174816086001504757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 351710312233088114668673009 263782734174816086001504757)
          ·
            refine ⟨24729631328889008062641071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 263782734174816086001504757 24729631328889008062641071)
            ·
              refine ⟨37094446993333512093961607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24729631328889008062641071 37094446993333512093961607)
              ·
                refine ⟨55641670490000268140942411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37094446993333512093961607 55641670490000268140942411)
                ·
                  refine ⟨83462505735000402211413617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 55641670490000268140942411 83462505735000402211413617)
                  ·
                    refine ⟨62596879301250301658560213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 83462505735000402211413617 62596879301250301658560213)
                    ·
                      refine ⟨1467114358623053945122505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 62596879301250301658560213 1467114358623053945122505)
                      ·
                        rfl

theorem cell23_2857195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 1, 1, 1, 2, 7].length) (baseStart_2857195 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2857195 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2857195 prefixEnd_2857195 := by exact prefixLift 2857195
  have htrace : WordTrace (prefixWord ++ tailWord_2857195) baseStart_2857195 baseEnd_2857195 := by
    simpa [prefixWord, tailWord_2857195, baseEnd_2857195] using wordTrace_append hprefix tailTrace_2857195
  have hstable : (prefixWord ++ tailWord_2857195).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2857195).length < 2 ^ (prefixWord ++ tailWord_2857195).sum := by decide
  have hdescent : baseEnd_2857195 < baseStart_2857195 := by decide
  rcases family_descends (prefixWord ++ tailWord_2857195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2857196 : List Nat := [2, 2, 1, 1, 2, 3, 2, 4, 2, 2, 2]
def baseStart_2857196 : Nat := 118140960795 + 2857196 * 2 ^ 59
def prefixEnd_2857196 : Nat := 4983230072969 + 3 ^ 40 * 2857196 * 2
def baseEnd_2857196 : Nat := 1467114872103708441210001

theorem tailTrace_2857196 : CollatzResearch.WordTrace tailWord_2857196 prefixEnd_2857196 1467114872103708441210001 := by
  unfold tailWord_2857196
  simp only [CollatzResearch.WordTrace]
  refine ⟨52105249678437168536307721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69473666237916224715076961 52105249678437168536307721)
  ·
    refine ⟨39078937258827876402230791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52105249678437168536307721 39078937258827876402230791)
    ·
      refine ⟨58618405888241814603346187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39078937258827876402230791 58618405888241814603346187)
      ·
        refine ⟨87927608832362721905019281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 58618405888241814603346187 87927608832362721905019281)
        ·
          refine ⟨65945706624272041428764461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 87927608832362721905019281 65945706624272041428764461)
          ·
            refine ⟨24729639984102015535786673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 65945706624272041428764461 24729639984102015535786673)
            ·
              refine ⟨18547229988076511651840005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24729639984102015535786673 18547229988076511651840005)
              ·
                refine ⟨3477605622764345934720001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18547229988076511651840005 3477605622764345934720001)
                ·
                  refine ⟨2608204217073259451040001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3477605622764345934720001 2608204217073259451040001)
                  ·
                    refine ⟨1956153162804944588280001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2608204217073259451040001 1956153162804944588280001)
                    ·
                      refine ⟨1467114872103708441210001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1956153162804944588280001 1467114872103708441210001)
                      ·
                        rfl

theorem cell23_2857196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 2, 2, 2].length) (baseStart_2857196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2857196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2857196 prefixEnd_2857196 := by exact prefixLift 2857196
  have htrace : WordTrace (prefixWord ++ tailWord_2857196) baseStart_2857196 baseEnd_2857196 := by
    simpa [prefixWord, tailWord_2857196, baseEnd_2857196] using wordTrace_append hprefix tailTrace_2857196
  have hstable : (prefixWord ++ tailWord_2857196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2857196).length < 2 ^ (prefixWord ++ tailWord_2857196).sum := by decide
  have hdescent : baseEnd_2857196 < baseStart_2857196 := by decide
  rcases family_descends (prefixWord ++ tailWord_2857196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2857253 : List Nat := [1, 3, 1, 2, 5, 2, 2, 2, 5]
def baseStart_2857253 : Nat := 118140960795 + 2857253 * 2 ^ 59
def prefixEnd_2857253 : Nat := 4983230072969 + 3 ^ 40 * 2857253 * 2
def baseEnd_2857253 : Nat := 163016015611223857577471

theorem tailTrace_2857253 : CollatzResearch.WordTrace tailWord_2857253 prefixEnd_2857253 163016015611223857577471 := by
  unfold tailWord_2857253
  simp only [CollatzResearch.WordTrace]
  refine ⟨104212578317667835807440413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69475052211778557204960275 104212578317667835807440413)
  ·
    refine ⟨39079716869125438427790155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 104212578317667835807440413 39079716869125438427790155)
    ·
      refine ⟨58619575303688157641685233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39079716869125438427790155 58619575303688157641685233)
      ·
        refine ⟨43964681477766118231263925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 58619575303688157641685233 43964681477766118231263925)
        ·
          refine ⟨4121688888540573584180993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 43964681477766118231263925 4121688888540573584180993)
          ·
            refine ⟨3091266666405430188135745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4121688888540573584180993 3091266666405430188135745)
            ·
              refine ⟨2318449999804072641101809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3091266666405430188135745 2318449999804072641101809)
              ·
                refine ⟨1738837499853054480826357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2318449999804072641101809 1738837499853054480826357)
                ·
                  refine ⟨163016015611223857577471, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1738837499853054480826357 163016015611223857577471)
                  ·
                    rfl

theorem cell23_2857253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 2, 2, 2, 5].length) (baseStart_2857253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2857253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2857253 prefixEnd_2857253 := by exact prefixLift 2857253
  have htrace : WordTrace (prefixWord ++ tailWord_2857253) baseStart_2857253 baseEnd_2857253 := by
    simpa [prefixWord, tailWord_2857253, baseEnd_2857253] using wordTrace_append hprefix tailTrace_2857253
  have hstable : (prefixWord ++ tailWord_2857253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2857253).length < 2 ^ (prefixWord ++ tailWord_2857253).sum := by decide
  have hdescent : baseEnd_2857253 < baseStart_2857253 := by decide
  rcases family_descends (prefixWord ++ tailWord_2857253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2857279 : List Nat := [1, 1, 2, 2, 4, 1, 3, 2, 3, 4]
def baseStart_2857279 : Nat := 118140960795 + 2857279 * 2 ^ 59
def prefixEnd_2857279 : Nat := 4983230072969 + 3 ^ 40 * 2857279 * 2
def baseEnd_2857279 : Nat := 489052496999343872157373

theorem tailTrace_2857279 : CollatzResearch.WordTrace tailWord_2857279 prefixEnd_2857279 489052496999343872157373 := by
  unfold tailWord_2857279
  simp only [CollatzResearch.WordTrace]
  refine ⟨104213526615573642247886891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 69475684410382428165257927 104213526615573642247886891)
  ·
    refine ⟨156320289923360463371830337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 104213526615573642247886891 156320289923360463371830337)
    ·
      refine ⟨117240217442520347528872753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 156320289923360463371830337 117240217442520347528872753)
      ·
        refine ⟨87930163081890260646654565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 117240217442520347528872753 87930163081890260646654565)
        ·
          refine ⟨16486905577854423871247731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 87930163081890260646654565 16486905577854423871247731)
          ·
            refine ⟨24730358366781635806871597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16486905577854423871247731 24730358366781635806871597)
            ·
              refine ⟨9273884387543113427576849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24730358366781635806871597 9273884387543113427576849)
              ·
                refine ⟨6955413290657335070682637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9273884387543113427576849 6955413290657335070682637)
                ·
                  refine ⟨2608279983996500651505989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6955413290657335070682637 2608279983996500651505989)
                  ·
                    refine ⟨489052496999343872157373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2608279983996500651505989 489052496999343872157373)
                    ·
                      rfl

theorem cell23_2857279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 3, 2, 3, 4].length) (baseStart_2857279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2857279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2857279 prefixEnd_2857279 := by exact prefixLift 2857279
  have htrace : WordTrace (prefixWord ++ tailWord_2857279) baseStart_2857279 baseEnd_2857279 := by
    simpa [prefixWord, tailWord_2857279, baseEnd_2857279] using wordTrace_append hprefix tailTrace_2857279
  have hstable : (prefixWord ++ tailWord_2857279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2857279).length < 2 ^ (prefixWord ++ tailWord_2857279).sum := by decide
  have hdescent : baseEnd_2857279 < baseStart_2857279 := by decide
  rcases family_descends (prefixWord ++ tailWord_2857279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2857292 : List Nat := [2, 2, 1, 3, 2, 1, 2, 2, 8]
def baseStart_2857292 : Nat := 118140960795 + 2857292 * 2 ^ 59
def prefixEnd_2857292 : Nat := 4983230072969 + 3 ^ 40 * 2857292 * 2
def baseEnd_2857292 : Nat := 163018240694060007289951

theorem tailTrace_2857292 : CollatzResearch.WordTrace tailWord_2857292 prefixEnd_2857292 163018240694060007289951 := by
  unfold tailWord_2857292
  simp only [CollatzResearch.WordTrace]
  refine ⟨52107000382263272734055065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 69476000509684363645406753 52107000382263272734055065)
  ·
    refine ⟨39080250286697454550541299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52107000382263272734055065 39080250286697454550541299)
    ·
      refine ⟨58620375430046181825811949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39080250286697454550541299 58620375430046181825811949)
      ·
        refine ⟨21982640786267318184679481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 58620375430046181825811949 21982640786267318184679481)
        ·
          refine ⟨16486980589700488638509611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21982640786267318184679481 16486980589700488638509611)
          ·
            refine ⟨24730470884550732957764417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16486980589700488638509611 24730470884550732957764417)
            ·
              refine ⟨18547853163413049718323313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24730470884550732957764417 18547853163413049718323313)
              ·
                refine ⟨13910889872559787288742485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18547853163413049718323313 13910889872559787288742485)
                ·
                  refine ⟨163018240694060007289951, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 13910889872559787288742485 163018240694060007289951)
                  ·
                    rfl

theorem cell23_2857292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 2, 2, 8].length) (baseStart_2857292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2857292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2857292 prefixEnd_2857292 := by exact prefixLift 2857292
  have htrace : WordTrace (prefixWord ++ tailWord_2857292) baseStart_2857292 baseEnd_2857292 := by
    simpa [prefixWord, tailWord_2857292, baseEnd_2857292] using wordTrace_append hprefix tailTrace_2857292
  have hstable : (prefixWord ++ tailWord_2857292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2857292).length < 2 ^ (prefixWord ++ tailWord_2857292).sum := by decide
  have hdescent : baseEnd_2857292 < baseStart_2857292 := by decide
  rcases family_descends (prefixWord ++ tailWord_2857292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
