import V185TrunkScan23Chunk0115

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_685854 : List Nat := [4, 3, 2, 2, 1, 11]
def baseStart_685854 : Nat := 118140960795 + 685854 * 2 ^ 59
def prefixEnd_685854 : Nat := 4983230072969 + 3 ^ 40 * 685854 * 2
def baseEnd_685854 : Nat := 1449270620612612455847

theorem tailTrace_685854 : CollatzResearch.WordTrace tailWord_685854 prefixEnd_685854 1449270620612612455847 := by
  unfold tailWord_685854
  simp only [CollatzResearch.WordTrace]
  refine ⟨3126893807159445922844077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 16676766971517044921835077 3126893807159445922844077)
  ·
    refine ⟨1172585177684792221066529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3126893807159445922844077 1172585177684792221066529)
    ·
      refine ⟨879438883263594165799897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1172585177684792221066529 879438883263594165799897)
      ·
        refine ⟨659579162447695624349923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 879438883263594165799897 659579162447695624349923)
        ·
          refine ⟨989368743671543436524885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 659579162447695624349923 989368743671543436524885)
          ·
            refine ⟨1449270620612612455847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 989368743671543436524885 1449270620612612455847)
            ·
              rfl

theorem cell23_685854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 11].length) (baseStart_685854 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_685854 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_685854 prefixEnd_685854 := by exact prefixLift 685854
  have htrace : WordTrace (prefixWord ++ tailWord_685854) baseStart_685854 baseEnd_685854 := by
    simpa [prefixWord, tailWord_685854, baseEnd_685854] using wordTrace_append hprefix tailTrace_685854
  have hstable : (prefixWord ++ tailWord_685854).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_685854).length < 2 ^ (prefixWord ++ tailWord_685854).sum := by decide
  have hdescent : baseEnd_685854 < baseStart_685854 := by decide
  rcases family_descends (prefixWord ++ tailWord_685854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_685874 : List Nat := [3, 2, 1, 1, 3, 2, 1, 2, 3, 3, 2]
def baseStart_685874 : Nat := 118140960795 + 685874 * 2 ^ 59
def prefixEnd_685874 : Nat := 4983230072969 + 3 ^ 40 * 685874 * 2
def baseEnd_685874 : Nat := 352183030421954748520729

theorem tailTrace_685874 : CollatzResearch.WordTrace tailWord_685874 prefixEnd_685874 352183030421954748520729 := by
  unfold tailWord_685874
  simp only [CollatzResearch.WordTrace]
  refine ⟨6253969979300777699620169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16677253278135407198987117 6253969979300777699620169)
  ·
    refine ⟨4690477484475583274715127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6253969979300777699620169 4690477484475583274715127)
    ·
      refine ⟨7035716226713374912072691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4690477484475583274715127 7035716226713374912072691)
      ·
        refine ⟨10553574340070062368109037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7035716226713374912072691 10553574340070062368109037)
        ·
          refine ⟨3957590377526273388040889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10553574340070062368109037 3957590377526273388040889)
          ·
            refine ⟨2968192783144705041030667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3957590377526273388040889 2968192783144705041030667)
            ·
              refine ⟨4452289174717057561546001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2968192783144705041030667 4452289174717057561546001)
              ·
                refine ⟨3339216881037793171159501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4452289174717057561546001 3339216881037793171159501)
                ·
                  refine ⟨1252206330389172439184813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3339216881037793171159501 1252206330389172439184813)
                  ·
                    refine ⟨469577373895939664694305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1252206330389172439184813 469577373895939664694305)
                    ·
                      refine ⟨352183030421954748520729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 469577373895939664694305 352183030421954748520729)
                      ·
                        rfl

theorem cell23_685874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 1, 2, 3, 3, 2].length) (baseStart_685874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_685874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_685874 prefixEnd_685874 := by exact prefixLift 685874
  have htrace : WordTrace (prefixWord ++ tailWord_685874) baseStart_685874 baseEnd_685874 := by
    simpa [prefixWord, tailWord_685874, baseEnd_685874] using wordTrace_append hprefix tailTrace_685874
  have hstable : (prefixWord ++ tailWord_685874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_685874).length < 2 ^ (prefixWord ++ tailWord_685874).sum := by decide
  have hdescent : baseEnd_685874 < baseStart_685874 := by decide
  rcases family_descends (prefixWord ++ tailWord_685874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_685880 : List Nat := [2, 1, 2, 1, 3, 3, 1, 1, 1, 8]
def baseStart_685880 : Nat := 118140960795 + 685880 * 2 ^ 59
def prefixEnd_685880 : Nat := 4983230072969 + 3 ^ 40 * 685880 * 2
def baseEnd_685880 : Nat := 117395370435293908348567

theorem tailTrace_685880 : CollatzResearch.WordTrace tailWord_685880 prefixEnd_685880 117395370435293908348567 := by
  unfold tailWord_685880
  simp only [CollatzResearch.WordTrace]
  refine ⟨12508049377590686911599547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16677399170120915882132729 12508049377590686911599547)
  ·
    refine ⟨18762074066386030367399321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12508049377590686911599547 18762074066386030367399321)
    ·
      refine ⟨14071555549789522775549491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18762074066386030367399321 14071555549789522775549491)
      ·
        refine ⟨21107333324684284163324237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14071555549789522775549491 21107333324684284163324237)
        ·
          refine ⟨7915249996756606561246589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21107333324684284163324237 7915249996756606561246589)
          ·
            refine ⟨2968218748783727460467471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7915249996756606561246589 2968218748783727460467471)
            ·
              refine ⟨4452328123175591190701207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2968218748783727460467471 4452328123175591190701207)
              ·
                refine ⟨6678492184763386786051811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4452328123175591190701207 6678492184763386786051811)
                ·
                  refine ⟨10017738277145080179077717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6678492184763386786051811 10017738277145080179077717)
                  ·
                    refine ⟨117395370435293908348567, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 10017738277145080179077717 117395370435293908348567)
                    ·
                      rfl

theorem cell23_685880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 1, 1, 1, 8].length) (baseStart_685880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_685880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_685880 prefixEnd_685880 := by exact prefixLift 685880
  have htrace : WordTrace (prefixWord ++ tailWord_685880) baseStart_685880 baseEnd_685880 := by
    simpa [prefixWord, tailWord_685880, baseEnd_685880] using wordTrace_append hprefix tailTrace_685880
  have hstable : (prefixWord ++ tailWord_685880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_685880).length < 2 ^ (prefixWord ++ tailWord_685880).sum := by decide
  have hdescent : baseEnd_685880 < baseStart_685880 := by decide
  rcases family_descends (prefixWord ++ tailWord_685880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_685881 : List Nat := [1, 2, 1, 7, 1, 1, 2, 1, 1, 3, 3]
def baseStart_685881 : Nat := 118140960795 + 685881 * 2 ^ 59
def prefixEnd_685881 : Nat := 4983230072969 + 3 ^ 40 * 685881 * 2
def baseEnd_685881 : Nat := 352186624786536221133197

theorem tailTrace_685881 : CollatzResearch.WordTrace tailWord_685881 prefixEnd_685881 352186624786536221133197 := by
  unfold tailWord_685881
  simp only [CollatzResearch.WordTrace]
  refine ⟨25016135228177750993985497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16677423485451833995990331 25016135228177750993985497)
  ·
    refine ⟨18762101421133313245489123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25016135228177750993985497 18762101421133313245489123)
    ·
      refine ⟨28143152131699969868233685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18762101421133313245489123 28143152131699969868233685)
      ·
        refine ⟨659605128086718043786727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 28143152131699969868233685 659605128086718043786727)
        ·
          refine ⟨989407692130077065680091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 659605128086718043786727 989407692130077065680091)
          ·
            refine ⟨1484111538195115598520137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 989407692130077065680091 1484111538195115598520137)
            ·
              refine ⟨1113083653646336698890103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1484111538195115598520137 1113083653646336698890103)
              ·
                refine ⟨1669625480469505048335155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1113083653646336698890103 1669625480469505048335155)
                ·
                  refine ⟨2504438220704257572502733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1669625480469505048335155 2504438220704257572502733)
                  ·
                    refine ⟨939164332764096589688525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2504438220704257572502733 939164332764096589688525)
                    ·
                      refine ⟨352186624786536221133197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 939164332764096589688525 352186624786536221133197)
                      ·
                        rfl

theorem cell23_685881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 1, 2, 1, 1, 3, 3].length) (baseStart_685881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_685881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_685881 prefixEnd_685881 := by exact prefixLift 685881
  have htrace : WordTrace (prefixWord ++ tailWord_685881) baseStart_685881 baseEnd_685881 := by
    simpa [prefixWord, tailWord_685881, baseEnd_685881] using wordTrace_append hprefix tailTrace_685881
  have hstable : (prefixWord ++ tailWord_685881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_685881).length < 2 ^ (prefixWord ++ tailWord_685881).sum := by decide
  have hdescent : baseEnd_685881 < baseStart_685881 := by decide
  rcases family_descends (prefixWord ++ tailWord_685881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_685904 : List Nat := [2, 1, 1, 1, 1, 4, 1, 4, 4, 2, 2]
def baseStart_685904 : Nat := 118140960795 + 685904 * 2 ^ 59
def prefixEnd_685904 : Nat := 4983230072969 + 3 ^ 40 * 685904 * 2
def baseEnd_685904 : Nat := 352198434841589631145591

theorem tailTrace_685904 : CollatzResearch.WordTrace tailWord_685904 prefixEnd_685904 352198434841589631145591 := by
  unfold tailWord_685904
  simp only [CollatzResearch.WordTrace]
  refine ⟨12508487053547212961036383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16677982738062950614715177 12508487053547212961036383)
  ·
    refine ⟨18762730580320819441554575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12508487053547212961036383 18762730580320819441554575)
    ·
      refine ⟨28144095870481229162331863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18762730580320819441554575 28144095870481229162331863)
      ·
        refine ⟨42216143805721843743497795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28144095870481229162331863 42216143805721843743497795)
        ·
          refine ⟨63324215708582765615246693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42216143805721843743497795 63324215708582765615246693)
          ·
            refine ⟨11873290445359268552858755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 63324215708582765615246693 11873290445359268552858755)
            ·
              refine ⟨17809935668038902829288133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11873290445359268552858755 17809935668038902829288133)
              ·
                refine ⟨3339362937757294280491525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17809935668038902829288133 3339362937757294280491525)
                ·
                  refine ⟨626130550829492677592161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3339362937757294280491525 626130550829492677592161)
                  ·
                    refine ⟨469597913122119508194121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 626130550829492677592161 469597913122119508194121)
                    ·
                      refine ⟨352198434841589631145591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 469597913122119508194121 352198434841589631145591)
                      ·
                        rfl

theorem cell23_685904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 4, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 4, 4, 2, 2].length) (baseStart_685904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_685904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_685904 prefixEnd_685904 := by exact prefixLift 685904
  have htrace : WordTrace (prefixWord ++ tailWord_685904) baseStart_685904 baseEnd_685904 := by
    simpa [prefixWord, tailWord_685904, baseEnd_685904] using wordTrace_append hprefix tailTrace_685904
  have hstable : (prefixWord ++ tailWord_685904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_685904).length < 2 ^ (prefixWord ++ tailWord_685904).sum := by decide
  have hdescent : baseEnd_685904 < baseStart_685904 := by decide
  rcases family_descends (prefixWord ++ tailWord_685904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_685908 : List Nat := [2, 4, 1, 1, 3, 1, 4, 1, 1, 3, 2]
def baseStart_685908 : Nat := 118140960795 + 685908 * 2 ^ 59
def prefixEnd_685908 : Nat := 4983230072969 + 3 ^ 40 * 685908 * 2
def baseEnd_685908 : Nat := 352200488764207615495573

theorem tailTrace_685908 : CollatzResearch.WordTrace tailWord_685908 prefixEnd_685908 352200488764207615495573 := by
  unfold tailWord_685908
  simp only [CollatzResearch.WordTrace]
  refine ⟨12508559999539967302609189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16678079999386623070145585 12508559999539967302609189)
  ·
    refine ⟨2345354999913743869239223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12508559999539967302609189 2345354999913743869239223)
    ·
      refine ⟨3518032499870615803858835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2345354999913743869239223 3518032499870615803858835)
      ·
        refine ⟨5277048749805923705788253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3518032499870615803858835 5277048749805923705788253)
        ·
          refine ⟨1978893281177221389670595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5277048749805923705788253 1978893281177221389670595)
          ·
            refine ⟨2968339921765832084505893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1978893281177221389670595 2968339921765832084505893)
            ·
              refine ⟨556563735331093515844855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2968339921765832084505893 556563735331093515844855)
              ·
                refine ⟨834845602996640273767283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 556563735331093515844855 834845602996640273767283)
                ·
                  refine ⟨1252268404494960410650925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 834845602996640273767283 1252268404494960410650925)
                  ·
                    refine ⟨469600651685610153994097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1252268404494960410650925 469600651685610153994097)
                    ·
                      refine ⟨352200488764207615495573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 469600651685610153994097 352200488764207615495573)
                      ·
                        rfl

theorem cell23_685908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 4, 1, 1, 3, 2].length) (baseStart_685908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_685908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_685908 prefixEnd_685908 := by exact prefixLift 685908
  have htrace : WordTrace (prefixWord ++ tailWord_685908) baseStart_685908 baseEnd_685908 := by
    simpa [prefixWord, tailWord_685908, baseEnd_685908] using wordTrace_append hprefix tailTrace_685908
  have hstable : (prefixWord ++ tailWord_685908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_685908).length < 2 ^ (prefixWord ++ tailWord_685908).sum := by decide
  have hdescent : baseEnd_685908 < baseStart_685908 := by decide
  rcases family_descends (prefixWord ++ tailWord_685908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_685927 : List Nat := [1, 1, 5, 1, 2, 1, 4, 1, 7]
def baseStart_685927 : Nat := 118140960795 + 685927 * 2 ^ 59
def prefixEnd_685927 : Nat := 4983230072969 + 3 ^ 40 * 685927 * 2
def baseEnd_685927 : Nat := 39134471655182560128665

theorem tailTrace_685927 : CollatzResearch.WordTrace tailWord_685927 prefixEnd_685927 39134471655182560128665 := by
  unfold tailWord_685927
  simp only [CollatzResearch.WordTrace]
  refine ⟨25017812986011100850160035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16678541990674067233440023 25017812986011100850160035)
  ·
    refine ⟨37526719479016651275240053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25017812986011100850160035 37526719479016651275240053)
    ·
      refine ⟨3518129951157811057053755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 37526719479016651275240053 3518129951157811057053755)
      ·
        refine ⟨5277194926736716585580633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3518129951157811057053755 5277194926736716585580633)
        ·
          refine ⟨3957896195052537439185475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5277194926736716585580633 3957896195052537439185475)
          ·
            refine ⟨5936844292578806158778213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3957896195052537439185475 5936844292578806158778213)
            ·
              refine ⟨1113158304858526154770915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5936844292578806158778213 1113158304858526154770915)
              ·
                refine ⟨1669737457287789232156373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1113158304858526154770915 1669737457287789232156373)
                ·
                  refine ⟨39134471655182560128665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1669737457287789232156373 39134471655182560128665)
                  ·
                    rfl

theorem cell23_685927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 4, 1, 7].length) (baseStart_685927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_685927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_685927 prefixEnd_685927 := by exact prefixLift 685927
  have htrace : WordTrace (prefixWord ++ tailWord_685927) baseStart_685927 baseEnd_685927 := by
    simpa [prefixWord, tailWord_685927, baseEnd_685927] using wordTrace_append hprefix tailTrace_685927
  have hstable : (prefixWord ++ tailWord_685927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_685927).length < 2 ^ (prefixWord ++ tailWord_685927).sum := by decide
  have hdescent : baseEnd_685927 < baseStart_685927 := by decide
  rcases family_descends (prefixWord ++ tailWord_685927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_685934 : List Nat := [4, 1, 2, 3, 1, 1, 2, 1, 2, 2, 4]
def baseStart_685934 : Nat := 118140960795 + 685934 * 2 ^ 59
def prefixEnd_685934 : Nat := 4983230072969 + 3 ^ 40 * 685934 * 2
def baseEnd_685934 : Nat := 352213839261224513770453

theorem tailTrace_685934 : CollatzResearch.WordTrace tailWord_685934 prefixEnd_685934 352213839261224513770453 := by
  unfold tailWord_685934
  simp only [CollatzResearch.WordTrace]
  refine ⟨3127258537123217630708107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 16678712197990494030443237 3127258537123217630708107)
  ·
    refine ⟨4690887805684826446062161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3127258537123217630708107 4690887805684826446062161)
    ·
      refine ⟨3518165854263619834546621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4690887805684826446062161 3518165854263619834546621)
      ·
        refine ⟨1319312195348857437954983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3518165854263619834546621 1319312195348857437954983)
        ·
          refine ⟨1978968293023286156932475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1319312195348857437954983 1978968293023286156932475)
          ·
            refine ⟨2968452439534929235398713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1978968293023286156932475 2968452439534929235398713)
            ·
              refine ⟨2226339329651196926549035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2968452439534929235398713 2226339329651196926549035)
              ·
                refine ⟨3339508994476795389823553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2226339329651196926549035 3339508994476795389823553)
                ·
                  refine ⟨2504631745857596542367665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3339508994476795389823553 2504631745857596542367665)
                  ·
                    refine ⟨1878473809393197406775749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2504631745857596542367665 1878473809393197406775749)
                    ·
                      refine ⟨352213839261224513770453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1878473809393197406775749 352213839261224513770453)
                      ·
                        rfl

theorem cell23_685934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 2, 1, 2, 2, 4].length) (baseStart_685934 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_685934 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_685934 prefixEnd_685934 := by exact prefixLift 685934
  have htrace : WordTrace (prefixWord ++ tailWord_685934) baseStart_685934 baseEnd_685934 := by
    simpa [prefixWord, tailWord_685934, baseEnd_685934] using wordTrace_append hprefix tailTrace_685934
  have hstable : (prefixWord ++ tailWord_685934).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_685934).length < 2 ^ (prefixWord ++ tailWord_685934).sum := by decide
  have hdescent : baseEnd_685934 < baseStart_685934 := by decide
  rcases family_descends (prefixWord ++ tailWord_685934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_685937 : List Nat := [1, 2, 2, 2, 1, 3, 1, 3, 2, 3, 3]
def baseStart_685937 : Nat := 118140960795 + 685937 * 2 ^ 59
def prefixEnd_685937 : Nat := 4983230072969 + 3 ^ 40 * 685937 * 2
def baseEnd_685937 : Nat := 352215379703188002032939

theorem tailTrace_685937 : CollatzResearch.WordTrace tailWord_685937 prefixEnd_685937 352215379703188002032939 := by
  unfold tailWord_685937
  simp only [CollatzResearch.WordTrace]
  refine ⟨25018177715974872558024065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16678785143983248372016043 25018177715974872558024065)
  ·
    refine ⟨18763633286981154418518049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25018177715974872558024065 18763633286981154418518049)
    ·
      refine ⟨14072724965235865813888537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18763633286981154418518049 14072724965235865813888537)
      ·
        refine ⟨10554543723926899360416403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14072724965235865813888537 10554543723926899360416403)
        ·
          refine ⟨15831815585890349040624605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10554543723926899360416403 15831815585890349040624605)
          ·
            refine ⟨5936930844708880890234227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15831815585890349040624605 5936930844708880890234227)
            ·
              refine ⟨8905396267063321335351341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5936930844708880890234227 8905396267063321335351341)
              ·
                refine ⟨3339523600148745500756753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8905396267063321335351341 3339523600148745500756753)
                ·
                  refine ⟨2504642700111559125567565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3339523600148745500756753 2504642700111559125567565)
                  ·
                    refine ⟨939241012541834672087837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2504642700111559125567565 939241012541834672087837)
                    ·
                      refine ⟨352215379703188002032939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 939241012541834672087837 352215379703188002032939)
                      ·
                        rfl

theorem cell23_685937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 1, 3, 2, 3, 3].length) (baseStart_685937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_685937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_685937 prefixEnd_685937 := by exact prefixLift 685937
  have htrace : WordTrace (prefixWord ++ tailWord_685937) baseStart_685937 baseEnd_685937 := by
    simpa [prefixWord, tailWord_685937, baseEnd_685937] using wordTrace_append hprefix tailTrace_685937
  have hstable : (prefixWord ++ tailWord_685937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_685937).length < 2 ^ (prefixWord ++ tailWord_685937).sum := by decide
  have hdescent : baseEnd_685937 < baseStart_685937 := by decide
  rcases family_descends (prefixWord ++ tailWord_685937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_685957 : List Nat := [1, 3, 1, 1, 3, 2, 2, 3, 2, 5]
def baseStart_685957 : Nat := 118140960795 + 685957 * 2 ^ 59
def prefixEnd_685957 : Nat := 4983230072969 + 3 ^ 40 * 685957 * 2
def baseEnd_685957 : Nat := 117408549772092641260949

theorem tailTrace_685957 : CollatzResearch.WordTrace tailWord_685957 prefixEnd_685957 117408549772092641260949 := by
  unfold tailWord_685957
  simp only [CollatzResearch.WordTrace]
  refine ⟨25018907175902415973752125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16679271450601610649168083 25018907175902415973752125)
  ·
    refine ⟨9382090190963405990157047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25018907175902415973752125 9382090190963405990157047)
    ·
      refine ⟨14073135286445108985235571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9382090190963405990157047 14073135286445108985235571)
      ·
        refine ⟨21109702929667663477853357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14073135286445108985235571 21109702929667663477853357)
        ·
          refine ⟨7916138598625373804195009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21109702929667663477853357 7916138598625373804195009)
          ·
            refine ⟨5937103948969030353146257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7916138598625373804195009 5937103948969030353146257)
            ·
              refine ⟨4452827961726772764859693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5937103948969030353146257 4452827961726772764859693)
              ·
                refine ⟨1669810485647539786822385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4452827961726772764859693 1669810485647539786822385)
                ·
                  refine ⟨1252357864235654840116789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1669810485647539786822385 1252357864235654840116789)
                  ·
                    refine ⟨117408549772092641260949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1252357864235654840116789 117408549772092641260949)
                    ·
                      rfl

theorem cell23_685957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 2, 3, 2, 5].length) (baseStart_685957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_685957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_685957 prefixEnd_685957 := by exact prefixLift 685957
  have htrace : WordTrace (prefixWord ++ tailWord_685957) baseStart_685957 baseEnd_685957 := by
    simpa [prefixWord, tailWord_685957, baseEnd_685957] using wordTrace_append hprefix tailTrace_685957
  have hstable : (prefixWord ++ tailWord_685957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_685957).length < 2 ^ (prefixWord ++ tailWord_685957).sum := by decide
  have hdescent : baseEnd_685957 < baseStart_685957 := by decide
  rcases family_descends (prefixWord ++ tailWord_685957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_685977 : List Nat := [1, 2, 1, 2, 1, 3, 3, 1, 4, 1, 4]
def baseStart_685977 : Nat := 118140960795 + 685977 * 2 ^ 59
def prefixEnd_685977 : Nat := 4983230072969 + 3 ^ 40 * 685977 * 2
def baseEnd_685977 : Nat := 352235918929367845532755

theorem tailTrace_685977 : CollatzResearch.WordTrace tailWord_685977 prefixEnd_685977 352235918929367845532755 := by
  unfold tailWord_685977
  simp only [CollatzResearch.WordTrace]
  refine ⟨25019636635829959389480185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16679757757219972926320123 25019636635829959389480185)
  ·
    refine ⟨18764727476872469542110139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25019636635829959389480185 18764727476872469542110139)
    ·
      refine ⟨28147091215308704313165209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18764727476872469542110139 28147091215308704313165209)
      ·
        refine ⟨21110318411481528234873907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28147091215308704313165209 21110318411481528234873907)
        ·
          refine ⟨31665477617222292352310861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21110318411481528234873907 31665477617222292352310861)
          ·
            refine ⟨11874554106458359632116573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31665477617222292352310861 11874554106458359632116573)
            ·
              refine ⟨4452957789921884862043715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11874554106458359632116573 4452957789921884862043715)
              ·
                refine ⟨6679436684882827293065573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4452957789921884862043715 6679436684882827293065573)
                ·
                  refine ⟨1252394378415530117449795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6679436684882827293065573 1252394378415530117449795)
                  ·
                    refine ⟨1878591567623295176174693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1252394378415530117449795 1878591567623295176174693)
                    ·
                      refine ⟨352235918929367845532755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1878591567623295176174693 352235918929367845532755)
                      ·
                        rfl

theorem cell23_685977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 3, 1, 4, 1, 4].length) (baseStart_685977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_685977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_685977 prefixEnd_685977 := by exact prefixLift 685977
  have htrace : WordTrace (prefixWord ++ tailWord_685977) baseStart_685977 baseEnd_685977 := by
    simpa [prefixWord, tailWord_685977, baseEnd_685977] using wordTrace_append hprefix tailTrace_685977
  have hstable : (prefixWord ++ tailWord_685977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_685977).length < 2 ^ (prefixWord ++ tailWord_685977).sum := by decide
  have hdescent : baseEnd_685977 < baseStart_685977 := by decide
  rcases family_descends (prefixWord ++ tailWord_685977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_686097 : List Nat := [1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 4]
def baseStart_686097 : Nat := 118140960795 + 686097 * 2 ^ 59
def prefixEnd_686097 : Nat := 4983230072969 + 3 ^ 40 * 686097 * 2
def baseEnd_686097 : Nat := 352297536607907376032203

theorem tailTrace_686097 : CollatzResearch.WordTrace tailWord_686097 prefixEnd_686097 352297536607907376032203 := by
  unfold tailWord_686097
  simp only [CollatzResearch.WordTrace]
  refine ⟨25024013395395219883848545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16682675596930146589232363 25024013395395219883848545)
  ·
    refine ⟨18768010046546414912886409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25024013395395219883848545 18768010046546414912886409)
    ·
      refine ⟨14076007534909811184664807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18768010046546414912886409 14076007534909811184664807)
      ·
        refine ⟨21114011302364716776997211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14076007534909811184664807 21114011302364716776997211)
        ·
          refine ⟨31671016953547075165495817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21114011302364716776997211 31671016953547075165495817)
          ·
            refine ⟨23753262715160306374121863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31671016953547075165495817 23753262715160306374121863)
            ·
              refine ⟨35629894072740459561182795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23753262715160306374121863 35629894072740459561182795)
              ·
                refine ⟨53444841109110689341774193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35629894072740459561182795 53444841109110689341774193)
                ·
                  refine ⟨40083630831833017006330645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 53444841109110689341774193 40083630831833017006330645)
                  ·
                    refine ⟨1878920195242172672171749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 40083630831833017006330645 1878920195242172672171749)
                    ·
                      refine ⟨352297536607907376032203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1878920195242172672171749 352297536607907376032203)
                      ·
                        rfl

theorem cell23_686097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 4].length) (baseStart_686097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_686097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_686097 prefixEnd_686097 := by exact prefixLift 686097
  have htrace : WordTrace (prefixWord ++ tailWord_686097) baseStart_686097 baseEnd_686097 := by
    simpa [prefixWord, tailWord_686097, baseEnd_686097] using wordTrace_append hprefix tailTrace_686097
  have hstable : (prefixWord ++ tailWord_686097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_686097).length < 2 ^ (prefixWord ++ tailWord_686097).sum := by decide
  have hdescent : baseEnd_686097 < baseStart_686097 := by decide
  rcases family_descends (prefixWord ++ tailWord_686097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_686104 : List Nat := [2, 1, 2, 3, 2, 1, 3, 2, 1, 1, 5]
def baseStart_686104 : Nat := 118140960795 + 686104 * 2 ^ 59
def prefixEnd_686104 : Nat := 4983230072969 + 3 ^ 40 * 686104 * 2
def baseEnd_686104 : Nat := 352301130972488848644671

theorem tailTrace_686104 : CollatzResearch.WordTrace tailWord_686104 prefixEnd_686104 352301130972488848644671 := by
  unfold tailWord_686104
  simp only [CollatzResearch.WordTrace]
  refine ⟨12512134353184930039676683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16682845804246573386235577 12512134353184930039676683)
  ·
    refine ⟨18768201529777395059515025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12512134353184930039676683 18768201529777395059515025)
    ·
      refine ⟨14076151147333046294636269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18768201529777395059515025 14076151147333046294636269)
      ·
        refine ⟨5278556680249892360488601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14076151147333046294636269 5278556680249892360488601)
        ·
          refine ⟨3958917510187419270366451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5278556680249892360488601 3958917510187419270366451)
          ·
            refine ⟨5938376265281128905549677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3958917510187419270366451 5938376265281128905549677)
            ·
              refine ⟨2226891099480423339581129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5938376265281128905549677 2226891099480423339581129)
              ·
                refine ⟨1670168324610317504685847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2226891099480423339581129 1670168324610317504685847)
                ·
                  refine ⟨2505252486915476257028771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1670168324610317504685847 2505252486915476257028771)
                  ·
                    refine ⟨3757878730373214385543157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2505252486915476257028771 3757878730373214385543157)
                    ·
                      refine ⟨352301130972488848644671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3757878730373214385543157 352301130972488848644671)
                      ·
                        rfl

theorem cell23_686104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 3, 2, 1, 1, 5].length) (baseStart_686104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_686104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_686104 prefixEnd_686104 := by exact prefixLift 686104
  have htrace : WordTrace (prefixWord ++ tailWord_686104) baseStart_686104 baseEnd_686104 := by
    simpa [prefixWord, tailWord_686104, baseEnd_686104] using wordTrace_append hprefix tailTrace_686104
  have hstable : (prefixWord ++ tailWord_686104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_686104).length < 2 ^ (prefixWord ++ tailWord_686104).sum := by decide
  have hdescent : baseEnd_686104 < baseStart_686104 := by decide
  rcases family_descends (prefixWord ++ tailWord_686104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_686114 : List Nat := [3, 3, 1, 1, 1, 2, 3, 1, 1, 1, 6]
def baseStart_686114 : Nat := 118140960795 + 686114 * 2 ^ 59
def prefixEnd_686114 : Nat := 4983230072969 + 3 ^ 40 * 686114 * 2
def baseEnd_686114 : Nat := 352306265779033809519625

theorem tailTrace_686114 : CollatzResearch.WordTrace tailWord_686114 prefixEnd_686114 352306265779033809519625 := by
  unfold tailWord_686114
  simp only [CollatzResearch.WordTrace]
  refine ⟨6256158359083407946804349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16683088957555754524811597 6256158359083407946804349)
  ·
    refine ⟨2346059384656277980051631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6256158359083407946804349 2346059384656277980051631)
    ·
      refine ⟨3519089076984416970077447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2346059384656277980051631 3519089076984416970077447)
      ·
        refine ⟨5278633615476625455116171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3519089076984416970077447 5278633615476625455116171)
        ·
          refine ⟨7917950423214938182674257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5278633615476625455116171 7917950423214938182674257)
          ·
            refine ⟨5938462817411203637005693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7917950423214938182674257 5938462817411203637005693)
            ·
              refine ⟨2226923556529201363877135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5938462817411203637005693 2226923556529201363877135)
              ·
                refine ⟨3340385334793802045815703, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2226923556529201363877135 3340385334793802045815703)
                ·
                  refine ⟨5010578002190703068723555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3340385334793802045815703 5010578002190703068723555)
                  ·
                    refine ⟨7515867003286054603085333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5010578002190703068723555 7515867003286054603085333)
                    ·
                      refine ⟨352306265779033809519625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 7515867003286054603085333 352306265779033809519625)
                      ·
                        rfl

theorem cell23_686114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 3, 1, 1, 1, 6].length) (baseStart_686114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_686114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_686114 prefixEnd_686114 := by exact prefixLift 686114
  have htrace : WordTrace (prefixWord ++ tailWord_686114) baseStart_686114 baseEnd_686114 := by
    simpa [prefixWord, tailWord_686114, baseEnd_686114] using wordTrace_append hprefix tailTrace_686114
  have hstable : (prefixWord ++ tailWord_686114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_686114).length < 2 ^ (prefixWord ++ tailWord_686114).sum := by decide
  have hdescent : baseEnd_686114 < baseStart_686114 := by decide
  rcases family_descends (prefixWord ++ tailWord_686114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_686135 : List Nat := [1, 1, 3, 1, 2, 2, 5, 3, 1, 2, 2]
def baseStart_686135 : Nat := 118140960795 + 686135 * 2 ^ 59
def prefixEnd_686135 : Nat := 4983230072969 + 3 ^ 40 * 686135 * 2
def baseEnd_686135 : Nat := 352317048872778227357029

theorem tailTrace_686135 : CollatzResearch.WordTrace tailWord_686135 prefixEnd_686135 352317048872778227357029 := by
  unfold tailWord_686135
  simp only [CollatzResearch.WordTrace]
  refine ⟨25025399369257552373731859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16683599579505034915821239 25025399369257552373731859)
  ·
    refine ⟨37538099053886328560597789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25025399369257552373731859 37538099053886328560597789)
    ·
      refine ⟨14076787145207373210224171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37538099053886328560597789 14076787145207373210224171)
      ·
        refine ⟨21115180717811059815336257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14076787145207373210224171 21115180717811059815336257)
        ·
          refine ⟨15836385538358294861502193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21115180717811059815336257 15836385538358294861502193)
          ·
            refine ⟨11877289153768721146126645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15836385538358294861502193 11877289153768721146126645)
            ·
              refine ⟨1113495858165817607449373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 11877289153768721146126645 1113495858165817607449373)
              ·
                refine ⟨417560946812181602793515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1113495858165817607449373 417560946812181602793515)
                ·
                  refine ⟨626341420218272404190273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 417560946812181602793515 626341420218272404190273)
                  ·
                    refine ⟨469756065163704303142705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 626341420218272404190273 469756065163704303142705)
                    ·
                      refine ⟨352317048872778227357029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 469756065163704303142705 352317048872778227357029)
                      ·
                        rfl

theorem cell23_686135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 5, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 5, 3, 1, 2, 2].length) (baseStart_686135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_686135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_686135 prefixEnd_686135 := by exact prefixLift 686135
  have htrace : WordTrace (prefixWord ++ tailWord_686135) baseStart_686135 baseEnd_686135 := by
    simpa [prefixWord, tailWord_686135, baseEnd_686135] using wordTrace_append hprefix tailTrace_686135
  have hstable : (prefixWord ++ tailWord_686135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_686135).length < 2 ^ (prefixWord ++ tailWord_686135).sum := by decide
  have hdescent : baseEnd_686135 < baseStart_686135 := by decide
  rcases family_descends (prefixWord ++ tailWord_686135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_686151 : List Nat := [1, 1, 4, 1, 3, 1, 1, 3, 4, 1, 3]
def baseStart_686151 : Nat := 118140960795 + 686151 * 2 ^ 59
def prefixEnd_686151 : Nat := 4983230072969 + 3 ^ 40 * 686151 * 2
def baseEnd_686151 : Nat := 352325264563250164756955

theorem tailTrace_686151 : CollatzResearch.WordTrace tailWord_686151 prefixEnd_686151 352325264563250164756955 := by
  unfold tailWord_686151
  simp only [CollatzResearch.WordTrace]
  refine ⟨25025982937199587106314307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16683988624799724737542871 25025982937199587106314307)
  ·
    refine ⟨37538974405799380659471461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25025982937199587106314307 37538974405799380659471461)
    ·
      refine ⟨7038557701087383873650899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 37538974405799380659471461 7038557701087383873650899)
      ·
        refine ⟨10557836551631075810476349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7038557701087383873650899 10557836551631075810476349)
        ·
          refine ⟨3959188706861653428928631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10557836551631075810476349 3959188706861653428928631)
          ·
            refine ⟨5938783060292480143392947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3959188706861653428928631 5938783060292480143392947)
            ·
              refine ⟨8908174590438720215089421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5938783060292480143392947 8908174590438720215089421)
              ·
                refine ⟨3340565471414520080658533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8908174590438720215089421 3340565471414520080658533)
                ·
                  refine ⟨626356025890222515123475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3340565471414520080658533 626356025890222515123475)
                  ·
                    refine ⟨939534038835333772685213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 626356025890222515123475 939534038835333772685213)
                    ·
                      refine ⟨352325264563250164756955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 939534038835333772685213 352325264563250164756955)
                      ·
                        rfl

theorem cell23_686151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 1, 3, 4, 1, 3].length) (baseStart_686151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_686151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_686151 prefixEnd_686151 := by exact prefixLift 686151
  have htrace : WordTrace (prefixWord ++ tailWord_686151) baseStart_686151 baseEnd_686151 := by
    simpa [prefixWord, tailWord_686151, baseEnd_686151] using wordTrace_append hprefix tailTrace_686151
  have hstable : (prefixWord ++ tailWord_686151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_686151).length < 2 ^ (prefixWord ++ tailWord_686151).sum := by decide
  have hdescent : baseEnd_686151 < baseStart_686151 := by decide
  rcases family_descends (prefixWord ++ tailWord_686151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_686161 : List Nat := [1, 2, 2, 1, 3, 1, 1, 4, 3, 3, 2]
def baseStart_686161 : Nat := 118140960795 + 686161 * 2 ^ 59
def prefixEnd_686161 : Nat := 4983230072969 + 3 ^ 40 * 686161 * 2
def baseEnd_686161 : Nat := 352330399369795125631909

theorem tailTrace_686161 : CollatzResearch.WordTrace tailWord_686161 prefixEnd_686161 352330399369795125631909 := by
  unfold tailWord_686161
  simp only [CollatzResearch.WordTrace]
  refine ⟨25026347667163358814178337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16684231778108905876118891 25026347667163358814178337)
  ·
    refine ⟨18769760750372519110633753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25026347667163358814178337 18769760750372519110633753)
    ·
      refine ⟨14077320562779389332975315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18769760750372519110633753 14077320562779389332975315)
      ·
        refine ⟨21115980844169083999462973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14077320562779389332975315 21115980844169083999462973)
        ·
          refine ⟨7918492816563406499798615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21115980844169083999462973 7918492816563406499798615)
          ·
            refine ⟨11877739224845109749697923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7918492816563406499798615 11877739224845109749697923)
            ·
              refine ⟨17816608837267664624546885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11877739224845109749697923 17816608837267664624546885)
              ·
                refine ⟨3340614156987687117102541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17816608837267664624546885 3340614156987687117102541)
                ·
                  refine ⟨1252730308870382668913453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3340614156987687117102541 1252730308870382668913453)
                  ·
                    refine ⟨469773865826393500842545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1252730308870382668913453 469773865826393500842545)
                    ·
                      refine ⟨352330399369795125631909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 469773865826393500842545 352330399369795125631909)
                      ·
                        rfl

theorem cell23_686161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 4, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 4, 3, 3, 2].length) (baseStart_686161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_686161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_686161 prefixEnd_686161 := by exact prefixLift 686161
  have htrace : WordTrace (prefixWord ++ tailWord_686161) baseStart_686161 baseEnd_686161 := by
    simpa [prefixWord, tailWord_686161, baseEnd_686161] using wordTrace_append hprefix tailTrace_686161
  have hstable : (prefixWord ++ tailWord_686161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_686161).length < 2 ^ (prefixWord ++ tailWord_686161).sum := by decide
  have hdescent : baseEnd_686161 < baseStart_686161 := by decide
  rcases family_descends (prefixWord ++ tailWord_686161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_686162 : List Nat := [3, 2, 2, 1, 5, 1, 2, 1, 2, 4]
def baseStart_686162 : Nat := 118140960795 + 686162 * 2 ^ 59
def prefixEnd_686162 : Nat := 4983230072969 + 3 ^ 40 * 686162 * 2
def baseEnd_686162 : Nat := 117443637616816540573135

theorem tailTrace_686162 : CollatzResearch.WordTrace tailWord_686162 prefixEnd_686162 117443637616816540573135 := by
  unfold tailWord_686162
  simp only [CollatzResearch.WordTrace]
  refine ⟨6256596035039933996241185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16684256093439823989976493 6256596035039933996241185)
  ·
    refine ⟨4692447026279950497180889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6256596035039933996241185 4692447026279950497180889)
    ·
      refine ⟨3519335269709962872885667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4692447026279950497180889 3519335269709962872885667)
      ·
        refine ⟨5279002904564944309328501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3519335269709962872885667 5279002904564944309328501)
        ·
          refine ⟨494906522302963528999547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 5279002904564944309328501 494906522302963528999547)
          ·
            refine ⟨742359783454445293499321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 494906522302963528999547 742359783454445293499321)
            ·
              refine ⟨556769837590833970124491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 742359783454445293499321 556769837590833970124491)
              ·
                refine ⟨835154756386250955186737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 556769837590833970124491 835154756386250955186737)
                ·
                  refine ⟨626366067289688216390053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 835154756386250955186737 626366067289688216390053)
                  ·
                    refine ⟨117443637616816540573135, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 626366067289688216390053 117443637616816540573135)
                    ·
                      rfl

theorem cell23_686162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 5, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 5, 1, 2, 1, 2, 4].length) (baseStart_686162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_686162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_686162 prefixEnd_686162 := by exact prefixLift 686162
  have htrace : WordTrace (prefixWord ++ tailWord_686162) baseStart_686162 baseEnd_686162 := by
    simpa [prefixWord, tailWord_686162, baseEnd_686162] using wordTrace_append hprefix tailTrace_686162
  have hstable : (prefixWord ++ tailWord_686162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_686162).length < 2 ^ (prefixWord ++ tailWord_686162).sum := by decide
  have hdescent : baseEnd_686162 < baseStart_686162 := by decide
  rcases family_descends (prefixWord ++ tailWord_686162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_686168 : List Nat := [2, 1, 2, 2, 1, 5, 1, 3, 2, 1, 3]
def baseStart_686168 : Nat := 118140960795 + 686168 * 2 ^ 59
def prefixEnd_686168 : Nat := 4983230072969 + 3 ^ 40 * 686168 * 2
def baseEnd_686168 : Nat := 352333993734376598244377

theorem tailTrace_686168 : CollatzResearch.WordTrace tailWord_686168 prefixEnd_686168 352333993734376598244377 := by
  unfold tailWord_686168
  simp only [CollatzResearch.WordTrace]
  refine ⟨12513301489068999504841579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16684401985425332673122105 12513301489068999504841579)
  ·
    refine ⟨18769952233603499257262369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12513301489068999504841579 18769952233603499257262369)
    ·
      refine ⟨14077464175202624442946777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18769952233603499257262369 14077464175202624442946777)
      ·
        refine ⟨10558098131401968332210083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14077464175202624442946777 10558098131401968332210083)
        ·
          refine ⟨15837147197102952498315125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10558098131401968332210083 15837147197102952498315125)
          ·
            refine ⟨1484732549728401796717043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 15837147197102952498315125 1484732549728401796717043)
            ·
              refine ⟨2227098824592602695075565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1484732549728401796717043 2227098824592602695075565)
              ·
                refine ⟨835162059222226010653337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2227098824592602695075565 835162059222226010653337)
                ·
                  refine ⟨626371544416669507990003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 835162059222226010653337 626371544416669507990003)
                  ·
                    refine ⟨939557316625004261985005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 626371544416669507990003 939557316625004261985005)
                    ·
                      refine ⟨352333993734376598244377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 939557316625004261985005 352333993734376598244377)
                      ·
                        rfl

theorem cell23_686168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 5, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 5, 1, 3, 2, 1, 3].length) (baseStart_686168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_686168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_686168 prefixEnd_686168 := by exact prefixLift 686168
  have htrace : WordTrace (prefixWord ++ tailWord_686168) baseStart_686168 baseEnd_686168 := by
    simpa [prefixWord, tailWord_686168, baseEnd_686168] using wordTrace_append hprefix tailTrace_686168
  have hstable : (prefixWord ++ tailWord_686168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_686168).length < 2 ^ (prefixWord ++ tailWord_686168).sum := by decide
  have hdescent : baseEnd_686168 < baseStart_686168 := by decide
  rcases family_descends (prefixWord ++ tailWord_686168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_686191 : List Nat := [1, 1, 2, 1, 3, 4, 1, 1, 3, 4, 2]
def baseStart_686191 : Nat := 118140960795 + 686191 * 2 ^ 59
def prefixEnd_686191 : Nat := 4983230072969 + 3 ^ 40 * 686191 * 2
def baseEnd_686191 : Nat := 352345803789430008256771

theorem tailTrace_686191 : CollatzResearch.WordTrace tailWord_686191 prefixEnd_686191 352345803789430008256771 := by
  unfold tailWord_686191
  simp only [CollatzResearch.WordTrace]
  refine ⟨25027441857054673937770427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16684961238036449291846951 25027441857054673937770427)
  ·
    refine ⟨37541162785582010906655641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25027441857054673937770427 37541162785582010906655641)
    ·
      refine ⟨28155872089186508179991731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37541162785582010906655641 28155872089186508179991731)
      ·
        refine ⟨42233808133779762269987597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28155872089186508179991731 42233808133779762269987597)
        ·
          refine ⟨15837678050167410851245349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42233808133779762269987597 15837678050167410851245349)
          ·
            refine ⟨2969564634406389534608503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15837678050167410851245349 2969564634406389534608503)
            ·
              refine ⟨4454346951609584301912755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2969564634406389534608503 4454346951609584301912755)
              ·
                refine ⟨6681520427414376452869133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4454346951609584301912755 6681520427414376452869133)
                ·
                  refine ⟨2505570160280391169825925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6681520427414376452869133 2505570160280391169825925)
                  ·
                    refine ⟨469794405052573344342361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2505570160280391169825925 469794405052573344342361)
                    ·
                      refine ⟨352345803789430008256771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 469794405052573344342361 352345803789430008256771)
                      ·
                        rfl

theorem cell23_686191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 1, 1, 3, 4, 2].length) (baseStart_686191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_686191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_686191 prefixEnd_686191 := by exact prefixLift 686191
  have htrace : WordTrace (prefixWord ++ tailWord_686191) baseStart_686191 baseEnd_686191 := by
    simpa [prefixWord, tailWord_686191, baseEnd_686191] using wordTrace_append hprefix tailTrace_686191
  have hstable : (prefixWord ++ tailWord_686191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_686191).length < 2 ^ (prefixWord ++ tailWord_686191).sum := by decide
  have hdescent : baseEnd_686191 < baseStart_686191 := by decide
  rcases family_descends (prefixWord ++ tailWord_686191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_686231 : List Nat := [1, 1, 3, 3, 4, 1, 1, 2, 7]
def baseStart_686231 : Nat := 118140960795 + 686231 * 2 ^ 59
def prefixEnd_686231 : Nat := 4983230072969 + 3 ^ 40 * 686231 * 2
def baseEnd_686231 : Nat := 39151815890623316861843

theorem tailTrace_686231 : CollatzResearch.WordTrace tailWord_686231 prefixEnd_686231 39151815890623316861843 := by
  unfold tailWord_686231
  simp only [CollatzResearch.WordTrace]
  refine ⟨25028900776909760769226547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16685933851273173846151031 25028900776909760769226547)
  ·
    refine ⟨37543351165364641153839821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25028900776909760769226547 37543351165364641153839821)
    ·
      refine ⟨14078756687011740432689933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37543351165364641153839821 14078756687011740432689933)
      ·
        refine ⟨5279533757629402662258725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14078756687011740432689933 5279533757629402662258725)
        ·
          refine ⟨989912579555512999173511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5279533757629402662258725 989912579555512999173511)
          ·
            refine ⟨1484868869333269498760267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 989912579555512999173511 1484868869333269498760267)
            ·
              refine ⟨2227303303999904248140401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1484868869333269498760267 2227303303999904248140401)
              ·
                refine ⟨1670477477999928186105301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2227303303999904248140401 1670477477999928186105301)
                ·
                  refine ⟨39151815890623316861843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1670477477999928186105301 39151815890623316861843)
                  ·
                    rfl

theorem cell23_686231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 1, 1, 2, 7].length) (baseStart_686231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_686231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_686231 prefixEnd_686231 := by exact prefixLift 686231
  have htrace : WordTrace (prefixWord ++ tailWord_686231) baseStart_686231 baseEnd_686231 := by
    simpa [prefixWord, tailWord_686231, baseEnd_686231] using wordTrace_append hprefix tailTrace_686231
  have hstable : (prefixWord ++ tailWord_686231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_686231).length < 2 ^ (prefixWord ++ tailWord_686231).sum := by decide
  have hdescent : baseEnd_686231 < baseStart_686231 := by decide
  rcases family_descends (prefixWord ++ tailWord_686231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_686281 : List Nat := [1, 2, 1, 1, 2, 1, 1, 5, 1, 6, 2]
def baseStart_686281 : Nat := 118140960795 + 686281 * 2 ^ 59
def prefixEnd_686281 : Nat := 4983230072969 + 3 ^ 40 * 686281 * 2
def baseEnd_686281 : Nat := 352392017048334656131357

theorem tailTrace_686281 : CollatzResearch.WordTrace tailWord_686281 prefixEnd_686281 352392017048334656131357 := by
  unfold tailWord_686281
  simp only [CollatzResearch.WordTrace]
  refine ⟨25030724426728619308546697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16687149617819079539031131 25030724426728619308546697)
  ·
    refine ⟨18773043320046464481410023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25030724426728619308546697 18773043320046464481410023)
    ·
      refine ⟨28159564980069696722115035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18773043320046464481410023 28159564980069696722115035)
      ·
        refine ⟨42239347470104545083172553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28159564980069696722115035 42239347470104545083172553)
        ·
          refine ⟨31679510602578408812379415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42239347470104545083172553 31679510602578408812379415)
          ·
            refine ⟨47519265903867613218569123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31679510602578408812379415 47519265903867613218569123)
            ·
              refine ⟨71278898855801419827853685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47519265903867613218569123 71278898855801419827853685)
              ·
                refine ⟨6682396767731383108861283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 71278898855801419827853685 6682396767731383108861283)
                ·
                  refine ⟨10023595151597074663291925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6682396767731383108861283 10023595151597074663291925)
                  ·
                    refine ⟨469856022731112874841809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10023595151597074663291925 469856022731112874841809)
                    ·
                      refine ⟨352392017048334656131357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 469856022731112874841809 352392017048334656131357)
                      ·
                        rfl

theorem cell23_686281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 5, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 5, 1, 6, 2].length) (baseStart_686281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_686281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_686281 prefixEnd_686281 := by exact prefixLift 686281
  have htrace : WordTrace (prefixWord ++ tailWord_686281) baseStart_686281 baseEnd_686281 := by
    simpa [prefixWord, tailWord_686281, baseEnd_686281] using wordTrace_append hprefix tailTrace_686281
  have hstable : (prefixWord ++ tailWord_686281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_686281).length < 2 ^ (prefixWord ++ tailWord_686281).sum := by decide
  have hdescent : baseEnd_686281 < baseStart_686281 := by decide
  rcases family_descends (prefixWord ++ tailWord_686281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_686304 : List Nat := [2, 1, 1, 3, 1, 3, 1, 1, 10]
def baseStart_686304 : Nat := 118140960795 + 686304 * 2 ^ 59
def prefixEnd_686304 : Nat := 4983230072969 + 3 ^ 40 * 686304 * 2
def baseEnd_686304 : Nat := 39155980789265340682639

theorem tailTrace_686304 : CollatzResearch.WordTrace tailWord_686304 prefixEnd_686304 39155980789265340682639 := by
  unfold tailWord_686304
  simp only [CollatzResearch.WordTrace]
  refine ⟨12515781652822647118316983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16687708870430196157755977 12515781652822647118316983)
  ·
    refine ⟨18773672479233970677475475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12515781652822647118316983 18773672479233970677475475)
    ·
      refine ⟨28160508718850956016213213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18773672479233970677475475 28160508718850956016213213)
      ·
        refine ⟨10560190769569108506079955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28160508718850956016213213 10560190769569108506079955)
        ·
          refine ⟨15840286154353662759119933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10560190769569108506079955 15840286154353662759119933)
          ·
            refine ⟨5940107307882623534669975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15840286154353662759119933 5940107307882623534669975)
            ·
              refine ⟨8910160961823935302004963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5940107307882623534669975 8910160961823935302004963)
              ·
                refine ⟨13365241442735902953007445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8910160961823935302004963 13365241442735902953007445)
                ·
                  refine ⟨39155980789265340682639, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 13365241442735902953007445 39155980789265340682639)
                  ·
                    rfl

theorem cell23_686304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 1, 1, 10].length) (baseStart_686304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_686304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_686304 prefixEnd_686304 := by exact prefixLift 686304
  have htrace : WordTrace (prefixWord ++ tailWord_686304) baseStart_686304 baseEnd_686304 := by
    simpa [prefixWord, tailWord_686304, baseEnd_686304] using wordTrace_append hprefix tailTrace_686304
  have hstable : (prefixWord ++ tailWord_686304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_686304).length < 2 ^ (prefixWord ++ tailWord_686304).sum := by decide
  have hdescent : baseEnd_686304 < baseStart_686304 := by decide
  rcases family_descends (prefixWord ++ tailWord_686304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_686348 : List Nat := [2, 2, 1, 2, 2, 2, 2, 1, 5, 1, 3]
def baseStart_686348 : Nat := 118140960795 + 686348 * 2 ^ 59
def prefixEnd_686348 : Nat := 4983230072969 + 3 ^ 40 * 686348 * 2
def baseEnd_686348 : Nat := 352426420252185893993549

theorem tailTrace_686348 : CollatzResearch.WordTrace tailWord_686348 prefixEnd_686348 352426420252185893993549 := by
  unfold tailWord_686348
  simp only [CollatzResearch.WordTrace]
  refine ⟨12516584058742944875617849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16688778744990593167490465 12516584058742944875617849)
  ·
    refine ⟨9387438044057208656713387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12516584058742944875617849 9387438044057208656713387)
    ·
      refine ⟨14081157066085812985070081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9387438044057208656713387 14081157066085812985070081)
      ·
        refine ⟨10560867799564359738802561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14081157066085812985070081 10560867799564359738802561)
        ·
          refine ⟨7920650849673269804101921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10560867799564359738802561 7920650849673269804101921)
          ·
            refine ⟨5940488137254952353076441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7920650849673269804101921 5940488137254952353076441)
            ·
              refine ⟨4455366102941214264807331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5940488137254952353076441 4455366102941214264807331)
              ·
                refine ⟨6683049154411821397210997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4455366102941214264807331 6683049154411821397210997)
                ·
                  refine ⟨626535858226108255988531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 6683049154411821397210997 626535858226108255988531)
                  ·
                    refine ⟨939803787339162383982797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 626535858226108255988531 939803787339162383982797)
                    ·
                      refine ⟨352426420252185893993549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 939803787339162383982797 352426420252185893993549)
                      ·
                        rfl

theorem cell23_686348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 2, 1, 5, 1, 3].length) (baseStart_686348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_686348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_686348 prefixEnd_686348 := by exact prefixLift 686348
  have htrace : WordTrace (prefixWord ++ tailWord_686348) baseStart_686348 baseEnd_686348 := by
    simpa [prefixWord, tailWord_686348, baseEnd_686348] using wordTrace_append hprefix tailTrace_686348
  have hstable : (prefixWord ++ tailWord_686348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_686348).length < 2 ^ (prefixWord ++ tailWord_686348).sum := by decide
  have hdescent : baseEnd_686348 < baseStart_686348 := by decide
  rcases family_descends (prefixWord ++ tailWord_686348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_686376 : List Nat := [2, 1, 5, 1, 4, 1, 2, 2, 1, 4]
def baseStart_686376 : Nat := 118140960795 + 686376 * 2 ^ 59
def prefixEnd_686376 : Nat := 4983230072969 + 3 ^ 40 * 686376 * 2
def baseEnd_686376 : Nat := 117480265903503928147807

theorem tailTrace_686376 : CollatzResearch.WordTrace tailWord_686376 prefixEnd_686376 117480265903503928147807 := by
  unfold tailWord_686376
  simp only [CollatzResearch.WordTrace]
  refine ⟨12517094680692225266627491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16689459574256300355503321 12517094680692225266627491)
  ·
    refine ⟨18775642021038337899941237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12517094680692225266627491 18775642021038337899941237)
    ·
      refine ⟨1760216439472344178119491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 18775642021038337899941237 1760216439472344178119491)
      ·
        refine ⟨2640324659208516267179237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1760216439472344178119491 2640324659208516267179237)
        ·
          refine ⟨495060873601596800096107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2640324659208516267179237 495060873601596800096107)
          ·
            refine ⟨742591310402395200144161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 495060873601596800096107 742591310402395200144161)
            ·
              refine ⟨556943482801796400108121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 742591310402395200144161 556943482801796400108121)
              ·
                refine ⟨417707612101347300081091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 556943482801796400108121 417707612101347300081091)
                ·
                  refine ⟨626561418152020950121637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 417707612101347300081091 626561418152020950121637)
                  ·
                    refine ⟨117480265903503928147807, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 626561418152020950121637 117480265903503928147807)
                    ·
                      rfl

theorem cell23_686376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 4, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 4, 1, 2, 2, 1, 4].length) (baseStart_686376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_686376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_686376 prefixEnd_686376 := by exact prefixLift 686376
  have htrace : WordTrace (prefixWord ++ tailWord_686376) baseStart_686376 baseEnd_686376 := by
    simpa [prefixWord, tailWord_686376, baseEnd_686376] using wordTrace_append hprefix tailTrace_686376
  have hstable : (prefixWord ++ tailWord_686376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_686376).length < 2 ^ (prefixWord ++ tailWord_686376).sum := by decide
  have hdescent : baseEnd_686376 < baseStart_686376 := by decide
  rcases family_descends (prefixWord ++ tailWord_686376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_686391 : List Nat := [1, 1, 3, 1, 2, 1, 1, 6, 1, 1, 5]
def baseStart_686391 : Nat := 118140960795 + 686391 * 2 ^ 59
def prefixEnd_686391 : Nat := 4983230072969 + 3 ^ 40 * 686391 * 2
def baseEnd_686391 : Nat := 352448499920329225755851

theorem tailTrace_686391 : CollatzResearch.WordTrace tailWord_686391 prefixEnd_686391 352448499920329225755851 := by
  unfold tailWord_686391
  simp only [CollatzResearch.WordTrace]
  refine ⟨25034736456330108095051027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16689824304220072063367351 25034736456330108095051027)
  ·
    refine ⟨37552104684495162142576541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25034736456330108095051027 37552104684495162142576541)
    ·
      refine ⟨14082039256685685803466203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37552104684495162142576541 14082039256685685803466203)
      ·
        refine ⟨21123058885028528705199305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14082039256685685803466203 21123058885028528705199305)
        ·
          refine ⟨15842294163771396528899479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21123058885028528705199305 15842294163771396528899479)
          ·
            refine ⟨23763441245657094793349219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15842294163771396528899479 23763441245657094793349219)
            ·
              refine ⟨35645161868485642190023829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23763441245657094793349219 35645161868485642190023829)
              ·
                refine ⟨1670866962585264477657367, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 35645161868485642190023829 1670866962585264477657367)
                ·
                  refine ⟨2506300443877896716486051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1670866962585264477657367 2506300443877896716486051)
                  ·
                    refine ⟨3759450665816845074729077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2506300443877896716486051 3759450665816845074729077)
                    ·
                      refine ⟨352448499920329225755851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3759450665816845074729077 352448499920329225755851)
                      ·
                        rfl

theorem cell23_686391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 6, 1, 1, 5].length) (baseStart_686391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_686391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_686391 prefixEnd_686391 := by exact prefixLift 686391
  have htrace : WordTrace (prefixWord ++ tailWord_686391) baseStart_686391 baseEnd_686391 := by
    simpa [prefixWord, tailWord_686391, baseEnd_686391] using wordTrace_append hprefix tailTrace_686391
  have hstable : (prefixWord ++ tailWord_686391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_686391).length < 2 ^ (prefixWord ++ tailWord_686391).sum := by decide
  have hdescent : baseEnd_686391 < baseStart_686391 := by decide
  rcases family_descends (prefixWord ++ tailWord_686391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_686398 : List Nat := [4, 2, 1, 2, 1, 2, 1, 3, 1, 6]
def baseStart_686398 : Nat := 118140960795 + 686398 * 2 ^ 59
def prefixEnd_686398 : Nat := 4983230072969 + 3 ^ 40 * 686398 * 2
def baseEnd_686398 : Nat := 117484031428303566122773

theorem tailTrace_686398 : CollatzResearch.WordTrace tailWord_686398 prefixEnd_686398 117484031428303566122773 := by
  unfold tailWord_686398
  simp only [CollatzResearch.WordTrace]
  refine ⟨3129373970913093536319481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 16689994511536498860370565 3129373970913093536319481)
  ·
    refine ⟨2347030478184820152239611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3129373970913093536319481 2347030478184820152239611)
    ·
      refine ⟨3520545717277230228359417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2347030478184820152239611 3520545717277230228359417)
      ·
        refine ⟨2640409287957922671269563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3520545717277230228359417 2640409287957922671269563)
        ·
          refine ⟨3960613931936884006904345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2640409287957922671269563 3960613931936884006904345)
          ·
            refine ⟨2970460448952663005178259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3960613931936884006904345 2970460448952663005178259)
            ·
              refine ⟨4455690673428994507767389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2970460448952663005178259 4455690673428994507767389)
              ·
                refine ⟨1670884002535872940412771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4455690673428994507767389 1670884002535872940412771)
                ·
                  refine ⟨2506326003803809410619157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1670884002535872940412771 2506326003803809410619157)
                  ·
                    refine ⟨117484031428303566122773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2506326003803809410619157 117484031428303566122773)
                    ·
                      rfl

theorem cell23_686398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 1, 3, 1, 6].length) (baseStart_686398 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_686398 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_686398 prefixEnd_686398 := by exact prefixLift 686398
  have htrace : WordTrace (prefixWord ++ tailWord_686398) baseStart_686398 baseEnd_686398 := by
    simpa [prefixWord, tailWord_686398, baseEnd_686398] using wordTrace_append hprefix tailTrace_686398
  have hstable : (prefixWord ++ tailWord_686398).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_686398).length < 2 ^ (prefixWord ++ tailWord_686398).sum := by decide
  have hdescent : baseEnd_686398 < baseStart_686398 := by decide
  rcases family_descends (prefixWord ++ tailWord_686398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_686408 : List Nat := [2, 1, 3, 1, 1, 2, 4, 1, 3, 2, 3]
def baseStart_686408 : Nat := 118140960795 + 686408 * 2 ^ 59
def prefixEnd_686408 : Nat := 4983230072969 + 3 ^ 40 * 686408 * 2
def baseEnd_686408 : Nat := 352457229091455659243273

theorem tailTrace_686408 : CollatzResearch.WordTrace tailWord_686408 prefixEnd_686408 352457229091455659243273 := by
  unfold tailWord_686408
  simp only [CollatzResearch.WordTrace]
  refine ⟨12517678248634259999209939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16690237664845679998946585 12517678248634259999209939)
  ·
    refine ⟨18776517372951389998814909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12517678248634259999209939 18776517372951389998814909)
    ·
      refine ⟨7041194014856771249555591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18776517372951389998814909 7041194014856771249555591)
      ·
        refine ⟨10561791022285156874333387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7041194014856771249555591 10561791022285156874333387)
        ·
          refine ⟨15842686533427735311500081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10561791022285156874333387 15842686533427735311500081)
          ·
            refine ⟨11882014900070801483625061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15842686533427735311500081 11882014900070801483625061)
            ·
              refine ⟨2227877793763275278179699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11882014900070801483625061 2227877793763275278179699)
              ·
                refine ⟨3341816690644912917269549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2227877793763275278179699 3341816690644912917269549)
                ·
                  refine ⟨1253181258991842343976081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3341816690644912917269549 1253181258991842343976081)
                  ·
                    refine ⟨939885944243881757982061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1253181258991842343976081 939885944243881757982061)
                    ·
                      refine ⟨352457229091455659243273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 939885944243881757982061 352457229091455659243273)
                      ·
                        rfl

theorem cell23_686408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 4, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 4, 1, 3, 2, 3].length) (baseStart_686408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_686408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_686408 prefixEnd_686408 := by exact prefixLift 686408
  have htrace : WordTrace (prefixWord ++ tailWord_686408) baseStart_686408 baseEnd_686408 := by
    simpa [prefixWord, tailWord_686408, baseEnd_686408] using wordTrace_append hprefix tailTrace_686408
  have hstable : (prefixWord ++ tailWord_686408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_686408).length < 2 ^ (prefixWord ++ tailWord_686408).sum := by decide
  have hdescent : baseEnd_686408 < baseStart_686408 := by decide
  rcases family_descends (prefixWord ++ tailWord_686408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_686418 : List Nat := [3, 2, 2, 1, 1, 1, 4, 2, 1, 2, 4]
def baseStart_686418 : Nat := 118140960795 + 686418 * 2 ^ 59
def prefixEnd_686418 : Nat := 4983230072969 + 3 ^ 40 * 686418 * 2
def baseEnd_686418 : Nat := 352462363898000620118227

theorem tailTrace_686418 : CollatzResearch.WordTrace tailWord_686418 prefixEnd_686418 352462363898000620118227 := by
  unfold tailWord_686418
  simp only [CollatzResearch.WordTrace]
  refine ⟨6258930306808072926570977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16690480818154861137522605 6258930306808072926570977)
  ·
    refine ⟨4694197730106054694928233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6258930306808072926570977 4694197730106054694928233)
    ·
      refine ⟨3520648297579541021196175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4694197730106054694928233 3520648297579541021196175)
      ·
        refine ⟨5280972446369311531794263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3520648297579541021196175 5280972446369311531794263)
        ·
          refine ⟨7921458669553967297691395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5280972446369311531794263 7921458669553967297691395)
          ·
            refine ⟨11882188004330950946537093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7921458669553967297691395 11882188004330950946537093)
            ·
              refine ⟨2227910250812053302475705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11882188004330950946537093 2227910250812053302475705)
              ·
                refine ⟨1670932688109039976856779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2227910250812053302475705 1670932688109039976856779)
                ·
                  refine ⟨2506399032163559965285169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1670932688109039976856779 2506399032163559965285169)
                  ·
                    refine ⟨1879799274122669973963877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2506399032163559965285169 1879799274122669973963877)
                    ·
                      refine ⟨352462363898000620118227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1879799274122669973963877 352462363898000620118227)
                      ·
                        rfl

theorem cell23_686418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 4, 2, 1, 2, 4].length) (baseStart_686418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_686418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_686418 prefixEnd_686418 := by exact prefixLift 686418
  have htrace : WordTrace (prefixWord ++ tailWord_686418) baseStart_686418 baseEnd_686418 := by
    simpa [prefixWord, tailWord_686418, baseEnd_686418] using wordTrace_append hprefix tailTrace_686418
  have hstable : (prefixWord ++ tailWord_686418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_686418).length < 2 ^ (prefixWord ++ tailWord_686418).sum := by decide
  have hdescent : baseEnd_686418 < baseStart_686418 := by decide
  rcases family_descends (prefixWord ++ tailWord_686418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_686432 : List Nat := [2, 1, 1, 3, 5, 2, 1, 2, 2, 4]
def baseStart_686432 : Nat := 118140960795 + 686432 * 2 ^ 59
def prefixEnd_686432 : Nat := 4983230072969 + 3 ^ 40 * 686432 * 2
def baseEnd_686432 : Nat := 117489850875721188447721

theorem tailTrace_686432 : CollatzResearch.WordTrace tailWord_686432 prefixEnd_686432 117489850875721188447721 := by
  unfold tailWord_686432
  simp only [CollatzResearch.WordTrace]
  refine ⟨12518115924590786048646775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16690821232787714731529033 12518115924590786048646775)
  ·
    refine ⟨18777173886886179072970163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12518115924590786048646775 18777173886886179072970163)
    ·
      refine ⟨28165760830329268609455245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18777173886886179072970163 28165760830329268609455245)
      ·
        refine ⟨10562160311373475728545717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28165760830329268609455245 10562160311373475728545717)
        ·
          refine ⟨990202529191263349551161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 10562160311373475728545717 990202529191263349551161)
          ·
            refine ⟨742651896893447512163371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 990202529191263349551161 742651896893447512163371)
            ·
              refine ⟨1113977845340171268245057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 742651896893447512163371 1113977845340171268245057)
              ·
                refine ⟨835483384005128451183793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1113977845340171268245057 835483384005128451183793)
                ·
                  refine ⟨626612538003846338387845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 835483384005128451183793 626612538003846338387845)
                  ·
                    refine ⟨117489850875721188447721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 626612538003846338387845 117489850875721188447721)
                    ·
                      rfl

theorem cell23_686432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 2, 1, 2, 2, 4].length) (baseStart_686432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_686432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_686432 prefixEnd_686432 := by exact prefixLift 686432
  have htrace : WordTrace (prefixWord ++ tailWord_686432) baseStart_686432 baseEnd_686432 := by
    simpa [prefixWord, tailWord_686432, baseEnd_686432] using wordTrace_append hprefix tailTrace_686432
  have hstable : (prefixWord ++ tailWord_686432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_686432).length < 2 ^ (prefixWord ++ tailWord_686432).sum := by decide
  have hdescent : baseEnd_686432 < baseStart_686432 := by decide
  rcases family_descends (prefixWord ++ tailWord_686432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_686439 : List Nat := [1, 1, 5, 1, 3, 1, 2, 4, 1, 2, 2]
def baseStart_686439 : Nat := 118140960795 + 686439 * 2 ^ 59
def prefixEnd_686439 : Nat := 4983230072969 + 3 ^ 40 * 686439 * 2
def baseEnd_686439 : Nat := 352473146991745037955631

theorem tailTrace_686439 : CollatzResearch.WordTrace tailWord_686439 prefixEnd_686439 352473146991745037955631 := by
  unfold tailWord_686439
  simp only [CollatzResearch.WordTrace]
  refine ⟨25036487160156212292798371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16690991440104141528532247 25036487160156212292798371)
  ·
    refine ⟨37554730740234318439197557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25036487160156212292798371 37554730740234318439197557)
    ·
      refine ⟨3520756006896967353674771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 37554730740234318439197557 3520756006896967353674771)
      ·
        refine ⟨5281134010345451030512157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3520756006896967353674771 5281134010345451030512157)
        ·
          refine ⟨1980425253879544136442059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5281134010345451030512157 1980425253879544136442059)
          ·
            refine ⟨2970637880819316204663089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1980425253879544136442059 2970637880819316204663089)
            ·
              refine ⟨2227978410614487153497317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2970637880819316204663089 2227978410614487153497317)
              ·
                refine ⟨417745951990216341280747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2227978410614487153497317 417745951990216341280747)
                ·
                  refine ⟨626618927985324511921121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 417745951990216341280747 626618927985324511921121)
                  ·
                    refine ⟨469964195988993383940841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 626618927985324511921121 469964195988993383940841)
                    ·
                      refine ⟨352473146991745037955631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 469964195988993383940841 352473146991745037955631)
                      ·
                        rfl

theorem cell23_686439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 2, 4, 1, 2, 2].length) (baseStart_686439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_686439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_686439 prefixEnd_686439 := by exact prefixLift 686439
  have htrace : WordTrace (prefixWord ++ tailWord_686439) baseStart_686439 baseEnd_686439 := by
    simpa [prefixWord, tailWord_686439, baseEnd_686439] using wordTrace_append hprefix tailTrace_686439
  have hstable : (prefixWord ++ tailWord_686439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_686439).length < 2 ^ (prefixWord ++ tailWord_686439).sum := by decide
  have hdescent : baseEnd_686439 < baseStart_686439 := by decide
  rcases family_descends (prefixWord ++ tailWord_686439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_686491 : List Nat := [1, 1, 1, 1, 1, 1, 2, 1, 2, 8, 4]
def baseStart_686491 : Nat := 118140960795 + 686491 * 2 ^ 59
def prefixEnd_686491 : Nat := 4983230072969 + 3 ^ 40 * 686491 * 2
def baseEnd_686491 : Nat := 352499847985778834505391

theorem tailTrace_686491 : CollatzResearch.WordTrace tailWord_686491 prefixEnd_686491 352499847985778834505391 := by
  unfold tailWord_686491
  simp only [CollatzResearch.WordTrace]
  refine ⟨25038383755967825173691327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16692255837311883449127551 25038383755967825173691327)
  ·
    refine ⟨37557575633951737760536991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25038383755967825173691327 37557575633951737760536991)
    ·
      refine ⟨56336363450927606640805487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37557575633951737760536991 56336363450927606640805487)
      ·
        refine ⟨84504545176391409961208231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56336363450927606640805487 84504545176391409961208231)
        ·
          refine ⟨126756817764587114941812347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84504545176391409961208231 126756817764587114941812347)
          ·
            refine ⟨190135226646880672412718521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 126756817764587114941812347 190135226646880672412718521)
            ·
              refine ⟨142601419985160504309538891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 190135226646880672412718521 142601419985160504309538891)
              ·
                refine ⟨213902129977740756464308337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 142601419985160504309538891 213902129977740756464308337)
                ·
                  refine ⟨160426597483305567348231253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 213902129977740756464308337 160426597483305567348231253)
                  ·
                    refine ⟨1879999189257487117362085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 160426597483305567348231253 1879999189257487117362085)
                    ·
                      refine ⟨352499847985778834505391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1879999189257487117362085 352499847985778834505391)
                      ·
                        rfl

theorem cell23_686491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 2, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 2, 8, 4].length) (baseStart_686491 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_686491 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_686491 prefixEnd_686491 := by exact prefixLift 686491
  have htrace : WordTrace (prefixWord ++ tailWord_686491) baseStart_686491 baseEnd_686491 := by
    simpa [prefixWord, tailWord_686491, baseEnd_686491] using wordTrace_append hprefix tailTrace_686491
  have hstable : (prefixWord ++ tailWord_686491).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_686491).length < 2 ^ (prefixWord ++ tailWord_686491).sum := by decide
  have hdescent : baseEnd_686491 < baseStart_686491 := by decide
  rcases family_descends (prefixWord ++ tailWord_686491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_686498 : List Nat := [3, 3, 1, 2, 1, 1, 1, 2, 1, 3, 5]
def baseStart_686498 : Nat := 118140960795 + 686498 * 2 ^ 59
def prefixEnd_686498 : Nat := 4983230072969 + 3 ^ 40 * 686498 * 2
def baseEnd_686498 : Nat := 352503442350360307117859

theorem tailTrace_686498 : CollatzResearch.WordTrace tailWord_686498 prefixEnd_686498 352503442350360307117859 := by
  unfold tailWord_686498
  simp only [CollatzResearch.WordTrace]
  refine ⟨6259659766735616342299037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16692426044628310246130765 6259659766735616342299037)
  ·
    refine ⟨2347372412525856128362139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6259659766735616342299037 2347372412525856128362139)
    ·
      refine ⟨3521058618788784192543209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2347372412525856128362139 3521058618788784192543209)
      ·
        refine ⟨2640793964091588144407407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3521058618788784192543209 2640793964091588144407407)
        ·
          refine ⟨3961190946137382216611111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2640793964091588144407407 3961190946137382216611111)
          ·
            refine ⟨5941786419206073324916667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3961190946137382216611111 5941786419206073324916667)
            ·
              refine ⟨8912679628809109987375001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5941786419206073324916667 8912679628809109987375001)
              ·
                refine ⟨6684509721606832490531251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8912679628809109987375001 6684509721606832490531251)
                ·
                  refine ⟨10026764582410248735796877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6684509721606832490531251 10026764582410248735796877)
                  ·
                    refine ⟨3760036718403843275923829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10026764582410248735796877 3760036718403843275923829)
                    ·
                      refine ⟨352503442350360307117859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3760036718403843275923829 352503442350360307117859)
                      ·
                        rfl

theorem cell23_686498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 1, 2, 1, 3, 5].length) (baseStart_686498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_686498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_686498 prefixEnd_686498 := by exact prefixLift 686498
  have htrace : WordTrace (prefixWord ++ tailWord_686498) baseStart_686498 baseEnd_686498 := by
    simpa [prefixWord, tailWord_686498, baseEnd_686498] using wordTrace_append hprefix tailTrace_686498
  have hstable : (prefixWord ++ tailWord_686498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_686498).length < 2 ^ (prefixWord ++ tailWord_686498).sum := by decide
  have hdescent : baseEnd_686498 < baseStart_686498 := by decide
  rcases family_descends (prefixWord ++ tailWord_686498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_686516 : List Nat := [2, 5, 2, 2, 1, 1, 1, 1, 3, 3, 2]
def baseStart_686516 : Nat := 118140960795 + 686516 * 2 ^ 59
def prefixEnd_686516 : Nat := 4983230072969 + 3 ^ 40 * 686516 * 2
def baseEnd_686516 : Nat := 352512685002141236692777

theorem tailTrace_686516 : CollatzResearch.WordTrace tailWord_686516 prefixEnd_686516 352512685002141236692777 := by
  unfold tailWord_686516
  simp only [CollatzResearch.WordTrace]
  refine ⟨12519647790438627221675701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16692863720584836295567601 12519647790438627221675701)
  ·
    refine ⟨1173716980353621302032097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 12519647790438627221675701 1173716980353621302032097)
    ·
      refine ⟨880287735265215976524073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1173716980353621302032097 880287735265215976524073)
      ·
        refine ⟨660215801448911982393055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 880287735265215976524073 660215801448911982393055)
        ·
          refine ⟨990323702173367973589583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 660215801448911982393055 990323702173367973589583)
          ·
            refine ⟨1485485553260051960384375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 990323702173367973589583 1485485553260051960384375)
            ·
              refine ⟨2228228329890077940576563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1485485553260051960384375 2228228329890077940576563)
              ·
                refine ⟨3342342494835116910864845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2228228329890077940576563 3342342494835116910864845)
                ·
                  refine ⟨1253378435563168841574317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3342342494835116910864845 1253378435563168841574317)
                  ·
                    refine ⟨470016913336188315590369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1253378435563168841574317 470016913336188315590369)
                    ·
                      refine ⟨352512685002141236692777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 470016913336188315590369 352512685002141236692777)
                      ·
                        rfl

theorem cell23_686516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 1, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 1, 1, 1, 3, 3, 2].length) (baseStart_686516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_686516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_686516 prefixEnd_686516 := by exact prefixLift 686516
  have htrace : WordTrace (prefixWord ++ tailWord_686516) baseStart_686516 baseEnd_686516 := by
    simpa [prefixWord, tailWord_686516, baseEnd_686516] using wordTrace_append hprefix tailTrace_686516
  have hstable : (prefixWord ++ tailWord_686516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_686516).length < 2 ^ (prefixWord ++ tailWord_686516).sum := by decide
  have hdescent : baseEnd_686516 < baseStart_686516 := by decide
  rcases family_descends (prefixWord ++ tailWord_686516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_686528 : List Nat := [2, 1, 1, 2, 3, 1, 1, 2, 4, 3, 3]
def baseStart_686528 : Nat := 118140960795 + 686528 * 2 ^ 59
def prefixEnd_686528 : Nat := 4983230072969 + 3 ^ 40 * 686528 * 2
def baseEnd_686528 : Nat := 352518846769995189742721

theorem tailTrace_686528 : CollatzResearch.WordTrace tailWord_686528 prefixEnd_686528 352518846769995189742721 := by
  unfold tailWord_686528
  simp only [CollatzResearch.WordTrace]
  refine ⟨12519866628416890246394119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16693155504555853661858825 12519866628416890246394119)
  ·
    refine ⟨18779799942625335369591179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12519866628416890246394119 18779799942625335369591179)
    ·
      refine ⟨28169699913938003054386769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18779799942625335369591179 28169699913938003054386769)
      ·
        refine ⟨21127274935453502290790077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28169699913938003054386769 21127274935453502290790077)
        ·
          refine ⟨7922728100795063359046279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21127274935453502290790077 7922728100795063359046279)
          ·
            refine ⟨11884092151192595038569419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7922728100795063359046279 11884092151192595038569419)
            ·
              refine ⟨17826138226788892557854129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11884092151192595038569419 17826138226788892557854129)
              ·
                refine ⟨13369603670091669418390597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17826138226788892557854129 13369603670091669418390597)
                ·
                  refine ⟨2506800688142188015948237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13369603670091669418390597 2506800688142188015948237)
                  ·
                    refine ⟨940050258053320505980589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2506800688142188015948237 940050258053320505980589)
                    ·
                      refine ⟨352518846769995189742721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 940050258053320505980589 352518846769995189742721)
                      ·
                        rfl

theorem cell23_686528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 2, 4, 3, 3].length) (baseStart_686528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_686528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_686528 prefixEnd_686528 := by exact prefixLift 686528
  have htrace : WordTrace (prefixWord ++ tailWord_686528) baseStart_686528 baseEnd_686528 := by
    simpa [prefixWord, tailWord_686528, baseEnd_686528] using wordTrace_append hprefix tailTrace_686528
  have hstable : (prefixWord ++ tailWord_686528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_686528).length < 2 ^ (prefixWord ++ tailWord_686528).sum := by decide
  have hdescent : baseEnd_686528 < baseStart_686528 := by decide
  rcases family_descends (prefixWord ++ tailWord_686528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_686585 : List Nat := [1, 2, 1, 3, 1, 2, 5, 1, 2, 1, 4]
def baseStart_686585 : Nat := 118140960795 + 686585 * 2 ^ 59
def prefixEnd_686585 : Nat := 4983230072969 + 3 ^ 40 * 686585 * 2
def baseEnd_686585 : Nat := 352548115167301466729959

theorem tailTrace_686585 : CollatzResearch.WordTrace tailWord_686585 prefixEnd_686585 352548115167301466729959 := by
  unfold tailWord_686585
  simp only [CollatzResearch.WordTrace]
  refine ⟨25041812217627279227613209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16694541478418186151742139 25041812217627279227613209)
  ·
    refine ⟨18781359163220459420709907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25041812217627279227613209 18781359163220459420709907)
    ·
      refine ⟨28172038744830689131064861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18781359163220459420709907 28172038744830689131064861)
      ·
        refine ⟨10564514529311508424149323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28172038744830689131064861 10564514529311508424149323)
        ·
          refine ⟨15846771793967262636223985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10564514529311508424149323 15846771793967262636223985)
          ·
            refine ⟨11885078845475446977167989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15846771793967262636223985 11885078845475446977167989)
            ·
              refine ⟨1114226141763323154109499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 11885078845475446977167989 1114226141763323154109499)
              ·
                refine ⟨1671339212644984731164249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1114226141763323154109499 1671339212644984731164249)
                ·
                  refine ⟨1253504409483738548373187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1671339212644984731164249 1253504409483738548373187)
                  ·
                    refine ⟨1880256614225607822559781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1253504409483738548373187 1880256614225607822559781)
                    ·
                      refine ⟨352548115167301466729959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1880256614225607822559781 352548115167301466729959)
                      ·
                        rfl

theorem cell23_686585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 5, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 5, 1, 2, 1, 4].length) (baseStart_686585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_686585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_686585 prefixEnd_686585 := by exact prefixLift 686585
  have htrace : WordTrace (prefixWord ++ tailWord_686585) baseStart_686585 baseEnd_686585 := by
    simpa [prefixWord, tailWord_686585, baseEnd_686585] using wordTrace_append hprefix tailTrace_686585
  have hstable : (prefixWord ++ tailWord_686585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_686585).length < 2 ^ (prefixWord ++ tailWord_686585).sum := by decide
  have hdescent : baseEnd_686585 < baseStart_686585 := by decide
  rcases family_descends (prefixWord ++ tailWord_686585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_686646 : List Nat := [5, 1, 2, 1, 2, 1, 3, 3, 1, 4]
def baseStart_686646 : Nat := 118140960795 + 686646 * 2 ^ 59
def prefixEnd_686646 : Nat := 4983230072969 + 3 ^ 40 * 686646 * 2
def baseEnd_686646 : Nat := 117526479162408576022393

theorem tailTrace_686646 : CollatzResearch.WordTrace tailWord_686646 prefixEnd_686646 117526479162408576022393 := by
  unfold tailWord_686646
  simp only [CollatzResearch.WordTrace]
  refine ⟨1565252316900392915348987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 16696024713604191097055861 1565252316900392915348987)
  ·
    refine ⟨2347878475350589373023481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1565252316900392915348987 2347878475350589373023481)
    ·
      refine ⟨1760908856512942029767611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2347878475350589373023481 1760908856512942029767611)
      ·
        refine ⟨2641363284769413044651417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1760908856512942029767611 2641363284769413044651417)
        ·
          refine ⟨1981022463577059783488563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2641363284769413044651417 1981022463577059783488563)
          ·
            refine ⟨2971533695365589675232845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1981022463577059783488563 2971533695365589675232845)
            ·
              refine ⟨1114325135762096128212317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2971533695365589675232845 1114325135762096128212317)
              ·
                refine ⟨417871925910786048079619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1114325135762096128212317 417871925910786048079619)
                ·
                  refine ⟨626807888866179072119429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 417871925910786048079619 626807888866179072119429)
                  ·
                    refine ⟨117526479162408576022393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 626807888866179072119429 117526479162408576022393)
                    ·
                      rfl

theorem cell23_686646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 3, 3, 1, 4].length) (baseStart_686646 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_686646 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_686646 prefixEnd_686646 := by exact prefixLift 686646
  have htrace : WordTrace (prefixWord ++ tailWord_686646) baseStart_686646 baseEnd_686646 := by
    simpa [prefixWord, tailWord_686646, baseEnd_686646] using wordTrace_append hprefix tailTrace_686646
  have hstable : (prefixWord ++ tailWord_686646).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_686646).length < 2 ^ (prefixWord ++ tailWord_686646).sum := by decide
  have hdescent : baseEnd_686646 < baseStart_686646 := by decide
  rcases family_descends (prefixWord ++ tailWord_686646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_686655 : List Nat := [1, 1, 2, 2, 3, 2, 1, 5, 1, 5]
def baseStart_686655 : Nat := 118140960795 + 686655 * 2 ^ 59
def prefixEnd_686655 : Nat := 4983230072969 + 3 ^ 40 * 686655 * 2
def baseEnd_686655 : Nat := 117528019604372064284879

theorem tailTrace_686655 : CollatzResearch.WordTrace tailWord_686655 prefixEnd_686655 117528019604372064284879 := by
  unfold tailWord_686655
  simp only [CollatzResearch.WordTrace]
  refine ⟨25044365327373681182661419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16696243551582454121774279 25044365327373681182661419)
  ·
    refine ⟨37566547991060521773992129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25044365327373681182661419 37566547991060521773992129)
    ·
      refine ⟨28174910993295391330494097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37566547991060521773992129 28174910993295391330494097)
      ·
        refine ⟨21131183244971543497870573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28174910993295391330494097 21131183244971543497870573)
        ·
          refine ⟨7924193716864328811701465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21131183244971543497870573 7924193716864328811701465)
          ·
            refine ⟨5943145287648246608776099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7924193716864328811701465 5943145287648246608776099)
            ·
              refine ⟨8914717931472369913164149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5943145287648246608776099 8914717931472369913164149)
              ·
                refine ⟨835754806075534679359139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8914717931472369913164149 835754806075534679359139)
                ·
                  refine ⟨1253632209113302019038709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 835754806075534679359139 1253632209113302019038709)
                  ·
                    refine ⟨117528019604372064284879, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1253632209113302019038709 117528019604372064284879)
                    ·
                      rfl

theorem cell23_686655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 1, 5, 1, 5].length) (baseStart_686655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_686655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_686655 prefixEnd_686655 := by exact prefixLift 686655
  have htrace : WordTrace (prefixWord ++ tailWord_686655) baseStart_686655 baseEnd_686655 := by
    simpa [prefixWord, tailWord_686655, baseEnd_686655] using wordTrace_append hprefix tailTrace_686655
  have hstable : (prefixWord ++ tailWord_686655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_686655).length < 2 ^ (prefixWord ++ tailWord_686655).sum := by decide
  have hdescent : baseEnd_686655 < baseStart_686655 := by decide
  rcases family_descends (prefixWord ++ tailWord_686655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_686696 : List Nat := [2, 1, 4, 3, 2, 1, 2, 1, 2, 3, 2]
def baseStart_686696 : Nat := 118140960795 + 686696 * 2 ^ 59
def prefixEnd_686696 : Nat := 4983230072969 + 3 ^ 40 * 686696 * 2
def baseEnd_686696 : Nat := 352605111519950532441949

theorem tailTrace_686696 : CollatzResearch.WordTrace tailWord_686696 prefixEnd_686696 352605111519950532441949 := by
  unfold tailWord_686696
  simp only [CollatzResearch.WordTrace]
  refine ⟨12522930360112572592451971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16697240480150096789935961 12522930360112572592451971)
  ·
    refine ⟨18784395540168858888677957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12522930360112572592451971 18784395540168858888677957)
    ·
      refine ⟨3522074163781661041627117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18784395540168858888677957 3522074163781661041627117)
      ·
        refine ⟨1320777811418122890610169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3522074163781661041627117 1320777811418122890610169)
        ·
          refine ⟨990583358563592167957627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1320777811418122890610169 990583358563592167957627)
          ·
            refine ⟨1485875037845388251936441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 990583358563592167957627 1485875037845388251936441)
            ·
              refine ⟨1114406278384041188952331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1485875037845388251936441 1114406278384041188952331)
              ·
                refine ⟨1671609417576061783428497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1114406278384041188952331 1671609417576061783428497)
                ·
                  refine ⟨1253707063182046337571373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1671609417576061783428497 1253707063182046337571373)
                  ·
                    refine ⟨470140148693267376589265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1253707063182046337571373 470140148693267376589265)
                    ·
                      refine ⟨352605111519950532441949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 470140148693267376589265 352605111519950532441949)
                      ·
                        rfl

theorem cell23_686696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 1, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 1, 2, 1, 2, 3, 2].length) (baseStart_686696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_686696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_686696 prefixEnd_686696 := by exact prefixLift 686696
  have htrace : WordTrace (prefixWord ++ tailWord_686696) baseStart_686696 baseEnd_686696 := by
    simpa [prefixWord, tailWord_686696, baseEnd_686696] using wordTrace_append hprefix tailTrace_686696
  have hstable : (prefixWord ++ tailWord_686696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_686696).length < 2 ^ (prefixWord ++ tailWord_686696).sum := by decide
  have hdescent : baseEnd_686696 < baseStart_686696 := by decide
  rcases family_descends (prefixWord ++ tailWord_686696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_686702 : List Nat := [4, 1, 2, 2, 2, 2, 1, 2, 1, 6]
def baseStart_686702 : Nat := 118140960795 + 686702 * 2 ^ 59
def prefixEnd_686702 : Nat := 4983230072969 + 3 ^ 40 * 686702 * 2
def baseEnd_686702 : Nat := 117536064134625836322307

theorem tailTrace_686702 : CollatzResearch.WordTrace tailWord_686702 prefixEnd_686702 117536064134625836322307 := by
  unfold tailWord_686702
  simp only [CollatzResearch.WordTrace]
  refine ⟨3130759944775426026202795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 16697386372135605473081573 3130759944775426026202795)
  ·
    refine ⟨4696139917163139039304193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3130759944775426026202795 4696139917163139039304193)
    ·
      refine ⟨3522104937872354279478145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4696139917163139039304193 3522104937872354279478145)
      ·
        refine ⟨2641578703404265709608609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3522104937872354279478145 2641578703404265709608609)
        ·
          refine ⟨1981184027553199282206457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2641578703404265709608609 1981184027553199282206457)
          ·
            refine ⟨1485888020664899461654843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1981184027553199282206457 1485888020664899461654843)
            ·
              refine ⟨2228832030997349192482265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1485888020664899461654843 2228832030997349192482265)
              ·
                refine ⟨1671624023248011894361699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2228832030997349192482265 1671624023248011894361699)
                ·
                  refine ⟨2507436034872017841542549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1671624023248011894361699 2507436034872017841542549)
                  ·
                    refine ⟨117536064134625836322307, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2507436034872017841542549 117536064134625836322307)
                    ·
                      rfl

theorem cell23_686702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 2, 1, 2, 1, 6].length) (baseStart_686702 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_686702 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_686702 prefixEnd_686702 := by exact prefixLift 686702
  have htrace : WordTrace (prefixWord ++ tailWord_686702) baseStart_686702 baseEnd_686702 := by
    simpa [prefixWord, tailWord_686702, baseEnd_686702] using wordTrace_append hprefix tailTrace_686702
  have hstable : (prefixWord ++ tailWord_686702).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_686702).length < 2 ^ (prefixWord ++ tailWord_686702).sum := by decide
  have hdescent : baseEnd_686702 < baseStart_686702 := by decide
  rcases family_descends (prefixWord ++ tailWord_686702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_686790 : List Nat := [6, 1, 2, 1, 3, 1, 1, 1, 1, 2, 4]
def baseStart_686790 : Nat := 118140960795 + 686790 * 2 ^ 59
def prefixEnd_686790 : Nat := 4983230072969 + 3 ^ 40 * 686790 * 2
def baseEnd_686790 : Nat := 352653378701473164666517

theorem tailTrace_686790 : CollatzResearch.WordTrace tailWord_686790 prefixEnd_686790 352653378701473164666517 := by
  unfold tailWord_686790
  simp only [CollatzResearch.WordTrace]
  refine ⟨782790286933893726213307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 16699526121256399492550549 782790286933893726213307)
  ·
    refine ⟨1174185430400840589319961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 782790286933893726213307 1174185430400840589319961)
    ·
      refine ⟨880639072800630441989971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1174185430400840589319961 880639072800630441989971)
      ·
        refine ⟨1320958609200945662984957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 880639072800630441989971 1320958609200945662984957)
        ·
          refine ⟨495359478450354623619359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1320958609200945662984957 495359478450354623619359)
          ·
            refine ⟨743039217675531935429039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 495359478450354623619359 743039217675531935429039)
            ·
              refine ⟨1114558826513297903143559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 743039217675531935429039 1114558826513297903143559)
              ·
                refine ⟨1671838239769946854715339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1114558826513297903143559 1671838239769946854715339)
                ·
                  refine ⟨2507757359654920282073009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1671838239769946854715339 2507757359654920282073009)
                  ·
                    refine ⟨1880818019741190211554757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2507757359654920282073009 1880818019741190211554757)
                    ·
                      refine ⟨352653378701473164666517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1880818019741190211554757 352653378701473164666517)
                      ·
                        rfl

theorem cell23_686790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 3, 1, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 3, 1, 1, 1, 1, 2, 4].length) (baseStart_686790 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_686790 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_686790 prefixEnd_686790 := by exact prefixLift 686790
  have htrace : WordTrace (prefixWord ++ tailWord_686790) baseStart_686790 baseEnd_686790 := by
    simpa [prefixWord, tailWord_686790, baseEnd_686790] using wordTrace_append hprefix tailTrace_686790
  have hstable : (prefixWord ++ tailWord_686790).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_686790).length < 2 ^ (prefixWord ++ tailWord_686790).sum := by decide
  have hdescent : baseEnd_686790 < baseStart_686790 := by decide
  rcases family_descends (prefixWord ++ tailWord_686790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_686850 : List Nat := [3, 4, 1, 1, 1, 2, 4, 1, 2, 2, 2]
def baseStart_686850 : Nat := 118140960795 + 686850 * 2 ^ 59
def prefixEnd_686850 : Nat := 4983230072969 + 3 ^ 40 * 686850 * 2
def baseEnd_686850 : Nat := 352684187540742929916241

theorem tailTrace_686850 : CollatzResearch.WordTrace tailWord_686850 prefixEnd_686850 352684187540742929916241 := by
  unfold tailWord_686850
  simp only [CollatzResearch.WordTrace]
  refine ⟨6262869390416807371502501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16700985041111486324006669 6262869390416807371502501)
  ·
    refine ⟨1174288010703151382156719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6262869390416807371502501 1174288010703151382156719)
    ·
      refine ⟨1761432016054727073235079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1174288010703151382156719 1761432016054727073235079)
      ·
        refine ⟨2642148024082090609852619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1761432016054727073235079 2642148024082090609852619)
        ·
          refine ⟨3963222036123135914778929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2642148024082090609852619 3963222036123135914778929)
          ·
            refine ⟨2972416527092351936084197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3963222036123135914778929 2972416527092351936084197)
            ·
              refine ⟨557328098829815988015787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2972416527092351936084197 557328098829815988015787)
              ·
                refine ⟨835992148244723982023681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 557328098829815988015787 835992148244723982023681)
                ·
                  refine ⟨626994111183542986517761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 835992148244723982023681 626994111183542986517761)
                  ·
                    refine ⟨470245583387657239888321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 626994111183542986517761 470245583387657239888321)
                    ·
                      refine ⟨352684187540742929916241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 470245583387657239888321 352684187540742929916241)
                      ·
                        rfl

theorem cell23_686850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 4, 1, 2, 2, 2].length) (baseStart_686850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_686850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_686850 prefixEnd_686850 := by exact prefixLift 686850
  have htrace : WordTrace (prefixWord ++ tailWord_686850) baseStart_686850 baseEnd_686850 := by
    simpa [prefixWord, tailWord_686850, baseEnd_686850] using wordTrace_append hprefix tailTrace_686850
  have hstable : (prefixWord ++ tailWord_686850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_686850).length < 2 ^ (prefixWord ++ tailWord_686850).sum := by decide
  have hdescent : baseEnd_686850 < baseStart_686850 := by decide
  rcases family_descends (prefixWord ++ tailWord_686850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_686852 : List Nat := [2, 3, 2, 2, 1, 1, 1, 2, 4, 5]
def baseStart_686852 : Nat := 118140960795 + 686852 * 2 ^ 59
def prefixEnd_686852 : Nat := 4983230072969 + 3 ^ 40 * 686852 * 2
def baseEnd_686852 : Nat := 117561738167350640697077

theorem tailTrace_686852 : CollatzResearch.WordTrace tailWord_686852 prefixEnd_686852 117561738167350640697077 := by
  unfold tailWord_686852
  simp only [CollatzResearch.WordTrace]
  refine ⟨12525775253829991913791405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16701033671773322551721873 12525775253829991913791405)
  ·
    refine ⟨4697165720186246967671777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12525775253829991913791405 4697165720186246967671777)
    ·
      refine ⟨3522874290139685225753833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4697165720186246967671777 3522874290139685225753833)
      ·
        refine ⟨2642155717604763919315375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3522874290139685225753833 2642155717604763919315375)
        ·
          refine ⟨3963233576407145878973063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2642155717604763919315375 3963233576407145878973063)
          ·
            refine ⟨5944850364610718818459595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3963233576407145878973063 5944850364610718818459595)
            ·
              refine ⟨8917275546916078227689393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5944850364610718818459595 8917275546916078227689393)
              ·
                refine ⟨6687956660187058670767045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8917275546916078227689393 6687956660187058670767045)
                ·
                  refine ⟨1253991873785073500768821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6687956660187058670767045 1253991873785073500768821)
                  ·
                    refine ⟨117561738167350640697077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1253991873785073500768821 117561738167350640697077)
                    ·
                      rfl

theorem cell23_686852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 1, 2, 4, 5].length) (baseStart_686852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_686852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_686852 prefixEnd_686852 := by exact prefixLift 686852
  have htrace : WordTrace (prefixWord ++ tailWord_686852) baseStart_686852 baseEnd_686852 := by
    simpa [prefixWord, tailWord_686852, baseEnd_686852] using wordTrace_append hprefix tailTrace_686852
  have hstable : (prefixWord ++ tailWord_686852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_686852).length < 2 ^ (prefixWord ++ tailWord_686852).sum := by decide
  have hdescent : baseEnd_686852 < baseStart_686852 := by decide
  rcases family_descends (prefixWord ++ tailWord_686852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_686865 : List Nat := [1, 2, 2, 1, 1, 3, 2, 1, 2, 8]
def baseStart_686865 : Nat := 118140960795 + 686865 * 2 ^ 59
def prefixEnd_686865 : Nat := 4983230072969 + 3 ^ 40 * 686865 * 2
def baseEnd_686865 : Nat := 117563963250186790409557

theorem tailTrace_686865 : CollatzResearch.WordTrace tailWord_686865 prefixEnd_686865 117563963250186790409557 := by
  unfold tailWord_686865
  simp only [CollatzResearch.WordTrace]
  refine ⟨25052024656612887047806049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16701349771075258031870699 25052024656612887047806049)
  ·
    refine ⟨18789018492459665285854537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25052024656612887047806049 18789018492459665285854537)
    ·
      refine ⟨14091763869344748964390903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18789018492459665285854537 14091763869344748964390903)
      ·
        refine ⟨21137645804017123446586355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14091763869344748964390903 21137645804017123446586355)
        ·
          refine ⟨31706468706025685169879533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21137645804017123446586355 31706468706025685169879533)
          ·
            refine ⟨11889925764759631938704825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31706468706025685169879533 11889925764759631938704825)
            ·
              refine ⟨8917444323569723954028619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11889925764759631938704825 8917444323569723954028619)
              ·
                refine ⟨13376166485354585931042929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8917444323569723954028619 13376166485354585931042929)
                ·
                  refine ⟨10032124864015939448282197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13376166485354585931042929 10032124864015939448282197)
                  ·
                    refine ⟨117563963250186790409557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 10032124864015939448282197 117563963250186790409557)
                    ·
                      rfl

theorem cell23_686865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 8].length) (baseStart_686865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_686865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_686865 prefixEnd_686865 := by exact prefixLift 686865
  have htrace : WordTrace (prefixWord ++ tailWord_686865) baseStart_686865 baseEnd_686865 := by
    simpa [prefixWord, tailWord_686865, baseEnd_686865] using wordTrace_append hprefix tailTrace_686865
  have hstable : (prefixWord ++ tailWord_686865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_686865).length < 2 ^ (prefixWord ++ tailWord_686865).sum := by decide
  have hdescent : baseEnd_686865 < baseStart_686865 := by decide
  rcases family_descends (prefixWord ++ tailWord_686865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_686875 : List Nat := [1, 1, 1, 1, 1, 1, 4, 1, 4, 3, 5]
def baseStart_686875 : Nat := 118140960795 + 686875 * 2 ^ 59
def prefixEnd_686875 : Nat := 4983230072969 + 3 ^ 40 * 686875 * 2
def baseEnd_686875 : Nat := 352697024557105332103625

theorem tailTrace_686875 : CollatzResearch.WordTrace tailWord_686875 prefixEnd_686875 352697024557105332103625 := by
  unfold tailWord_686875
  simp only [CollatzResearch.WordTrace]
  refine ⟨25052389386576658755670079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16701592924384439170446719 25052389386576658755670079)
  ·
    refine ⟨37578584079864988133505119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25052389386576658755670079 37578584079864988133505119)
    ·
      refine ⟨56367876119797482200257679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37578584079864988133505119 56367876119797482200257679)
      ·
        refine ⟨84551814179696223300386519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56367876119797482200257679 84551814179696223300386519)
        ·
          refine ⟨126827721269544334950579779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84551814179696223300386519 126827721269544334950579779)
          ·
            refine ⟨190241581904316502425869669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 126827721269544334950579779 190241581904316502425869669)
            ·
              refine ⟨35670296607059344204850563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 190241581904316502425869669 35670296607059344204850563)
              ·
                refine ⟨53505444910589016307275845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35670296607059344204850563 53505444910589016307275845)
                ·
                  refine ⟨10032270920735440557614221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 53505444910589016307275845 10032270920735440557614221)
                  ·
                    refine ⟨3762101595275790209105333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10032270920735440557614221 3762101595275790209105333)
                    ·
                      refine ⟨352697024557105332103625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3762101595275790209105333 352697024557105332103625)
                      ·
                        rfl

theorem cell23_686875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 1, 4, 3, 5].length) (baseStart_686875 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_686875 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_686875 prefixEnd_686875 := by exact prefixLift 686875
  have htrace : WordTrace (prefixWord ++ tailWord_686875) baseStart_686875 baseEnd_686875 := by
    simpa [prefixWord, tailWord_686875, baseEnd_686875] using wordTrace_append hprefix tailTrace_686875
  have hstable : (prefixWord ++ tailWord_686875).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_686875).length < 2 ^ (prefixWord ++ tailWord_686875).sum := by decide
  have hdescent : baseEnd_686875 < baseStart_686875 := by decide
  rcases family_descends (prefixWord ++ tailWord_686875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_686890 : List Nat := [3, 1, 4, 3, 1, 2, 2, 2, 5]
def baseStart_686890 : Nat := 118140960795 + 686890 * 2 ^ 59
def prefixEnd_686890 : Nat := 4983230072969 + 3 ^ 40 * 686890 * 2
def baseEnd_686890 : Nat := 39189414085213641490673

theorem tailTrace_686890 : CollatzResearch.WordTrace tailWord_686890 prefixEnd_686890 39189414085213641490673 := by
  unfold tailWord_686890
  simp only [CollatzResearch.WordTrace]
  refine ⟨6263234120380579079366531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16701957654348210878310749 6263234120380579079366531)
  ·
    refine ⟨9394851180570868619049797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6263234120380579079366531 9394851180570868619049797)
    ·
      refine ⟨1761534596357037866071837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9394851180570868619049797 1761534596357037866071837)
      ·
        refine ⟨660575473633889199776939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1761534596357037866071837 660575473633889199776939)
        ·
          refine ⟨990863210450833799665409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 660575473633889199776939 990863210450833799665409)
          ·
            refine ⟨743147407838125349749057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 990863210450833799665409 743147407838125349749057)
            ·
              refine ⟨557360555878594012311793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 743147407838125349749057 557360555878594012311793)
              ·
                refine ⟨418020416908945509233845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 557360555878594012311793 418020416908945509233845)
                ·
                  refine ⟨39189414085213641490673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 418020416908945509233845 39189414085213641490673)
                  ·
                    rfl

theorem cell23_686890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 2, 2, 2, 5].length) (baseStart_686890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_686890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_686890 prefixEnd_686890 := by exact prefixLift 686890
  have htrace : WordTrace (prefixWord ++ tailWord_686890) baseStart_686890 baseEnd_686890 := by
    simpa [prefixWord, tailWord_686890, baseEnd_686890] using wordTrace_append hprefix tailTrace_686890
  have hstable : (prefixWord ++ tailWord_686890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_686890).length < 2 ^ (prefixWord ++ tailWord_686890).sum := by decide
  have hdescent : baseEnd_686890 < baseStart_686890 := by decide
  rcases family_descends (prefixWord ++ tailWord_686890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_686906 : List Nat := [3, 1, 1, 1, 6, 1, 1, 1, 2, 4, 2]
def baseStart_686906 : Nat := 118140960795 + 686906 * 2 ^ 59
def prefixEnd_686906 : Nat := 4983230072969 + 3 ^ 40 * 686906 * 2
def baseEnd_686906 : Nat := 352712942457394710815983

theorem tailTrace_686906 : CollatzResearch.WordTrace tailWord_686906 prefixEnd_686906 352712942457394710815983 := by
  unfold tailWord_686906
  simp only [CollatzResearch.WordTrace]
  refine ⟨6263380012366087762512143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16702346699642900700032381 6263380012366087762512143)
  ·
    refine ⟨9395070018549131643768215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6263380012366087762512143 9395070018549131643768215)
    ·
      refine ⟨14092605027823697465652323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9395070018549131643768215 14092605027823697465652323)
      ·
        refine ⟨21138907541735546198478485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14092605027823697465652323 21138907541735546198478485)
        ·
          refine ⟨990886291018853728053679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 21138907541735546198478485 990886291018853728053679)
          ·
            refine ⟨1486329436528280592080519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 990886291018853728053679 1486329436528280592080519)
            ·
              refine ⟨2229494154792420888120779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1486329436528280592080519 2229494154792420888120779)
              ·
                refine ⟨3344241232188631332181169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2229494154792420888120779 3344241232188631332181169)
                ·
                  refine ⟨2508180924141473499135877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3344241232188631332181169 2508180924141473499135877)
                  ·
                    refine ⟨470283923276526281087977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2508180924141473499135877 470283923276526281087977)
                    ·
                      refine ⟨352712942457394710815983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 470283923276526281087977 352712942457394710815983)
                      ·
                        rfl

theorem cell23_686906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 1, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 1, 1, 1, 2, 4, 2].length) (baseStart_686906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_686906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_686906 prefixEnd_686906 := by exact prefixLift 686906
  have htrace : WordTrace (prefixWord ++ tailWord_686906) baseStart_686906 baseEnd_686906 := by
    simpa [prefixWord, tailWord_686906, baseEnd_686906] using wordTrace_append hprefix tailTrace_686906
  have hstable : (prefixWord ++ tailWord_686906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_686906).length < 2 ^ (prefixWord ++ tailWord_686906).sum := by decide
  have hdescent : baseEnd_686906 < baseStart_686906 := by decide
  rcases family_descends (prefixWord ++ tailWord_686906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_686922 : List Nat := [3, 1, 2, 1, 1, 1, 2, 1, 1, 7, 3]
def baseStart_686922 : Nat := 118140960795 + 686922 * 2 ^ 59
def prefixEnd_686922 : Nat := 4983230072969 + 3 ^ 40 * 686922 * 2
def baseEnd_686922 : Nat := 352721158147866648215909

theorem tailTrace_686922 : CollatzResearch.WordTrace tailWord_686922 prefixEnd_686922 352721158147866648215909 := by
  unfold tailWord_686922
  simp only [CollatzResearch.WordTrace]
  refine ⟨6263525904351596445657755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16702735744937590521754013 6263525904351596445657755)
  ·
    refine ⟨9395288856527394668486633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6263525904351596445657755 9395288856527394668486633)
    ·
      refine ⟨7046466642395546001364975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9395288856527394668486633 7046466642395546001364975)
      ·
        refine ⟨10569699963593319002047463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7046466642395546001364975 10569699963593319002047463)
        ·
          refine ⟨15854549945389978503071195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10569699963593319002047463 15854549945389978503071195)
          ·
            refine ⟨23781824918084967754606793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15854549945389978503071195 23781824918084967754606793)
            ·
              refine ⟨17836368688563725815955095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23781824918084967754606793 17836368688563725815955095)
              ·
                refine ⟨26754553032845588723932643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17836368688563725815955095 26754553032845588723932643)
                ·
                  refine ⟨40131829549268383085898965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26754553032845588723932643 40131829549268383085898965)
                  ·
                    refine ⟨940589755060977728575757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 40131829549268383085898965 940589755060977728575757)
                    ·
                      refine ⟨352721158147866648215909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 940589755060977728575757 352721158147866648215909)
                      ·
                        rfl

theorem cell23_686922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 1, 1, 7, 3].length) (baseStart_686922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_686922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_686922 prefixEnd_686922 := by exact prefixLift 686922
  have htrace : WordTrace (prefixWord ++ tailWord_686922) baseStart_686922 baseEnd_686922 := by
    simpa [prefixWord, tailWord_686922, baseEnd_686922] using wordTrace_append hprefix tailTrace_686922
  have hstable : (prefixWord ++ tailWord_686922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_686922).length < 2 ^ (prefixWord ++ tailWord_686922).sum := by decide
  have hdescent : baseEnd_686922 < baseStart_686922 := by decide
  rcases family_descends (prefixWord ++ tailWord_686922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_686956 : List Nat := [2, 2, 1, 1, 4, 1, 4, 1, 3, 1, 3]
def baseStart_686956 : Nat := 118140960795 + 686956 * 2 ^ 59
def prefixEnd_686956 : Nat := 4983230072969 + 3 ^ 40 * 686956 * 2
def baseEnd_686956 : Nat := 352738616490119515190753

theorem tailTrace_686956 : CollatzResearch.WordTrace tailWord_686956 prefixEnd_686956 352738616490119515190753 := by
  unfold tailWord_686956
  simp only [CollatzResearch.WordTrace]
  refine ⟨12527671849641604794684361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16703562466188806392912481 12527671849641604794684361)
  ·
    refine ⟨9395753887231203596013271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12527671849641604794684361 9395753887231203596013271)
    ·
      refine ⟨14093630830846805394019907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9395753887231203596013271 14093630830846805394019907)
      ·
        refine ⟨21140446246270208091029861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14093630830846805394019907 21140446246270208091029861)
        ·
          refine ⟨3963833671175664017068099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21140446246270208091029861 3963833671175664017068099)
          ·
            refine ⟨5945750506763496025602149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3963833671175664017068099 5945750506763496025602149)
            ·
              refine ⟨1114828220018155504800403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5945750506763496025602149 1114828220018155504800403)
              ·
                refine ⟨1672242330027233257200605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1114828220018155504800403 1672242330027233257200605)
                ·
                  refine ⟨627090873760212471450227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1672242330027233257200605 627090873760212471450227)
                  ·
                    refine ⟨940636310640318707175341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 627090873760212471450227 940636310640318707175341)
                    ·
                      refine ⟨352738616490119515190753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 940636310640318707175341 352738616490119515190753)
                      ·
                        rfl

theorem cell23_686956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 3, 1, 3].length) (baseStart_686956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_686956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_686956 prefixEnd_686956 := by exact prefixLift 686956
  have htrace : WordTrace (prefixWord ++ tailWord_686956) baseStart_686956 baseEnd_686956 := by
    simpa [prefixWord, tailWord_686956, baseEnd_686956] using wordTrace_append hprefix tailTrace_686956
  have hstable : (prefixWord ++ tailWord_686956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_686956).length < 2 ^ (prefixWord ++ tailWord_686956).sum := by decide
  have hdescent : baseEnd_686956 < baseStart_686956 := by decide
  rcases family_descends (prefixWord ++ tailWord_686956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_686979 : List Nat := [1, 1, 1, 3, 4, 1, 1, 1, 2, 6, 2]
def baseStart_686979 : Nat := 118140960795 + 686979 * 2 ^ 59
def prefixEnd_686979 : Nat := 4983230072969 + 3 ^ 40 * 686979 * 2
def baseEnd_686979 : Nat := 352750426545172925203147

theorem tailTrace_686979 : CollatzResearch.WordTrace tailWord_686979 prefixEnd_686979 352750426545172925203147 := by
  unfold tailWord_686979
  simp only [CollatzResearch.WordTrace]
  refine ⟨25056182578199884517455991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16704121718799923011637327 25056182578199884517455991)
  ·
    refine ⟨37584273867299826776183987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25056182578199884517455991 37584273867299826776183987)
    ·
      refine ⟨56376410800949740164275981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37584273867299826776183987 56376410800949740164275981)
      ·
        refine ⟨21141154050356152561603493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 56376410800949740164275981 21141154050356152561603493)
        ·
          refine ⟨3963966384441778605300655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21141154050356152561603493 3963966384441778605300655)
          ·
            refine ⟨5945949576662667907950983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3963966384441778605300655 5945949576662667907950983)
            ·
              refine ⟨8918924364994001861926475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5945949576662667907950983 8918924364994001861926475)
              ·
                refine ⟨13378386547491002792889713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8918924364994001861926475 13378386547491002792889713)
                ·
                  refine ⟨10033789910618252094667285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13378386547491002792889713 10033789910618252094667285)
                  ·
                    refine ⟨470333902060230566937529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10033789910618252094667285 470333902060230566937529)
                    ·
                      refine ⟨352750426545172925203147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 470333902060230566937529 352750426545172925203147)
                      ·
                        rfl

theorem cell23_686979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 1, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 1, 1, 2, 6, 2].length) (baseStart_686979 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_686979 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_686979 prefixEnd_686979 := by exact prefixLift 686979
  have htrace : WordTrace (prefixWord ++ tailWord_686979) baseStart_686979 baseEnd_686979 := by
    simpa [prefixWord, tailWord_686979, baseEnd_686979] using wordTrace_append hprefix tailTrace_686979
  have hstable : (prefixWord ++ tailWord_686979).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_686979).length < 2 ^ (prefixWord ++ tailWord_686979).sum := by decide
  have hdescent : baseEnd_686979 < baseStart_686979 := by decide
  rcases family_descends (prefixWord ++ tailWord_686979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_686996 : List Nat := [2, 4, 2, 1, 1, 1, 1, 5, 1, 1, 4]
def baseStart_686996 : Nat := 118140960795 + 686996 * 2 ^ 59
def prefixEnd_686996 : Nat := 4983230072969 + 3 ^ 40 * 686996 * 2
def baseEnd_686996 : Nat := 352759155716299358690569

theorem tailTrace_686996 : CollatzResearch.WordTrace tailWord_686996 prefixEnd_686996 352759155716299358690569 := by
  unfold tailWord_686996
  simp only [CollatzResearch.WordTrace]
  refine ⟨12528401309569148210412421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16704535079425530947216561 12528401309569148210412421)
  ·
    refine ⟨2349075245544215289452329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12528401309569148210412421 2349075245544215289452329)
    ·
      refine ⟨1761806434158161467089247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2349075245544215289452329 1761806434158161467089247)
      ·
        refine ⟨2642709651237242200633871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1761806434158161467089247 2642709651237242200633871)
        ·
          refine ⟨3964064476855863300950807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2642709651237242200633871 3964064476855863300950807)
          ·
            refine ⟨5946096715283794951426211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3964064476855863300950807 5946096715283794951426211)
            ·
              refine ⟨8919145072925692427139317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5946096715283794951426211 8919145072925692427139317)
              ·
                refine ⟨836169850586783665044311, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8919145072925692427139317 836169850586783665044311)
                ·
                  refine ⟨1254254775880175497566467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 836169850586783665044311 1254254775880175497566467)
                  ·
                    refine ⟨1881382163820263246349701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1254254775880175497566467 1881382163820263246349701)
                    ·
                      refine ⟨352759155716299358690569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1881382163820263246349701 352759155716299358690569)
                      ·
                        rfl

theorem cell23_686996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 1, 5, 1, 1, 4].length) (baseStart_686996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_686996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_686996 prefixEnd_686996 := by exact prefixLift 686996
  have htrace : WordTrace (prefixWord ++ tailWord_686996) baseStart_686996 baseEnd_686996 := by
    simpa [prefixWord, tailWord_686996, baseEnd_686996] using wordTrace_append hprefix tailTrace_686996
  have hstable : (prefixWord ++ tailWord_686996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_686996).length < 2 ^ (prefixWord ++ tailWord_686996).sum := by decide
  have hdescent : baseEnd_686996 < baseStart_686996 := by decide
  rcases family_descends (prefixWord ++ tailWord_686996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_686999 : List Nat := [1, 1, 3, 3, 1, 2, 4, 1, 1, 1, 5]
def baseStart_686999 : Nat := 118140960795 + 686999 * 2 ^ 59
def prefixEnd_686999 : Nat := 4983230072969 + 3 ^ 40 * 686999 * 2
def baseEnd_686999 : Nat := 352760696158262846953055

theorem tailTrace_686999 : CollatzResearch.WordTrace tailWord_686999 prefixEnd_686999 352760696158262846953055 := by
  unfold tailWord_686999
  simp only [CollatzResearch.WordTrace]
  refine ⟨25056912038127427933184051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16704608025418285288789367 25056912038127427933184051)
  ·
    refine ⟨37585368057191141899776077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25056912038127427933184051 37585368057191141899776077)
    ·
      refine ⟨14094513021446678212416029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37585368057191141899776077 14094513021446678212416029)
      ·
        refine ⟨5285442383042504329656011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14094513021446678212416029 5285442383042504329656011)
        ·
          refine ⟨7928163574563756494484017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5285442383042504329656011 7928163574563756494484017)
          ·
            refine ⟨5946122680922817370863013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7928163574563756494484017 5946122680922817370863013)
            ·
              refine ⟨1114898002673028257036815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5946122680922817370863013 1114898002673028257036815)
              ·
                refine ⟨1672347004009542385555223, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1114898002673028257036815 1672347004009542385555223)
                ·
                  refine ⟨2508520506014313578332835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1672347004009542385555223 2508520506014313578332835)
                  ·
                    refine ⟨3762780759021470367499253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2508520506014313578332835 3762780759021470367499253)
                    ·
                      refine ⟨352760696158262846953055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3762780759021470367499253 352760696158262846953055)
                      ·
                        rfl

theorem cell23_686999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 4, 1, 1, 1, 5].length) (baseStart_686999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_686999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_686999 prefixEnd_686999 := by exact prefixLift 686999
  have htrace : WordTrace (prefixWord ++ tailWord_686999) baseStart_686999 baseEnd_686999 := by
    simpa [prefixWord, tailWord_686999, baseEnd_686999] using wordTrace_append hprefix tailTrace_686999
  have hstable : (prefixWord ++ tailWord_686999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_686999).length < 2 ^ (prefixWord ++ tailWord_686999).sum := by decide
  have hdescent : baseEnd_686999 < baseStart_686999 := by decide
  rcases family_descends (prefixWord ++ tailWord_686999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_687009 : List Nat := [1, 2, 3, 4, 1, 1, 1, 2, 1, 1, 6]
def baseStart_687009 : Nat := 118140960795 + 687009 * 2 ^ 59
def prefixEnd_687009 : Nat := 4983230072969 + 3 ^ 40 * 687009 * 2
def baseEnd_687009 : Nat := 352765830964807807828009

theorem tailTrace_687009 : CollatzResearch.WordTrace tailWord_687009 prefixEnd_687009 352765830964807807828009 := by
  unfold tailWord_687009
  simp only [CollatzResearch.WordTrace]
  refine ⟨25057276768091199641048081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16704851178727466427365387 25057276768091199641048081)
  ·
    refine ⟨18792957576068399730786061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25057276768091199641048081 18792957576068399730786061)
    ·
      refine ⟨7047359091025649899044773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18792957576068399730786061 7047359091025649899044773)
      ·
        refine ⟨1321379829567309356070895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7047359091025649899044773 1321379829567309356070895)
        ·
          refine ⟨1982069744350964034106343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1321379829567309356070895 1982069744350964034106343)
          ·
            refine ⟨2973104616526446051159515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1982069744350964034106343 2973104616526446051159515)
            ·
              refine ⟨4459656924789669076739273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2973104616526446051159515 4459656924789669076739273)
              ·
                refine ⟨3344742693592251807554455, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4459656924789669076739273 3344742693592251807554455)
                ·
                  refine ⟨5017114040388377711331683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3344742693592251807554455 5017114040388377711331683)
                  ·
                    refine ⟨7525671060582566566997525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5017114040388377711331683 7525671060582566566997525)
                    ·
                      refine ⟨352765830964807807828009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 7525671060582566566997525 352765830964807807828009)
                      ·
                        rfl

theorem cell23_687009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 1, 2, 1, 1, 6].length) (baseStart_687009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_687009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_687009 prefixEnd_687009 := by exact prefixLift 687009
  have htrace : WordTrace (prefixWord ++ tailWord_687009) baseStart_687009 baseEnd_687009 := by
    simpa [prefixWord, tailWord_687009, baseEnd_687009] using wordTrace_append hprefix tailTrace_687009
  have hstable : (prefixWord ++ tailWord_687009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_687009).length < 2 ^ (prefixWord ++ tailWord_687009).sum := by decide
  have hdescent : baseEnd_687009 < baseStart_687009 := by decide
  rcases family_descends (prefixWord ++ tailWord_687009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_687033 : List Nat := [1, 2, 1, 4, 2, 4, 1, 2, 1, 2, 3]
def baseStart_687033 : Nat := 118140960795 + 687033 * 2 ^ 59
def prefixEnd_687033 : Nat := 4983230072969 + 3 ^ 40 * 687033 * 2
def baseEnd_687033 : Nat := 352778154500515713927899

theorem tailTrace_687033 : CollatzResearch.WordTrace tailWord_687033 prefixEnd_687033 352778154500515713927899 := by
  unfold tailWord_687033
  simp only [CollatzResearch.WordTrace]
  refine ⟨25058152120004251739921753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16705434746669501159947835 25058152120004251739921753)
  ·
    refine ⟨18793614090003188804941315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25058152120004251739921753 18793614090003188804941315)
    ·
      refine ⟨28190421135004783207411973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18793614090003188804941315 28190421135004783207411973)
      ·
        refine ⟨5285703962813396851389745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 28190421135004783207411973 5285703962813396851389745)
        ·
          refine ⟨3964277972110047638542309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5285703962813396851389745 3964277972110047638542309)
          ·
            refine ⟨743302119770633932226683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3964277972110047638542309 743302119770633932226683)
            ·
              refine ⟨1114953179655950898340025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 743302119770633932226683 1114953179655950898340025)
              ·
                refine ⟨836214884741963173755019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1114953179655950898340025 836214884741963173755019)
                ·
                  refine ⟨1254322327112944760632529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 836214884741963173755019 1254322327112944760632529)
                  ·
                    refine ⟨940741745334708570474397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1254322327112944760632529 940741745334708570474397)
                    ·
                      refine ⟨352778154500515713927899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 940741745334708570474397 352778154500515713927899)
                      ·
                        rfl

theorem cell23_687033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 4, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 4, 1, 2, 1, 2, 3].length) (baseStart_687033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_687033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_687033 prefixEnd_687033 := by exact prefixLift 687033
  have htrace : WordTrace (prefixWord ++ tailWord_687033) baseStart_687033 baseEnd_687033 := by
    simpa [prefixWord, tailWord_687033, baseEnd_687033] using wordTrace_append hprefix tailTrace_687033
  have hstable : (prefixWord ++ tailWord_687033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_687033).length < 2 ^ (prefixWord ++ tailWord_687033).sum := by decide
  have hdescent : baseEnd_687033 < baseStart_687033 := by decide
  rcases family_descends (prefixWord ++ tailWord_687033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_687053 : List Nat := [1, 6, 3, 1, 1, 11]
def baseStart_687053 : Nat := 118140960795 + 687053 * 2 ^ 59
def prefixEnd_687053 : Nat := 4983230072969 + 3 ^ 40 * 687053 * 2
def baseEnd_687053 : Nat := 1451804214459282451349

theorem tailTrace_687053 : CollatzResearch.WordTrace tailWord_687053 prefixEnd_687053 1451804214459282451349 := by
  unfold tailWord_687053
  simp only [CollatzResearch.WordTrace]
  refine ⟨25058881579931795155649813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16705921053287863437099875 25058881579931795155649813)
  ·
    refine ⟨1174635074059302897921085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 25058881579931795155649813 1174635074059302897921085)
    ·
      refine ⟨440488152772238586720407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1174635074059302897921085 440488152772238586720407)
      ·
        refine ⟨660732229158357880080611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 440488152772238586720407 660732229158357880080611)
        ·
          refine ⟨991098343737536820120917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 660732229158357880080611 991098343737536820120917)
          ·
            refine ⟨1451804214459282451349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 991098343737536820120917 1451804214459282451349)
            ·
              rfl

theorem cell23_687053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 11].length) (baseStart_687053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_687053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_687053 prefixEnd_687053 := by exact prefixLift 687053
  have htrace : WordTrace (prefixWord ++ tailWord_687053) baseStart_687053 baseEnd_687053 := by
    simpa [prefixWord, tailWord_687053, baseEnd_687053] using wordTrace_append hprefix tailTrace_687053
  have hstable : (prefixWord ++ tailWord_687053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_687053).length < 2 ^ (prefixWord ++ tailWord_687053).sum := by decide
  have hdescent : baseEnd_687053 < baseStart_687053 := by decide
  rcases family_descends (prefixWord ++ tailWord_687053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_687079 : List Nat := [1, 1, 5, 2, 2, 1, 1, 1, 1, 8]
def baseStart_687079 : Nat := 118140960795 + 687079 * 2 ^ 59
def prefixEnd_687079 : Nat := 4983230072969 + 3 ^ 40 * 687079 * 2
def baseEnd_687079 : Nat := 117600591536874177984229

theorem tailTrace_687079 : CollatzResearch.WordTrace tailWord_687079 prefixEnd_687079 117600591536874177984229 := by
  unfold tailWord_687079
  simp only [CollatzResearch.WordTrace]
  refine ⟨25059829877837601596096291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16706553251891734397397527 25059829877837601596096291)
  ·
    refine ⟨37589744816756402394144437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25059829877837601596096291 37589744816756402394144437)
    ·
      refine ⟨3524038576570912724451041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 37589744816756402394144437 3524038576570912724451041)
      ·
        refine ⟨2643028932428184543338281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3524038576570912724451041 2643028932428184543338281)
        ·
          refine ⟨1982271699321138407503711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2643028932428184543338281 1982271699321138407503711)
          ·
            refine ⟨2973407548981707611255567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1982271699321138407503711 2973407548981707611255567)
            ·
              refine ⟨4460111323472561416883351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2973407548981707611255567 4460111323472561416883351)
              ·
                refine ⟨6690166985208842125325027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4460111323472561416883351 6690166985208842125325027)
                ·
                  refine ⟨10035250477813263187987541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6690166985208842125325027 10035250477813263187987541)
                  ·
                    refine ⟨117600591536874177984229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 10035250477813263187987541 117600591536874177984229)
                    ·
                      rfl

theorem cell23_687079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 1, 1, 1, 8].length) (baseStart_687079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_687079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_687079 prefixEnd_687079 := by exact prefixLift 687079
  have htrace : WordTrace (prefixWord ++ tailWord_687079) baseStart_687079 baseEnd_687079 := by
    simpa [prefixWord, tailWord_687079, baseEnd_687079] using wordTrace_append hprefix tailTrace_687079
  have hstable : (prefixWord ++ tailWord_687079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_687079).length < 2 ^ (prefixWord ++ tailWord_687079).sum := by decide
  have hdescent : baseEnd_687079 < baseStart_687079 := by decide
  rcases family_descends (prefixWord ++ tailWord_687079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_687137 : List Nat := [1, 2, 3, 2, 3, 2, 3, 1, 2, 2, 2]
def baseStart_687137 : Nat := 118140960795 + 687137 * 2 ^ 59
def prefixEnd_687137 : Nat := 4983230072969 + 3 ^ 40 * 687137 * 2
def baseEnd_687137 : Nat := 352831556488583307027421

theorem tailTrace_687137 : CollatzResearch.WordTrace tailWord_687137 prefixEnd_687137 352831556488583307027421 := by
  unfold tailWord_687137
  simp only [CollatzResearch.WordTrace]
  refine ⟨25061945311627477501707665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16707963541084985001138443 25061945311627477501707665)
  ·
    refine ⟨18796458983720608126280749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25061945311627477501707665 18796458983720608126280749)
    ·
      refine ⟨7048672118895228047355281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18796458983720608126280749 7048672118895228047355281)
      ·
        refine ⟨5286504089171421035516461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7048672118895228047355281 5286504089171421035516461)
        ·
          refine ⟨1982439033439282888318673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5286504089171421035516461 1982439033439282888318673)
          ·
            refine ⟨1486829275079462166239005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1982439033439282888318673 1486829275079462166239005)
            ·
              refine ⟨557560978154798312339627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1486829275079462166239005 557560978154798312339627)
              ·
                refine ⟨836341467232197468509441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 557560978154798312339627 836341467232197468509441)
                ·
                  refine ⟨627256100424148101382081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 836341467232197468509441 627256100424148101382081)
                  ·
                    refine ⟨470442075318111076036561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 627256100424148101382081 470442075318111076036561)
                    ·
                      refine ⟨352831556488583307027421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 470442075318111076036561 352831556488583307027421)
                      ·
                        rfl

theorem cell23_687137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 2, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 2, 3, 1, 2, 2, 2].length) (baseStart_687137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_687137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_687137 prefixEnd_687137 := by exact prefixLift 687137
  have htrace : WordTrace (prefixWord ++ tailWord_687137) baseStart_687137 baseEnd_687137 := by
    simpa [prefixWord, tailWord_687137, baseEnd_687137] using wordTrace_append hprefix tailTrace_687137
  have hstable : (prefixWord ++ tailWord_687137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_687137).length < 2 ^ (prefixWord ++ tailWord_687137).sum := by decide
  have hdescent : baseEnd_687137 < baseStart_687137 := by decide
  rcases family_descends (prefixWord ++ tailWord_687137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_687139 : List Nat := [1, 1, 1, 4, 3, 2, 1, 2, 1, 7]
def baseStart_687139 : Nat := 118140960795 + 687139 * 2 ^ 59
def prefixEnd_687139 : Nat := 4983230072969 + 3 ^ 40 * 687139 * 2
def baseEnd_687139 : Nat := 117610861149964099734137

theorem tailTrace_687139 : CollatzResearch.WordTrace tailWord_687139 prefixEnd_687139 117610861149964099734137 := by
  unfold tailWord_687139
  simp only [CollatzResearch.WordTrace]
  refine ⟨25062018257620231843280471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16708012171746821228853647 25062018257620231843280471)
  ·
    refine ⟨37593027386430347764920707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25062018257620231843280471 37593027386430347764920707)
    ·
      refine ⟨56389541079645521647381061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37593027386430347764920707 56389541079645521647381061)
      ·
        refine ⟨10573038952433535308883949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 56389541079645521647381061 10573038952433535308883949)
        ·
          refine ⟨3964889607162575740831481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10573038952433535308883949 3964889607162575740831481)
          ·
            refine ⟨2973667205371931805623611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3964889607162575740831481 2973667205371931805623611)
            ·
              refine ⟨4460500808057897708435417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2973667205371931805623611 4460500808057897708435417)
              ·
                refine ⟨3345375606043423281326563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4460500808057897708435417 3345375606043423281326563)
                ·
                  refine ⟨5018063409065134921989845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3345375606043423281326563 5018063409065134921989845)
                  ·
                    refine ⟨117610861149964099734137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 5018063409065134921989845 117610861149964099734137)
                    ·
                      rfl

theorem cell23_687139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 1, 2, 1, 7].length) (baseStart_687139 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_687139 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_687139 prefixEnd_687139 := by exact prefixLift 687139
  have htrace : WordTrace (prefixWord ++ tailWord_687139) baseStart_687139 baseEnd_687139 := by
    simpa [prefixWord, tailWord_687139, baseEnd_687139] using wordTrace_append hprefix tailTrace_687139
  have hstable : (prefixWord ++ tailWord_687139).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_687139).length < 2 ^ (prefixWord ++ tailWord_687139).sum := by decide
  have hdescent : baseEnd_687139 < baseStart_687139 := by decide
  rcases family_descends (prefixWord ++ tailWord_687139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_687176 : List Nat := [2, 1, 3, 1, 1, 1, 5, 2, 2, 1, 4]
def baseStart_687176 : Nat := 118140960795 + 687176 * 2 ^ 59
def prefixEnd_687176 : Nat := 4983230072969 + 3 ^ 40 * 687176 * 2
def baseEnd_687176 : Nat := 352851582234108654439741

theorem tailTrace_687176 : CollatzResearch.WordTrace tailWord_687176 prefixEnd_687176 352851582234108654439741 := by
  unfold tailWord_687176
  simp only [CollatzResearch.WordTrace]
  refine ⟨12531683879243093581188691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16708911838990791441584921 12531683879243093581188691)
  ·
    refine ⟨18797525818864640371783037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12531683879243093581188691 18797525818864640371783037)
    ·
      refine ⟨7049072182074240139418639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18797525818864640371783037 7049072182074240139418639)
      ·
        refine ⟨10573608273111360209127959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7049072182074240139418639 10573608273111360209127959)
        ·
          refine ⟨15860412409667040313691939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10573608273111360209127959 15860412409667040313691939)
          ·
            refine ⟨23790618614500560470537909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15860412409667040313691939 23790618614500560470537909)
            ·
              refine ⟨2230370495109427544112929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 23790618614500560470537909 2230370495109427544112929)
              ·
                refine ⟨1672777871332070658084697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2230370495109427544112929 1672777871332070658084697)
                ·
                  refine ⟨1254583403499052993563523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1672777871332070658084697 1254583403499052993563523)
                  ·
                    refine ⟨1881875105248579490345285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1254583403499052993563523 1881875105248579490345285)
                    ·
                      refine ⟨352851582234108654439741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1881875105248579490345285 352851582234108654439741)
                      ·
                        rfl

theorem cell23_687176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 5, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 5, 2, 2, 1, 4].length) (baseStart_687176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_687176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_687176 prefixEnd_687176 := by exact prefixLift 687176
  have htrace : WordTrace (prefixWord ++ tailWord_687176) baseStart_687176 baseEnd_687176 := by
    simpa [prefixWord, tailWord_687176, baseEnd_687176] using wordTrace_append hprefix tailTrace_687176
  have hstable : (prefixWord ++ tailWord_687176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_687176).length < 2 ^ (prefixWord ++ tailWord_687176).sum := by decide
  have hdescent : baseEnd_687176 < baseStart_687176 := by decide
  rcases family_descends (prefixWord ++ tailWord_687176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_687213 : List Nat := [1, 5, 1, 1, 2, 2, 1, 3, 2, 2, 3]
def baseStart_687213 : Nat := 118140960795 + 687213 * 2 ^ 59
def prefixEnd_687213 : Nat := 4983230072969 + 3 ^ 40 * 687213 * 2
def baseEnd_687213 : Nat := 352870581018325009677071

theorem tailTrace_687213 : CollatzResearch.WordTrace tailWord_687213 prefixEnd_687213 352870581018325009677071 := by
  unfold tailWord_687213
  simp only [CollatzResearch.WordTrace]
  refine ⟨25064717259352142481474293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16709811506234761654316195 25064717259352142481474293)
  ·
    refine ⟨2349817243064263357638215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 25064717259352142481474293 2349817243064263357638215)
    ·
      refine ⟨3524725864596395036457323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2349817243064263357638215 3524725864596395036457323)
      ·
        refine ⟨5287088796894592554685985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3524725864596395036457323 5287088796894592554685985)
        ·
          refine ⟨3965316597670944416014489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5287088796894592554685985 3965316597670944416014489)
          ·
            refine ⟨2973987448253208312010867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3965316597670944416014489 2973987448253208312010867)
            ·
              refine ⟨4460981172379812468016301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2973987448253208312010867 4460981172379812468016301)
              ·
                refine ⟨1672867939642429675506113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4460981172379812468016301 1672867939642429675506113)
                ·
                  refine ⟨1254650954731822256629585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1672867939642429675506113 1254650954731822256629585)
                  ·
                    refine ⟨940988216048866692472189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1254650954731822256629585 940988216048866692472189)
                    ·
                      refine ⟨352870581018325009677071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 940988216048866692472189 352870581018325009677071)
                      ·
                        rfl

theorem cell23_687213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 1, 3, 2, 2, 3].length) (baseStart_687213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_687213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_687213 prefixEnd_687213 := by exact prefixLift 687213
  have htrace : WordTrace (prefixWord ++ tailWord_687213) baseStart_687213 baseEnd_687213 := by
    simpa [prefixWord, tailWord_687213, baseEnd_687213] using wordTrace_append hprefix tailTrace_687213
  have hstable : (prefixWord ++ tailWord_687213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_687213).length < 2 ^ (prefixWord ++ tailWord_687213).sum := by decide
  have hdescent : baseEnd_687213 < baseStart_687213 := by decide
  rcases family_descends (prefixWord ++ tailWord_687213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_687233 : List Nat := [1, 2, 4, 2, 2, 2, 2, 2, 6]
def baseStart_687233 : Nat := 118140960795 + 687233 * 2 ^ 59
def prefixEnd_687233 : Nat := 4983230072969 + 3 ^ 40 * 687233 * 2
def baseEnd_687233 : Nat := 39208983403490547936331

theorem tailTrace_687233 : CollatzResearch.WordTrace tailWord_687233 prefixEnd_687233 39208983403490547936331 := by
  unfold tailWord_687233
  simp only [CollatzResearch.WordTrace]
  refine ⟨25065446719279685897202353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16710297812853123931468235 25065446719279685897202353)
  ·
    refine ⟨18799085039459764422901765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25065446719279685897202353 18799085039459764422901765)
    ·
      refine ⟨3524828444898705829294081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18799085039459764422901765 3524828444898705829294081)
      ·
        refine ⟨2643621333674029371970561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3524828444898705829294081 2643621333674029371970561)
        ·
          refine ⟨1982716000255522028977921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2643621333674029371970561 1982716000255522028977921)
          ·
            refine ⟨1487037000191641521733441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1982716000255522028977921 1487037000191641521733441)
            ·
              refine ⟨1115277750143731141300081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1487037000191641521733441 1115277750143731141300081)
              ·
                refine ⟨836458312607798355975061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1115277750143731141300081 836458312607798355975061)
                ·
                  refine ⟨39208983403490547936331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 836458312607798355975061 39208983403490547936331)
                  ·
                    rfl

theorem cell23_687233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 2, 2, 2, 6].length) (baseStart_687233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_687233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_687233 prefixEnd_687233 := by exact prefixLift 687233
  have htrace : WordTrace (prefixWord ++ tailWord_687233) baseStart_687233 baseEnd_687233 := by
    simpa [prefixWord, tailWord_687233, baseEnd_687233] using wordTrace_append hprefix tailTrace_687233
  have hstable : (prefixWord ++ tailWord_687233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_687233).length < 2 ^ (prefixWord ++ tailWord_687233).sum := by decide
  have hdescent : baseEnd_687233 < baseStart_687233 := by decide
  rcases family_descends (prefixWord ++ tailWord_687233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_687260 : List Nat := [2, 2, 3, 2, 1, 3, 1, 2, 3, 1, 3]
def baseStart_687260 : Nat := 118140960795 + 687260 * 2 ^ 59
def prefixEnd_687260 : Nat := 4983230072969 + 3 ^ 40 * 687260 * 2
def baseEnd_687260 : Nat := 352894714609086325789355

theorem tailTrace_687260 : CollatzResearch.WordTrace tailWord_687260 prefixEnd_687260 352894714609086325789355 := by
  unfold tailWord_687260
  simp only [CollatzResearch.WordTrace]
  refine ⟨12533215745090934754217617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16710954326787913005623489 12533215745090934754217617)
  ·
    refine ⟨9399911808818201065663213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12533215745090934754217617 9399911808818201065663213)
    ·
      refine ⟨3524966928306825399623705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9399911808818201065663213 3524966928306825399623705)
      ·
        refine ⟨2643725196230119049717779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3524966928306825399623705 2643725196230119049717779)
        ·
          refine ⟨3965587794345178574576669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2643725196230119049717779 3965587794345178574576669)
          ·
            refine ⟨1487095422879441965466251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3965587794345178574576669 1487095422879441965466251)
            ·
              refine ⟨2230643134319162948199377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1487095422879441965466251 2230643134319162948199377)
              ·
                refine ⟨1672982350739372211149533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2230643134319162948199377 1672982350739372211149533)
                ·
                  refine ⟨627368381527264579181075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1672982350739372211149533 627368381527264579181075)
                  ·
                    refine ⟨941052572290896868771613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 627368381527264579181075 941052572290896868771613)
                    ·
                      refine ⟨352894714609086325789355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 941052572290896868771613 352894714609086325789355)
                      ·
                        rfl

theorem cell23_687260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 3, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 3, 1, 2, 3, 1, 3].length) (baseStart_687260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_687260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_687260 prefixEnd_687260 := by exact prefixLift 687260
  have htrace : WordTrace (prefixWord ++ tailWord_687260) baseStart_687260 baseEnd_687260 := by
    simpa [prefixWord, tailWord_687260, baseEnd_687260] using wordTrace_append hprefix tailTrace_687260
  have hstable : (prefixWord ++ tailWord_687260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_687260).length < 2 ^ (prefixWord ++ tailWord_687260).sum := by decide
  have hdescent : baseEnd_687260 < baseStart_687260 := by decide
  rcases family_descends (prefixWord ++ tailWord_687260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_687310 : List Nat := [4, 1, 1, 1, 5, 2, 1, 1, 1, 6]
def baseStart_687310 : Nat := 118140960795 + 687310 * 2 ^ 59
def prefixEnd_687310 : Nat := 4983230072969 + 3 ^ 40 * 687310 * 2
def baseEnd_687310 : Nat := 117640129547270376721375

theorem tailTrace_687310 : CollatzResearch.WordTrace tailWord_687310 prefixEnd_687310 117640129547270376721375 := by
  unfold tailWord_687310
  simp only [CollatzResearch.WordTrace]
  refine ⟨3133531892500091005969423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 16712170093333818698503589 3133531892500091005969423)
  ·
    refine ⟨4700297838750136508954135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3133531892500091005969423 4700297838750136508954135)
    ·
      refine ⟨7050446758125204763431203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4700297838750136508954135 7050446758125204763431203)
      ·
        refine ⟨10575670137187807145146805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7050446758125204763431203 10575670137187807145146805)
        ·
          refine ⟨991469075361356919857513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 10575670137187807145146805 991469075361356919857513)
          ·
            refine ⟨743601806521017689893135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 991469075361356919857513 743601806521017689893135)
            ·
              refine ⟨1115402709781526534839703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 743601806521017689893135 1115402709781526534839703)
              ·
                refine ⟨1673104064672289802259555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1115402709781526534839703 1673104064672289802259555)
                ·
                  refine ⟨2509656097008434703389333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1673104064672289802259555 2509656097008434703389333)
                  ·
                    refine ⟨117640129547270376721375, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2509656097008434703389333 117640129547270376721375)
                    ·
                      rfl

theorem cell23_687310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 2, 1, 1, 1, 6].length) (baseStart_687310 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_687310 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_687310 prefixEnd_687310 := by exact prefixLift 687310
  have htrace : WordTrace (prefixWord ++ tailWord_687310) baseStart_687310 baseEnd_687310 := by
    simpa [prefixWord, tailWord_687310, baseEnd_687310] using wordTrace_append hprefix tailTrace_687310
  have hstable : (prefixWord ++ tailWord_687310).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_687310).length < 2 ^ (prefixWord ++ tailWord_687310).sum := by decide
  have hdescent : baseEnd_687310 < baseStart_687310 := by decide
  rcases family_descends (prefixWord ++ tailWord_687310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_687317 : List Nat := [1, 3, 2, 4, 1, 1, 2, 2, 3, 2, 2]
def baseStart_687317 : Nat := 118140960795 + 687317 * 2 ^ 59
def prefixEnd_687317 : Nat := 4983230072969 + 3 ^ 40 * 687317 * 2
def baseEnd_687317 : Nat := 352923983006392602776593

theorem tailTrace_687317 : CollatzResearch.WordTrace tailWord_687317 prefixEnd_687317 352923983006392602776593 := by
  unfold tailWord_687317
  simp only [CollatzResearch.WordTrace]
  refine ⟨25068510450975368243260205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16712340300650245495506803 25068510450975368243260205)
  ·
    refine ⟨9400691419115763091222577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25068510450975368243260205 9400691419115763091222577)
    ·
      refine ⟨7050518564336822318416933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9400691419115763091222577 7050518564336822318416933)
      ·
        refine ⟨1321972230813154184703175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7050518564336822318416933 1321972230813154184703175)
        ·
          refine ⟨1982958346219731277054763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1321972230813154184703175 1982958346219731277054763)
          ·
            refine ⟨2974437519329596915582145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1982958346219731277054763 2974437519329596915582145)
            ·
              refine ⟨2230828139497197686686609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2974437519329596915582145 2230828139497197686686609)
              ·
                refine ⟨1673121104622898265014957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2230828139497197686686609 1673121104622898265014957)
                ·
                  refine ⟨627420414233586849380609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1673121104622898265014957 627420414233586849380609)
                  ·
                    refine ⟨470565310675190137035457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 627420414233586849380609 470565310675190137035457)
                    ·
                      refine ⟨352923983006392602776593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 470565310675190137035457 352923983006392602776593)
                      ·
                        rfl

theorem cell23_687317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 2, 2, 3, 2, 2].length) (baseStart_687317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_687317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_687317 prefixEnd_687317 := by exact prefixLift 687317
  have htrace : WordTrace (prefixWord ++ tailWord_687317) baseStart_687317 baseEnd_687317 := by
    simpa [prefixWord, tailWord_687317, baseEnd_687317] using wordTrace_append hprefix tailTrace_687317
  have hstable : (prefixWord ++ tailWord_687317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_687317).length < 2 ^ (prefixWord ++ tailWord_687317).sum := by decide
  have hdescent : baseEnd_687317 < baseStart_687317 := by decide
  rcases family_descends (prefixWord ++ tailWord_687317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_687416 : List Nat := [2, 1, 2, 1, 3, 1, 1, 1, 2, 1, 8]
def baseStart_687416 : Nat := 118140960795 + 687416 * 2 ^ 59
def prefixEnd_687416 : Nat := 4983230072969 + 3 ^ 40 * 687416 * 2
def baseEnd_687416 : Nat := 352974817591187715438637

theorem tailTrace_687416 : CollatzResearch.WordTrace tailWord_687416 prefixEnd_687416 352974817591187715438637 := by
  unfold tailWord_687416
  simp only [CollatzResearch.WordTrace]
  refine ⟨12536060638808354075557051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16714747518411138767409401 12536060638808354075557051)
  ·
    refine ⟨18804090958212531113335577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12536060638808354075557051 18804090958212531113335577)
    ·
      refine ⟨14103068218659398335001683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18804090958212531113335577 14103068218659398335001683)
      ·
        refine ⟨21154602327989097502502525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14103068218659398335001683 21154602327989097502502525)
        ·
          refine ⟨7932975872995911563438447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21154602327989097502502525 7932975872995911563438447)
          ·
            refine ⟨11899463809493867345157671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7932975872995911563438447 11899463809493867345157671)
            ·
              refine ⟨17849195714240801017736507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11899463809493867345157671 17849195714240801017736507)
              ·
                refine ⟨26773793571361201526604761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17849195714240801017736507 26773793571361201526604761)
                ·
                  refine ⟨20080345178520901144953571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26773793571361201526604761 20080345178520901144953571)
                  ·
                    refine ⟨30120517767781351717430357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20080345178520901144953571 30120517767781351717430357)
                    ·
                      refine ⟨352974817591187715438637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 30120517767781351717430357 352974817591187715438637)
                      ·
                        rfl

theorem cell23_687416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 1, 2, 1, 8].length) (baseStart_687416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_687416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_687416 prefixEnd_687416 := by exact prefixLift 687416
  have htrace : WordTrace (prefixWord ++ tailWord_687416) baseStart_687416 baseEnd_687416 := by
    simpa [prefixWord, tailWord_687416, baseEnd_687416] using wordTrace_append hprefix tailTrace_687416
  have hstable : (prefixWord ++ tailWord_687416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_687416).length < 2 ^ (prefixWord ++ tailWord_687416).sum := by decide
  have hdescent : baseEnd_687416 < baseStart_687416 := by decide
  rcases family_descends (prefixWord ++ tailWord_687416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_687423 : List Nat := [1, 1, 2, 2, 4, 2, 1, 1, 1, 5, 3]
def baseStart_687423 : Nat := 118140960795 + 687423 * 2 ^ 59
def prefixEnd_687423 : Nat := 4983230072969 + 3 ^ 40 * 687423 * 2
def baseEnd_687423 : Nat := 352978411955769188051105

theorem tailTrace_687423 : CollatzResearch.WordTrace tailWord_687423 prefixEnd_687423 352978411955769188051105 := by
  unfold tailWord_687423
  simp only [CollatzResearch.WordTrace]
  refine ⟨25072376588591348346618923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16714917725727565564412615 25072376588591348346618923)
  ·
    refine ⟨37608564882887022519928385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25072376588591348346618923 37608564882887022519928385)
    ·
      refine ⟨28206423662165266889946289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37608564882887022519928385 28206423662165266889946289)
      ·
        refine ⟨21154817746623950167459717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28206423662165266889946289 21154817746623950167459717)
        ·
          refine ⟨3966528327491990656398697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21154817746623950167459717 3966528327491990656398697)
          ·
            refine ⟨2974896245618992992299023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3966528327491990656398697 2974896245618992992299023)
            ·
              refine ⟨4462344368428489488448535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2974896245618992992299023 4462344368428489488448535)
              ·
                refine ⟨6693516552642734232672803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4462344368428489488448535 6693516552642734232672803)
                ·
                  refine ⟨10040274828964101349009205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6693516552642734232672803 10040274828964101349009205)
                  ·
                    refine ⟨941275765215384501469613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10040274828964101349009205 941275765215384501469613)
                    ·
                      refine ⟨352978411955769188051105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 941275765215384501469613 352978411955769188051105)
                      ·
                        rfl

theorem cell23_687423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 1, 1, 1, 5, 3].length) (baseStart_687423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_687423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_687423 prefixEnd_687423 := by exact prefixLift 687423
  have htrace : WordTrace (prefixWord ++ tailWord_687423) baseStart_687423 baseEnd_687423 := by
    simpa [prefixWord, tailWord_687423, baseEnd_687423] using wordTrace_append hprefix tailTrace_687423
  have hstable : (prefixWord ++ tailWord_687423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_687423).length < 2 ^ (prefixWord ++ tailWord_687423).sum := by decide
  have hdescent : baseEnd_687423 < baseStart_687423 := by decide
  rcases family_descends (prefixWord ++ tailWord_687423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_687483 : List Nat := [1, 1, 1, 1, 1, 6, 1, 1, 3, 4, 3]
def baseStart_687483 : Nat := 118140960795 + 687483 * 2 ^ 59
def prefixEnd_687483 : Nat := 4983230072969 + 3 ^ 40 * 687483 * 2
def baseEnd_687483 : Nat := 353009220795038953300829

theorem tailTrace_687483 : CollatzResearch.WordTrace tailWord_687483 prefixEnd_687483 353009220795038953300829 := by
  unfold tailWord_687483
  simp only [CollatzResearch.WordTrace]
  refine ⟨25074564968373978593803103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16716376645582652395868735 25074564968373978593803103)
  ·
    refine ⟨37611847452560967890704655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25074564968373978593803103 37611847452560967890704655)
    ·
      refine ⟨56417771178841451836056983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37611847452560967890704655 56417771178841451836056983)
      ·
        refine ⟨84626656768262177754085475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56417771178841451836056983 84626656768262177754085475)
        ·
          refine ⟨126939985152393266631128213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84626656768262177754085475 126939985152393266631128213)
          ·
            refine ⟨5950311804018434373334135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 126939985152393266631128213 5950311804018434373334135)
            ·
              refine ⟨8925467706027651560001203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5950311804018434373334135 8925467706027651560001203)
              ·
                refine ⟨13388201559041477340001805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8925467706027651560001203 13388201559041477340001805)
                ·
                  refine ⟨5020575584640554002500677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13388201559041477340001805 5020575584640554002500677)
                  ·
                    refine ⟨941357922120103875468877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5020575584640554002500677 941357922120103875468877)
                    ·
                      refine ⟨353009220795038953300829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 941357922120103875468877 353009220795038953300829)
                      ·
                        rfl

theorem cell23_687483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 1, 1, 3, 4, 3].length) (baseStart_687483 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_687483 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_687483 prefixEnd_687483 := by exact prefixLift 687483
  have htrace : WordTrace (prefixWord ++ tailWord_687483) baseStart_687483 baseEnd_687483 := by
    simpa [prefixWord, tailWord_687483, baseEnd_687483] using wordTrace_append hprefix tailTrace_687483
  have hstable : (prefixWord ++ tailWord_687483).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_687483).length < 2 ^ (prefixWord ++ tailWord_687483).sum := by decide
  have hdescent : baseEnd_687483 < baseStart_687483 := by decide
  rcases family_descends (prefixWord ++ tailWord_687483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_687500 : List Nat := [2, 2, 1, 2, 1, 3, 2, 3, 2, 2, 3]
def baseStart_687500 : Nat := 118140960795 + 687500 * 2 ^ 59
def prefixEnd_687500 : Nat := 4983230072969 + 3 ^ 40 * 687500 * 2
def baseEnd_687500 : Nat := 353017949966165386788251

theorem tailTrace_687500 : CollatzResearch.WordTrace tailWord_687500 prefixEnd_687500 353017949966165386788251 := by
  unfold tailWord_687500
  simp only [CollatzResearch.WordTrace]
  refine ⟨12537592504656195248585977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16716790006208260331447969 12537592504656195248585977)
  ·
    refine ⟨9403194378492146436439483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12537592504656195248585977 9403194378492146436439483)
    ·
      refine ⟨14104791567738219654659225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9403194378492146436439483 14104791567738219654659225)
      ·
        refine ⟨10578593675803664740994419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14104791567738219654659225 10578593675803664740994419)
        ·
          refine ⟨15867890513705497111491629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10578593675803664740994419 15867890513705497111491629)
          ·
            refine ⟨5950458942639561416809361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15867890513705497111491629 5950458942639561416809361)
            ·
              refine ⟨4462844206979671062607021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5950458942639561416809361 4462844206979671062607021)
              ·
                refine ⟨1673566577617376648477633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4462844206979671062607021 1673566577617376648477633)
                ·
                  refine ⟨1255174933213032486358225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1673566577617376648477633 1255174933213032486358225)
                  ·
                    refine ⟨941381199909774364768669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1255174933213032486358225 941381199909774364768669)
                    ·
                      refine ⟨353017949966165386788251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 941381199909774364768669 353017949966165386788251)
                      ·
                        rfl

theorem cell23_687500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 2, 3, 2, 2, 3].length) (baseStart_687500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_687500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_687500 prefixEnd_687500 := by exact prefixLift 687500
  have htrace : WordTrace (prefixWord ++ tailWord_687500) baseStart_687500 baseEnd_687500 := by
    simpa [prefixWord, tailWord_687500, baseEnd_687500] using wordTrace_append hprefix tailTrace_687500
  have hstable : (prefixWord ++ tailWord_687500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_687500).length < 2 ^ (prefixWord ++ tailWord_687500).sum := by decide
  have hdescent : baseEnd_687500 < baseStart_687500 := by decide
  rcases family_descends (prefixWord ++ tailWord_687500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_687517 : List Nat := [1, 4, 2, 1, 3, 2, 1, 2, 2, 2, 3]
def baseStart_687517 : Nat := 118140960795 + 687517 * 2 ^ 59
def prefixEnd_687517 : Nat := 4983230072969 + 3 ^ 40 * 687517 * 2
def baseEnd_687517 : Nat := 353026679137291820275673

theorem tailTrace_687517 : CollatzResearch.WordTrace tailWord_687517 prefixEnd_687517 353026679137291820275673 := by
  unfold tailWord_687517
  simp only [CollatzResearch.WordTrace]
  refine ⟨25075805050250802400540805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16717203366833868267027203 25075805050250802400540805)
  ·
    refine ⟨4701713446922025450101401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 25075805050250802400540805 4701713446922025450101401)
    ·
      refine ⟨3526285085191519087576051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4701713446922025450101401 3526285085191519087576051)
      ·
        refine ⟨5289427627787278631364077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3526285085191519087576051 5289427627787278631364077)
        ·
          refine ⟨1983535360420229486761529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5289427627787278631364077 1983535360420229486761529)
          ·
            refine ⟨1487651520315172115071147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1983535360420229486761529 1487651520315172115071147)
            ·
              refine ⟨2231477280472758172606721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1487651520315172115071147 2231477280472758172606721)
              ·
                refine ⟨1673607960354568629455041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2231477280472758172606721 1673607960354568629455041)
                ·
                  refine ⟨1255205970265926472091281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1673607960354568629455041 1255205970265926472091281)
                  ·
                    refine ⟨941404477699444854068461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1255205970265926472091281 941404477699444854068461)
                    ·
                      refine ⟨353026679137291820275673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 941404477699444854068461 353026679137291820275673)
                      ·
                        rfl

theorem cell23_687517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 2, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 2, 1, 2, 2, 2, 3].length) (baseStart_687517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_687517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_687517 prefixEnd_687517 := by exact prefixLift 687517
  have htrace : WordTrace (prefixWord ++ tailWord_687517) baseStart_687517 baseEnd_687517 := by
    simpa [prefixWord, tailWord_687517, baseEnd_687517] using wordTrace_append hprefix tailTrace_687517
  have hstable : (prefixWord ++ tailWord_687517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_687517).length < 2 ^ (prefixWord ++ tailWord_687517).sum := by decide
  have hdescent : baseEnd_687517 < baseStart_687517 := by decide
  rcases family_descends (prefixWord ++ tailWord_687517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_687563 : List Nat := [1, 1, 1, 1, 3, 3, 3, 1, 3, 6]
def baseStart_687563 : Nat := 118140960795 + 687563 * 2 ^ 59
def prefixEnd_687563 : Nat := 4983230072969 + 3 ^ 40 * 687563 * 2
def baseEnd_687563 : Nat := 117683433082466213433487

theorem tailTrace_687563 : CollatzResearch.WordTrace tailWord_687563 prefixEnd_687563 117683433082466213433487 := by
  unfold tailWord_687563
  simp only [CollatzResearch.WordTrace]
  refine ⟨25077482808084152256715343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16718321872056101504476895 25077482808084152256715343)
  ·
    refine ⟨37616224212126228385073015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25077482808084152256715343 37616224212126228385073015)
    ·
      refine ⟨56424336318189342577609523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37616224212126228385073015 56424336318189342577609523)
      ·
        refine ⟨84636504477284013866414285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56424336318189342577609523 84636504477284013866414285)
        ·
          refine ⟨31738689178981505199905357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 84636504477284013866414285 31738689178981505199905357)
          ·
            refine ⟨11902008442118064449964509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31738689178981505199905357 11902008442118064449964509)
            ·
              refine ⟨4463253165794274168736691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11902008442118064449964509 4463253165794274168736691)
              ·
                refine ⟨6694879748691411253105037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4463253165794274168736691 6694879748691411253105037)
                ·
                  refine ⟨2510579905759279219914389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6694879748691411253105037 2510579905759279219914389)
                  ·
                    refine ⟨117683433082466213433487, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2510579905759279219914389 117683433082466213433487)
                    ·
                      rfl

theorem cell23_687563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 3, 1, 3, 6].length) (baseStart_687563 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_687563 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_687563 prefixEnd_687563 := by exact prefixLift 687563
  have htrace : WordTrace (prefixWord ++ tailWord_687563) baseStart_687563 baseEnd_687563 := by
    simpa [prefixWord, tailWord_687563, baseEnd_687563] using wordTrace_append hprefix tailTrace_687563
  have hstable : (prefixWord ++ tailWord_687563).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_687563).length < 2 ^ (prefixWord ++ tailWord_687563).sum := by decide
  have hdescent : baseEnd_687563 < baseStart_687563 := by decide
  rcases family_descends (prefixWord ++ tailWord_687563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_687581 : List Nat := [1, 4, 3, 1, 1, 3, 1, 4, 1, 1, 3]
def baseStart_687581 : Nat := 118140960795 + 687581 * 2 ^ 59
def prefixEnd_687581 : Nat := 4983230072969 + 3 ^ 40 * 687581 * 2
def baseEnd_687581 : Nat := 353059541899179569875379

theorem tailTrace_687581 : CollatzResearch.WordTrace tailWord_687581 prefixEnd_687581 353059541899179569875379 := by
  unfold tailWord_687581
  simp only [CollatzResearch.WordTrace]
  refine ⟨25078139322018941330870597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16718759548012627553913731 25078139322018941330870597)
  ·
    refine ⟨4702151122878551499538237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 25078139322018941330870597 4702151122878551499538237)
    ·
      refine ⟨1763306671079456812326839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4702151122878551499538237 1763306671079456812326839)
      ·
        refine ⟨2644960006619185218490259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1763306671079456812326839 2644960006619185218490259)
        ·
          refine ⟨3967440009928777827735389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2644960006619185218490259 3967440009928777827735389)
          ·
            refine ⟨1487790003723291685400771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3967440009928777827735389 1487790003723291685400771)
            ·
              refine ⟨2231685005584937528101157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1487790003723291685400771 2231685005584937528101157)
              ·
                refine ⟨418440938547175786518967, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2231685005584937528101157 418440938547175786518967)
                ·
                  refine ⟨627661407820763679778451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 418440938547175786518967 627661407820763679778451)
                  ·
                    refine ⟨941492111731145519667677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 627661407820763679778451 941492111731145519667677)
                    ·
                      refine ⟨353059541899179569875379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 941492111731145519667677 353059541899179569875379)
                      ·
                        rfl

theorem cell23_687581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 3, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 3, 1, 4, 1, 1, 3].length) (baseStart_687581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_687581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_687581 prefixEnd_687581 := by exact prefixLift 687581
  have htrace : WordTrace (prefixWord ++ tailWord_687581) baseStart_687581 baseEnd_687581 := by
    simpa [prefixWord, tailWord_687581, baseEnd_687581] using wordTrace_append hprefix tailTrace_687581
  have hstable : (prefixWord ++ tailWord_687581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_687581).length < 2 ^ (prefixWord ++ tailWord_687581).sum := by decide
  have hdescent : baseEnd_687581 < baseStart_687581 := by decide
  rcases family_descends (prefixWord ++ tailWord_687581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_687600 : List Nat := [2, 1, 1, 1, 3, 4, 1, 3, 1, 2, 4]
def baseStart_687600 : Nat := 118140960795 + 687600 * 2 ^ 59
def prefixEnd_687600 : Nat := 4983230072969 + 3 ^ 40 * 687600 * 2
def baseEnd_687600 : Nat := 353069298031614995537791

theorem tailTrace_687600 : CollatzResearch.WordTrace tailWord_687600 prefixEnd_687600 353069298031614995537791 := by
  unfold tailWord_687600
  simp only [CollatzResearch.WordTrace]
  refine ⟨12539416154475053787906127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16719221539300071717208169 12539416154475053787906127)
  ·
    refine ⟨18809124231712580681859191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12539416154475053787906127 18809124231712580681859191)
    ·
      refine ⟨28213686347568871022788787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18809124231712580681859191 28213686347568871022788787)
      ·
        refine ⟨42320529521353306534183181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28213686347568871022788787 42320529521353306534183181)
        ·
          refine ⟨15870198570507489950318693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42320529521353306534183181 15870198570507489950318693)
          ·
            refine ⟨2975662231970154365684755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15870198570507489950318693 2975662231970154365684755)
            ·
              refine ⟨4463493347955231548527133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2975662231970154365684755 4463493347955231548527133)
              ·
                refine ⟨1673810005483211830697675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4463493347955231548527133 1673810005483211830697675)
                ·
                  refine ⟨2510715008224817746046513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1673810005483211830697675 2510715008224817746046513)
                  ·
                    refine ⟨1883036256168613309534885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2510715008224817746046513 1883036256168613309534885)
                    ·
                      refine ⟨353069298031614995537791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1883036256168613309534885 353069298031614995537791)
                      ·
                        rfl

theorem cell23_687600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 1, 3, 1, 2, 4].length) (baseStart_687600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_687600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_687600 prefixEnd_687600 := by exact prefixLift 687600
  have htrace : WordTrace (prefixWord ++ tailWord_687600) baseStart_687600 baseEnd_687600 := by
    simpa [prefixWord, tailWord_687600, baseEnd_687600] using wordTrace_append hprefix tailTrace_687600
  have hstable : (prefixWord ++ tailWord_687600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_687600).length < 2 ^ (prefixWord ++ tailWord_687600).sum := by decide
  have hdescent : baseEnd_687600 < baseStart_687600 := by decide
  rcases family_descends (prefixWord ++ tailWord_687600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_687610 : List Nat := [3, 1, 1, 1, 1, 2, 7, 7]
def baseStart_687610 : Nat := 118140960795 + 687610 * 2 ^ 59
def prefixEnd_687610 : Nat := 4983230072969 + 3 ^ 40 * 687610 * 2
def baseEnd_687610 : Nat := 13076830845857776163435

theorem tailTrace_687610 : CollatzResearch.WordTrace tailWord_687610 prefixEnd_687610 13076830845857776163435 := by
  unfold tailWord_687610
  simp only [CollatzResearch.WordTrace]
  refine ⟨6269799259728469820919071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16719464692609252855784189 6269799259728469820919071)
  ·
    refine ⟨9404698889592704731378607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6269799259728469820919071 9404698889592704731378607)
    ·
      refine ⟨14107048334389057097067911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9404698889592704731378607 14107048334389057097067911)
      ·
        refine ⟨21160572501583585645601867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14107048334389057097067911 21160572501583585645601867)
        ·
          refine ⟨31740858752375378468402801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21160572501583585645601867 31740858752375378468402801)
          ·
            refine ⟨23805644064281533851302101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31740858752375378468402801 23805644064281533851302101)
            ·
              refine ⟨557944782756598449639893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 23805644064281533851302101 557944782756598449639893)
              ·
                refine ⟨13076830845857776163435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 557944782756598449639893 13076830845857776163435)
                ·
                  rfl

theorem cell23_687610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 7, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 7, 7].length) (baseStart_687610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_687610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_687610 prefixEnd_687610 := by exact prefixLift 687610
  have htrace : WordTrace (prefixWord ++ tailWord_687610) baseStart_687610 baseEnd_687610 := by
    simpa [prefixWord, tailWord_687610, baseEnd_687610] using wordTrace_append hprefix tailTrace_687610
  have hstable : (prefixWord ++ tailWord_687610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_687610).length < 2 ^ (prefixWord ++ tailWord_687610).sum := by decide
  have hdescent : baseEnd_687610 < baseStart_687610 := by decide
  rcases family_descends (prefixWord ++ tailWord_687610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_687624 : List Nat := [2, 1, 3, 2, 1, 1, 6, 1, 1, 2, 3]
def baseStart_687624 : Nat := 118140960795 + 687624 * 2 ^ 59
def prefixEnd_687624 : Nat := 4983230072969 + 3 ^ 40 * 687624 * 2
def baseEnd_687624 : Nat := 353081621567322901637681

theorem tailTrace_687624 : CollatzResearch.WordTrace tailWord_687624 prefixEnd_687624 353081621567322901637681 := by
  unfold tailWord_687624
  simp only [CollatzResearch.WordTrace]
  refine ⟨12539853830431579837342963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16719805107242106449790617 12539853830431579837342963)
  ·
    refine ⟨18809780745647369756014445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12539853830431579837342963 18809780745647369756014445)
    ·
      refine ⟨7053667779617763658505417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18809780745647369756014445 7053667779617763658505417)
      ·
        refine ⟨5290250834713322743879063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7053667779617763658505417 5290250834713322743879063)
        ·
          refine ⟨7935376252069984115818595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5290250834713322743879063 7935376252069984115818595)
          ·
            refine ⟨11903064378104976173727893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7935376252069984115818595 11903064378104976173727893)
            ·
              refine ⟨557956142723670758143495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 11903064378104976173727893 557956142723670758143495)
              ·
                refine ⟨836934214085506137215243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 557956142723670758143495 836934214085506137215243)
                ·
                  refine ⟨1255401321128259205822865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 836934214085506137215243 1255401321128259205822865)
                  ·
                    refine ⟨941550990846194404367149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1255401321128259205822865 941550990846194404367149)
                    ·
                      refine ⟨353081621567322901637681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 941550990846194404367149 353081621567322901637681)
                      ·
                        rfl

theorem cell23_687624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 6, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 6, 1, 1, 2, 3].length) (baseStart_687624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_687624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_687624 prefixEnd_687624 := by exact prefixLift 687624
  have htrace : WordTrace (prefixWord ++ tailWord_687624) baseStart_687624 baseEnd_687624 := by
    simpa [prefixWord, tailWord_687624, baseEnd_687624] using wordTrace_append hprefix tailTrace_687624
  have hstable : (prefixWord ++ tailWord_687624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_687624).length < 2 ^ (prefixWord ++ tailWord_687624).sum := by decide
  have hdescent : baseEnd_687624 < baseStart_687624 := by decide
  rcases family_descends (prefixWord ++ tailWord_687624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_687647 : List Nat := [1, 1, 2, 4, 1, 1, 2, 1, 5, 3, 2]
def baseStart_687647 : Nat := 118140960795 + 687647 * 2 ^ 59
def prefixEnd_687647 : Nat := 4983230072969 + 3 ^ 40 * 687647 * 2
def baseEnd_687647 : Nat := 353093431622376311650075

theorem tailTrace_687647 : CollatzResearch.WordTrace tailWord_687647 prefixEnd_687647 353093431622376311650075 := by
  unfold tailWord_687647
  simp only [CollatzResearch.WordTrace]
  refine ⟨25080546539779834602773195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16720364359853223068515463 25080546539779834602773195)
  ·
    refine ⟨37620819809669751904159793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25080546539779834602773195 37620819809669751904159793)
    ·
      refine ⟨28215614857252313928119845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37620819809669751904159793 28215614857252313928119845)
      ·
        refine ⟨5290427785734808861522471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 28215614857252313928119845 5290427785734808861522471)
        ·
          refine ⟨7935641678602213292283707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5290427785734808861522471 7935641678602213292283707)
          ·
            refine ⟨11903462517903319938425561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7935641678602213292283707 11903462517903319938425561)
            ·
              refine ⟨8927596888427489953819171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11903462517903319938425561 8927596888427489953819171)
              ·
                refine ⟨13391395332641234930728757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8927596888427489953819171 13391395332641234930728757)
                ·
                  refine ⟨1255443312435115774755821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 13391395332641234930728757 1255443312435115774755821)
                  ·
                    refine ⟨470791242163168415533433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1255443312435115774755821 470791242163168415533433)
                    ·
                      refine ⟨353093431622376311650075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 470791242163168415533433 353093431622376311650075)
                      ·
                        rfl

theorem cell23_687647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 2, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 2, 1, 5, 3, 2].length) (baseStart_687647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_687647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_687647 prefixEnd_687647 := by exact prefixLift 687647
  have htrace : WordTrace (prefixWord ++ tailWord_687647) baseStart_687647 baseEnd_687647 := by
    simpa [prefixWord, tailWord_687647, baseEnd_687647] using wordTrace_append hprefix tailTrace_687647
  have hstable : (prefixWord ++ tailWord_687647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_687647).length < 2 ^ (prefixWord ++ tailWord_687647).sum := by decide
  have hdescent : baseEnd_687647 < baseStart_687647 := by decide
  rcases family_descends (prefixWord ++ tailWord_687647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_687680 : List Nat := [2, 1, 1, 2, 2, 2, 1, 2, 1, 6, 3]
def baseStart_687680 : Nat := 118140960795 + 687680 * 2 ^ 59
def prefixEnd_687680 : Nat := 4983230072969 + 3 ^ 40 * 687680 * 2
def baseEnd_687680 : Nat := 353110376483974682537423

theorem tailTrace_687680 : CollatzResearch.WordTrace tailWord_687680 prefixEnd_687680 353110376483974682537423 := by
  unfold tailWord_687680
  simp only [CollatzResearch.WordTrace]
  refine ⟨12540875074330140619362247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16721166765773520825816329 12540875074330140619362247)
  ·
    refine ⟨18811312611495210929043371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12540875074330140619362247 18811312611495210929043371)
    ·
      refine ⟨28216968917242816393565057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18811312611495210929043371 28216968917242816393565057)
      ·
        refine ⟨21162726687932112295173793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28216968917242816393565057 21162726687932112295173793)
        ·
          refine ⟨15872045015949084221380345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21162726687932112295173793 15872045015949084221380345)
          ·
            refine ⟨11904033761961813166035259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15872045015949084221380345 11904033761961813166035259)
            ·
              refine ⟨17856050642942719749052889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11904033761961813166035259 17856050642942719749052889)
              ·
                refine ⟨13392037982207039811789667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17856050642942719749052889 13392037982207039811789667)
                ·
                  refine ⟨20088056973310559717684501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13392037982207039811789667 20088056973310559717684501)
                  ·
                    refine ⟨941627670623932486766461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20088056973310559717684501 941627670623932486766461)
                    ·
                      refine ⟨353110376483974682537423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 941627670623932486766461 353110376483974682537423)
                      ·
                        rfl

theorem cell23_687680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 2, 1, 6, 3].length) (baseStart_687680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_687680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_687680 prefixEnd_687680 := by exact prefixLift 687680
  have htrace : WordTrace (prefixWord ++ tailWord_687680) baseStart_687680 baseEnd_687680 := by
    simpa [prefixWord, tailWord_687680, baseEnd_687680] using wordTrace_append hprefix tailTrace_687680
  have hstable : (prefixWord ++ tailWord_687680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_687680).length < 2 ^ (prefixWord ++ tailWord_687680).sum := by decide
  have hdescent : baseEnd_687680 < baseStart_687680 := by decide
  rcases family_descends (prefixWord ++ tailWord_687680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_687751 : List Nat := [1, 1, 4, 2, 1, 5, 2, 2, 5]
def baseStart_687751 : Nat := 118140960795 + 687751 * 2 ^ 59
def prefixEnd_687751 : Nat := 4983230072969 + 3 ^ 40 * 687751 * 2
def baseEnd_687751 : Nat := 39238537067827100527733

theorem tailTrace_687751 : CollatzResearch.WordTrace tailWord_687751 prefixEnd_687751 39238537067827100527733 := by
  unfold tailWord_687751
  simp only [CollatzResearch.WordTrace]
  refine ⟨25084339731403060364559107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16722893154268706909706071 25084339731403060364559107)
  ·
    refine ⟨37626509597104590546838661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25084339731403060364559107 37626509597104590546838661)
    ·
      refine ⟨7054970549457110727532249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 37626509597104590546838661 7054970549457110727532249)
      ·
        refine ⟨5291227912092833045649187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7054970549457110727532249 5291227912092833045649187)
        ·
          refine ⟨7936841868139249568473781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5291227912092833045649187 7936841868139249568473781)
          ·
            refine ⟨744078925138054647044417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 7936841868139249568473781 744078925138054647044417)
            ·
              refine ⟨558059193853540985283313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 744078925138054647044417 558059193853540985283313)
              ·
                refine ⟨418544395390155738962485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 558059193853540985283313 418544395390155738962485)
                ·
                  refine ⟨39238537067827100527733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 418544395390155738962485 39238537067827100527733)
                  ·
                    rfl

theorem cell23_687751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 5, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 5, 2, 2, 5].length) (baseStart_687751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_687751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_687751 prefixEnd_687751 := by exact prefixLift 687751
  have htrace : WordTrace (prefixWord ++ tailWord_687751) baseStart_687751 baseEnd_687751 := by
    simpa [prefixWord, tailWord_687751, baseEnd_687751] using wordTrace_append hprefix tailTrace_687751
  have hstable : (prefixWord ++ tailWord_687751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_687751).length < 2 ^ (prefixWord ++ tailWord_687751).sum := by decide
  have hdescent : baseEnd_687751 < baseStart_687751 := by decide
  rcases family_descends (prefixWord ++ tailWord_687751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_687754 : List Nat := [3, 1, 2, 3, 2, 1, 1, 1, 2, 5, 2]
def baseStart_687754 : Nat := 118140960795 + 687754 * 2 ^ 59
def prefixEnd_687754 : Nat := 4983230072969 + 3 ^ 40 * 687754 * 2
def baseEnd_687754 : Nat := 353148374052407393012083

theorem tailTrace_687754 : CollatzResearch.WordTrace tailWord_687754 prefixEnd_687754 353148374052407393012083 := by
  unfold tailWord_687754
  simp only [CollatzResearch.WordTrace]
  refine ⟨6271112287598047969229579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16722966100261461251278877 6271112287598047969229579)
  ·
    refine ⟨9406668431397071953844369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6271112287598047969229579 9406668431397071953844369)
    ·
      refine ⟨7055001323547803965383277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9406668431397071953844369 7055001323547803965383277)
      ·
        refine ⟨2645625496330426487018729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7055001323547803965383277 2645625496330426487018729)
        ·
          refine ⟨1984219122247819865264047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2645625496330426487018729 1984219122247819865264047)
          ·
            refine ⟨2976328683371729797896071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1984219122247819865264047 2976328683371729797896071)
            ·
              refine ⟨4464493025057594696844107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2976328683371729797896071 4464493025057594696844107)
              ·
                refine ⟨6696739537586392045266161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4464493025057594696844107 6696739537586392045266161)
                ·
                  refine ⟨5022554653189794033949621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6696739537586392045266161 5022554653189794033949621)
                  ·
                    refine ⟨470864498736543190682777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5022554653189794033949621 470864498736543190682777)
                    ·
                      refine ⟨353148374052407393012083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 470864498736543190682777 353148374052407393012083)
                      ·
                        rfl

theorem cell23_687754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 1, 1, 2, 5, 2].length) (baseStart_687754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_687754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_687754 prefixEnd_687754 := by exact prefixLift 687754
  have htrace : WordTrace (prefixWord ++ tailWord_687754) baseStart_687754 baseEnd_687754 := by
    simpa [prefixWord, tailWord_687754, baseEnd_687754] using wordTrace_append hprefix tailTrace_687754
  have hstable : (prefixWord ++ tailWord_687754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_687754).length < 2 ^ (prefixWord ++ tailWord_687754).sum := by decide
  have hdescent : baseEnd_687754 < baseStart_687754 := by decide
  rcases family_descends (prefixWord ++ tailWord_687754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_687821 : List Nat := [1, 6, 2, 1, 1, 1, 1, 2, 1, 4, 3]
def baseStart_687821 : Nat := 118140960795 + 687821 * 2 ^ 59
def prefixEnd_687821 : Nat := 4983230072969 + 3 ^ 40 * 687821 * 2
def baseEnd_687821 : Nat := 353182777256258630874275

theorem tailTrace_687821 : CollatzResearch.WordTrace tailWord_687821 prefixEnd_687821 353182777256258630874275 := by
  unfold tailWord_687821
  simp only [CollatzResearch.WordTrace]
  refine ⟨25086892841149462319607317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16724595227432974879738211 25086892841149462319607317)
  ·
    refine ⟨1175948101928881046231593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 25086892841149462319607317 1175948101928881046231593)
    ·
      refine ⟨881961076446660784673695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1175948101928881046231593 881961076446660784673695)
      ·
        refine ⟨1322941614669991177010543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 881961076446660784673695 1322941614669991177010543)
        ·
          refine ⟨1984412422004986765515815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1322941614669991177010543 1984412422004986765515815)
          ·
            refine ⟨2976618633007480148273723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1984412422004986765515815 2976618633007480148273723)
            ·
              refine ⟨4464927949511220222410585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2976618633007480148273723 4464927949511220222410585)
              ·
                refine ⟨3348695962133415166807939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4464927949511220222410585 3348695962133415166807939)
                ·
                  refine ⟨5023043943200122750211909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3348695962133415166807939 5023043943200122750211909)
                  ·
                    refine ⟨941820739350023015664733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5023043943200122750211909 941820739350023015664733)
                    ·
                      refine ⟨353182777256258630874275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 941820739350023015664733 353182777256258630874275)
                      ·
                        rfl

theorem cell23_687821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 1, 2, 1, 4, 3].length) (baseStart_687821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_687821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_687821 prefixEnd_687821 := by exact prefixLift 687821
  have htrace : WordTrace (prefixWord ++ tailWord_687821) baseStart_687821 baseEnd_687821 := by
    simpa [prefixWord, tailWord_687821, baseEnd_687821] using wordTrace_append hprefix tailTrace_687821
  have hstable : (prefixWord ++ tailWord_687821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_687821).length < 2 ^ (prefixWord ++ tailWord_687821).sum := by decide
  have hdescent : baseEnd_687821 < baseStart_687821 := by decide
  rcases family_descends (prefixWord ++ tailWord_687821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_687844 : List Nat := [2, 3, 1, 1, 1, 3, 1, 3, 1, 5, 2]
def baseStart_687844 : Nat := 118140960795 + 687844 * 2 ^ 59
def prefixEnd_687844 : Nat := 4983230072969 + 3 ^ 40 * 687844 * 2
def baseEnd_687844 : Nat := 353194587311312040886669

theorem tailTrace_687844 : CollatzResearch.WordTrace tailWord_687844 prefixEnd_687844 353194587311312040886669 := by
  unfold tailWord_687844
  simp only [CollatzResearch.WordTrace]
  refine ⟨12543865860033068623847293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16725154480044091498463057 12543865860033068623847293)
  ·
    refine ⟨4703949697512400733942735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12543865860033068623847293 4703949697512400733942735)
    ·
      refine ⟨7055924546268601100914103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4703949697512400733942735 7055924546268601100914103)
      ·
        refine ⟨10583886819402901651371155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7055924546268601100914103 10583886819402901651371155)
        ·
          refine ⟨15875830229104352477056733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10583886819402901651371155 15875830229104352477056733)
          ·
            refine ⟨5953436335914132178896275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15875830229104352477056733 5953436335914132178896275)
            ·
              refine ⟨8930154503871198268344413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5953436335914132178896275 8930154503871198268344413)
              ·
                refine ⟨3348807938951699350629155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8930154503871198268344413 3348807938951699350629155)
                ·
                  refine ⟨5023211908427549025943733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3348807938951699350629155 5023211908427549025943733)
                  ·
                    refine ⟨470926116415082721182225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5023211908427549025943733 470926116415082721182225)
                    ·
                      refine ⟨353194587311312040886669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 470926116415082721182225 353194587311312040886669)
                      ·
                        rfl

theorem cell23_687844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 1, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 1, 3, 1, 5, 2].length) (baseStart_687844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_687844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_687844 prefixEnd_687844 := by exact prefixLift 687844
  have htrace : WordTrace (prefixWord ++ tailWord_687844) baseStart_687844 baseEnd_687844 := by
    simpa [prefixWord, tailWord_687844, baseEnd_687844] using wordTrace_append hprefix tailTrace_687844
  have hstable : (prefixWord ++ tailWord_687844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_687844).length < 2 ^ (prefixWord ++ tailWord_687844).sum := by decide
  have hdescent : baseEnd_687844 < baseStart_687844 := by decide
  rcases family_descends (prefixWord ++ tailWord_687844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_687854 : List Nat := [4, 1, 2, 1, 1, 2, 1, 5, 1, 5]
def baseStart_687854 : Nat := 118140960795 + 687854 * 2 ^ 59
def prefixEnd_687854 : Nat := 4983230072969 + 3 ^ 40 * 687854 * 2
def baseEnd_687854 : Nat := 117733240705952333920541

theorem tailTrace_687854 : CollatzResearch.WordTrace tailWord_687854 prefixEnd_687854 117733240705952333920541 := by
  unfold tailWord_687854
  simp only [CollatzResearch.WordTrace]
  refine ⟨3136012056253738619444827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 16725397633353272637039077 3136012056253738619444827)
  ·
    refine ⟨4704018084380607929167241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3136012056253738619444827 4704018084380607929167241)
    ·
      refine ⟨3528013563285455946875431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4704018084380607929167241 3528013563285455946875431)
      ·
        refine ⟨5292020344928183920313147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3528013563285455946875431 5292020344928183920313147)
        ·
          refine ⟨7938030517392275880469721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5292020344928183920313147 7938030517392275880469721)
          ·
            refine ⟨5953522888044206910352291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7938030517392275880469721 5953522888044206910352291)
            ·
              refine ⟨8930284332066310365528437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5953522888044206910352291 8930284332066310365528437)
              ·
                refine ⟨837214156131216596768291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8930284332066310365528437 837214156131216596768291)
                ·
                  refine ⟨1255821234196824895152437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 837214156131216596768291 1255821234196824895152437)
                  ·
                    refine ⟨117733240705952333920541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1255821234196824895152437 117733240705952333920541)
                    ·
                      rfl

theorem cell23_687854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 1, 5, 1, 5].length) (baseStart_687854 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_687854 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_687854 prefixEnd_687854 := by exact prefixLift 687854
  have htrace : WordTrace (prefixWord ++ tailWord_687854) baseStart_687854 baseEnd_687854 := by
    simpa [prefixWord, tailWord_687854, baseEnd_687854] using wordTrace_append hprefix tailTrace_687854
  have hstable : (prefixWord ++ tailWord_687854).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_687854).length < 2 ^ (prefixWord ++ tailWord_687854).sum := by decide
  have hdescent : baseEnd_687854 < baseStart_687854 := by decide
  rcases family_descends (prefixWord ++ tailWord_687854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_687877 : List Nat := [1, 3, 1, 1, 2, 1, 1, 1, 1, 8, 3]
def baseStart_687877 : Nat := 118140960795 + 687877 * 2 ^ 59
def prefixEnd_687877 : Nat := 4983230072969 + 3 ^ 40 * 687877 * 2
def baseEnd_687877 : Nat := 353211532172910411774017

theorem tailTrace_687877 : CollatzResearch.WordTrace tailWord_687877 prefixEnd_687877 353211532172910411774017 := by
  unfold tailWord_687877
  simp only [CollatzResearch.WordTrace]
  refine ⟨25088935328946583883645885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16725956885964389255763923 25088935328946583883645885)
  ·
    refine ⟨9408350748354968956367207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25088935328946583883645885 9408350748354968956367207)
    ·
      refine ⟨14112526122532453434550811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9408350748354968956367207 14112526122532453434550811)
      ·
        refine ⟨21168789183798680151826217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14112526122532453434550811 21168789183798680151826217)
        ·
          refine ⟨15876591887849010113869663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21168789183798680151826217 15876591887849010113869663)
          ·
            refine ⟨23814887831773515170804495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15876591887849010113869663 23814887831773515170804495)
            ·
              refine ⟨35722331747660272756206743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23814887831773515170804495 35722331747660272756206743)
              ·
                refine ⟨53583497621490409134310115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35722331747660272756206743 53583497621490409134310115)
                ·
                  refine ⟨80375246432235613701465173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 53583497621490409134310115 80375246432235613701465173)
                  ·
                    refine ⟨941897419127761098064045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 80375246432235613701465173 941897419127761098064045)
                    ·
                      refine ⟨353211532172910411774017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 941897419127761098064045 353211532172910411774017)
                      ·
                        rfl

theorem cell23_687877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 1, 1, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 1, 1, 8, 3].length) (baseStart_687877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_687877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_687877 prefixEnd_687877 := by exact prefixLift 687877
  have htrace : WordTrace (prefixWord ++ tailWord_687877) baseStart_687877 baseEnd_687877 := by
    simpa [prefixWord, tailWord_687877, baseEnd_687877] using wordTrace_append hprefix tailTrace_687877
  have hstable : (prefixWord ++ tailWord_687877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_687877).length < 2 ^ (prefixWord ++ tailWord_687877).sum := by decide
  have hdescent : baseEnd_687877 < baseStart_687877 := by decide
  rcases family_descends (prefixWord ++ tailWord_687877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_687904 : List Nat := [2, 1, 1, 5, 1, 1, 3, 2, 1, 2, 4]
def baseStart_687904 : Nat := 118140960795 + 687904 * 2 ^ 59
def prefixEnd_687904 : Nat := 4983230072969 + 3 ^ 40 * 687904 * 2
def baseEnd_687904 : Nat := 353225396150581806136393

theorem tailTrace_687904 : CollatzResearch.WordTrace tailWord_687904 prefixEnd_687904 353225396150581806136393 := by
  unfold tailWord_687904
  simp only [CollatzResearch.WordTrace]
  refine ⟨12544960049924383747439383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16726613399899178329919177 12544960049924383747439383)
  ·
    refine ⟨18817440074886575621159075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12544960049924383747439383 18817440074886575621159075)
    ·
      refine ⟨28226160112329863431738613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18817440074886575621159075 28226160112329863431738613)
      ·
        refine ⟨2646202510530924696725495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 28226160112329863431738613 2646202510530924696725495)
        ·
          refine ⟨3969303765796387045088243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2646202510530924696725495 3969303765796387045088243)
          ·
            refine ⟨5953955648694580567632365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3969303765796387045088243 5953955648694580567632365)
            ·
              refine ⟨2232733368260467712862137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5953955648694580567632365 2232733368260467712862137)
              ·
                refine ⟨1674550026195350784646603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2232733368260467712862137 1674550026195350784646603)
                ·
                  refine ⟨2511825039293026176969905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1674550026195350784646603 2511825039293026176969905)
                  ·
                    refine ⟨1883868779469769632727429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2511825039293026176969905 1883868779469769632727429)
                    ·
                      refine ⟨353225396150581806136393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1883868779469769632727429 353225396150581806136393)
                      ·
                        rfl

theorem cell23_687904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 3, 2, 1, 2, 4].length) (baseStart_687904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_687904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_687904 prefixEnd_687904 := by exact prefixLift 687904
  have htrace : WordTrace (prefixWord ++ tailWord_687904) baseStart_687904 baseEnd_687904 := by
    simpa [prefixWord, tailWord_687904, baseEnd_687904] using wordTrace_append hprefix tailTrace_687904
  have hstable : (prefixWord ++ tailWord_687904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_687904).length < 2 ^ (prefixWord ++ tailWord_687904).sum := by decide
  have hdescent : baseEnd_687904 < baseStart_687904 := by decide
  rcases family_descends (prefixWord ++ tailWord_687904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_687908 : List Nat := [2, 3, 1, 3, 2, 2, 3, 1, 1, 1, 4]
def baseStart_687908 : Nat := 118140960795 + 687908 * 2 ^ 59
def prefixEnd_687908 : Nat := 4983230072969 + 3 ^ 40 * 687908 * 2
def baseEnd_687908 : Nat := 353227450073199790486375

theorem tailTrace_687908 : CollatzResearch.WordTrace tailWord_687908 prefixEnd_687908 353227450073199790486375 := by
  unfold tailWord_687908
  simp only [CollatzResearch.WordTrace]
  refine ⟨12545032995917138089012189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16726710661222850785349585 12545032995917138089012189)
  ·
    refine ⟨4704387373468926783379571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12545032995917138089012189 4704387373468926783379571)
    ·
      refine ⟨7056581060203390175069357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4704387373468926783379571 7056581060203390175069357)
      ·
        refine ⟨2646217897576271315651009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7056581060203390175069357 2646217897576271315651009)
        ·
          refine ⟨1984663423182203486738257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2646217897576271315651009 1984663423182203486738257)
          ·
            refine ⟨1488497567386652615053693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1984663423182203486738257 1488497567386652615053693)
            ·
              refine ⟨558186587769994730645135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1488497567386652615053693 558186587769994730645135)
              ·
                refine ⟨837279881654992095967703, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 558186587769994730645135 837279881654992095967703)
                ·
                  refine ⟨1255919822482488143951555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 837279881654992095967703 1255919822482488143951555)
                  ·
                    refine ⟨1883879733723732215927333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1255919822482488143951555 1883879733723732215927333)
                    ·
                      refine ⟨353227450073199790486375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1883879733723732215927333 353227450073199790486375)
                      ·
                        rfl

theorem cell23_687908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 2, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 2, 3, 1, 1, 1, 4].length) (baseStart_687908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_687908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_687908 prefixEnd_687908 := by exact prefixLift 687908
  have htrace : WordTrace (prefixWord ++ tailWord_687908) baseStart_687908 baseEnd_687908 := by
    simpa [prefixWord, tailWord_687908, baseEnd_687908] using wordTrace_append hprefix tailTrace_687908
  have hstable : (prefixWord ++ tailWord_687908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_687908).length < 2 ^ (prefixWord ++ tailWord_687908).sum := by decide
  have hdescent : baseEnd_687908 < baseStart_687908 := by decide
  rcases family_descends (prefixWord ++ tailWord_687908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_687941 : List Nat := [1, 3, 1, 1, 1, 2, 3, 5, 2, 1, 3]
def baseStart_687941 : Nat := 118140960795 + 687941 * 2 ^ 59
def prefixEnd_687941 : Nat := 4983230072969 + 3 ^ 40 * 687941 * 2
def baseEnd_687941 : Nat := 353244394934798161373723

theorem tailTrace_687941 : CollatzResearch.WordTrace tailWord_687941 prefixEnd_687941 353244394934798161373723 := by
  unfold tailWord_687941
  simp only [CollatzResearch.WordTrace]
  refine ⟨25091269600714722813975677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16727513067143148542650451 25091269600714722813975677)
  ·
    refine ⟨9409226100268021055240879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25091269600714722813975677 9409226100268021055240879)
    ·
      refine ⟨14113839150402031582861319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9409226100268021055240879 14113839150402031582861319)
      ·
        refine ⟨21170758725603047374291979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14113839150402031582861319 21170758725603047374291979)
        ·
          refine ⟨31756138088404571061437969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21170758725603047374291979 31756138088404571061437969)
          ·
            refine ⟨23817103566303428296078477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31756138088404571061437969 23817103566303428296078477)
            ·
              refine ⟨8931413837363785611029429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23817103566303428296078477 8931413837363785611029429)
              ·
                refine ⟨837320047252854901034009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8931413837363785611029429 837320047252854901034009)
                ·
                  refine ⟨627990035439641175775507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 837320047252854901034009 627990035439641175775507)
                  ·
                    refine ⟨941985053159461763663261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 627990035439641175775507 941985053159461763663261)
                    ·
                      refine ⟨353244394934798161373723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 941985053159461763663261 353244394934798161373723)
                      ·
                        rfl

theorem cell23_687941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 3, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 3, 5, 2, 1, 3].length) (baseStart_687941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_687941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_687941 prefixEnd_687941 := by exact prefixLift 687941
  have htrace : WordTrace (prefixWord ++ tailWord_687941) baseStart_687941 baseEnd_687941 := by
    simpa [prefixWord, tailWord_687941, baseEnd_687941] using wordTrace_append hprefix tailTrace_687941
  have hstable : (prefixWord ++ tailWord_687941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_687941).length < 2 ^ (prefixWord ++ tailWord_687941).sum := by decide
  have hdescent : baseEnd_687941 < baseStart_687941 := by decide
  rcases family_descends (prefixWord ++ tailWord_687941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_687942 : List Nat := [6, 1, 1, 2, 1, 2, 1, 2, 3, 2, 2]
def baseStart_687942 : Nat := 118140960795 + 687942 * 2 ^ 59
def prefixEnd_687942 : Nat := 4983230072969 + 3 ^ 40 * 687942 * 2
def baseEnd_687942 : Nat := 353244908415452657461219

theorem tailTrace_687942 : CollatzResearch.WordTrace tailWord_687942 prefixEnd_687942 353244908415452657461219 := by
  unfold tailWord_687942
  simp only [CollatzResearch.WordTrace]
  refine ⟨784103314803471874523815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 16727537382474066656508053 784103314803471874523815)
  ·
    refine ⟨1176154972205207811785723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 784103314803471874523815 1176154972205207811785723)
    ·
      refine ⟨1764232458307811717678585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1176154972205207811785723 1764232458307811717678585)
      ·
        refine ⟨1323174343730858788258939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1764232458307811717678585 1323174343730858788258939)
        ·
          refine ⟨1984761515596288182388409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1323174343730858788258939 1984761515596288182388409)
          ·
            refine ⟨1488571136697216136791307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1984761515596288182388409 1488571136697216136791307)
            ·
              refine ⟨2232856705045824205186961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1488571136697216136791307 2232856705045824205186961)
              ·
                refine ⟨1674642528784368153890221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2232856705045824205186961 1674642528784368153890221)
                ·
                  refine ⟨627990948294138057708833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1674642528784368153890221 627990948294138057708833)
                  ·
                    refine ⟨470993211220603543281625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 627990948294138057708833 470993211220603543281625)
                    ·
                      refine ⟨353244908415452657461219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 470993211220603543281625 353244908415452657461219)
                      ·
                        rfl

theorem cell23_687942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 2, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 2, 1, 2, 3, 2, 2].length) (baseStart_687942 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_687942 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_687942 prefixEnd_687942 := by exact prefixLift 687942
  have htrace : WordTrace (prefixWord ++ tailWord_687942) baseStart_687942 baseEnd_687942 := by
    simpa [prefixWord, tailWord_687942, baseEnd_687942] using wordTrace_append hprefix tailTrace_687942
  have hstable : (prefixWord ++ tailWord_687942).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_687942).length < 2 ^ (prefixWord ++ tailWord_687942).sum := by decide
  have hdescent : baseEnd_687942 < baseStart_687942 := by decide
  rcases family_descends (prefixWord ++ tailWord_687942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_687968 : List Nat := [2, 1, 1, 3, 3, 3, 1, 3, 1, 3, 2]
def baseStart_687968 : Nat := 118140960795 + 687968 * 2 ^ 59
def prefixEnd_687968 : Nat := 4983230072969 + 3 ^ 40 * 687968 * 2
def baseEnd_687968 : Nat := 353258258912469555736099

theorem tailTrace_687968 : CollatzResearch.WordTrace tailWord_687968 prefixEnd_687968 353258258912469555736099 := by
  unfold tailWord_687968
  simp only [CollatzResearch.WordTrace]
  refine ⟨12546127185808453212604279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16728169581077937616805705 12546127185808453212604279)
  ·
    refine ⟨18819190778712679818906419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12546127185808453212604279 18819190778712679818906419)
    ·
      refine ⟨28228786168069019728359629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18819190778712679818906419 28228786168069019728359629)
      ·
        refine ⟨10585794813025882398134861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28228786168069019728359629 10585794813025882398134861)
        ·
          refine ⟨3969673054884705899300573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10585794813025882398134861 3969673054884705899300573)
          ·
            refine ⟨1488627395581764712237715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3969673054884705899300573 1488627395581764712237715)
            ·
              refine ⟨2232941093372647068356573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1488627395581764712237715 2232941093372647068356573)
              ·
                refine ⟨837352910014742650633715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2232941093372647068356573 837352910014742650633715)
                ·
                  refine ⟨1256029365022113975950573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 837352910014742650633715 1256029365022113975950573)
                  ·
                    refine ⟨471011011883292740981465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1256029365022113975950573 471011011883292740981465)
                    ·
                      refine ⟨353258258912469555736099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 471011011883292740981465 353258258912469555736099)
                      ·
                        rfl

theorem cell23_687968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 3, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 3, 1, 3, 1, 3, 2].length) (baseStart_687968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_687968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_687968 prefixEnd_687968 := by exact prefixLift 687968
  have htrace : WordTrace (prefixWord ++ tailWord_687968) baseStart_687968 baseEnd_687968 := by
    simpa [prefixWord, tailWord_687968, baseEnd_687968] using wordTrace_append hprefix tailTrace_687968
  have hstable : (prefixWord ++ tailWord_687968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_687968).length < 2 ^ (prefixWord ++ tailWord_687968).sum := by decide
  have hdescent : baseEnd_687968 < baseStart_687968 := by decide
  rcases family_descends (prefixWord ++ tailWord_687968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_687981 : List Nat := [1, 5, 1, 1, 1, 1, 2, 2, 3, 4, 2]
def baseStart_687981 : Nat := 118140960795 + 687981 * 2 ^ 59
def prefixEnd_687981 : Nat := 4983230072969 + 3 ^ 40 * 687981 * 2
def baseEnd_687981 : Nat := 353264934160978004873539

theorem tailTrace_687981 : CollatzResearch.WordTrace tailWord_687981 prefixEnd_687981 353264934160978004873539 := by
  unfold tailWord_687981
  simp only [CollatzResearch.WordTrace]
  refine ⟨25092728520569809645431797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16728485680379873096954531 25092728520569809645431797)
  ·
    refine ⟨2352443298803419654259231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 25092728520569809645431797 2352443298803419654259231)
    ·
      refine ⟨3528664948205129481388847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2352443298803419654259231 3528664948205129481388847)
      ·
        refine ⟨5292997422307694222083271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3528664948205129481388847 5292997422307694222083271)
        ·
          refine ⟨7939496133461541333124907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5292997422307694222083271 7939496133461541333124907)
          ·
            refine ⟨11909244200192311999687361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7939496133461541333124907 11909244200192311999687361)
            ·
              refine ⟨8931933150144233999765521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11909244200192311999687361 8931933150144233999765521)
              ·
                refine ⟨6698949862608175499824141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8931933150144233999765521 6698949862608175499824141)
                ·
                  refine ⟨2512106198478065812434053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6698949862608175499824141 2512106198478065812434053)
                  ·
                    refine ⟨471019912214637339831385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2512106198478065812434053 471019912214637339831385)
                    ·
                      refine ⟨353264934160978004873539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 471019912214637339831385 353264934160978004873539)
                      ·
                        rfl

theorem cell23_687981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 2, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 2, 2, 3, 4, 2].length) (baseStart_687981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_687981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_687981 prefixEnd_687981 := by exact prefixLift 687981
  have htrace : WordTrace (prefixWord ++ tailWord_687981) baseStart_687981 baseEnd_687981 := by
    simpa [prefixWord, tailWord_687981, baseEnd_687981] using wordTrace_append hprefix tailTrace_687981
  have hstable : (prefixWord ++ tailWord_687981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_687981).length < 2 ^ (prefixWord ++ tailWord_687981).sum := by decide
  have hdescent : baseEnd_687981 < baseStart_687981 := by decide
  rcases family_descends (prefixWord ++ tailWord_687981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_687994 : List Nat := [3, 1, 1, 1, 1, 1, 6, 1, 2, 2, 4]
def baseStart_687994 : Nat := 118140960795 + 687994 * 2 ^ 59
def prefixEnd_687994 : Nat := 4983230072969 + 3 ^ 40 * 687994 * 2
def baseEnd_687994 : Nat := 353271609409486454010979

theorem tailTrace_687994 : CollatzResearch.WordTrace tailWord_687994 prefixEnd_687994 353271609409486454010979 := by
  unfold tailWord_687994
  simp only [CollatzResearch.WordTrace]
  refine ⟨6273300667380678216413759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16728801779681808577103357 6273300667380678216413759)
  ·
    refine ⟨9409951001071017324620639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6273300667380678216413759 9409951001071017324620639)
    ·
      refine ⟨14114926501606525986930959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9409951001071017324620639 14114926501606525986930959)
      ·
        refine ⟨21172389752409788980396439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14114926501606525986930959 21172389752409788980396439)
        ·
          refine ⟨31758584628614683470594659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21172389752409788980396439 31758584628614683470594659)
          ·
            refine ⟨47637876942922025205891989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31758584628614683470594659 47637876942922025205891989)
            ·
              refine ⟨2233025481699469931526187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 47637876942922025205891989 2233025481699469931526187)
              ·
                refine ⟨3349538222549204897289281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2233025481699469931526187 3349538222549204897289281)
                ·
                  refine ⟨2512153666911903672966961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3349538222549204897289281 2512153666911903672966961)
                  ·
                    refine ⟨1884115250183927754725221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2512153666911903672966961 1884115250183927754725221)
                    ·
                      refine ⟨353271609409486454010979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1884115250183927754725221 353271609409486454010979)
                      ·
                        rfl

theorem cell23_687994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 6, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 6, 1, 2, 2, 4].length) (baseStart_687994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_687994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_687994 prefixEnd_687994 := by exact prefixLift 687994
  have htrace : WordTrace (prefixWord ++ tailWord_687994) baseStart_687994 baseEnd_687994 := by
    simpa [prefixWord, tailWord_687994, baseEnd_687994] using wordTrace_append hprefix tailTrace_687994
  have hstable : (prefixWord ++ tailWord_687994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_687994).length < 2 ^ (prefixWord ++ tailWord_687994).sum := by decide
  have hdescent : baseEnd_687994 < baseStart_687994 := by decide
  rcases family_descends (prefixWord ++ tailWord_687994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_688004 : List Nat := [2, 3, 2, 1, 1, 1, 4, 2, 7]
def baseStart_688004 : Nat := 118140960795 + 688004 * 2 ^ 59
def prefixEnd_688004 : Nat := 4983230072969 + 3 ^ 40 * 688004 * 2
def baseEnd_688004 : Nat := 39252971579559046098437

theorem tailTrace_688004 : CollatzResearch.WordTrace tailWord_688004 prefixEnd_688004 39252971579559046098437 := by
  unfold tailWord_688004
  simp only [CollatzResearch.WordTrace]
  refine ⟨12546783699743242286759533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16729044932990989715679377 12546783699743242286759533)
  ·
    refine ⟨4705043887403715857534825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12546783699743242286759533 4705043887403715857534825)
    ·
      refine ⟨3528782915552786893151119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4705043887403715857534825 3528782915552786893151119)
      ·
        refine ⟨5293174373329180339726679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3528782915552786893151119 5293174373329180339726679)
        ·
          refine ⟨7939761559993770509590019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5293174373329180339726679 7939761559993770509590019)
          ·
            refine ⟨11909642339990655764385029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7939761559993770509590019 11909642339990655764385029)
            ·
              refine ⟨2233057938748247955822193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11909642339990655764385029 2233057938748247955822193)
              ·
                refine ⟨1674793454061185966866645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2233057938748247955822193 1674793454061185966866645)
                ·
                  refine ⟨39252971579559046098437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1674793454061185966866645 39252971579559046098437)
                  ·
                    rfl

theorem cell23_688004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 4, 2, 7].length) (baseStart_688004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_688004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_688004 prefixEnd_688004 := by exact prefixLift 688004
  have htrace : WordTrace (prefixWord ++ tailWord_688004) baseStart_688004 baseEnd_688004 := by
    simpa [prefixWord, tailWord_688004, baseEnd_688004] using wordTrace_append hprefix tailTrace_688004
  have hstable : (prefixWord ++ tailWord_688004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_688004).length < 2 ^ (prefixWord ++ tailWord_688004).sum := by decide
  have hdescent : baseEnd_688004 < baseStart_688004 := by decide
  rcases family_descends (prefixWord ++ tailWord_688004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_688071 : List Nat := [1, 1, 4, 1, 1, 2, 1, 2, 4, 4, 2]
def baseStart_688071 : Nat := 118140960795 + 688071 * 2 ^ 59
def prefixEnd_688071 : Nat := 4983230072969 + 3 ^ 40 * 688071 * 2
def baseEnd_688071 : Nat := 353311147419882652748125

theorem tailTrace_688071 : CollatzResearch.WordTrace tailWord_688071 prefixEnd_688071 353311147419882652748125 := by
  unfold tailWord_688071
  simp only [CollatzResearch.WordTrace]
  refine ⟨25096011090243755016208067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16730674060162503344138711 25096011090243755016208067)
  ·
    refine ⟨37644016635365632524312101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25096011090243755016208067 37644016635365632524312101)
    ·
      refine ⟨7058253119131056098308519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 37644016635365632524312101 7058253119131056098308519)
      ·
        refine ⟨10587379678696584147462779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7058253119131056098308519 10587379678696584147462779)
        ·
          refine ⟨15881069518044876221194169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10587379678696584147462779 15881069518044876221194169)
          ·
            refine ⟨11910802138533657165895627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15881069518044876221194169 11910802138533657165895627)
            ·
              refine ⟨17866203207800485748843441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11910802138533657165895627 17866203207800485748843441)
              ·
                refine ⟨13399652405850364311632581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17866203207800485748843441 13399652405850364311632581)
                ·
                  refine ⟨2512434826096943308431109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13399652405850364311632581 2512434826096943308431109)
                  ·
                    refine ⟨471081529893176870330833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2512434826096943308431109 471081529893176870330833)
                    ·
                      refine ⟨353311147419882652748125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 471081529893176870330833 353311147419882652748125)
                      ·
                        rfl

theorem cell23_688071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 2, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 2, 4, 4, 2].length) (baseStart_688071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_688071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_688071 prefixEnd_688071 := by exact prefixLift 688071
  have htrace : WordTrace (prefixWord ++ tailWord_688071) baseStart_688071 baseEnd_688071 := by
    simpa [prefixWord, tailWord_688071, baseEnd_688071] using wordTrace_append hprefix tailTrace_688071
  have hstable : (prefixWord ++ tailWord_688071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_688071).length < 2 ^ (prefixWord ++ tailWord_688071).sum := by decide
  have hdescent : baseEnd_688071 < baseStart_688071 := by decide
  rcases family_descends (prefixWord ++ tailWord_688071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_688178 : List Nat := [3, 2, 1, 1, 2, 3, 1, 4, 1, 1, 4]
def baseStart_688178 : Nat := 118140960795 + 688178 * 2 ^ 59
def prefixEnd_688178 : Nat := 4983230072969 + 3 ^ 40 * 688178 * 2
def baseEnd_688178 : Nat := 353366089849913734110133

theorem tailTrace_688178 : CollatzResearch.WordTrace tailWord_688178 prefixEnd_688178 353366089849913734110133 := by
  unfold tailWord_688178
  simp only [CollatzResearch.WordTrace]
  refine ⟨6274978425214028072588297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16733275800570741526902125 6274978425214028072588297)
  ·
    refine ⟨4706233818910521054441223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6274978425214028072588297 4706233818910521054441223)
    ·
      refine ⟨7059350728365781581661835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4706233818910521054441223 7059350728365781581661835)
      ·
        refine ⟨10589026092548672372492753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7059350728365781581661835 10589026092548672372492753)
        ·
          refine ⟨7941769569411504279369565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10589026092548672372492753 7941769569411504279369565)
          ·
            refine ⟨2978163588529314104763587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7941769569411504279369565 2978163588529314104763587)
            ·
              refine ⟨4467245382793971157145381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2978163588529314104763587 4467245382793971157145381)
              ·
                refine ⟨837608509273869591964759, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4467245382793971157145381 837608509273869591964759)
                ·
                  refine ⟨1256412763910804387947139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 837608509273869591964759 1256412763910804387947139)
                  ·
                    refine ⟨1884619145866206581920709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1256412763910804387947139 1884619145866206581920709)
                    ·
                      refine ⟨353366089849913734110133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1884619145866206581920709 353366089849913734110133)
                      ·
                        rfl

theorem cell23_688178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 1, 4, 1, 1, 4].length) (baseStart_688178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_688178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_688178 prefixEnd_688178 := by exact prefixLift 688178
  have htrace : WordTrace (prefixWord ++ tailWord_688178) baseStart_688178 baseEnd_688178 := by
    simpa [prefixWord, tailWord_688178, baseEnd_688178] using wordTrace_append hprefix tailTrace_688178
  have hstable : (prefixWord ++ tailWord_688178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_688178).length < 2 ^ (prefixWord ++ tailWord_688178).sum := by decide
  have hdescent : baseEnd_688178 < baseStart_688178 := by decide
  rcases family_descends (prefixWord ++ tailWord_688178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_688191 : List Nat := [1, 1, 2, 2, 3, 1, 2, 4, 1, 2, 4]
def baseStart_688191 : Nat := 118140960795 + 688191 * 2 ^ 59
def prefixEnd_688191 : Nat := 4983230072969 + 3 ^ 40 * 688191 * 2
def baseEnd_688191 : Nat := 353372765098422183247573

theorem tailTrace_688191 : CollatzResearch.WordTrace tailWord_688191 prefixEnd_688191 353372765098422183247573 := by
  unfold tailWord_688191
  simp only [CollatzResearch.WordTrace]
  refine ⟨25100387849809015510576427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16733591899872677007050951 25100387849809015510576427)
  ·
    refine ⟨37650581774713523265864641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25100387849809015510576427 37650581774713523265864641)
    ·
      refine ⟨28237936331035142449398481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37650581774713523265864641 28237936331035142449398481)
      ·
        refine ⟨21178452248276356837048861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28237936331035142449398481 21178452248276356837048861)
        ·
          refine ⟨7941919593103633813893323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21178452248276356837048861 7941919593103633813893323)
          ·
            refine ⟨11912879389655450720839985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7941919593103633813893323 11912879389655450720839985)
            ·
              refine ⟨8934659542241588040629989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11912879389655450720839985 8934659542241588040629989)
              ·
                refine ⟨1675248664170297757618123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8934659542241588040629989 1675248664170297757618123)
                ·
                  refine ⟨2512872996255446636427185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1675248664170297757618123 2512872996255446636427185)
                  ·
                    refine ⟨1884654747191584977320389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2512872996255446636427185 1884654747191584977320389)
                    ·
                      refine ⟨353372765098422183247573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1884654747191584977320389 353372765098422183247573)
                      ·
                        rfl

theorem cell23_688191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 2, 4, 1, 2, 4].length) (baseStart_688191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_688191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_688191 prefixEnd_688191 := by exact prefixLift 688191
  have htrace : WordTrace (prefixWord ++ tailWord_688191) baseStart_688191 baseEnd_688191 := by
    simpa [prefixWord, tailWord_688191, baseEnd_688191] using wordTrace_append hprefix tailTrace_688191
  have hstable : (prefixWord ++ tailWord_688191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_688191).length < 2 ^ (prefixWord ++ tailWord_688191).sum := by decide
  have hdescent : baseEnd_688191 < baseStart_688191 := by decide
  rcases family_descends (prefixWord ++ tailWord_688191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_688205 : List Nat := [1, 6, 1, 1, 1, 1, 2, 4, 2, 4]
def baseStart_688205 : Nat := 118140960795 + 688205 * 2 ^ 59
def prefixEnd_688205 : Nat := 4983230072969 + 3 ^ 40 * 688205 * 2
def baseEnd_688205 : Nat := 117793317942528376157503

theorem tailTrace_688205 : CollatzResearch.WordTrace tailWord_688205 prefixEnd_688205 117793317942528376157503 := by
  unfold tailWord_688205
  simp only [CollatzResearch.WordTrace]
  refine ⟨25100898471758295901586069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16733932314505530601057379 25100898471758295901586069)
  ·
    refine ⟨1176604615863670120386847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 25100898471758295901586069 1176604615863670120386847)
    ·
      refine ⟨1764906923795505180580271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1176604615863670120386847 1764906923795505180580271)
      ·
        refine ⟨2647360385693257770870407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1764906923795505180580271 2647360385693257770870407)
        ·
          refine ⟨3971040578539886656305611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2647360385693257770870407 3971040578539886656305611)
          ·
            refine ⟨5956560867809829984458417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3971040578539886656305611 5956560867809829984458417)
            ·
              refine ⟨4467420650857372488343813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5956560867809829984458417 4467420650857372488343813)
              ·
                refine ⟨837641372035757341564465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4467420650857372488343813 837641372035757341564465)
                ·
                  refine ⟨628231029026818006173349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 837641372035757341564465 628231029026818006173349)
                  ·
                    refine ⟨117793317942528376157503, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 628231029026818006173349 117793317942528376157503)
                    ·
                      rfl

theorem cell23_688205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 2, 4, 2, 4].length) (baseStart_688205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_688205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_688205 prefixEnd_688205 := by exact prefixLift 688205
  have htrace : WordTrace (prefixWord ++ tailWord_688205) baseStart_688205 baseEnd_688205 := by
    simpa [prefixWord, tailWord_688205, baseEnd_688205] using wordTrace_append hprefix tailTrace_688205
  have hstable : (prefixWord ++ tailWord_688205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_688205).length < 2 ^ (prefixWord ++ tailWord_688205).sum := by decide
  have hdescent : baseEnd_688205 < baseStart_688205 := by decide
  rcases family_descends (prefixWord ++ tailWord_688205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_688285 : List Nat := [1, 4, 2, 1, 1, 3, 1, 3, 1, 4, 2]
def baseStart_688285 : Nat := 118140960795 + 688285 * 2 ^ 59
def prefixEnd_688285 : Nat := 4983230072969 + 3 ^ 40 * 688285 * 2
def baseEnd_688285 : Nat := 353421032279944815472141

theorem tailTrace_688285 : CollatzResearch.WordTrace tailWord_688285 prefixEnd_688285 353421032279944815472141 := by
  unfold tailWord_688285
  simp only [CollatzResearch.WordTrace]
  refine ⟨25103816311468469564498309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16735877540978979709665539 25103816311468469564498309)
  ·
    refine ⟨4706965558400338043343433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 25103816311468469564498309 4706965558400338043343433)
    ·
      refine ⟨3530224168800253532507575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4706965558400338043343433 3530224168800253532507575)
      ·
        refine ⟨5295336253200380298761363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3530224168800253532507575 5295336253200380298761363)
        ·
          refine ⟨7943004379800570448142045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5295336253200380298761363 7943004379800570448142045)
          ·
            refine ⟨2978626642425213918053267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7943004379800570448142045 2978626642425213918053267)
            ·
              refine ⟨4467939963637820877079901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2978626642425213918053267 4467939963637820877079901)
              ·
                refine ⟨1675477486364182828904963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4467939963637820877079901 1675477486364182828904963)
                ·
                  refine ⟨2513216229546274243357445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1675477486364182828904963 2513216229546274243357445)
                  ·
                    refine ⟨471228043039926420629521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2513216229546274243357445 471228043039926420629521)
                    ·
                      refine ⟨353421032279944815472141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 471228043039926420629521 353421032279944815472141)
                      ·
                        rfl

theorem cell23_688285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 1, 3, 1, 4, 2].length) (baseStart_688285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_688285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_688285 prefixEnd_688285 := by exact prefixLift 688285
  have htrace : WordTrace (prefixWord ++ tailWord_688285) baseStart_688285 baseEnd_688285 := by
    simpa [prefixWord, tailWord_688285, baseEnd_688285] using wordTrace_append hprefix tailTrace_688285
  have hstable : (prefixWord ++ tailWord_688285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_688285).length < 2 ^ (prefixWord ++ tailWord_688285).sum := by decide
  have hdescent : baseEnd_688285 < baseStart_688285 := by decide
  rcases family_descends (prefixWord ++ tailWord_688285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_688331 : List Nat := [1, 1, 1, 1, 3, 2, 4, 1, 1, 1, 7]
def baseStart_688331 : Nat := 118140960795 + 688331 * 2 ^ 59
def prefixEnd_688331 : Nat := 4983230072969 + 3 ^ 40 * 688331 * 2
def baseEnd_688331 : Nat := 353444652390051635496929

theorem tailTrace_688331 : CollatzResearch.WordTrace tailWord_688331 prefixEnd_688331 353444652390051635496929 := by
  unfold tailWord_688331
  simp only [CollatzResearch.WordTrace]
  refine ⟨25105494069301819420672847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16736996046201212947115231 25105494069301819420672847)
  ·
    refine ⟨37658241103952729131009271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25105494069301819420672847 37658241103952729131009271)
    ·
      refine ⟨56487361655929093696513907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37658241103952729131009271 56487361655929093696513907)
      ·
        refine ⟨84731042483893640544770861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56487361655929093696513907 84731042483893640544770861)
        ·
          refine ⟨31774140931460115204289073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 84731042483893640544770861 31774140931460115204289073)
          ·
            refine ⟨23830605698595086403216805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31774140931460115204289073 23830605698595086403216805)
            ·
              refine ⟨4468238568486578700603151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23830605698595086403216805 4468238568486578700603151)
              ·
                refine ⟨6702357852729868050904727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4468238568486578700603151 6702357852729868050904727)
                ·
                  refine ⟨10053536779094802076357091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6702357852729868050904727 10053536779094802076357091)
                  ·
                    refine ⟨15080305168642203114535637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10053536779094802076357091 15080305168642203114535637)
                    ·
                      refine ⟨353444652390051635496929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 15080305168642203114535637 353444652390051635496929)
                      ·
                        rfl

theorem cell23_688331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 4, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 4, 1, 1, 1, 7].length) (baseStart_688331 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_688331 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_688331 prefixEnd_688331 := by exact prefixLift 688331
  have htrace : WordTrace (prefixWord ++ tailWord_688331) baseStart_688331 baseEnd_688331 := by
    simpa [prefixWord, tailWord_688331, baseEnd_688331] using wordTrace_append hprefix tailTrace_688331
  have hstable : (prefixWord ++ tailWord_688331).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_688331).length < 2 ^ (prefixWord ++ tailWord_688331).sum := by decide
  have hdescent : baseEnd_688331 < baseStart_688331 := by decide
  rcases family_descends (prefixWord ++ tailWord_688331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_688338 : List Nat := [3, 2, 2, 2, 1, 2, 1, 2, 1, 7]
def baseStart_688338 : Nat := 118140960795 + 688338 * 2 ^ 59
def prefixEnd_688338 : Nat := 4983230072969 + 3 ^ 40 * 688338 * 2
def baseEnd_688338 : Nat := 117816082251544369369799

theorem tailTrace_688338 : CollatzResearch.WordTrace tailWord_688338 prefixEnd_688338 117816082251544369369799 := by
  unfold tailWord_688338
  simp only [CollatzResearch.WordTrace]
  refine ⟨6276437345069114904044417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16737166253517639744118445 6276437345069114904044417)
  ·
    refine ⟨4707328008801836178033313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6276437345069114904044417 4707328008801836178033313)
    ·
      refine ⟨3530496006601377133524985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4707328008801836178033313 3530496006601377133524985)
      ·
        refine ⟨2647872004951032850143739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3530496006601377133524985 2647872004951032850143739)
        ·
          refine ⟨3971808007426549275215609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2647872004951032850143739 3971808007426549275215609)
          ·
            refine ⟨2978856005569911956411707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3971808007426549275215609 2978856005569911956411707)
            ·
              refine ⟨4468284008354867934617561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2978856005569911956411707 4468284008354867934617561)
              ·
                refine ⟨3351213006266150950963171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4468284008354867934617561 3351213006266150950963171)
                ·
                  refine ⟨5026819509399226426444757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3351213006266150950963171 5026819509399226426444757)
                  ·
                    refine ⟨117816082251544369369799, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 5026819509399226426444757 117816082251544369369799)
                    ·
                      rfl

theorem cell23_688338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 1, 2, 1, 7].length) (baseStart_688338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_688338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_688338 prefixEnd_688338 := by exact prefixLift 688338
  have htrace : WordTrace (prefixWord ++ tailWord_688338) baseStart_688338 baseEnd_688338 := by
    simpa [prefixWord, tailWord_688338, baseEnd_688338] using wordTrace_append hprefix tailTrace_688338
  have hstable : (prefixWord ++ tailWord_688338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_688338).length < 2 ^ (prefixWord ++ tailWord_688338).sum := by decide
  have hdescent : baseEnd_688338 < baseStart_688338 := by decide
  rcases family_descends (prefixWord ++ tailWord_688338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_688351 : List Nat := [1, 1, 2, 3, 2, 1, 1, 1, 1, 10]
def baseStart_688351 : Nat := 118140960795 + 688351 * 2 ^ 59
def prefixEnd_688351 : Nat := 4983230072969 + 3 ^ 40 * 688351 * 2
def baseEnd_688351 : Nat := 117818307334380519082279

theorem tailTrace_688351 : CollatzResearch.WordTrace tailWord_688351 prefixEnd_688351 117818307334380519082279 := by
  unfold tailWord_688351
  simp only [CollatzResearch.WordTrace]
  refine ⟨25106223529229362836400907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16737482352819575224267271 25106223529229362836400907)
  ·
    refine ⟨37659335293844044254601361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25106223529229362836400907 37659335293844044254601361)
    ·
      refine ⟨28244501470383033190951021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37659335293844044254601361 28244501470383033190951021)
      ·
        refine ⟨10591688051393637446606633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28244501470383033190951021 10591688051393637446606633)
        ·
          refine ⟨7943766038545228084954975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10591688051393637446606633 7943766038545228084954975)
          ·
            refine ⟨11915649057817842127432463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7943766038545228084954975 11915649057817842127432463)
            ·
              refine ⟨17873473586726763191148695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11915649057817842127432463 17873473586726763191148695)
              ·
                refine ⟨26810210380090144786723043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17873473586726763191148695 26810210380090144786723043)
                ·
                  refine ⟨40215315570135217180084565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26810210380090144786723043 40215315570135217180084565)
                  ·
                    refine ⟨117818307334380519082279, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 40215315570135217180084565 117818307334380519082279)
                    ·
                      rfl

theorem cell23_688351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 1, 1, 10].length) (baseStart_688351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_688351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_688351 prefixEnd_688351 := by exact prefixLift 688351
  have htrace : WordTrace (prefixWord ++ tailWord_688351) baseStart_688351 baseEnd_688351 := by
    simpa [prefixWord, tailWord_688351, baseEnd_688351] using wordTrace_append hprefix tailTrace_688351
  have hstable : (prefixWord ++ tailWord_688351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_688351).length < 2 ^ (prefixWord ++ tailWord_688351).sum := by decide
  have hdescent : baseEnd_688351 < baseStart_688351 := by decide
  rcases family_descends (prefixWord ++ tailWord_688351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_688368 : List Nat := [2, 1, 1, 1, 3, 1, 1, 4, 5, 4]
def baseStart_688368 : Nat := 118140960795 + 688368 * 2 ^ 59
def prefixEnd_688368 : Nat := 4983230072969 + 3 ^ 40 * 688368 * 2
def baseEnd_688368 : Nat := 117821217058089330244753

theorem tailTrace_688368 : CollatzResearch.WordTrace tailWord_688368 prefixEnd_688368 117821217058089330244753 := by
  unfold tailWord_688368
  simp only [CollatzResearch.WordTrace]
  refine ⟨12553421785083887369884879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16737895713445183159846505 12553421785083887369884879)
  ·
    refine ⟨18830132677625831054827319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12553421785083887369884879 18830132677625831054827319)
    ·
      refine ⟨28245199016438746582240979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18830132677625831054827319 28245199016438746582240979)
      ·
        refine ⟨42367798524658119873361469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28245199016438746582240979 42367798524658119873361469)
        ·
          refine ⟨15887924446746794952510551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42367798524658119873361469 15887924446746794952510551)
          ·
            refine ⟨23831886670120192428765827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15887924446746794952510551 23831886670120192428765827)
            ·
              refine ⟨35747830005180288643148741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23831886670120192428765827 35747830005180288643148741)
              ·
                refine ⟨6702718125971304120590389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 35747830005180288643148741 6702718125971304120590389)
                ·
                  refine ⟨628379824309809761305349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 6702718125971304120590389 628379824309809761305349)
                  ·
                    refine ⟨117821217058089330244753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 628379824309809761305349 117821217058089330244753)
                    ·
                      rfl

theorem cell23_688368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 4, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 4, 5, 4].length) (baseStart_688368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_688368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_688368 prefixEnd_688368 := by exact prefixLift 688368
  have htrace : WordTrace (prefixWord ++ tailWord_688368) baseStart_688368 baseEnd_688368 := by
    simpa [prefixWord, tailWord_688368, baseEnd_688368] using wordTrace_append hprefix tailTrace_688368
  have hstable : (prefixWord ++ tailWord_688368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_688368).length < 2 ^ (prefixWord ++ tailWord_688368).sum := by decide
  have hdescent : baseEnd_688368 < baseStart_688368 := by decide
  rcases family_descends (prefixWord ++ tailWord_688368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_688436 : List Nat := [2, 5, 1, 1, 1, 2, 4, 2, 1, 4]
def baseStart_688436 : Nat := 118140960795 + 688436 * 2 ^ 59
def prefixEnd_688436 : Nat := 4983230072969 + 3 ^ 40 * 688436 * 2
def baseEnd_688436 : Nat := 117832855952924574894649

theorem tailTrace_688436 : CollatzResearch.WordTrace tailWord_688436 prefixEnd_688436 117832855952924574894649 := by
  unfold tailWord_688436
  simp only [CollatzResearch.WordTrace]
  refine ⟨12554661866960711176622581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16739549155947614902163441 12554661866960711176622581)
  ·
    refine ⟨1176999550027566672808367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 12554661866960711176622581 1176999550027566672808367)
    ·
      refine ⟨1765499325041350009212551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1176999550027566672808367 1765499325041350009212551)
      ·
        refine ⟨2648248987562025013818827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1765499325041350009212551 2648248987562025013818827)
        ·
          refine ⟨3972373481343037520728241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2648248987562025013818827 3972373481343037520728241)
          ·
            refine ⟨2979280111007278140546181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3972373481343037520728241 2979280111007278140546181)
            ·
              refine ⟨558615020813864651352409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2979280111007278140546181 558615020813864651352409)
              ·
                refine ⟨418961265610398488514307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 558615020813864651352409 418961265610398488514307)
                ·
                  refine ⟨628441898415597732771461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 418961265610398488514307 628441898415597732771461)
                  ·
                    refine ⟨117832855952924574894649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 628441898415597732771461 117832855952924574894649)
                    ·
                      rfl

theorem cell23_688436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 4, 2, 1, 4].length) (baseStart_688436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_688436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_688436 prefixEnd_688436 := by exact prefixLift 688436
  have htrace : WordTrace (prefixWord ++ tailWord_688436) baseStart_688436 baseEnd_688436 := by
    simpa [prefixWord, tailWord_688436, baseEnd_688436] using wordTrace_append hprefix tailTrace_688436
  have hstable : (prefixWord ++ tailWord_688436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_688436).length < 2 ^ (prefixWord ++ tailWord_688436).sum := by decide
  have hdescent : baseEnd_688436 < baseStart_688436 := by decide
  rcases family_descends (prefixWord ++ tailWord_688436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_688465 : List Nat := [1, 2, 2, 1, 4, 2, 2, 1, 3, 1, 4]
def baseStart_688465 : Nat := 118140960795 + 688465 * 2 ^ 59
def prefixEnd_688465 : Nat := 4983230072969 + 3 ^ 40 * 688465 * 2
def baseEnd_688465 : Nat := 353513458797754111221313

theorem tailTrace_688465 : CollatzResearch.WordTrace tailWord_688465 prefixEnd_688465 353513458797754111221313 := by
  unfold tailWord_688465
  simp only [CollatzResearch.WordTrace]
  refine ⟨25110381450816360306050849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16740254300544240204033899 25110381450816360306050849)
  ·
    refine ⟨18832786088112270229538137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25110381450816360306050849 18832786088112270229538137)
    ·
      refine ⟨14124589566084202672153603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18832786088112270229538137 14124589566084202672153603)
      ·
        refine ⟨21186884349126304008230405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14124589566084202672153603 21186884349126304008230405)
        ·
          refine ⟨3972540815461182001543201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21186884349126304008230405 3972540815461182001543201)
          ·
            refine ⟨2979405611595886501157401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3972540815461182001543201 2979405611595886501157401)
            ·
              refine ⟨2234554208696914875868051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2979405611595886501157401 2234554208696914875868051)
              ·
                refine ⟨3351831313045372313802077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2234554208696914875868051 3351831313045372313802077)
                ·
                  refine ⟨1256936742392014617675779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3351831313045372313802077 1256936742392014617675779)
                  ·
                    refine ⟨1885405113588021926513669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1256936742392014617675779 1885405113588021926513669)
                    ·
                      refine ⟨353513458797754111221313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1885405113588021926513669 353513458797754111221313)
                      ·
                        rfl

theorem cell23_688465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 2, 1, 3, 1, 4].length) (baseStart_688465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_688465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_688465 prefixEnd_688465 := by exact prefixLift 688465
  have htrace : WordTrace (prefixWord ++ tailWord_688465) baseStart_688465 baseEnd_688465 := by
    simpa [prefixWord, tailWord_688465, baseEnd_688465] using wordTrace_append hprefix tailTrace_688465
  have hstable : (prefixWord ++ tailWord_688465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_688465).length < 2 ^ (prefixWord ++ tailWord_688465).sum := by decide
  have hdescent : baseEnd_688465 < baseStart_688465 := by decide
  rcases family_descends (prefixWord ++ tailWord_688465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_688492 : List Nat := [2, 2, 1, 1, 6, 1, 1, 1, 4, 4]
def baseStart_688492 : Nat := 118140960795 + 688492 * 2 ^ 59
def prefixEnd_688492 : Nat := 4983230072969 + 3 ^ 40 * 688492 * 2
def baseEnd_688492 : Nat := 117842440925141835194563

theorem tailTrace_688492 : CollatzResearch.WordTrace tailWord_688492 prefixEnd_688492 117842440925141835194563 := by
  unfold tailWord_688492
  simp only [CollatzResearch.WordTrace]
  refine ⟨12555683110859271958641865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16740910814479029278189153 12555683110859271958641865)
  ·
    refine ⟨9416762333144453968981399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12555683110859271958641865 9416762333144453968981399)
    ·
      refine ⟨14125143499716680953472099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9416762333144453968981399 14125143499716680953472099)
      ·
        refine ⟨21187715249575021430208149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14125143499716680953472099 21187715249575021430208149)
        ·
          refine ⟨993174152323829129541007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 21187715249575021430208149 993174152323829129541007)
          ·
            refine ⟨1489761228485743694311511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 993174152323829129541007 1489761228485743694311511)
            ·
              refine ⟨2234641842728615541467267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1489761228485743694311511 2234641842728615541467267)
              ·
                refine ⟨3351962764092923312200901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2234641842728615541467267 3351962764092923312200901)
                ·
                  refine ⟨628493018267423121037669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3351962764092923312200901 628493018267423121037669)
                  ·
                    refine ⟨117842440925141835194563, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 628493018267423121037669 117842440925141835194563)
                    ·
                      rfl

theorem cell23_688492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 4, 4].length) (baseStart_688492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_688492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_688492 prefixEnd_688492 := by exact prefixLift 688492
  have htrace : WordTrace (prefixWord ++ tailWord_688492) baseStart_688492 baseEnd_688492 := by
    simpa [prefixWord, tailWord_688492, baseEnd_688492] using wordTrace_append hprefix tailTrace_688492
  have hstable : (prefixWord ++ tailWord_688492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_688492).length < 2 ^ (prefixWord ++ tailWord_688492).sum := by decide
  have hdescent : baseEnd_688492 < baseStart_688492 := by decide
  rcases family_descends (prefixWord ++ tailWord_688492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_688508 : List Nat := [2, 2, 2, 1, 1, 1, 2, 1, 1, 4, 6]
def baseStart_688508 : Nat := 118140960795 + 688508 * 2 ^ 59
def prefixEnd_688508 : Nat := 4983230072969 + 3 ^ 40 * 688508 * 2
def baseEnd_688508 : Nat := 353535538465897442983615

theorem tailTrace_688508 : CollatzResearch.WordTrace tailWord_688508 prefixEnd_688508 353535538465897442983615 := by
  unfold tailWord_688508
  simp only [CollatzResearch.WordTrace]
  refine ⟨12555974894830289324933089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16741299859773719099910785 12555974894830289324933089)
  ·
    refine ⟨9416981171122716993699817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12555974894830289324933089 9416981171122716993699817)
    ·
      refine ⟨7062735878342037745274863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9416981171122716993699817 7062735878342037745274863)
      ·
        refine ⟨10594103817513056617912295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7062735878342037745274863 10594103817513056617912295)
        ·
          refine ⟨15891155726269584926868443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10594103817513056617912295 15891155726269584926868443)
          ·
            refine ⟨23836733589404377390302665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15891155726269584926868443 23836733589404377390302665)
            ·
              refine ⟨17877550192053283042726999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23836733589404377390302665 17877550192053283042726999)
              ·
                refine ⟨26816325288079924564090499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17877550192053283042726999 26816325288079924564090499)
                ·
                  refine ⟨40224487932119886846135749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26816325288079924564090499 40224487932119886846135749)
                  ·
                    refine ⟨7542091487272478783650453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 40224487932119886846135749 7542091487272478783650453)
                    ·
                      refine ⟨353535538465897442983615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 7542091487272478783650453 353535538465897442983615)
                      ·
                        rfl

theorem cell23_688508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 1, 1, 4, 6].length) (baseStart_688508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_688508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_688508 prefixEnd_688508 := by exact prefixLift 688508
  have htrace : WordTrace (prefixWord ++ tailWord_688508) baseStart_688508 baseEnd_688508 := by
    simpa [prefixWord, tailWord_688508, baseEnd_688508] using wordTrace_append hprefix tailTrace_688508
  have hstable : (prefixWord ++ tailWord_688508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_688508).length < 2 ^ (prefixWord ++ tailWord_688508).sum := by decide
  have hdescent : baseEnd_688508 < baseStart_688508 := by decide
  rcases family_descends (prefixWord ++ tailWord_688508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_688509 : List Nat := [1, 4, 1, 1, 2, 4, 3, 1, 2, 4]
def baseStart_688509 : Nat := 118140960795 + 688509 * 2 ^ 59
def prefixEnd_688509 : Nat := 4983230072969 + 3 ^ 40 * 688509 * 2
def baseEnd_688509 : Nat := 117845350648850646357037

theorem tailTrace_688509 : CollatzResearch.WordTrace tailWord_688509 prefixEnd_688509 117845350648850646357037 := by
  unfold tailWord_688509
  simp only [CollatzResearch.WordTrace]
  refine ⟨25111986262656955820652581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16741324175104637213768387 25111986262656955820652581)
  ·
    refine ⟨4708497424248179216372359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 25111986262656955820652581 4708497424248179216372359)
    ·
      refine ⟨7062746136372268824558539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4708497424248179216372359 7062746136372268824558539)
      ·
        refine ⟨10594119204558403236837809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7062746136372268824558539 10594119204558403236837809)
        ·
          refine ⟨7945589403418802427628357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10594119204558403236837809 7945589403418802427628357)
          ·
            refine ⟨1489798013141025455180317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7945589403418802427628357 1489798013141025455180317)
            ·
              refine ⟨558674254927884545692619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1489798013141025455180317 558674254927884545692619)
              ·
                refine ⟨838011382391826818538929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 558674254927884545692619 838011382391826818538929)
                ·
                  refine ⟨628508536793870113904197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 838011382391826818538929 628508536793870113904197)
                  ·
                    refine ⟨117845350648850646357037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 628508536793870113904197 117845350648850646357037)
                    ·
                      rfl

theorem cell23_688509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 4, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 4, 3, 1, 2, 4].length) (baseStart_688509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_688509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_688509 prefixEnd_688509 := by exact prefixLift 688509
  have htrace : WordTrace (prefixWord ++ tailWord_688509) baseStart_688509 baseEnd_688509 := by
    simpa [prefixWord, tailWord_688509, baseEnd_688509] using wordTrace_append hprefix tailTrace_688509
  have hstable : (prefixWord ++ tailWord_688509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_688509).length < 2 ^ (prefixWord ++ tailWord_688509).sum := by decide
  have hdescent : baseEnd_688509 < baseStart_688509 := by decide
  rcases family_descends (prefixWord ++ tailWord_688509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_688522 : List Nat := [3, 1, 2, 5, 1, 1, 1, 9]
def baseStart_688522 : Nat := 118140960795 + 688522 * 2 ^ 59
def prefixEnd_688522 : Nat := 4983230072969 + 3 ^ 40 * 688522 * 2
def baseEnd_688522 : Nat := 13094175081298532896613

theorem tailTrace_688522 : CollatzResearch.WordTrace tailWord_688522 prefixEnd_688522 13094175081298532896613 := by
  unfold tailWord_688522
  simp only [CollatzResearch.WordTrace]
  refine ⟨6278115102902464760218955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16741640274406572693917213 6278115102902464760218955)
  ·
    refine ⟨9417172654353697140328433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6278115102902464760218955 9417172654353697140328433)
    ·
      refine ⟨7062879490765272855246325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9417172654353697140328433 7062879490765272855246325)
      ·
        refine ⟨662144952259244330179343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 7062879490765272855246325 662144952259244330179343)
        ·
          refine ⟨993217428388866495269015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 662144952259244330179343 993217428388866495269015)
          ·
            refine ⟨1489826142583299742903523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 993217428388866495269015 1489826142583299742903523)
            ·
              refine ⟨2234739213874949614355285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1489826142583299742903523 2234739213874949614355285)
              ·
                refine ⟨13094175081298532896613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 2234739213874949614355285 13094175081298532896613)
                ·
                  rfl

theorem cell23_688522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 1, 1, 9].length) (baseStart_688522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_688522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_688522 prefixEnd_688522 := by exact prefixLift 688522
  have htrace : WordTrace (prefixWord ++ tailWord_688522) baseStart_688522 baseEnd_688522 := by
    simpa [prefixWord, tailWord_688522, baseEnd_688522] using wordTrace_append hprefix tailTrace_688522
  have hstable : (prefixWord ++ tailWord_688522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_688522).length < 2 ^ (prefixWord ++ tailWord_688522).sum := by decide
  have hdescent : baseEnd_688522 < baseStart_688522 := by decide
  rcases family_descends (prefixWord ++ tailWord_688522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_688622 : List Nat := [4, 1, 2, 1, 2, 2, 1, 1, 1, 5, 3]
def baseStart_688622 : Nat := 118140960795 + 688622 * 2 ^ 59
def prefixEnd_688622 : Nat := 4983230072969 + 3 ^ 40 * 688622 * 2
def baseEnd_688622 : Nat := 353594075260509996958091

theorem tailTrace_688622 : CollatzResearch.WordTrace tailWord_688622 prefixEnd_688622 353594075260509996958091 := by
  unfold tailWord_688622
  simp only [CollatzResearch.WordTrace]
  refine ⟨3139513463905947014939515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 16744071807498384079677413 3139513463905947014939515)
  ·
    refine ⟨4709270195858920522409273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3139513463905947014939515 4709270195858920522409273)
    ·
      refine ⟨3531952646894190391806955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4709270195858920522409273 3531952646894190391806955)
      ·
        refine ⟨5297928970341285587710433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3531952646894190391806955 5297928970341285587710433)
        ·
          refine ⟨3973446727755964190782825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5297928970341285587710433 3973446727755964190782825)
          ·
            refine ⟨2980085045816973143087119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3973446727755964190782825 2980085045816973143087119)
            ·
              refine ⟨4470127568725459714630679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2980085045816973143087119 4470127568725459714630679)
              ·
                refine ⟨6705191353088189571946019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4470127568725459714630679 6705191353088189571946019)
                ·
                  refine ⟨10057787029632284357919029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6705191353088189571946019 10057787029632284357919029)
                  ·
                    refine ⟨942917534028026658554909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10057787029632284357919029 942917534028026658554909)
                    ·
                      refine ⟨353594075260509996958091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 942917534028026658554909 353594075260509996958091)
                      ·
                        rfl

theorem cell23_688622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 1, 1, 1, 5, 3].length) (baseStart_688622 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_688622 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_688622 prefixEnd_688622 := by exact prefixLift 688622
  have htrace : WordTrace (prefixWord ++ tailWord_688622) baseStart_688622 baseEnd_688622 := by
    simpa [prefixWord, tailWord_688622, baseEnd_688622] using wordTrace_append hprefix tailTrace_688622
  have hstable : (prefixWord ++ tailWord_688622).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_688622).length < 2 ^ (prefixWord ++ tailWord_688622).sum := by decide
  have hdescent : baseEnd_688622 < baseStart_688622 := by decide
  rcases family_descends (prefixWord ++ tailWord_688622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_688625 : List Nat := [1, 2, 2, 2, 3, 1, 2, 2, 1, 7]
def baseStart_688625 : Nat := 118140960795 + 688625 * 2 ^ 59
def prefixEnd_688625 : Nat := 4983230072969 + 3 ^ 40 * 688625 * 2
def baseEnd_688625 : Nat := 117865205234157828406859

theorem tailTrace_688625 : CollatzResearch.WordTrace tailWord_688625 prefixEnd_688625 117865205234157828406859 := by
  unfold tailWord_688625
  simp only [CollatzResearch.WordTrace]
  refine ⟨25116217130236707631875329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16744144753491138421250219 25116217130236707631875329)
  ·
    refine ⟨18837162847677530723906497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25116217130236707631875329 18837162847677530723906497)
    ·
      refine ⟨14127872135758148042929873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18837162847677530723906497 14127872135758148042929873)
      ·
        refine ⟨10595904101818611032197405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14127872135758148042929873 10595904101818611032197405)
        ·
          refine ⟨3973464038181979137074027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10595904101818611032197405 3973464038181979137074027)
          ·
            refine ⟨5960196057272968705611041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3973464038181979137074027 5960196057272968705611041)
            ·
              refine ⟨4470147042954726529208281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5960196057272968705611041 4470147042954726529208281)
              ·
                refine ⟨3352610282216044896906211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4470147042954726529208281 3352610282216044896906211)
                ·
                  refine ⟨5028915423324067345359317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3352610282216044896906211 5028915423324067345359317)
                  ·
                    refine ⟨117865205234157828406859, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 5028915423324067345359317 117865205234157828406859)
                    ·
                      rfl

theorem cell23_688625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 2, 2, 1, 7].length) (baseStart_688625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_688625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_688625 prefixEnd_688625 := by exact prefixLift 688625
  have htrace : WordTrace (prefixWord ++ tailWord_688625) baseStart_688625 baseEnd_688625 := by
    simpa [prefixWord, tailWord_688625, baseEnd_688625] using wordTrace_append hprefix tailTrace_688625
  have hstable : (prefixWord ++ tailWord_688625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_688625).length < 2 ^ (prefixWord ++ tailWord_688625).sum := by decide
  have hdescent : baseEnd_688625 < baseStart_688625 := by decide
  rcases family_descends (prefixWord ++ tailWord_688625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_688629 : List Nat := [1, 3, 5, 1, 2, 1, 1, 2, 7]
def baseStart_688629 : Nat := 118140960795 + 688629 * 2 ^ 59
def prefixEnd_688629 : Nat := 4983230072969 + 3 ^ 40 * 688629 * 2
def baseEnd_688629 : Nat := 39288629958343496618951

theorem tailTrace_688629 : CollatzResearch.WordTrace tailWord_688629 prefixEnd_688629 39288629958343496618951 := by
  unfold tailWord_688629
  simp only [CollatzResearch.WordTrace]
  refine ⟨25116363022222216315020941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16744242014814810876680627 25116363022222216315020941)
  ·
    refine ⟨9418636133333331118132853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25116363022222216315020941 9418636133333331118132853)
    ·
      refine ⟨882997137499999792324955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 9418636133333331118132853 882997137499999792324955)
      ·
        refine ⟨1324495706249999688487433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 882997137499999792324955 1324495706249999688487433)
        ·
          refine ⟨993371779687499766365575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1324495706249999688487433 993371779687499766365575)
          ·
            refine ⟨1490057669531249649548363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 993371779687499766365575 1490057669531249649548363)
            ·
              refine ⟨2235086504296874474322545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1490057669531249649548363 2235086504296874474322545)
              ·
                refine ⟨1676314878222655855741909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2235086504296874474322545 1676314878222655855741909)
                ·
                  refine ⟨39288629958343496618951, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1676314878222655855741909 39288629958343496618951)
                  ·
                    rfl

theorem cell23_688629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 1, 1, 2, 7].length) (baseStart_688629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_688629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_688629 prefixEnd_688629 := by exact prefixLift 688629
  have htrace : WordTrace (prefixWord ++ tailWord_688629) baseStart_688629 baseEnd_688629 := by
    simpa [prefixWord, tailWord_688629, baseEnd_688629] using wordTrace_append hprefix tailTrace_688629
  have hstable : (prefixWord ++ tailWord_688629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_688629).length < 2 ^ (prefixWord ++ tailWord_688629).sum := by decide
  have hdescent : baseEnd_688629 < baseStart_688629 := by decide
  rcases family_descends (prefixWord ++ tailWord_688629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_688632 : List Nat := [2, 1, 2, 1, 1, 4, 1, 2, 2, 5, 2]
def baseStart_688632 : Nat := 118140960795 + 688632 * 2 ^ 59
def prefixEnd_688632 : Nat := 4983230072969 + 3 ^ 40 * 688632 * 2
def baseEnd_688632 : Nat := 353599210067054957833045

theorem tailTrace_688632 : CollatzResearch.WordTrace tailWord_688632 prefixEnd_688632 353599210067054957833045 := by
  unfold tailWord_688632
  simp only [CollatzResearch.WordTrace]
  refine ⟨12558236220605673913690075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16744314960807565218253433 12558236220605673913690075)
  ·
    refine ⟨18837354330908510870535113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12558236220605673913690075 18837354330908510870535113)
    ·
      refine ⟨14128015748181383152901335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18837354330908510870535113 14128015748181383152901335)
      ·
        refine ⟨21192023622272074729352003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14128015748181383152901335 21192023622272074729352003)
        ·
          refine ⟨31788035433408112094028005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21192023622272074729352003 31788035433408112094028005)
          ·
            refine ⟨5960256643764021017630251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 31788035433408112094028005 5960256643764021017630251)
            ·
              refine ⟨8940384965646031526445377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5960256643764021017630251 8940384965646031526445377)
              ·
                refine ⟨6705288724234523644834033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8940384965646031526445377 6705288724234523644834033)
                ·
                  refine ⟨5028966543175892733625525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6705288724234523644834033 5028966543175892733625525)
                  ·
                    refine ⟨471465613422739943777393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5028966543175892733625525 471465613422739943777393)
                    ·
                      refine ⟨353599210067054957833045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 471465613422739943777393 353599210067054957833045)
                      ·
                        rfl

theorem cell23_688632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 1, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 1, 2, 2, 5, 2].length) (baseStart_688632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_688632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_688632 prefixEnd_688632 := by exact prefixLift 688632
  have htrace : WordTrace (prefixWord ++ tailWord_688632) baseStart_688632 baseEnd_688632 := by
    simpa [prefixWord, tailWord_688632, baseEnd_688632] using wordTrace_append hprefix tailTrace_688632
  have hstable : (prefixWord ++ tailWord_688632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_688632).length < 2 ^ (prefixWord ++ tailWord_688632).sum := by decide
  have hdescent : baseEnd_688632 < baseStart_688632 := by decide
  rcases family_descends (prefixWord ++ tailWord_688632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_688739 : List Nat := [1, 1, 1, 5, 1, 2, 1, 2, 4, 3, 2]
def baseStart_688739 : Nat := 118140960795 + 688739 * 2 ^ 59
def prefixEnd_688739 : Nat := 4983230072969 + 3 ^ 40 * 688739 * 2
def baseEnd_688739 : Nat := 353654152497086039195053

theorem tailTrace_688739 : CollatzResearch.WordTrace tailWord_688739 prefixEnd_688739 353654152497086039195053 := by
  unfold tailWord_688739
  simp only [CollatzResearch.WordTrace]
  refine ⟨25120375051823705101525271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16746916701215803401016847 25120375051823705101525271)
  ·
    refine ⟨37680562577735557652287907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25120375051823705101525271 37680562577735557652287907)
    ·
      refine ⟨56520843866603336478431861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37680562577735557652287907 56520843866603336478431861)
      ·
        refine ⟨5298829112494062794852987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 56520843866603336478431861 5298829112494062794852987)
        ·
          refine ⟨7948243668741094192279481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5298829112494062794852987 7948243668741094192279481)
          ·
            refine ⟨5961182751555820644209611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7948243668741094192279481 5961182751555820644209611)
            ·
              refine ⟨8941774127333730966314417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5961182751555820644209611 8941774127333730966314417)
              ·
                refine ⟨6706330595500298224735813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8941774127333730966314417 6706330595500298224735813)
                ·
                  refine ⟨1257436986656305917137965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6706330595500298224735813 1257436986656305917137965)
                  ·
                    refine ⟨471538869996114718926737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1257436986656305917137965 471538869996114718926737)
                    ·
                      refine ⟨353654152497086039195053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 471538869996114718926737 353654152497086039195053)
                      ·
                        rfl

theorem cell23_688739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 1, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 1, 2, 4, 3, 2].length) (baseStart_688739 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_688739 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_688739 prefixEnd_688739 := by exact prefixLift 688739
  have htrace : WordTrace (prefixWord ++ tailWord_688739) baseStart_688739 baseEnd_688739 := by
    simpa [prefixWord, tailWord_688739, baseEnd_688739] using wordTrace_append hprefix tailTrace_688739
  have hstable : (prefixWord ++ tailWord_688739).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_688739).length < 2 ^ (prefixWord ++ tailWord_688739).sum := by decide
  have hdescent : baseEnd_688739 < baseStart_688739 := by decide
  rcases family_descends (prefixWord ++ tailWord_688739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_688749 : List Nat := [1, 5, 1, 1, 3, 2, 1, 1, 3, 5]
def baseStart_688749 : Nat := 118140960795 + 688749 * 2 ^ 59
def prefixEnd_688749 : Nat := 4983230072969 + 3 ^ 40 * 688749 * 2
def baseEnd_688749 : Nat := 117886429101210333356669

theorem tailTrace_688749 : CollatzResearch.WordTrace tailWord_688749 prefixEnd_688749 117886429101210333356669 := by
  unfold tailWord_688749
  simp only [CollatzResearch.WordTrace]
  refine ⟨25120739781787476809389301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16747159854524984539592867 25120739781787476809389301)
  ·
    refine ⟨2355069354542575950880247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 25120739781787476809389301 2355069354542575950880247)
    ·
      refine ⟨3532604031813863926320371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2355069354542575950880247 3532604031813863926320371)
      ·
        refine ⟨5298906047720795889480557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3532604031813863926320371 5298906047720795889480557)
        ·
          refine ⟨1987089767895298458555209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5298906047720795889480557 1987089767895298458555209)
          ·
            refine ⟨1490317325921473843916407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1987089767895298458555209 1490317325921473843916407)
            ·
              refine ⟨2235475988882210765874611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1490317325921473843916407 2235475988882210765874611)
              ·
                refine ⟨3353213983323316148811917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2235475988882210765874611 3353213983323316148811917)
                ·
                  refine ⟨1257455243746243555804469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3353213983323316148811917 1257455243746243555804469)
                  ·
                    refine ⟨117886429101210333356669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1257455243746243555804469 117886429101210333356669)
                    ·
                      rfl

theorem cell23_688749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 2, 1, 1, 3, 5].length) (baseStart_688749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_688749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_688749 prefixEnd_688749 := by exact prefixLift 688749
  have htrace : WordTrace (prefixWord ++ tailWord_688749) baseStart_688749 baseEnd_688749 := by
    simpa [prefixWord, tailWord_688749, baseEnd_688749] using wordTrace_append hprefix tailTrace_688749
  have hstable : (prefixWord ++ tailWord_688749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_688749).length < 2 ^ (prefixWord ++ tailWord_688749).sum := by decide
  have hdescent : baseEnd_688749 < baseStart_688749 := by decide
  rcases family_descends (prefixWord ++ tailWord_688749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_688770 : List Nat := [3, 4, 3, 1, 1, 1, 2, 2, 6]
def baseStart_688770 : Nat := 118140960795 + 688770 * 2 ^ 59
def prefixEnd_688770 : Nat := 4983230072969 + 3 ^ 40 * 688770 * 2
def baseEnd_688770 : Nat := 39296674488597268656379

theorem tailTrace_688770 : CollatzResearch.WordTrace tailWord_688770 prefixEnd_688770 39296674488597268656379 := by
  unfold tailWord_688770
  simp only [CollatzResearch.WordTrace]
  refine ⟨6280376428677849348975941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16747670476474264930602509 6280376428677849348975941)
  ·
    refine ⟨1177570580377096752932989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6280376428677849348975941 1177570580377096752932989)
    ·
      refine ⟨441588967641411282349871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1177570580377096752932989 441588967641411282349871)
      ·
        refine ⟨662383451462116923524807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 441588967641411282349871 662383451462116923524807)
        ·
          refine ⟨993575177193175385287211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 662383451462116923524807 993575177193175385287211)
          ·
            refine ⟨1490362765789763077930817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 993575177193175385287211 1490362765789763077930817)
            ·
              refine ⟨1117772074342322308448113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1490362765789763077930817 1117772074342322308448113)
              ·
                refine ⟨838329055756741731336085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1117772074342322308448113 838329055756741731336085)
                ·
                  refine ⟨39296674488597268656379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 838329055756741731336085 39296674488597268656379)
                  ·
                    rfl

theorem cell23_688770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 1, 2, 2, 6].length) (baseStart_688770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_688770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_688770 prefixEnd_688770 := by exact prefixLift 688770
  have htrace : WordTrace (prefixWord ++ tailWord_688770) baseStart_688770 baseEnd_688770 := by
    simpa [prefixWord, tailWord_688770, baseEnd_688770] using wordTrace_append hprefix tailTrace_688770
  have hstable : (prefixWord ++ tailWord_688770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_688770).length < 2 ^ (prefixWord ++ tailWord_688770).sum := by decide
  have hdescent : baseEnd_688770 < baseStart_688770 := by decide
  rcases family_descends (prefixWord ++ tailWord_688770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_688796 : List Nat := [2, 2, 3, 2, 2, 1, 2, 3, 2, 4]
def baseStart_688796 : Nat := 118140960795 + 688796 * 2 ^ 59
def prefixEnd_688796 : Nat := 4983230072969 + 3 ^ 40 * 688796 * 2
def baseEnd_688796 : Nat := 117894473631464105394097

theorem tailTrace_688796 : CollatzResearch.WordTrace tailWord_688796 prefixEnd_688796 117894473631464105394097 := by
  unfold tailWord_688796
  simp only [CollatzResearch.WordTrace]
  refine ⟨12561227006308601918175121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16748302675078135890900161 12561227006308601918175121)
  ·
    refine ⟨9420920254731451438631341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12561227006308601918175121 9420920254731451438631341)
    ·
      refine ⟨3532845095524294289486753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9420920254731451438631341 3532845095524294289486753)
      ·
        refine ⟨2649633821643220717115065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3532845095524294289486753 2649633821643220717115065)
        ·
          refine ⟨1987225366232415537836299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2649633821643220717115065 1987225366232415537836299)
          ·
            refine ⟨2980838049348623306754449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1987225366232415537836299 2980838049348623306754449)
            ·
              refine ⟨2235628537011467480065837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2980838049348623306754449 2235628537011467480065837)
              ·
                refine ⟨838360701379300305024689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2235628537011467480065837 838360701379300305024689)
                ·
                  refine ⟨628770526034475228768517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 838360701379300305024689 628770526034475228768517)
                  ·
                    refine ⟨117894473631464105394097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 628770526034475228768517 117894473631464105394097)
                    ·
                      rfl

theorem cell23_688796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 2, 3, 2, 4].length) (baseStart_688796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_688796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_688796 prefixEnd_688796 := by exact prefixLift 688796
  have htrace : WordTrace (prefixWord ++ tailWord_688796) baseStart_688796 baseEnd_688796 := by
    simpa [prefixWord, tailWord_688796, baseEnd_688796] using wordTrace_append hprefix tailTrace_688796
  have hstable : (prefixWord ++ tailWord_688796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_688796).length < 2 ^ (prefixWord ++ tailWord_688796).sum := by decide
  have hdescent : baseEnd_688796 < baseStart_688796 := by decide
  rcases family_descends (prefixWord ++ tailWord_688796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_688807 : List Nat := [1, 1, 6, 3, 2, 1, 1, 1, 2, 3, 2]
def baseStart_688807 : Nat := 118140960795 + 688807 * 2 ^ 59
def prefixEnd_688807 : Nat := 4983230072969 + 3 ^ 40 * 688807 * 2
def baseEnd_688807 : Nat := 353689069181591773144741

theorem tailTrace_688807 : CollatzResearch.WordTrace tailWord_688807 prefixEnd_688807 353689069181591773144741 := by
  unfold tailWord_688807
  simp only [CollatzResearch.WordTrace]
  refine ⟨25122855215577352715000675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16748570143718235143333783 25122855215577352715000675)
  ·
    refine ⟨37684282823366029072501013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25122855215577352715000675 37684282823366029072501013)
    ·
      refine ⟨1766450757345282612773485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 37684282823366029072501013 1766450757345282612773485)
      ·
        refine ⟨662419034004480979790057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1766450757345282612773485 662419034004480979790057)
        ·
          refine ⟨496814275503360734842543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 662419034004480979790057 496814275503360734842543)
          ·
            refine ⟨745221413255041102263815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 496814275503360734842543 745221413255041102263815)
            ·
              refine ⟨1117832119882561653395723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 745221413255041102263815 1117832119882561653395723)
              ·
                refine ⟨1676748179823842480093585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1117832119882561653395723 1676748179823842480093585)
                ·
                  refine ⟨1257561134867881860070189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1676748179823842480093585 1257561134867881860070189)
                  ·
                    refine ⟨471585425575455697526321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1257561134867881860070189 471585425575455697526321)
                    ·
                      refine ⟨353689069181591773144741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 471585425575455697526321 353689069181591773144741)
                      ·
                        rfl

theorem cell23_688807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 2, 1, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 2, 1, 1, 1, 2, 3, 2].length) (baseStart_688807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_688807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_688807 prefixEnd_688807 := by exact prefixLift 688807
  have htrace : WordTrace (prefixWord ++ tailWord_688807) baseStart_688807 baseEnd_688807 := by
    simpa [prefixWord, tailWord_688807, baseEnd_688807] using wordTrace_append hprefix tailTrace_688807
  have hstable : (prefixWord ++ tailWord_688807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_688807).length < 2 ^ (prefixWord ++ tailWord_688807).sum := by decide
  have hdescent : baseEnd_688807 < baseStart_688807 := by decide
  rcases family_descends (prefixWord ++ tailWord_688807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_688819 : List Nat := [1, 1, 1, 2, 3, 4, 2, 2, 1, 3, 3]
def baseStart_688819 : Nat := 118140960795 + 688819 * 2 ^ 59
def prefixEnd_688819 : Nat := 4983230072969 + 3 ^ 40 * 688819 * 2
def baseEnd_688819 : Nat := 353695230949445726194685

theorem tailTrace_688819 : CollatzResearch.WordTrace tailWord_688819 prefixEnd_688819 353695230949445726194685 := by
  unfold tailWord_688819
  simp only [CollatzResearch.WordTrace]
  refine ⟨25123292891533878764437511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16748861927689252509625007 25123292891533878764437511)
  ·
    refine ⟨37684939337300818146656267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25123292891533878764437511 37684939337300818146656267)
    ·
      refine ⟨56527409005951227219984401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37684939337300818146656267 56527409005951227219984401)
      ·
        refine ⟨42395556754463420414988301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56527409005951227219984401 42395556754463420414988301)
        ·
          refine ⟨15898333782923782655620613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42395556754463420414988301 15898333782923782655620613)
          ·
            refine ⟨2980937584298209247928865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15898333782923782655620613 2980937584298209247928865)
            ·
              refine ⟨2235703188223656935946649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2980937584298209247928865 2235703188223656935946649)
              ·
                refine ⟨1676777391167742701959987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2235703188223656935946649 1676777391167742701959987)
                ·
                  refine ⟨2515166086751614052939981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1676777391167742701959987 2515166086751614052939981)
                  ·
                    refine ⟨943187282531855269852493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2515166086751614052939981 943187282531855269852493)
                    ·
                      refine ⟨353695230949445726194685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 943187282531855269852493 353695230949445726194685)
                      ·
                        rfl

theorem cell23_688819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 2, 2, 1, 3, 3].length) (baseStart_688819 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_688819 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_688819 prefixEnd_688819 := by exact prefixLift 688819
  have htrace : WordTrace (prefixWord ++ tailWord_688819) baseStart_688819 baseEnd_688819 := by
    simpa [prefixWord, tailWord_688819, baseEnd_688819] using wordTrace_append hprefix tailTrace_688819
  have hstable : (prefixWord ++ tailWord_688819).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_688819).length < 2 ^ (prefixWord ++ tailWord_688819).sum := by decide
  have hdescent : baseEnd_688819 < baseStart_688819 := by decide
  rcases family_descends (prefixWord ++ tailWord_688819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_688859 : List Nat := [1, 1, 1, 1, 1, 1, 1, 3, 7, 4, 2]
def baseStart_688859 : Nat := 118140960795 + 688859 * 2 ^ 59
def prefixEnd_688859 : Nat := 4983230072969 + 3 ^ 40 * 688859 * 2
def baseEnd_688859 : Nat := 353715770175625569694501

theorem tailTrace_688859 : CollatzResearch.WordTrace tailWord_688859 prefixEnd_688859 353715770175625569694501 := by
  unfold tailWord_688859
  simp only [CollatzResearch.WordTrace]
  refine ⟨25124751811388965595893631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16749834540925977063929087 25124751811388965595893631)
  ·
    refine ⟨37687127717083448393840447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25124751811388965595893631 37687127717083448393840447)
    ·
      refine ⟨56530691575625172590760671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37687127717083448393840447 56530691575625172590760671)
      ·
        refine ⟨84796037363437758886141007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56530691575625172590760671 84796037363437758886141007)
        ·
          refine ⟨127194056045156638329211511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84796037363437758886141007 127194056045156638329211511)
          ·
            refine ⟨190791084067734957493817267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 127194056045156638329211511 190791084067734957493817267)
            ·
              refine ⟨286186626101602436240725901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 190791084067734957493817267 286186626101602436240725901)
              ·
                refine ⟨107319984788100913590272213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 286186626101602436240725901 107319984788100913590272213)
                ·
                  refine ⟨2515312143471115162272005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 107319984788100913590272213 2515312143471115162272005)
                  ·
                    refine ⟨471621026900834092926001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2515312143471115162272005 471621026900834092926001)
                    ·
                      refine ⟨353715770175625569694501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 471621026900834092926001 353715770175625569694501)
                      ·
                        rfl

theorem cell23_688859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 7, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 7, 4, 2].length) (baseStart_688859 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_688859 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_688859 prefixEnd_688859 := by exact prefixLift 688859
  have htrace : WordTrace (prefixWord ++ tailWord_688859) baseStart_688859 baseEnd_688859 := by
    simpa [prefixWord, tailWord_688859, baseEnd_688859] using wordTrace_append hprefix tailTrace_688859
  have hstable : (prefixWord ++ tailWord_688859).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_688859).length < 2 ^ (prefixWord ++ tailWord_688859).sum := by decide
  have hdescent : baseEnd_688859 < baseStart_688859 := by decide
  rcases family_descends (prefixWord ++ tailWord_688859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_688863 : List Nat := [1, 1, 2, 3, 2, 4, 2, 2, 1, 3, 2]
def baseStart_688863 : Nat := 118140960795 + 688863 * 2 ^ 59
def prefixEnd_688863 : Nat := 4983230072969 + 3 ^ 40 * 688863 * 2
def baseEnd_688863 : Nat := 353717824098243554044483

theorem tailTrace_688863 : CollatzResearch.WordTrace tailWord_688863 prefixEnd_688863 353717824098243554044483 := by
  unfold tailWord_688863
  simp only [CollatzResearch.WordTrace]
  refine ⟨25124897703374474279039243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16749931802249649519359495 25124897703374474279039243)
  ·
    refine ⟨37687346555061711418558865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25124897703374474279039243 37687346555061711418558865)
    ·
      refine ⟨28265509916296283563919149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37687346555061711418558865 28265509916296283563919149)
      ·
        refine ⟨10599566218611106336469681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28265509916296283563919149 10599566218611106336469681)
        ·
          refine ⟨7949674663958329752352261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10599566218611106336469681 7949674663958329752352261)
          ·
            refine ⟨1490563999492186828566049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7949674663958329752352261 1490563999492186828566049)
            ·
              refine ⟨1117922999619140121424537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1490563999492186828566049 1117922999619140121424537)
              ·
                refine ⟨838442249714355091068403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1117922999619140121424537 838442249714355091068403)
                ·
                  refine ⟨1257663374571532636602605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 838442249714355091068403 1257663374571532636602605)
                  ·
                    refine ⟨471623765464324738725977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1257663374571532636602605 471623765464324738725977)
                    ·
                      refine ⟨353717824098243554044483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 471623765464324738725977 353717824098243554044483)
                      ·
                        rfl

theorem cell23_688863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 4, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 4, 2, 2, 1, 3, 2].length) (baseStart_688863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_688863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_688863 prefixEnd_688863 := by exact prefixLift 688863
  have htrace : WordTrace (prefixWord ++ tailWord_688863) baseStart_688863 baseEnd_688863 := by
    simpa [prefixWord, tailWord_688863, baseEnd_688863] using wordTrace_append hprefix tailTrace_688863
  have hstable : (prefixWord ++ tailWord_688863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_688863).length < 2 ^ (prefixWord ++ tailWord_688863).sum := by decide
  have hdescent : baseEnd_688863 < baseStart_688863 := by decide
  rcases family_descends (prefixWord ++ tailWord_688863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_688879 : List Nat := [1, 1, 2, 1, 5, 3, 1, 1, 2, 1, 5]
def baseStart_688879 : Nat := 118140960795 + 688879 * 2 ^ 59
def prefixEnd_688879 : Nat := 4983230072969 + 3 ^ 40 * 688879 * 2
def baseEnd_688879 : Nat := 353726039788715491444409

theorem tailTrace_688879 : CollatzResearch.WordTrace tailWord_688879 prefixEnd_688879 353726039788715491444409 := by
  unfold tailWord_688879
  simp only [CollatzResearch.WordTrace]
  refine ⟨25125481271316509011621691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16750320847544339341081127 25125481271316509011621691)
  ·
    refine ⟨37688221906974763517432537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25125481271316509011621691 37688221906974763517432537)
    ·
      refine ⟨28266166430231072638074403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37688221906974763517432537 28266166430231072638074403)
      ·
        refine ⟨42399249645346608957111605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28266166430231072638074403 42399249645346608957111605)
        ·
          refine ⟨3974929654251244589729213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 42399249645346608957111605 3974929654251244589729213)
          ·
            refine ⟨1490598620344216721148455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3974929654251244589729213 1490598620344216721148455)
            ·
              refine ⟨2235897930516325081722683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1490598620344216721148455 2235897930516325081722683)
              ·
                refine ⟨3353846895774487622584025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2235897930516325081722683 3353846895774487622584025)
                ·
                  refine ⟨2515385171830865716938019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3353846895774487622584025 2515385171830865716938019)
                  ·
                    refine ⟨3773077757746298575407029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2515385171830865716938019 3773077757746298575407029)
                    ·
                      refine ⟨353726039788715491444409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3773077757746298575407029 353726039788715491444409)
                      ·
                        rfl

theorem cell23_688879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 3, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 3, 1, 1, 2, 1, 5].length) (baseStart_688879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_688879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_688879 prefixEnd_688879 := by exact prefixLift 688879
  have htrace : WordTrace (prefixWord ++ tailWord_688879) baseStart_688879 baseEnd_688879 := by
    simpa [prefixWord, tailWord_688879, baseEnd_688879] using wordTrace_append hprefix tailTrace_688879
  have hstable : (prefixWord ++ tailWord_688879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_688879).length < 2 ^ (prefixWord ++ tailWord_688879).sum := by decide
  have hdescent : baseEnd_688879 < baseStart_688879 := by decide
  rcases family_descends (prefixWord ++ tailWord_688879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_688893 : List Nat := [1, 4, 1, 1, 1, 1, 4, 4, 2, 2, 2]
def baseStart_688893 : Nat := 118140960795 + 688893 * 2 ^ 59
def prefixEnd_688893 : Nat := 4983230072969 + 3 ^ 40 * 688893 * 2
def baseEnd_688893 : Nat := 353733228517878436669345

theorem tailTrace_688893 : CollatzResearch.WordTrace tailWord_688893 prefixEnd_688893 353733228517878436669345 := by
  unfold tailWord_688893
  simp only [CollatzResearch.WordTrace]
  refine ⟨25125991893265789402631333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16750661262177192935087555 25125991893265789402631333)
  ·
    refine ⟨4711123479987335512993375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 25125991893265789402631333 4711123479987335512993375)
    ·
      refine ⟨7066685219981003269490063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4711123479987335512993375 7066685219981003269490063)
      ·
        refine ⟨10600027829971504904235095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7066685219981003269490063 10600027829971504904235095)
        ·
          refine ⟨15900041744957257356352643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10600027829971504904235095 15900041744957257356352643)
          ·
            refine ⟨23850062617435886034528965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15900041744957257356352643 23850062617435886034528965)
            ·
              refine ⟨4471886740769228631474181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23850062617435886034528965 4471886740769228631474181)
              ·
                refine ⟨838478763894230368401409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4471886740769228631474181 838478763894230368401409)
                ·
                  refine ⟨628859072920672776301057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 838478763894230368401409 628859072920672776301057)
                  ·
                    refine ⟨471644304690504582225793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 628859072920672776301057 471644304690504582225793)
                    ·
                      refine ⟨353733228517878436669345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 471644304690504582225793 353733228517878436669345)
                      ·
                        rfl

theorem cell23_688893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 4, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 4, 4, 2, 2, 2].length) (baseStart_688893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_688893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_688893 prefixEnd_688893 := by exact prefixLift 688893
  have htrace : WordTrace (prefixWord ++ tailWord_688893) baseStart_688893 baseEnd_688893 := by
    simpa [prefixWord, tailWord_688893, baseEnd_688893] using wordTrace_append hprefix tailTrace_688893
  have hstable : (prefixWord ++ tailWord_688893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_688893).length < 2 ^ (prefixWord ++ tailWord_688893).sum := by decide
  have hdescent : baseEnd_688893 < baseStart_688893 := by decide
  rcases family_descends (prefixWord ++ tailWord_688893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_688914 : List Nat := [3, 2, 4, 1, 3, 1, 1, 2, 1, 3, 2]
def baseStart_688914 : Nat := 118140960795 + 688914 * 2 ^ 59
def prefixEnd_688914 : Nat := 4983230072969 + 3 ^ 40 * 688914 * 2
def baseEnd_688914 : Nat := 353744011611622854506749

theorem tailTrace_688914 : CollatzResearch.WordTrace tailWord_688914 prefixEnd_688914 353744011611622854506749 := by
  unfold tailWord_688914
  simp only [CollatzResearch.WordTrace]
  refine ⟨6281689456547427497286449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16751171884126473326097197 6281689456547427497286449)
  ·
    refine ⟨4711267092410570622964837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6281689456547427497286449 4711267092410570622964837)
    ·
      refine ⟨883362579826981991805907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4711267092410570622964837 883362579826981991805907)
      ·
        refine ⟨1325043869740472987708861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 883362579826981991805907 1325043869740472987708861)
        ·
          refine ⟨496891451152677370390823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1325043869740472987708861 496891451152677370390823)
          ·
            refine ⟨745337176729016055586235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 496891451152677370390823 745337176729016055586235)
            ·
              refine ⟨1118005765093524083379353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 745337176729016055586235 1118005765093524083379353)
              ·
                refine ⟨838504323820143062534515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1118005765093524083379353 838504323820143062534515)
                ·
                  refine ⟨1257756485730214593801773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 838504323820143062534515 1257756485730214593801773)
                  ·
                    refine ⟨471658682148830472675665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1257756485730214593801773 471658682148830472675665)
                    ·
                      refine ⟨353744011611622854506749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 471658682148830472675665 353744011611622854506749)
                      ·
                        rfl

theorem cell23_688914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 3, 1, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 3, 1, 1, 2, 1, 3, 2].length) (baseStart_688914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_688914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_688914 prefixEnd_688914 := by exact prefixLift 688914
  have htrace : WordTrace (prefixWord ++ tailWord_688914) baseStart_688914 baseEnd_688914 := by
    simpa [prefixWord, tailWord_688914, baseEnd_688914] using wordTrace_append hprefix tailTrace_688914
  have hstable : (prefixWord ++ tailWord_688914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_688914).length < 2 ^ (prefixWord ++ tailWord_688914).sum := by decide
  have hdescent : baseEnd_688914 < baseStart_688914 := by decide
  rcases family_descends (prefixWord ++ tailWord_688914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_688950 : List Nat := [5, 1, 2, 2, 2, 1, 1, 4, 5]
def baseStart_688950 : Nat := 118140960795 + 688950 * 2 ^ 59
def prefixEnd_688950 : Nat := 4983230072969 + 3 ^ 40 * 688950 * 2
def baseEnd_688950 : Nat := 39306944101687190406287

theorem tailTrace_688950 : CollatzResearch.WordTrace tailWord_688950 prefixEnd_688950 39306944101687190406287 := by
  unfold tailWord_688950
  simp only [CollatzResearch.WordTrace]
  refine ⟨1570504428378705508591019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 16752047236039525424970869 1570504428378705508591019)
  ·
    refine ⟨2355756642568058262886529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1570504428378705508591019 2355756642568058262886529)
    ·
      refine ⟨1766817481926043697164897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2355756642568058262886529 1766817481926043697164897)
      ·
        refine ⟨1325113111444532772873673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1766817481926043697164897 1325113111444532772873673)
        ·
          refine ⟨993834833583399579655255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1325113111444532772873673 993834833583399579655255)
          ·
            refine ⟨1490752250375099369482883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 993834833583399579655255 1490752250375099369482883)
            ·
              refine ⟨2236128375562649054224325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1490752250375099369482883 2236128375562649054224325)
              ·
                refine ⟨419274070417996697667061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2236128375562649054224325 419274070417996697667061)
                ·
                  refine ⟨39306944101687190406287, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 419274070417996697667061 39306944101687190406287)
                  ·
                    rfl

theorem cell23_688950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 1, 1, 4, 5].length) (baseStart_688950 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_688950 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_688950 prefixEnd_688950 := by exact prefixLift 688950
  have htrace : WordTrace (prefixWord ++ tailWord_688950) baseStart_688950 baseEnd_688950 := by
    simpa [prefixWord, tailWord_688950, baseEnd_688950] using wordTrace_append hprefix tailTrace_688950
  have hstable : (prefixWord ++ tailWord_688950).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_688950).length < 2 ^ (prefixWord ++ tailWord_688950).sum := by decide
  have hdescent : baseEnd_688950 < baseStart_688950 := by decide
  rcases family_descends (prefixWord ++ tailWord_688950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_688980 : List Nat := [2, 4, 1, 1, 5, 1, 1, 1, 2, 5]
def baseStart_688980 : Nat := 118140960795 + 688980 * 2 ^ 59
def prefixEnd_688980 : Nat := 4983230072969 + 3 ^ 40 * 688980 * 2
def baseEnd_688980 : Nat := 117925967111606532093815

theorem tailTrace_688980 : CollatzResearch.WordTrace tailWord_688980 prefixEnd_688980 117925967111606532093815 := by
  unfold tailWord_688980
  simp only [CollatzResearch.WordTrace]
  refine ⟨12564582521975301630524197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16752776695967068840698929 12564582521975301630524197)
  ·
    refine ⟨2355859222870369055723287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12564582521975301630524197 2355859222870369055723287)
    ·
      refine ⟨3533788834305553583584931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2355859222870369055723287 3533788834305553583584931)
      ·
        refine ⟨5300683251458330375377397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3533788834305553583584931 5300683251458330375377397)
        ·
          refine ⟨496939054824218472691631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 5300683251458330375377397 496939054824218472691631)
          ·
            refine ⟨745408582236327709037447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 496939054824218472691631 745408582236327709037447)
            ·
              refine ⟨1118112873354491563556171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 745408582236327709037447 1118112873354491563556171)
              ·
                refine ⟨1677169310031737345334257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1118112873354491563556171 1677169310031737345334257)
                ·
                  refine ⟨1257876982523803009000693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1677169310031737345334257 1257876982523803009000693)
                  ·
                    refine ⟨117925967111606532093815, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1257876982523803009000693 117925967111606532093815)
                    ·
                      rfl

theorem cell23_688980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 5, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 5, 1, 1, 1, 2, 5].length) (baseStart_688980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_688980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_688980 prefixEnd_688980 := by exact prefixLift 688980
  have htrace : WordTrace (prefixWord ++ tailWord_688980) baseStart_688980 baseEnd_688980 := by
    simpa [prefixWord, tailWord_688980, baseEnd_688980] using wordTrace_append hprefix tailTrace_688980
  have hstable : (prefixWord ++ tailWord_688980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_688980).length < 2 ^ (prefixWord ++ tailWord_688980).sum := by decide
  have hdescent : baseEnd_688980 < baseStart_688980 := by decide
  rcases family_descends (prefixWord ++ tailWord_688980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_688983 : List Nat := [1, 1, 3, 2, 4, 3, 1, 1, 2, 1, 4]
def baseStart_688983 : Nat := 118140960795 + 688983 * 2 ^ 59
def prefixEnd_688983 : Nat := 4983230072969 + 3 ^ 40 * 688983 * 2
def baseEnd_688983 : Nat := 353779441776783084543931

theorem tailTrace_688983 : CollatzResearch.WordTrace tailWord_688983 prefixEnd_688983 353779441776783084543931 := by
  unfold tailWord_688983
  simp only [CollatzResearch.WordTrace]
  refine ⟨25129274462939734773407603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16752849641959823182271735 25129274462939734773407603)
  ·
    refine ⟨37693911694409602160111405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25129274462939734773407603 37693911694409602160111405)
    ·
      refine ⟨14135216885403600810041777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37693911694409602160111405 14135216885403600810041777)
      ·
        refine ⟨10601412664052700607531333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14135216885403600810041777 10601412664052700607531333)
        ·
          refine ⟨1987764874509881363912125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10601412664052700607531333 1987764874509881363912125)
          ·
            refine ⟨745411827941205511467047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1987764874509881363912125 745411827941205511467047)
            ·
              refine ⟨1118117741911808267200571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 745411827941205511467047 1118117741911808267200571)
              ·
                refine ⟨1677176612867712400800857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1118117741911808267200571 1677176612867712400800857)
                ·
                  refine ⟨1257882459650784300600643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1677176612867712400800857 1257882459650784300600643)
                  ·
                    refine ⟨1886823689476176450900965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1257882459650784300600643 1886823689476176450900965)
                    ·
                      refine ⟨353779441776783084543931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1886823689476176450900965 353779441776783084543931)
                      ·
                        rfl

theorem cell23_688983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 3, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 3, 1, 1, 2, 1, 4].length) (baseStart_688983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_688983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_688983 prefixEnd_688983 := by exact prefixLift 688983
  have htrace : WordTrace (prefixWord ++ tailWord_688983) baseStart_688983 baseEnd_688983 := by
    simpa [prefixWord, tailWord_688983, baseEnd_688983] using wordTrace_append hprefix tailTrace_688983
  have hstable : (prefixWord ++ tailWord_688983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_688983).length < 2 ^ (prefixWord ++ tailWord_688983).sum := by decide
  have hdescent : baseEnd_688983 < baseStart_688983 := by decide
  rcases family_descends (prefixWord ++ tailWord_688983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_688986 : List Nat := [3, 1, 1, 2, 1, 5, 1, 1, 1, 4, 3]
def baseStart_688986 : Nat := 118140960795 + 688986 * 2 ^ 59
def prefixEnd_688986 : Nat := 4983230072969 + 3 ^ 40 * 688986 * 2
def baseEnd_688986 : Nat := 353780982218746572806417

theorem tailTrace_688986 : CollatzResearch.WordTrace tailWord_688986 prefixEnd_688986 353780982218746572806417 := by
  unfold tailWord_688986
  simp only [CollatzResearch.WordTrace]
  refine ⟨6282345970482216571441703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16752922587952577523844541 6282345970482216571441703)
  ·
    refine ⟨9423518955723324857162555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6282345970482216571441703 9423518955723324857162555)
    ·
      refine ⟨14135278433584987285743833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9423518955723324857162555 14135278433584987285743833)
      ·
        refine ⟨10601458825188740464307875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14135278433584987285743833 10601458825188740464307875)
        ·
          refine ⟨15902188237783110696461813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10601458825188740464307875 15902188237783110696461813)
          ·
            refine ⟨1490830147292166627793295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 15902188237783110696461813 1490830147292166627793295)
            ·
              refine ⟨2236245220938249941689943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1490830147292166627793295 2236245220938249941689943)
              ·
                refine ⟨3354367831407374912534915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2236245220938249941689943 3354367831407374912534915)
                ·
                  refine ⟨5031551747111062368802373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3354367831407374912534915 5031551747111062368802373)
                  ·
                    refine ⟨943415952583324194150445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5031551747111062368802373 943415952583324194150445)
                    ·
                      refine ⟨353780982218746572806417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 943415952583324194150445 353780982218746572806417)
                      ·
                        rfl

theorem cell23_688986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 5, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 5, 1, 1, 1, 4, 3].length) (baseStart_688986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_688986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_688986 prefixEnd_688986 := by exact prefixLift 688986
  have htrace : WordTrace (prefixWord ++ tailWord_688986) baseStart_688986 baseEnd_688986 := by
    simpa [prefixWord, tailWord_688986, baseEnd_688986] using wordTrace_append hprefix tailTrace_688986
  have hstable : (prefixWord ++ tailWord_688986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_688986).length < 2 ^ (prefixWord ++ tailWord_688986).sum := by decide
  have hdescent : baseEnd_688986 < baseStart_688986 := by decide
  rcases family_descends (prefixWord ++ tailWord_688986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_689009 : List Nat := [1, 2, 2, 2, 1, 4, 1, 1, 1, 2, 6]
def baseStart_689009 : Nat := 118140960795 + 689009 * 2 ^ 59
def prefixEnd_689009 : Nat := 4983230072969 + 3 ^ 40 * 689009 * 2
def baseEnd_689009 : Nat := 353792792273799982818811

theorem tailTrace_689009 : CollatzResearch.WordTrace tailWord_689009 prefixEnd_689009 353792792273799982818811 := by
  unfold tailWord_689009
  simp only [CollatzResearch.WordTrace]
  refine ⟨25130222760845541213854081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16753481840563694142569387 25130222760845541213854081)
  ·
    refine ⟨18847667070634155910390561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25130222760845541213854081 18847667070634155910390561)
    ·
      refine ⟨14135750302975616932792921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18847667070634155910390561 14135750302975616932792921)
      ·
        refine ⟨10601812727231712699594691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14135750302975616932792921 10601812727231712699594691)
        ·
          refine ⟨15902719090847569049392037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10601812727231712699594691 15902719090847569049392037)
          ·
            refine ⟨2981759829533919196761007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15902719090847569049392037 2981759829533919196761007)
            ·
              refine ⟨4472639744300878795141511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2981759829533919196761007 4472639744300878795141511)
              ·
                refine ⟨6708959616451318192712267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4472639744300878795141511 6708959616451318192712267)
                ·
                  refine ⟨10063439424676977289068401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6708959616451318192712267 10063439424676977289068401)
                  ·
                    refine ⟨7547579568507732966801301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10063439424676977289068401 7547579568507732966801301)
                    ·
                      refine ⟨353792792273799982818811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 7547579568507732966801301 353792792273799982818811)
                      ·
                        rfl

theorem cell23_689009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 1, 1, 1, 2, 6].length) (baseStart_689009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_689009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_689009 prefixEnd_689009 := by exact prefixLift 689009
  have htrace : WordTrace (prefixWord ++ tailWord_689009) baseStart_689009 baseEnd_689009 := by
    simpa [prefixWord, tailWord_689009, baseEnd_689009] using wordTrace_append hprefix tailTrace_689009
  have hstable : (prefixWord ++ tailWord_689009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_689009).length < 2 ^ (prefixWord ++ tailWord_689009).sum := by decide
  have hdescent : baseEnd_689009 < baseStart_689009 := by decide
  rcases family_descends (prefixWord ++ tailWord_689009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_689019 : List Nat := [1, 1, 1, 1, 1, 5, 2, 1, 5, 5]
def baseStart_689019 : Nat := 118140960795 + 689019 * 2 ^ 59
def prefixEnd_689019 : Nat := 4983230072969 + 3 ^ 40 * 689019 * 2
def baseEnd_689019 : Nat := 117932642360114981231255

theorem tailTrace_689019 : CollatzResearch.WordTrace tailWord_689019 prefixEnd_689019 117932642360114981231255 := by
  unfold tailWord_689019
  simp only [CollatzResearch.WordTrace]
  refine ⟨25130587490809312921718111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16753724993872875281145407 25130587490809312921718111)
  ·
    refine ⟨37695881236213969382577167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25130587490809312921718111 37695881236213969382577167)
    ·
      refine ⟨56543821854320954073865751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37695881236213969382577167 56543821854320954073865751)
      ·
        refine ⟨84815732781481431110798627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56543821854320954073865751 84815732781481431110798627)
        ·
          refine ⟨127223599172222146666197941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84815732781481431110798627 127223599172222146666197941)
          ·
            refine ⟨11927212422395826249956057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 127223599172222146666197941 11927212422395826249956057)
            ·
              refine ⟨8945409316796869687467043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11927212422395826249956057 8945409316796869687467043)
              ·
                refine ⟨13418113975195304531200565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8945409316796869687467043 13418113975195304531200565)
                ·
                  refine ⟨1257948185174559799800053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 13418113975195304531200565 1257948185174559799800053)
                  ·
                    refine ⟨117932642360114981231255, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1257948185174559799800053 117932642360114981231255)
                    ·
                      rfl

theorem cell23_689019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 2, 1, 5, 5].length) (baseStart_689019 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_689019 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_689019 prefixEnd_689019 := by exact prefixLift 689019
  have htrace : WordTrace (prefixWord ++ tailWord_689019) baseStart_689019 baseEnd_689019 := by
    simpa [prefixWord, tailWord_689019, baseEnd_689019] using wordTrace_append hprefix tailTrace_689019
  have hstable : (prefixWord ++ tailWord_689019).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_689019).length < 2 ^ (prefixWord ++ tailWord_689019).sum := by decide
  have hdescent : baseEnd_689019 < baseStart_689019 := by decide
  rcases family_descends (prefixWord ++ tailWord_689019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_689033 : List Nat := [1, 2, 1, 1, 5, 2, 2, 2, 3, 1, 3]
def baseStart_689033 : Nat := 118140960795 + 689033 * 2 ^ 59
def prefixEnd_689033 : Nat := 4983230072969 + 3 ^ 40 * 689033 * 2
def baseEnd_689033 : Nat := 353805115809507888918701

theorem tailTrace_689033 : CollatzResearch.WordTrace tailWord_689033 prefixEnd_689033 353805115809507888918701 := by
  unfold tailWord_689033
  simp only [CollatzResearch.WordTrace]
  refine ⟨25131098112758593312727753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16754065408505728875151835 25131098112758593312727753)
  ·
    refine ⟨18848323584568944984545815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25131098112758593312727753 18848323584568944984545815)
    ·
      refine ⟨28272485376853417476818723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18848323584568944984545815 28272485376853417476818723)
      ·
        refine ⟨42408728065280126215228085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28272485376853417476818723 42408728065280126215228085)
        ·
          refine ⟨3975818256120011832677633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 42408728065280126215228085 3975818256120011832677633)
          ·
            refine ⟨2981863692090008874508225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3975818256120011832677633 2981863692090008874508225)
            ·
              refine ⟨2236397769067506655881169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2981863692090008874508225 2236397769067506655881169)
              ·
                refine ⟨1677298326800629991910877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2236397769067506655881169 1677298326800629991910877)
                ·
                  refine ⟨628986872550236246966579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1677298326800629991910877 628986872550236246966579)
                  ·
                    refine ⟨943480308825354370449869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 628986872550236246966579 943480308825354370449869)
                    ·
                      refine ⟨353805115809507888918701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 943480308825354370449869 353805115809507888918701)
                      ·
                        rfl

theorem cell23_689033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 2, 2, 3, 1, 3].length) (baseStart_689033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_689033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_689033 prefixEnd_689033 := by exact prefixLift 689033
  have htrace : WordTrace (prefixWord ++ tailWord_689033) baseStart_689033 baseEnd_689033 := by
    simpa [prefixWord, tailWord_689033, baseEnd_689033] using wordTrace_append hprefix tailTrace_689033
  have hstable : (prefixWord ++ tailWord_689033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_689033).length < 2 ^ (prefixWord ++ tailWord_689033).sum := by decide
  have hdescent : baseEnd_689033 < baseStart_689033 := by decide
  rcases family_descends (prefixWord ++ tailWord_689033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_689036 : List Nat := [2, 2, 1, 2, 1, 2, 3, 4, 1, 5]
def baseStart_689036 : Nat := 118140960795 + 689036 * 2 ^ 59
def prefixEnd_689036 : Nat := 4983230072969 + 3 ^ 40 * 689036 * 2
def baseEnd_689036 : Nat := 117935552083823792393729

theorem tailTrace_689036 : CollatzResearch.WordTrace tailWord_689036 prefixEnd_689036 117935552083823792393729 := by
  unfold tailWord_689036
  simp only [CollatzResearch.WordTrace]
  refine ⟨12565603765873862412543481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16754138354498483216724641 12565603765873862412543481)
  ·
    refine ⟨9424202824405396809407611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12565603765873862412543481 9424202824405396809407611)
    ·
      refine ⟨14136304236608095214111417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9424202824405396809407611 14136304236608095214111417)
      ·
        refine ⟨10602228177456071410583563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14136304236608095214111417 10602228177456071410583563)
        ·
          refine ⟨15903342266184107115875345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10602228177456071410583563 15903342266184107115875345)
          ·
            refine ⟨11927506699638080336906509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15903342266184107115875345 11927506699638080336906509)
            ·
              refine ⟨4472815012364280126339941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11927506699638080336906509 4472815012364280126339941)
              ·
                refine ⟨838652814818302523688739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4472815012364280126339941 838652814818302523688739)
                ·
                  refine ⟨1257979222227453785533109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 838652814818302523688739 1257979222227453785533109)
                  ·
                    refine ⟨117935552083823792393729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1257979222227453785533109 117935552083823792393729)
                    ·
                      rfl

theorem cell23_689036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 3, 4, 1, 5].length) (baseStart_689036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_689036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_689036 prefixEnd_689036 := by exact prefixLift 689036
  have htrace : WordTrace (prefixWord ++ tailWord_689036) baseStart_689036 baseEnd_689036 := by
    simpa [prefixWord, tailWord_689036, baseEnd_689036] using wordTrace_append hprefix tailTrace_689036
  have hstable : (prefixWord ++ tailWord_689036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_689036).length < 2 ^ (prefixWord ++ tailWord_689036).sum := by decide
  have hdescent : baseEnd_689036 < baseStart_689036 := by decide
  rcases family_descends (prefixWord ++ tailWord_689036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_689049 : List Nat := [1, 2, 1, 2, 1, 3, 1, 3, 3, 6]
def baseStart_689049 : Nat := 118140960795 + 689049 * 2 ^ 59
def prefixEnd_689049 : Nat := 4983230072969 + 3 ^ 40 * 689049 * 2
def baseEnd_689049 : Nat := 117937777166659942106209

theorem tailTrace_689049 : CollatzResearch.WordTrace tailWord_689049 prefixEnd_689049 117937777166659942106209 := by
  unfold tailWord_689049
  simp only [CollatzResearch.WordTrace]
  refine ⟨25131681680700628045310201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16754454453800418696873467 25131681680700628045310201)
  ·
    refine ⟨18848761260525471033982651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25131681680700628045310201 18848761260525471033982651)
    ·
      refine ⟨28273141890788206550973977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18848761260525471033982651 28273141890788206550973977)
      ·
        refine ⟨21204856418091154913230483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28273141890788206550973977 21204856418091154913230483)
        ·
          refine ⟨31807284627136732369845725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21204856418091154913230483 31807284627136732369845725)
          ·
            refine ⟨11927731735176274638692147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31807284627136732369845725 11927731735176274638692147)
            ·
              refine ⟨17891597602764411958038221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11927731735176274638692147 17891597602764411958038221)
              ·
                refine ⟨6709349101036654484264333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17891597602764411958038221 6709349101036654484264333)
                ·
                  refine ⟨2516005912888745431599125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6709349101036654484264333 2516005912888745431599125)
                  ·
                    refine ⟨117937777166659942106209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2516005912888745431599125 117937777166659942106209)
                    ·
                      rfl

theorem cell23_689049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 3, 3, 6].length) (baseStart_689049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_689049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_689049 prefixEnd_689049 := by exact prefixLift 689049
  have htrace : WordTrace (prefixWord ++ tailWord_689049) baseStart_689049 baseEnd_689049 := by
    simpa [prefixWord, tailWord_689049, baseEnd_689049] using wordTrace_append hprefix tailTrace_689049
  have hstable : (prefixWord ++ tailWord_689049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_689049).length < 2 ^ (prefixWord ++ tailWord_689049).sum := by decide
  have hdescent : baseEnd_689049 < baseStart_689049 := by decide
  rcases family_descends (prefixWord ++ tailWord_689049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_689079 : List Nat := [1, 1, 3, 1, 3, 1, 3, 10]
def baseStart_689079 : Nat := 118140960795 + 689079 * 2 ^ 59
def prefixEnd_689079 : Nat := 4983230072969 + 3 ^ 40 * 689079 * 2
def baseEnd_689079 : Nat := 13104767997022766997907

theorem tailTrace_689079 : CollatzResearch.WordTrace tailWord_689079 prefixEnd_689079 13104767997022766997907 := by
  unfold tailWord_689079
  simp only [CollatzResearch.WordTrace]
  refine ⟨25132775870591943168902291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16755183913727962112601527 25132775870591943168902291)
  ·
    refine ⟨37699163805887914753353437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25132775870591943168902291 37699163805887914753353437)
    ·
      refine ⟨14137186427207968032507539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37699163805887914753353437 14137186427207968032507539)
      ·
        refine ⟨21205779640811952048761309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14137186427207968032507539 21205779640811952048761309)
        ·
          refine ⟨7952167365304482018285491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21205779640811952048761309 7952167365304482018285491)
          ·
            refine ⟨11928251047956723027428237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7952167365304482018285491 11928251047956723027428237)
            ·
              refine ⟨4473094142983771135285589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11928251047956723027428237 4473094142983771135285589)
              ·
                refine ⟨13104767997022766997907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 4473094142983771135285589 13104767997022766997907)
                ·
                  rfl

theorem cell23_689079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 3, 10].length) (baseStart_689079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_689079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_689079 prefixEnd_689079 := by exact prefixLift 689079
  have htrace : WordTrace (prefixWord ++ tailWord_689079) baseStart_689079 baseEnd_689079 := by
    simpa [prefixWord, tailWord_689079, baseEnd_689079] using wordTrace_append hprefix tailTrace_689079
  have hstable : (prefixWord ++ tailWord_689079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_689079).length < 2 ^ (prefixWord ++ tailWord_689079).sum := by decide
  have hdescent : baseEnd_689079 < baseStart_689079 := by decide
  rcases family_descends (prefixWord ++ tailWord_689079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_689086 : List Nat := [4, 2, 1, 1, 1, 2, 1, 3, 1, 1, 6]
def baseStart_689086 : Nat := 118140960795 + 689086 * 2 ^ 59
def prefixEnd_689086 : Nat := 4983230072969 + 3 ^ 40 * 689086 * 2
def baseEnd_689086 : Nat := 353832330284196181555957

theorem tailTrace_689086 : CollatzResearch.WordTrace tailWord_689086 prefixEnd_689086 353832330284196181555957 := by
  unfold tailWord_689086
  simp only [CollatzResearch.WordTrace]
  refine ⟨3141628897695822920550889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 16755354121044388909604741 3141628897695822920550889)
  ·
    refine ⟨2356221673271867190413167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3141628897695822920550889 2356221673271867190413167)
    ·
      refine ⟨3534332509907800785619751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2356221673271867190413167 3534332509907800785619751)
      ·
        refine ⟨5301498764861701178429627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3534332509907800785619751 5301498764861701178429627)
        ·
          refine ⟨7952248147292551767644441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5301498764861701178429627 7952248147292551767644441)
          ·
            refine ⟨5964186110469413825733331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7952248147292551767644441 5964186110469413825733331)
            ·
              refine ⟨8946279165704120738599997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5964186110469413825733331 8946279165704120738599997)
              ·
                refine ⟨3354854687139045276974999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8946279165704120738599997 3354854687139045276974999)
                ·
                  refine ⟨5032282030708567915462499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3354854687139045276974999 5032282030708567915462499)
                  ·
                    refine ⟨7548423046062851873193749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5032282030708567915462499 7548423046062851873193749)
                    ·
                      refine ⟨353832330284196181555957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 7548423046062851873193749 353832330284196181555957)
                      ·
                        rfl

theorem cell23_689086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 1, 3, 1, 1, 6].length) (baseStart_689086 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_689086 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_689086 prefixEnd_689086 := by exact prefixLift 689086
  have htrace : WordTrace (prefixWord ++ tailWord_689086) baseStart_689086 baseEnd_689086 := by
    simpa [prefixWord, tailWord_689086, baseEnd_689086] using wordTrace_append hprefix tailTrace_689086
  have hstable : (prefixWord ++ tailWord_689086).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_689086).length < 2 ^ (prefixWord ++ tailWord_689086).sum := by decide
  have hdescent : baseEnd_689086 < baseStart_689086 := by decide
  rcases family_descends (prefixWord ++ tailWord_689086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_689110 : List Nat := [5, 2, 1, 1, 2, 1, 3, 1, 1, 1, 5]
def baseStart_689110 : Nat := 118140960795 + 689110 * 2 ^ 59
def prefixEnd_689110 : Nat := 4983230072969 + 3 ^ 40 * 689110 * 2
def baseEnd_689110 : Nat := 353844653819904087655847

theorem tailTrace_689110 : CollatzResearch.WordTrace tailWord_689110 prefixEnd_689110 353844653819904087655847 := by
  unfold tailWord_689110
  simp only [CollatzResearch.WordTrace]
  refine ⟨1570869158342477216455049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 16755937688986423642187189 1570869158342477216455049)
  ·
    refine ⟨1178151868756857912341287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1570869158342477216455049 1178151868756857912341287)
    ·
      refine ⟨1767227803135286868511931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1178151868756857912341287 1767227803135286868511931)
      ·
        refine ⟨2650841704702930302767897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1767227803135286868511931 2650841704702930302767897)
        ·
          refine ⟨1988131278527197727075923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2650841704702930302767897 1988131278527197727075923)
          ·
            refine ⟨2982196917790796590613885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1988131278527197727075923 2982196917790796590613885)
            ·
              refine ⟨1118323844171548721480207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2982196917790796590613885 1118323844171548721480207)
              ·
                refine ⟨1677485766257323082220311, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1118323844171548721480207 1677485766257323082220311)
                ·
                  refine ⟨2516228649385984623330467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1677485766257323082220311 2516228649385984623330467)
                  ·
                    refine ⟨3774342974078976934995701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2516228649385984623330467 3774342974078976934995701)
                    ·
                      refine ⟨353844653819904087655847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3774342974078976934995701 353844653819904087655847)
                      ·
                        rfl

theorem cell23_689110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 3, 1, 1, 1, 5].length) (baseStart_689110 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_689110 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_689110 prefixEnd_689110 := by exact prefixLift 689110
  have htrace : WordTrace (prefixWord ++ tailWord_689110) baseStart_689110 baseEnd_689110 := by
    simpa [prefixWord, tailWord_689110, baseEnd_689110] using wordTrace_append hprefix tailTrace_689110
  have hstable : (prefixWord ++ tailWord_689110).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_689110).length < 2 ^ (prefixWord ++ tailWord_689110).sum := by decide
  have hdescent : baseEnd_689110 < baseStart_689110 := by decide
  rcases family_descends (prefixWord ++ tailWord_689110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_689216 : List Nat := [2, 1, 1, 2, 2, 3, 1, 3, 1, 7]
def baseStart_689216 : Nat := 118140960795 + 689216 * 2 ^ 59
def prefixEnd_689216 : Nat := 4983230072969 + 3 ^ 40 * 689216 * 2
def baseEnd_689216 : Nat := 117966360923093557643453

theorem tailTrace_689216 : CollatzResearch.WordTrace tailWord_689216 prefixEnd_689216 117966360923093557643453 := by
  unfold tailWord_689216
  simp only [CollatzResearch.WordTrace]
  refine ⟨12568886335547807783319751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16758515114063743711093001 12568886335547807783319751)
  ·
    refine ⟨18853329503321711674979627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12568886335547807783319751 18853329503321711674979627)
    ·
      refine ⟨28279994254982567512469441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18853329503321711674979627 28279994254982567512469441)
      ·
        refine ⟨21209995691236925634352081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28279994254982567512469441 21209995691236925634352081)
        ·
          refine ⟨15907496768427694225764061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21209995691236925634352081 15907496768427694225764061)
          ·
            refine ⟨5965311288160385334661523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15907496768427694225764061 5965311288160385334661523)
            ·
              refine ⟨8947966932240578001992285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5965311288160385334661523 8947966932240578001992285)
              ·
                refine ⟨3355487599590216750747107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8947966932240578001992285 3355487599590216750747107)
                ·
                  refine ⟨5033231399385325126120661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3355487599590216750747107 5033231399385325126120661)
                  ·
                    refine ⟨117966360923093557643453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 5033231399385325126120661 117966360923093557643453)
                    ·
                      rfl

theorem cell23_689216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 1, 3, 1, 7].length) (baseStart_689216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_689216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_689216 prefixEnd_689216 := by exact prefixLift 689216
  have htrace : WordTrace (prefixWord ++ tailWord_689216) baseStart_689216 baseEnd_689216 := by
    simpa [prefixWord, tailWord_689216, baseEnd_689216] using wordTrace_append hprefix tailTrace_689216
  have hstable : (prefixWord ++ tailWord_689216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_689216).length < 2 ^ (prefixWord ++ tailWord_689216).sum := by decide
  have hdescent : baseEnd_689216 < baseStart_689216 := by decide
  rcases family_descends (prefixWord ++ tailWord_689216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_689253 : List Nat := [1, 3, 1, 3, 2, 1, 1, 2, 4, 1, 4]
def baseStart_689253 : Nat := 118140960795 + 689253 * 2 ^ 59
def prefixEnd_689253 : Nat := 4983230072969 + 3 ^ 40 * 689253 * 2
def baseEnd_689253 : Nat := 353918081553497028167689

theorem tailTrace_689253 : CollatzResearch.WordTrace tailWord_689253 prefixEnd_689253 353918081553497028167689 := by
  unfold tailWord_689253
  simp only [CollatzResearch.WordTrace]
  refine ⟨25139122171961570885736413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16759414781307713923824275 25139122171961570885736413)
  ·
    refine ⟨9427170814485589082151155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25139122171961570885736413 9427170814485589082151155)
    ·
      refine ⟨14140756221728383623226733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9427170814485589082151155 14140756221728383623226733)
      ·
        refine ⟨5302783583148143858710025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14140756221728383623226733 5302783583148143858710025)
        ·
          refine ⟨3977087687361107894032519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5302783583148143858710025 3977087687361107894032519)
          ·
            refine ⟨5965631531041661841048779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3977087687361107894032519 5965631531041661841048779)
            ·
              refine ⟨8948447296562492761573169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5965631531041661841048779 8948447296562492761573169)
              ·
                refine ⟨6711335472421869571179877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8948447296562492761573169 6711335472421869571179877)
                ·
                  refine ⟨1258375401079100544596227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6711335472421869571179877 1258375401079100544596227)
                  ·
                    refine ⟨1887563101618650816894341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1258375401079100544596227 1887563101618650816894341)
                    ·
                      refine ⟨353918081553497028167689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1887563101618650816894341 353918081553497028167689)
                      ·
                        rfl

theorem cell23_689253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 1, 2, 4, 1, 4].length) (baseStart_689253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_689253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_689253 prefixEnd_689253 := by exact prefixLift 689253
  have htrace : WordTrace (prefixWord ++ tailWord_689253) baseStart_689253 baseEnd_689253 := by
    simpa [prefixWord, tailWord_689253, baseEnd_689253] using wordTrace_append hprefix tailTrace_689253
  have hstable : (prefixWord ++ tailWord_689253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_689253).length < 2 ^ (prefixWord ++ tailWord_689253).sum := by decide
  have hdescent : baseEnd_689253 < baseStart_689253 := by decide
  rcases family_descends (prefixWord ++ tailWord_689253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_689263 : List Nat := [1, 1, 2, 1, 3, 3, 2, 1, 5, 4]
def baseStart_689263 : Nat := 118140960795 + 689263 * 2 ^ 59
def prefixEnd_689263 : Nat := 4983230072969 + 3 ^ 40 * 689263 * 2
def baseEnd_689263 : Nat := 117974405453347329680881

theorem tailTrace_689263 : CollatzResearch.WordTrace tailWord_689263 prefixEnd_689263 117974405453347329680881 := by
  unfold tailWord_689263
  simp only [CollatzResearch.WordTrace]
  refine ⟨25139486901925342593600443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16759657934616895062400295 25139486901925342593600443)
  ·
    refine ⟨37709230352888013890400665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25139486901925342593600443 37709230352888013890400665)
    ·
      refine ⟨28281922764666010417800499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37709230352888013890400665 28281922764666010417800499)
      ·
        refine ⟨42422884146999015626700749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28281922764666010417800499 42422884146999015626700749)
        ·
          refine ⟨15908581555124630860012781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42422884146999015626700749 15908581555124630860012781)
          ·
            refine ⟨5965718083171736572504793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15908581555124630860012781 5965718083171736572504793)
            ·
              refine ⟨4474288562378802429378595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5965718083171736572504793 4474288562378802429378595)
              ·
                refine ⟨6711432843568203644067893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4474288562378802429378595 6711432843568203644067893)
                ·
                  refine ⟨629196829084519091631365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 6711432843568203644067893 629196829084519091631365)
                  ·
                    refine ⟨117974405453347329680881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 629196829084519091631365 117974405453347329680881)
                    ·
                      rfl

theorem cell23_689263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 2, 1, 5, 4].length) (baseStart_689263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_689263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_689263 prefixEnd_689263 := by exact prefixLift 689263
  have htrace : WordTrace (prefixWord ++ tailWord_689263) baseStart_689263 baseEnd_689263 := by
    simpa [prefixWord, tailWord_689263, baseEnd_689263] using wordTrace_append hprefix tailTrace_689263
  have hstable : (prefixWord ++ tailWord_689263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_689263).length < 2 ^ (prefixWord ++ tailWord_689263).sum := by decide
  have hdescent : baseEnd_689263 < baseStart_689263 := by decide
  rcases family_descends (prefixWord ++ tailWord_689263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_689290 : List Nat := [3, 1, 2, 3, 1, 1, 1, 4, 2, 2, 3]
def baseStart_689290 : Nat := 118140960795 + 689290 * 2 ^ 59
def prefixEnd_689290 : Nat := 4983230072969 + 3 ^ 40 * 689290 * 2
def baseEnd_689290 : Nat := 353937080337713383405019

theorem tailTrace_689290 : CollatzResearch.WordTrace tailWord_689290 prefixEnd_689290 353937080337713383405019 := by
  unfold tailWord_689290
  simp only [CollatzResearch.WordTrace]
  refine ⟨6285117918206881551208331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16760314448551684136555549 6285117918206881551208331)
  ·
    refine ⟨9427676877310322326812497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6285117918206881551208331 9427676877310322326812497)
    ·
      refine ⟨7070757657982741745109373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9427676877310322326812497 7070757657982741745109373)
      ·
        refine ⟨2651534121743528154416015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7070757657982741745109373 2651534121743528154416015)
        ·
          refine ⟨3977301182615292231624023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2651534121743528154416015 3977301182615292231624023)
          ·
            refine ⟨5965951773922938347436035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3977301182615292231624023 5965951773922938347436035)
            ·
              refine ⟨8948927660884407521154053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5965951773922938347436035 8948927660884407521154053)
              ·
                refine ⟨1677923936415826410216385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8948927660884407521154053 1677923936415826410216385)
                ·
                  refine ⟨1258442952311869807662289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1677923936415826410216385 1258442952311869807662289)
                  ·
                    refine ⟨943832214233902355746717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1258442952311869807662289 943832214233902355746717)
                    ·
                      refine ⟨353937080337713383405019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 943832214233902355746717 353937080337713383405019)
                      ·
                        rfl

theorem cell23_689290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 1, 4, 2, 2, 3].length) (baseStart_689290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_689290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_689290 prefixEnd_689290 := by exact prefixLift 689290
  have htrace : WordTrace (prefixWord ++ tailWord_689290) baseStart_689290 baseEnd_689290 := by
    simpa [prefixWord, tailWord_689290, baseEnd_689290] using wordTrace_append hprefix tailTrace_689290
  have hstable : (prefixWord ++ tailWord_689290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_689290).length < 2 ^ (prefixWord ++ tailWord_689290).sum := by decide
  have hdescent : baseEnd_689290 < baseStart_689290 := by decide
  rcases family_descends (prefixWord ++ tailWord_689290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_689354 : List Nat := [3, 1, 2, 1, 3, 2, 2, 4, 1, 1, 3]
def baseStart_689354 : Nat := 118140960795 + 689354 * 2 ^ 59
def prefixEnd_689354 : Nat := 4983230072969 + 3 ^ 40 * 689354 * 2
def baseEnd_689354 : Nat := 353969943099601133004725

theorem tailTrace_689354 : CollatzResearch.WordTrace tailWord_689354 prefixEnd_689354 353969943099601133004725 := by
  unfold tailWord_689354
  simp only [CollatzResearch.WordTrace]
  refine ⟨6285701486148916283790779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16761870629730443423442077 6285701486148916283790779)
  ·
    refine ⟨9428552229223374425686169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6285701486148916283790779 9428552229223374425686169)
    ·
      refine ⟨7071414171917530819264627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9428552229223374425686169 7071414171917530819264627)
      ·
        refine ⟨10607121257876296228896941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7071414171917530819264627 10607121257876296228896941)
        ·
          refine ⟨3977670471703611085836353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10607121257876296228896941 3977670471703611085836353)
          ·
            refine ⟨2983252853777708314377265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3977670471703611085836353 2983252853777708314377265)
            ·
              refine ⟨2237439640333281235782949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2983252853777708314377265 2237439640333281235782949)
              ·
                refine ⟨419519932562490231709303, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2237439640333281235782949 419519932562490231709303)
                ·
                  refine ⟨629279898843735347563955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 419519932562490231709303 629279898843735347563955)
                  ·
                    refine ⟨943919848265603021345933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 629279898843735347563955 943919848265603021345933)
                    ·
                      refine ⟨353969943099601133004725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 943919848265603021345933 353969943099601133004725)
                      ·
                        rfl

theorem cell23_689354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 2, 4, 1, 1, 3].length) (baseStart_689354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_689354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_689354 prefixEnd_689354 := by exact prefixLift 689354
  have htrace : WordTrace (prefixWord ++ tailWord_689354) baseStart_689354 baseEnd_689354 := by
    simpa [prefixWord, tailWord_689354, baseEnd_689354] using wordTrace_append hprefix tailTrace_689354
  have hstable : (prefixWord ++ tailWord_689354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_689354).length < 2 ^ (prefixWord ++ tailWord_689354).sum := by decide
  have hdescent : baseEnd_689354 < baseStart_689354 := by decide
  rcases family_descends (prefixWord ++ tailWord_689354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_689363 : List Nat := [1, 1, 1, 2, 1, 1, 1, 8, 1, 1, 5]
def baseStart_689363 : Nat := 118140960795 + 689363 * 2 ^ 59
def prefixEnd_689363 : Nat := 4983230072969 + 3 ^ 40 * 689363 * 2
def baseEnd_689363 : Nat := 353974564425491597792183

theorem tailTrace_689363 : CollatzResearch.WordTrace tailWord_689363 prefixEnd_689363 353974564425491597792183 := by
  unfold tailWord_689363
  simp only [CollatzResearch.WordTrace]
  refine ⟨25143134201563059672240743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16762089467708706448160495 25143134201563059672240743)
  ·
    refine ⟨37714701302344589508361115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25143134201563059672240743 37714701302344589508361115)
    ·
      refine ⟨56572051953516884262541673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37714701302344589508361115 56572051953516884262541673)
      ·
        refine ⟨42429038965137663196906255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56572051953516884262541673 42429038965137663196906255)
        ·
          refine ⟨63643558447706494795359383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42429038965137663196906255 63643558447706494795359383)
          ·
            refine ⟨95465337671559742193039075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63643558447706494795359383 95465337671559742193039075)
            ·
              refine ⟨143198006507339613289558613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 95465337671559742193039075 143198006507339613289558613)
              ·
                refine ⟨1678101638757886093237015, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 143198006507339613289558613 1678101638757886093237015)
                ·
                  refine ⟨2517152458136829139855523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1678101638757886093237015 2517152458136829139855523)
                  ·
                    refine ⟨3775728687205243709783285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2517152458136829139855523 3775728687205243709783285)
                    ·
                      refine ⟨353974564425491597792183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3775728687205243709783285 353974564425491597792183)
                      ·
                        rfl

theorem cell23_689363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 8, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 8, 1, 1, 5].length) (baseStart_689363 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_689363 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_689363 prefixEnd_689363 := by exact prefixLift 689363
  have htrace : WordTrace (prefixWord ++ tailWord_689363) baseStart_689363 baseEnd_689363 := by
    simpa [prefixWord, tailWord_689363, baseEnd_689363] using wordTrace_append hprefix tailTrace_689363
  have hstable : (prefixWord ++ tailWord_689363).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_689363).length < 2 ^ (prefixWord ++ tailWord_689363).sum := by decide
  have hdescent : baseEnd_689363 < baseStart_689363 := by decide
  rcases family_descends (prefixWord ++ tailWord_689363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_689377 : List Nat := [1, 2, 3, 1, 3, 3, 2, 2, 1, 1, 4]
def baseStart_689377 : Nat := 118140960795 + 689377 * 2 ^ 59
def prefixEnd_689377 : Nat := 4983230072969 + 3 ^ 40 * 689377 * 2
def baseEnd_689377 : Nat := 353981753154654543017119

theorem tailTrace_689377 : CollatzResearch.WordTrace tailWord_689377 prefixEnd_689377 353981753154654543017119 := by
  unfold tailWord_689377
  simp only [CollatzResearch.WordTrace]
  refine ⟨25143644823512340063250385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16762429882341560042166923 25143644823512340063250385)
  ·
    refine ⟨18857733617634255047437789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25143644823512340063250385 18857733617634255047437789)
    ·
      refine ⟨7071650106612845642789171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18857733617634255047437789 7071650106612845642789171)
      ·
        refine ⟨10607475159919268464183757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7071650106612845642789171 10607475159919268464183757)
        ·
          refine ⟨3977803184969725674068909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10607475159919268464183757 3977803184969725674068909)
          ·
            refine ⟨1491676194363647127775841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3977803184969725674068909 1491676194363647127775841)
            ·
              refine ⟨1118757145772735345831881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1491676194363647127775841 1118757145772735345831881)
              ·
                refine ⟨839067859329551509373911, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1118757145772735345831881 839067859329551509373911)
                ·
                  refine ⟨1258601788994327264060867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 839067859329551509373911 1258601788994327264060867)
                  ·
                    refine ⟨1887902683491490896091301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1258601788994327264060867 1887902683491490896091301)
                    ·
                      refine ⟨353981753154654543017119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1887902683491490896091301 353981753154654543017119)
                      ·
                        rfl

theorem cell23_689377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 3, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 3, 2, 2, 1, 1, 4].length) (baseStart_689377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_689377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_689377 prefixEnd_689377 := by exact prefixLift 689377
  have htrace : WordTrace (prefixWord ++ tailWord_689377) baseStart_689377 baseEnd_689377 := by
    simpa [prefixWord, tailWord_689377, baseEnd_689377] using wordTrace_append hprefix tailTrace_689377
  have hstable : (prefixWord ++ tailWord_689377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_689377).length < 2 ^ (prefixWord ++ tailWord_689377).sum := by decide
  have hdescent : baseEnd_689377 < baseStart_689377 := by decide
  rcases family_descends (prefixWord ++ tailWord_689377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_689380 : List Nat := [2, 3, 1, 1, 1, 2, 2, 3, 3, 2, 3]
def baseStart_689380 : Nat := 118140960795 + 689380 * 2 ^ 59
def prefixEnd_689380 : Nat := 4983230072969 + 3 ^ 40 * 689380 * 2
def baseEnd_689380 : Nat := 353983293596618031279605

theorem tailTrace_689380 : CollatzResearch.WordTrace tailWord_689380 prefixEnd_689380 353983293596618031279605 := by
  unfold tailWord_689380
  simp only [CollatzResearch.WordTrace]
  refine ⟨12571877121250735787804797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16762502828334314383739729 12571877121250735787804797)
  ·
    refine ⟨4714453920469025920426799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12571877121250735787804797 4714453920469025920426799)
    ·
      refine ⟨7071680880703538880640199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4714453920469025920426799 7071680880703538880640199)
      ·
        refine ⟨10607521321055308320960299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7071680880703538880640199 10607521321055308320960299)
        ·
          refine ⟨15911281981582962481440449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10607521321055308320960299 15911281981582962481440449)
          ·
            refine ⟨11933461486187221861080337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15911281981582962481440449 11933461486187221861080337)
            ·
              refine ⟨8950096114640416395810253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11933461486187221861080337 8950096114640416395810253)
              ·
                refine ⟨3356286042990156148428845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8950096114640416395810253 3356286042990156148428845)
                ·
                  refine ⟨1258607266121308555660817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3356286042990156148428845 1258607266121308555660817)
                  ·
                    refine ⟨943955449590981416745613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1258607266121308555660817 943955449590981416745613)
                    ·
                      refine ⟨353983293596618031279605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 943955449590981416745613 353983293596618031279605)
                      ·
                        rfl

theorem cell23_689380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 2, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 2, 3, 3, 2, 3].length) (baseStart_689380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_689380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_689380 prefixEnd_689380 := by exact prefixLift 689380
  have htrace : WordTrace (prefixWord ++ tailWord_689380) baseStart_689380 baseEnd_689380 := by
    simpa [prefixWord, tailWord_689380, baseEnd_689380] using wordTrace_append hprefix tailTrace_689380
  have hstable : (prefixWord ++ tailWord_689380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_689380).length < 2 ^ (prefixWord ++ tailWord_689380).sum := by decide
  have hdescent : baseEnd_689380 < baseStart_689380 := by decide
  rcases family_descends (prefixWord ++ tailWord_689380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_689390 : List Nat := [4, 1, 2, 1, 1, 1, 2, 4, 1, 2, 4]
def baseStart_689390 : Nat := 118140960795 + 689390 * 2 ^ 59
def prefixEnd_689390 : Nat := 4983230072969 + 3 ^ 40 * 689390 * 2
def baseEnd_689390 : Nat := 353988428403162992154559

theorem tailTrace_689390 : CollatzResearch.WordTrace tailWord_689390 prefixEnd_689390 353988428403162992154559 := by
  unfold tailWord_689390
  simp only [CollatzResearch.WordTrace]
  refine ⟨3143014871558155410434203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 16762745981643495522315749 3143014871558155410434203)
  ·
    refine ⟨4714522307337233115651305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3143014871558155410434203 4714522307337233115651305)
    ·
      refine ⟨3535891730502924836738479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4714522307337233115651305 3535891730502924836738479)
      ·
        refine ⟨5303837595754387255107719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3535891730502924836738479 5303837595754387255107719)
        ·
          refine ⟨7955756393631580882661579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5303837595754387255107719 7955756393631580882661579)
          ·
            refine ⟨11933634590447371323992369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7955756393631580882661579 11933634590447371323992369)
            ·
              refine ⟨8950225942835528492994277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11933634590447371323992369 8950225942835528492994277)
              ·
                refine ⟨1678167364281661592436427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8950225942835528492994277 1678167364281661592436427)
                ·
                  refine ⟨2517251046422492388654641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1678167364281661592436427 2517251046422492388654641)
                  ·
                    refine ⟨1887938284816869291490981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2517251046422492388654641 1887938284816869291490981)
                    ·
                      refine ⟨353988428403162992154559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1887938284816869291490981 353988428403162992154559)
                      ·
                        rfl

theorem cell23_689390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 2, 4, 1, 2, 4].length) (baseStart_689390 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_689390 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_689390 prefixEnd_689390 := by exact prefixLift 689390
  have htrace : WordTrace (prefixWord ++ tailWord_689390) baseStart_689390 baseEnd_689390 := by
    simpa [prefixWord, tailWord_689390, baseEnd_689390] using wordTrace_append hprefix tailTrace_689390
  have hstable : (prefixWord ++ tailWord_689390).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_689390).length < 2 ^ (prefixWord ++ tailWord_689390).sum := by decide
  have hdescent : baseEnd_689390 < baseStart_689390 := by decide
  rcases family_descends (prefixWord ++ tailWord_689390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_689413 : List Nat := [1, 3, 1, 1, 2, 1, 4, 1, 2, 7]
def baseStart_689413 : Nat := 118140960795 + 689413 * 2 ^ 59
def prefixEnd_689413 : Nat := 4983230072969 + 3 ^ 40 * 689413 * 2
def baseEnd_689413 : Nat := 118000079486072134055651

theorem tailTrace_689413 : CollatzResearch.WordTrace tailWord_689413 prefixEnd_689413 118000079486072134055651 := by
  unfold tailWord_689413
  simp only [CollatzResearch.WordTrace]
  refine ⟨25144957851381918211560893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16763305234254612141040595 25144957851381918211560893)
  ·
    refine ⟨9429359194268219329335335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25144957851381918211560893 9429359194268219329335335)
    ·
      refine ⟨14144038791402328994003003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9429359194268219329335335 14144038791402328994003003)
      ·
        refine ⟨21216058187103493491004505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14144038791402328994003003 21216058187103493491004505)
        ·
          refine ⟨15912043640327620118253379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21216058187103493491004505 15912043640327620118253379)
          ·
            refine ⟨23868065460491430177380069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15912043640327620118253379 23868065460491430177380069)
            ·
              refine ⟨4475262273842143158258763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23868065460491430177380069 4475262273842143158258763)
              ·
                refine ⟨6712893410763214737388145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4475262273842143158258763 6712893410763214737388145)
                ·
                  refine ⟨5034670058072411053041109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6712893410763214737388145 5034670058072411053041109)
                  ·
                    refine ⟨118000079486072134055651, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 5034670058072411053041109 118000079486072134055651)
                    ·
                      rfl

theorem cell23_689413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 4, 1, 2, 7].length) (baseStart_689413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_689413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_689413 prefixEnd_689413 := by exact prefixLift 689413
  have htrace : WordTrace (prefixWord ++ tailWord_689413) baseStart_689413 baseEnd_689413 := by
    simpa [prefixWord, tailWord_689413, baseEnd_689413] using wordTrace_append hprefix tailTrace_689413
  have hstable : (prefixWord ++ tailWord_689413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_689413).length < 2 ^ (prefixWord ++ tailWord_689413).sum := by decide
  have hdescent : baseEnd_689413 < baseStart_689413 := by decide
  rcases family_descends (prefixWord ++ tailWord_689413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_689463 : List Nat := [1, 1, 3, 1, 2, 1, 1, 1, 1, 5, 6]
def baseStart_689463 : Nat := 118140960795 + 689463 * 2 ^ 59
def prefixEnd_689463 : Nat := 4983230072969 + 3 ^ 40 * 689463 * 2
def baseEnd_689463 : Nat := 354025912490941206541723

theorem tailTrace_689463 : CollatzResearch.WordTrace tailWord_689463 prefixEnd_689463 354025912490941206541723 := by
  unfold tailWord_689463
  simp only [CollatzResearch.WordTrace]
  refine ⟨25146781501200776750881043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16764521000800517833920695 25146781501200776750881043)
  ·
    refine ⟨37720172251801165126321565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25146781501200776750881043 37720172251801165126321565)
    ·
      refine ⟨14145064594425436922370587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37720172251801165126321565 14145064594425436922370587)
      ·
        refine ⟨21217596891638155383555881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14145064594425436922370587 21217596891638155383555881)
        ·
          refine ⟨15913197668728616537666911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21217596891638155383555881 15913197668728616537666911)
          ·
            refine ⟨23869796503092924806500367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15913197668728616537666911 23869796503092924806500367)
            ·
              refine ⟨35804694754639387209750551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23869796503092924806500367 35804694754639387209750551)
              ·
                refine ⟨53707042131959080814625827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35804694754639387209750551 53707042131959080814625827)
                ·
                  refine ⟨80560563197938621221938741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 53707042131959080814625827 80560563197938621221938741)
                  ·
                    refine ⟨7552552799806745739556757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 80560563197938621221938741 7552552799806745739556757)
                    ·
                      refine ⟨354025912490941206541723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 7552552799806745739556757 354025912490941206541723)
                      ·
                        rfl

theorem cell23_689463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 5, 6].length) (baseStart_689463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_689463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_689463 prefixEnd_689463 := by exact prefixLift 689463
  have htrace : WordTrace (prefixWord ++ tailWord_689463) baseStart_689463 baseEnd_689463 := by
    simpa [prefixWord, tailWord_689463, baseEnd_689463] using wordTrace_append hprefix tailTrace_689463
  have hstable : (prefixWord ++ tailWord_689463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_689463).length < 2 ^ (prefixWord ++ tailWord_689463).sum := by decide
  have hdescent : baseEnd_689463 < baseStart_689463 := by decide
  rcases family_descends (prefixWord ++ tailWord_689463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_689467 : List Nat := [1, 1, 1, 1, 1, 2, 1, 1, 10, 2, 2]
def baseStart_689467 : Nat := 118140960795 + 689467 * 2 ^ 59
def prefixEnd_689467 : Nat := 4983230072969 + 3 ^ 40 * 689467 * 2
def baseEnd_689467 : Nat := 354027966413559190891705

theorem tailTrace_689467 : CollatzResearch.WordTrace tailWord_689467 prefixEnd_689467 354027966413559190891705 := by
  unfold tailWord_689467
  simp only [CollatzResearch.WordTrace]
  refine ⟨25146927393186285434026655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16764618262124190289351103 25146927393186285434026655)
  ·
    refine ⟨37720391089779428151039983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25146927393186285434026655 37720391089779428151039983)
    ·
      refine ⟨56580586634669142226559975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37720391089779428151039983 56580586634669142226559975)
      ·
        refine ⟨84870879952003713339839963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56580586634669142226559975 84870879952003713339839963)
        ·
          refine ⟨127306319928005570009759945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84870879952003713339839963 127306319928005570009759945)
          ·
            refine ⟨95479739946004177507319959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 127306319928005570009759945 95479739946004177507319959)
            ·
              refine ⟨143219609919006266260979939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 95479739946004177507319959 143219609919006266260979939)
              ·
                refine ⟨214829414878509399391469909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 143219609919006266260979939 214829414878509399391469909)
                ·
                  refine ⟨629383051401883006029697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 214829414878509399391469909 629383051401883006029697)
                  ·
                    refine ⟨472037288551412254522273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 629383051401883006029697 472037288551412254522273)
                    ·
                      refine ⟨354027966413559190891705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 472037288551412254522273 354027966413559190891705)
                      ·
                        rfl

theorem cell23_689467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 10, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 10, 2, 2].length) (baseStart_689467 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_689467 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_689467 prefixEnd_689467 := by exact prefixLift 689467
  have htrace : WordTrace (prefixWord ++ tailWord_689467) baseStart_689467 baseEnd_689467 := by
    simpa [prefixWord, tailWord_689467, baseEnd_689467] using wordTrace_append hprefix tailTrace_689467
  have hstable : (prefixWord ++ tailWord_689467).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_689467).length < 2 ^ (prefixWord ++ tailWord_689467).sum := by decide
  have hdescent : baseEnd_689467 < baseStart_689467 := by decide
  rcases family_descends (prefixWord ++ tailWord_689467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_689478 : List Nat := [6, 1, 1, 3, 1, 1, 2, 1, 1, 3, 3]
def baseStart_689478 : Nat := 118140960795 + 689478 * 2 ^ 59
def prefixEnd_689478 : Nat := 4983230072969 + 3 ^ 40 * 689478 * 2
def baseEnd_689478 : Nat := 354033614700758647854155

theorem tailTrace_689478 : CollatzResearch.WordTrace tailWord_689478 prefixEnd_689478 354033614700758647854155 := by
  unfold tailWord_689478
  simp only [CollatzResearch.WordTrace]
  refine ⟨785854018629576072271159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 16764885730764289541784725 785854018629576072271159)
  ·
    refine ⟨1178781027944364108406739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 785854018629576072271159 1178781027944364108406739)
    ·
      refine ⟨1768171541916546162610109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1178781027944364108406739 1768171541916546162610109)
      ·
        refine ⟨663064328218704810978791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1768171541916546162610109 663064328218704810978791)
        ·
          refine ⟨994596492328057216468187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 663064328218704810978791 994596492328057216468187)
          ·
            refine ⟨1491894738492085824702281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 994596492328057216468187 1491894738492085824702281)
            ·
              refine ⟨1118921053869064368526711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1491894738492085824702281 1118921053869064368526711)
              ·
                refine ⟨1678381580803596552790067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1118921053869064368526711 1678381580803596552790067)
                ·
                  refine ⟨2517572371205394829185101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1678381580803596552790067 2517572371205394829185101)
                  ·
                    refine ⟨944089639202023060944413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2517572371205394829185101 944089639202023060944413)
                    ·
                      refine ⟨354033614700758647854155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 944089639202023060944413 354033614700758647854155)
                      ·
                        rfl

theorem cell23_689478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 1, 2, 1, 1, 3, 3].length) (baseStart_689478 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_689478 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_689478 prefixEnd_689478 := by exact prefixLift 689478
  have htrace : WordTrace (prefixWord ++ tailWord_689478) baseStart_689478 baseEnd_689478 := by
    simpa [prefixWord, tailWord_689478, baseEnd_689478] using wordTrace_append hprefix tailTrace_689478
  have hstable : (prefixWord ++ tailWord_689478).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_689478).length < 2 ^ (prefixWord ++ tailWord_689478).sum := by decide
  have hdescent : baseEnd_689478 < baseStart_689478 := by decide
  rcases family_descends (prefixWord ++ tailWord_689478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_689483 : List Nat := [1, 1, 1, 1, 3, 1, 1, 2, 3, 2, 7]
def baseStart_689483 : Nat := 118140960795 + 689483 * 2 ^ 59
def prefixEnd_689483 : Nat := 4983230072969 + 3 ^ 40 * 689483 * 2
def baseEnd_689483 : Nat := 354036182104031128291631

theorem tailTrace_689483 : CollatzResearch.WordTrace tailWord_689483 prefixEnd_689483 354036182104031128291631 := by
  unfold tailWord_689483
  simp only [CollatzResearch.WordTrace]
  refine ⟨25147510961128320166609103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16765007307418880111072735 25147510961128320166609103)
  ·
    refine ⟨37721266441692480249913655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25147510961128320166609103 37721266441692480249913655)
    ·
      refine ⟨56581899662538720374870483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37721266441692480249913655 56581899662538720374870483)
      ·
        refine ⟨84872849493808080562305725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56581899662538720374870483 84872849493808080562305725)
        ·
          refine ⟨31827318560178030210864647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 84872849493808080562305725 31827318560178030210864647)
          ·
            refine ⟨47740977840267045316296971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31827318560178030210864647 47740977840267045316296971)
            ·
              refine ⟨71611466760400567974445457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47740977840267045316296971 71611466760400567974445457)
              ·
                refine ⟨53708600070300425980834093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 71611466760400567974445457 53708600070300425980834093)
                ·
                  refine ⟨20140725026362659742812785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 53708600070300425980834093 20140725026362659742812785)
                  ·
                    refine ⟨15105543769771994807109589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20140725026362659742812785 15105543769771994807109589)
                    ·
                      refine ⟨354036182104031128291631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 15105543769771994807109589 354036182104031128291631)
                      ·
                        rfl

theorem cell23_689483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 2, 3, 2, 7].length) (baseStart_689483 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_689483 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_689483 prefixEnd_689483 := by exact prefixLift 689483
  have htrace : WordTrace (prefixWord ++ tailWord_689483) baseStart_689483 baseEnd_689483 := by
    simpa [prefixWord, tailWord_689483, baseEnd_689483] using wordTrace_append hprefix tailTrace_689483
  have hstable : (prefixWord ++ tailWord_689483).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_689483).length < 2 ^ (prefixWord ++ tailWord_689483).sum := by decide
  have hdescent : baseEnd_689483 < baseStart_689483 := by decide
  rcases family_descends (prefixWord ++ tailWord_689483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_689484 : List Nat := [2, 2, 1, 3, 2, 3, 2, 1, 1, 4, 2]
def baseStart_689484 : Nat := 118140960795 + 689484 * 2 ^ 59
def prefixEnd_689484 : Nat := 4983230072969 + 3 ^ 40 * 689484 * 2
def baseEnd_689484 : Nat := 354036695584685624379127

theorem tailTrace_689484 : CollatzResearch.WordTrace tailWord_689484 prefixEnd_689484 354036695584685624379127 := by
  unfold tailWord_689484
  simp only [CollatzResearch.WordTrace]
  refine ⟨12573773717062348668697753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16765031622749798224930337 12573773717062348668697753)
  ·
    refine ⟨9430330287796761501523315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12573773717062348668697753 9430330287796761501523315)
    ·
      refine ⟨14145495431695142252284973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9430330287796761501523315 14145495431695142252284973)
      ·
        refine ⟨5304560786885678344606865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14145495431695142252284973 5304560786885678344606865)
        ·
          refine ⟨3978420590164258758455149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5304560786885678344606865 3978420590164258758455149)
          ·
            refine ⟨1491907721311597034420681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3978420590164258758455149 1491907721311597034420681)
            ·
              refine ⟨1118930790983697775815511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1491907721311597034420681 1118930790983697775815511)
              ·
                refine ⟨1678396186475546663723267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1118930790983697775815511 1678396186475546663723267)
                ·
                  refine ⟨2517594279713319995584901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1678396186475546663723267 2517594279713319995584901)
                  ·
                    refine ⟨472048927446247499172169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2517594279713319995584901 472048927446247499172169)
                    ·
                      refine ⟨354036695584685624379127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 472048927446247499172169 354036695584685624379127)
                      ·
                        rfl

theorem cell23_689484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 3, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 3, 2, 1, 1, 4, 2].length) (baseStart_689484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_689484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_689484 prefixEnd_689484 := by exact prefixLift 689484
  have htrace : WordTrace (prefixWord ++ tailWord_689484) baseStart_689484 baseEnd_689484 := by
    simpa [prefixWord, tailWord_689484, baseEnd_689484] using wordTrace_append hprefix tailTrace_689484
  have hstable : (prefixWord ++ tailWord_689484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_689484).length < 2 ^ (prefixWord ++ tailWord_689484).sum := by decide
  have hdescent : baseEnd_689484 < baseStart_689484 := by decide
  rcases family_descends (prefixWord ++ tailWord_689484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_689507 : List Nat := [1, 1, 1, 5, 2, 2, 1, 5, 5]
def baseStart_689507 : Nat := 118140960795 + 689507 * 2 ^ 59
def prefixEnd_689507 : Nat := 4983230072969 + 3 ^ 40 * 689507 * 2
def baseEnd_689507 : Nat := 39338722848859892710169

theorem tailTrace_689507 : CollatzResearch.WordTrace tailWord_689507 prefixEnd_689507 39338722848859892710169 := by
  unfold tailWord_689507
  simp only [CollatzResearch.WordTrace]
  refine ⟨25148386313041372265482775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16765590875360914843655183 25148386313041372265482775)
  ·
    refine ⟨37722579469562058398224163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25148386313041372265482775 37722579469562058398224163)
    ·
      refine ⟨56583869204343087597336245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37722579469562058398224163 56583869204343087597336245)
      ·
        refine ⟨5304737737907164462250273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 56583869204343087597336245 5304737737907164462250273)
        ·
          refine ⟨3978553303430373346687705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5304737737907164462250273 3978553303430373346687705)
          ·
            refine ⟨2983914977572780010015779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3978553303430373346687705 2983914977572780010015779)
            ·
              refine ⟨4475872466359170015023669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2983914977572780010015779 4475872466359170015023669)
              ·
                refine ⟨419613043721172188908469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4475872466359170015023669 419613043721172188908469)
                ·
                  refine ⟨39338722848859892710169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 419613043721172188908469 39338722848859892710169)
                  ·
                    rfl

theorem cell23_689507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 1, 5, 5].length) (baseStart_689507 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_689507 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_689507 prefixEnd_689507 := by exact prefixLift 689507
  have htrace : WordTrace (prefixWord ++ tailWord_689507) baseStart_689507 baseEnd_689507 := by
    simpa [prefixWord, tailWord_689507, baseEnd_689507] using wordTrace_append hprefix tailTrace_689507
  have hstable : (prefixWord ++ tailWord_689507).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_689507).length < 2 ^ (prefixWord ++ tailWord_689507).sum := by decide
  have hdescent : baseEnd_689507 < baseStart_689507 := by decide
  rcases family_descends (prefixWord ++ tailWord_689507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_689517 : List Nat := [1, 5, 1, 1, 1, 3, 1, 2, 2, 3, 3]
def baseStart_689517 : Nat := 118140960795 + 689517 * 2 ^ 59
def prefixEnd_689517 : Nat := 4983230072969 + 3 ^ 40 * 689517 * 2
def baseEnd_689517 : Nat := 354053640446283995266475

theorem tailTrace_689517 : CollatzResearch.WordTrace tailWord_689517 prefixEnd_689517 354053640446283995266475 := by
  unfold tailWord_689517
  simp only [CollatzResearch.WordTrace]
  refine ⟨25148751043005143973346805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16765834028670095982231203 25148751043005143973346805)
  ·
    refine ⟨2357695410281732247501263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 25148751043005143973346805 2357695410281732247501263)
    ·
      refine ⟨3536543115422598371251895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2357695410281732247501263 3536543115422598371251895)
      ·
        refine ⟨5304814673133897556877843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3536543115422598371251895 5304814673133897556877843)
        ·
          refine ⟨7957222009700846335316765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5304814673133897556877843 7957222009700846335316765)
          ·
            refine ⟨2983958253637817375743787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7957222009700846335316765 2983958253637817375743787)
            ·
              refine ⟨4475937380456726063615681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2983958253637817375743787 4475937380456726063615681)
              ·
                refine ⟨3356953035342544547711761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4475937380456726063615681 3356953035342544547711761)
                ·
                  refine ⟨2517714776506908410783821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3356953035342544547711761 2517714776506908410783821)
                  ·
                    refine ⟨944143041190090654043933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2517714776506908410783821 944143041190090654043933)
                    ·
                      refine ⟨354053640446283995266475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 944143041190090654043933 354053640446283995266475)
                      ·
                        rfl

theorem cell23_689517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 1, 2, 2, 3, 3].length) (baseStart_689517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_689517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_689517 prefixEnd_689517 := by exact prefixLift 689517
  have htrace : WordTrace (prefixWord ++ tailWord_689517) baseStart_689517 baseEnd_689517 := by
    simpa [prefixWord, tailWord_689517, baseEnd_689517] using wordTrace_append hprefix tailTrace_689517
  have hstable : (prefixWord ++ tailWord_689517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_689517).length < 2 ^ (prefixWord ++ tailWord_689517).sum := by decide
  have hdescent : baseEnd_689517 < baseStart_689517 := by decide
  rcases family_descends (prefixWord ++ tailWord_689517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_689518 : List Nat := [4, 1, 2, 4, 1, 1, 1, 1, 4, 2, 2]
def baseStart_689518 : Nat := 118140960795 + 689518 * 2 ^ 59
def prefixEnd_689518 : Nat := 4983230072969 + 3 ^ 40 * 689518 * 2
def baseEnd_689518 : Nat := 354054153926938491353971

theorem tailTrace_689518 : CollatzResearch.WordTrace tailWord_689518 prefixEnd_689518 354054153926938491353971 := by
  unfold tailWord_689518
  simp only [CollatzResearch.WordTrace]
  refine ⟨3143598439500190143016651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 16765858344001014096088805 3143598439500190143016651)
  ·
    refine ⟨4715397659250285214524977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3143598439500190143016651 4715397659250285214524977)
    ·
      refine ⟨3536548244437713910893733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4715397659250285214524977 3536548244437713910893733)
      ·
        refine ⟨663102795832071358292575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3536548244437713910893733 663102795832071358292575)
        ·
          refine ⟨994654193748107037438863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 663102795832071358292575 994654193748107037438863)
          ·
            refine ⟨1491981290622160556158295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 994654193748107037438863 1491981290622160556158295)
            ·
              refine ⟨2237971935933240834237443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1491981290622160556158295 2237971935933240834237443)
              ·
                refine ⟨3356957903899861251356165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2237971935933240834237443 3356957903899861251356165)
                ·
                  refine ⟨629429606981223984629281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3356957903899861251356165 629429606981223984629281)
                  ·
                    refine ⟨472072205235917988471961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 629429606981223984629281 472072205235917988471961)
                    ·
                      refine ⟨354054153926938491353971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 472072205235917988471961 354054153926938491353971)
                      ·
                        rfl

theorem cell23_689518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 1, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 1, 1, 1, 4, 2, 2].length) (baseStart_689518 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_689518 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_689518 prefixEnd_689518 := by exact prefixLift 689518
  have htrace : WordTrace (prefixWord ++ tailWord_689518) baseStart_689518 baseEnd_689518 := by
    simpa [prefixWord, tailWord_689518, baseEnd_689518] using wordTrace_append hprefix tailTrace_689518
  have hstable : (prefixWord ++ tailWord_689518).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_689518).length < 2 ^ (prefixWord ++ tailWord_689518).sum := by decide
  have hdescent : baseEnd_689518 < baseStart_689518 := by decide
  rcases family_descends (prefixWord ++ tailWord_689518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_689520 : List Nat := [2, 1, 1, 1, 4, 2, 2, 1, 4, 5]
def baseStart_689520 : Nat := 118140960795 + 689520 * 2 ^ 59
def prefixEnd_689520 : Nat := 4983230072969 + 3 ^ 40 * 689520 * 2
def baseEnd_689520 : Nat := 118018393629415827842987

theorem tailTrace_689520 : CollatzResearch.WordTrace tailWord_689520 prefixEnd_689520 118018393629415827842987 := by
  unfold tailWord_689520
  simp only [CollatzResearch.WordTrace]
  refine ⟨12574430230997137742853007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16765906974662850323804009 12574430230997137742853007)
  ·
    refine ⟨18861645346495706614279511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12574430230997137742853007 18861645346495706614279511)
    ·
      refine ⟨28292468019743559921419267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18861645346495706614279511 28292468019743559921419267)
      ·
        refine ⟨42438702029615339882128901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28292468019743559921419267 42438702029615339882128901)
        ·
          refine ⟨7957256630552876227899169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 42438702029615339882128901 7957256630552876227899169)
          ·
            refine ⟨5967942472914657170924377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7957256630552876227899169 5967942472914657170924377)
            ·
              refine ⟨4475956854685992878193283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5967942472914657170924377 4475956854685992878193283)
              ·
                refine ⟨6713935282028989317289925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4475956854685992878193283 6713935282028989317289925)
                ·
                  refine ⟨1258862865380435496991861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6713935282028989317289925 1258862865380435496991861)
                  ·
                    refine ⟨118018393629415827842987, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1258862865380435496991861 118018393629415827842987)
                    ·
                      rfl

theorem cell23_689520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 2, 1, 4, 5].length) (baseStart_689520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_689520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_689520 prefixEnd_689520 := by exact prefixLift 689520
  have htrace : WordTrace (prefixWord ++ tailWord_689520) baseStart_689520 baseEnd_689520 := by
    simpa [prefixWord, tailWord_689520, baseEnd_689520] using wordTrace_append hprefix tailTrace_689520
  have hstable : (prefixWord ++ tailWord_689520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_689520).length < 2 ^ (prefixWord ++ tailWord_689520).sum := by decide
  have hdescent : baseEnd_689520 < baseStart_689520 := by decide
  rcases family_descends (prefixWord ++ tailWord_689520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_689557 : List Nat := [1, 3, 2, 1, 1, 2, 2, 2, 1, 6, 2]
def baseStart_689557 : Nat := 118140960795 + 689557 * 2 ^ 59
def prefixEnd_689557 : Nat := 4983230072969 + 3 ^ 40 * 689557 * 2
def baseEnd_689557 : Nat := 354074179672463838766291

theorem tailTrace_689557 : CollatzResearch.WordTrace tailWord_689557 prefixEnd_689557 354074179672463838766291 := by
  unfold tailWord_689557
  simp only [CollatzResearch.WordTrace]
  refine ⟨25150209962860230804802925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16766806641906820536535283 25150209962860230804802925)
  ·
    refine ⟨9431328736072586551801097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25150209962860230804802925 9431328736072586551801097)
    ·
      refine ⟨7073496552054439913850823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9431328736072586551801097 7073496552054439913850823)
      ·
        refine ⟨10610244828081659870776235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7073496552054439913850823 10610244828081659870776235)
        ·
          refine ⟨15915367242122489806164353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10610244828081659870776235 15915367242122489806164353)
          ·
            refine ⟨11936525431591867354623265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15915367242122489806164353 11936525431591867354623265)
            ·
              refine ⟨8952394073693900515967449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11936525431591867354623265 8952394073693900515967449)
              ·
                refine ⟨6714295555270425386975587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8952394073693900515967449 6714295555270425386975587)
                ·
                  refine ⟨10071443332905638080463381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6714295555270425386975587 10071443332905638080463381)
                  ·
                    refine ⟨472098906229951785021721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10071443332905638080463381 472098906229951785021721)
                    ·
                      refine ⟨354074179672463838766291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 472098906229951785021721 354074179672463838766291)
                      ·
                        rfl

theorem cell23_689557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 2, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 2, 2, 1, 6, 2].length) (baseStart_689557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_689557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_689557 prefixEnd_689557 := by exact prefixLift 689557
  have htrace : WordTrace (prefixWord ++ tailWord_689557) baseStart_689557 baseEnd_689557 := by
    simpa [prefixWord, tailWord_689557, baseEnd_689557] using wordTrace_append hprefix tailTrace_689557
  have hstable : (prefixWord ++ tailWord_689557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_689557).length < 2 ^ (prefixWord ++ tailWord_689557).sum := by decide
  have hdescent : baseEnd_689557 < baseStart_689557 := by decide
  rcases family_descends (prefixWord ++ tailWord_689557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_689580 : List Nat := [2, 2, 1, 1, 1, 1, 6, 1, 8]
def baseStart_689580 : Nat := 118140960795 + 689580 * 2 ^ 59
def prefixEnd_689580 : Nat := 4983230072969 + 3 ^ 40 * 689580 * 2
def baseEnd_689580 : Nat := 39342887747501916530965

theorem tailTrace_689580 : CollatzResearch.WordTrace tailWord_689580 prefixEnd_689580 39342887747501916530965 := by
  unfold tailWord_689580
  simp only [CollatzResearch.WordTrace]
  refine ⟨12575524420888452866445097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16767365894517937155260129 12575524420888452866445097)
  ·
    refine ⟨9431643315666339649833823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12575524420888452866445097 9431643315666339649833823)
    ·
      refine ⟨14147464973499509474750735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9431643315666339649833823 14147464973499509474750735)
      ·
        refine ⟨21221197460249264212126103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14147464973499509474750735 21221197460249264212126103)
        ·
          refine ⟨31831796190373896318189155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21221197460249264212126103 31831796190373896318189155)
          ·
            refine ⟨47747694285560844477283733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31831796190373896318189155 47747694285560844477283733)
            ·
              refine ⟨2238173169635664584872675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 47747694285560844477283733 2238173169635664584872675)
              ·
                refine ⟨3357259754453496877309013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2238173169635664584872675 3357259754453496877309013)
                ·
                  refine ⟨39342887747501916530965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 3357259754453496877309013 39342887747501916530965)
                  ·
                    rfl

theorem cell23_689580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 8].length) (baseStart_689580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_689580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_689580 prefixEnd_689580 := by exact prefixLift 689580
  have htrace : WordTrace (prefixWord ++ tailWord_689580) baseStart_689580 baseEnd_689580 := by
    simpa [prefixWord, tailWord_689580, baseEnd_689580] using wordTrace_append hprefix tailTrace_689580
  have hstable : (prefixWord ++ tailWord_689580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_689580).length < 2 ^ (prefixWord ++ tailWord_689580).sum := by decide
  have hdescent : baseEnd_689580 < baseStart_689580 := by decide
  rcases family_descends (prefixWord ++ tailWord_689580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_689597 : List Nat := [1, 4, 1, 2, 2, 1, 3, 3, 6]
def baseStart_689597 : Nat := 118140960795 + 689597 * 2 ^ 59
def prefixEnd_689597 : Nat := 4983230072969 + 3 ^ 40 * 689597 * 2
def baseEnd_689597 : Nat := 39343857655404853585123

theorem tailTrace_689597 : CollatzResearch.WordTrace tailWord_689597 prefixEnd_689597 39343857655404853585123 := by
  unfold tailWord_689597
  simp only [CollatzResearch.WordTrace]
  refine ⟨25151668882715317636259045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16767779255143545090839363 25151668882715317636259045)
  ·
    refine ⟨4715937915509122056798571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 25151668882715317636259045 4715937915509122056798571)
    ·
      refine ⟨7073906873263683085197857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4715937915509122056798571 7073906873263683085197857)
      ·
        refine ⟨5305430154947762313898393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7073906873263683085197857 5305430154947762313898393)
        ·
          refine ⟨3979072616210821735423795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5305430154947762313898393 3979072616210821735423795)
          ·
            refine ⟨5968608924316232603135693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3979072616210821735423795 5968608924316232603135693)
            ·
              refine ⟨2238228346618587226175885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5968608924316232603135693 2238228346618587226175885)
              ·
                refine ⟨839335629981970209815957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2238228346618587226175885 839335629981970209815957)
                ·
                  refine ⟨39343857655404853585123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 839335629981970209815957 39343857655404853585123)
                  ·
                    rfl

theorem cell23_689597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 3, 3, 6].length) (baseStart_689597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_689597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_689597 prefixEnd_689597 := by exact prefixLift 689597
  have htrace : WordTrace (prefixWord ++ tailWord_689597) baseStart_689597 baseEnd_689597 := by
    simpa [prefixWord, tailWord_689597, baseEnd_689597] using wordTrace_append hprefix tailTrace_689597
  have hstable : (prefixWord ++ tailWord_689597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_689597).length < 2 ^ (prefixWord ++ tailWord_689597).sum := by decide
  have hdescent : baseEnd_689597 < baseStart_689597 := by decide
  rcases family_descends (prefixWord ++ tailWord_689597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_689600 : List Nat := [2, 1, 1, 2, 3, 1, 2, 2, 1, 2, 6]
def baseStart_689600 : Nat := 118140960795 + 689600 * 2 ^ 59
def prefixEnd_689600 : Nat := 4983230072969 + 3 ^ 40 * 689600 * 2
def baseEnd_689600 : Nat := 354096259340607170528593

theorem tailTrace_689600 : CollatzResearch.WordTrace tailWord_689600 prefixEnd_689600 354096259340607170528593 := by
  unfold tailWord_689600
  simp only [CollatzResearch.WordTrace]
  refine ⟨12575889150852224574309127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16767852201136299432412169 12575889150852224574309127)
  ·
    refine ⟨18863833726278336861463691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12575889150852224574309127 18863833726278336861463691)
    ·
      refine ⟨28295750589417505292195537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18863833726278336861463691 28295750589417505292195537)
      ·
        refine ⟨21221812942063128969146653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28295750589417505292195537 21221812942063128969146653)
        ·
          refine ⟨7958179853273673363429995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21221812942063128969146653 7958179853273673363429995)
          ·
            refine ⟨11937269779910510045144993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7958179853273673363429995 11937269779910510045144993)
            ·
              refine ⟨8952952334932882533858745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11937269779910510045144993 8952952334932882533858745)
              ·
                refine ⟨6714714251199661900394059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8952952334932882533858745 6714714251199661900394059)
                ·
                  refine ⟨10072071376799492850591089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6714714251199661900394059 10072071376799492850591089)
                  ·
                    refine ⟨7554053532599619637943317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10072071376799492850591089 7554053532599619637943317)
                    ·
                      refine ⟨354096259340607170528593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 7554053532599619637943317 354096259340607170528593)
                      ·
                        rfl

theorem cell23_689600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 2, 2, 1, 2, 6].length) (baseStart_689600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_689600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_689600 prefixEnd_689600 := by exact prefixLift 689600
  have htrace : WordTrace (prefixWord ++ tailWord_689600) baseStart_689600 baseEnd_689600 := by
    simpa [prefixWord, tailWord_689600, baseEnd_689600] using wordTrace_append hprefix tailTrace_689600
  have hstable : (prefixWord ++ tailWord_689600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_689600).length < 2 ^ (prefixWord ++ tailWord_689600).sum := by decide
  have hdescent : baseEnd_689600 < baseStart_689600 := by decide
  rcases family_descends (prefixWord ++ tailWord_689600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_689647 : List Nat := [1, 1, 2, 1, 4, 1, 3, 2, 3, 1, 4]
def baseStart_689647 : Nat := 118140960795 + 689647 * 2 ^ 59
def prefixEnd_689647 : Nat := 4983230072969 + 3 ^ 40 * 689647 * 2
def baseEnd_689647 : Nat := 354120392931368486640877

theorem tailTrace_689647 : CollatzResearch.WordTrace tailWord_689647 prefixEnd_689647 354120392931368486640877 := by
  unfold tailWord_689647
  simp only [CollatzResearch.WordTrace]
  refine ⟨25153492532534176175579195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16768995021689450783719463 25153492532534176175579195)
  ·
    refine ⟨37730238798801264263368793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25153492532534176175579195 37730238798801264263368793)
    ·
      refine ⟨28297679099100948197526595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37730238798801264263368793 28297679099100948197526595)
      ·
        refine ⟨42446518648651422296289893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28297679099100948197526595 42446518648651422296289893)
        ·
          refine ⟨7958722246622141680554355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 42446518648651422296289893 7958722246622141680554355)
          ·
            refine ⟨11938083369933212520831533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7958722246622141680554355 11938083369933212520831533)
            ·
              refine ⟨4476781263724954695311825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11938083369933212520831533 4476781263724954695311825)
              ·
                refine ⟨3357585947793716021483869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4476781263724954695311825 3357585947793716021483869)
                ·
                  refine ⟨1259094730422643508056451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3357585947793716021483869 1259094730422643508056451)
                  ·
                    refine ⟨1888642095633965262084677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1259094730422643508056451 1888642095633965262084677)
                    ·
                      refine ⟨354120392931368486640877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1888642095633965262084677 354120392931368486640877)
                      ·
                        rfl

theorem cell23_689647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 3, 2, 3, 1, 4].length) (baseStart_689647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_689647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_689647 prefixEnd_689647 := by exact prefixLift 689647
  have htrace : WordTrace (prefixWord ++ tailWord_689647) baseStart_689647 baseEnd_689647 := by
    simpa [prefixWord, tailWord_689647, baseEnd_689647] using wordTrace_append hprefix tailTrace_689647
  have hstable : (prefixWord ++ tailWord_689647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_689647).length < 2 ^ (prefixWord ++ tailWord_689647).sum := by decide
  have hdescent : baseEnd_689647 < baseStart_689647 := by decide
  rcases family_descends (prefixWord ++ tailWord_689647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_689657 : List Nat := [1, 2, 1, 3, 1, 2, 1, 2, 6, 4]
def baseStart_689657 : Nat := 118140960795 + 689657 * 2 ^ 59
def prefixEnd_689657 : Nat := 4983230072969 + 3 ^ 40 * 689657 * 2
def baseEnd_689657 : Nat := 118041842579304482505277

theorem tailTrace_689657 : CollatzResearch.WordTrace tailWord_689657 prefixEnd_689657 118041842579304482505277 := by
  unfold tailWord_689657
  simp only [CollatzResearch.WordTrace]
  refine ⟨25153857262497947883443225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16769238174998631922295483 25153857262497947883443225)
  ·
    refine ⟨18865392946873460912582419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25153857262497947883443225 18865392946873460912582419)
    ·
      refine ⟨28298089420310191368873629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18865392946873460912582419 28298089420310191368873629)
      ·
        refine ⟨10611783532616321763327611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28298089420310191368873629 10611783532616321763327611)
        ·
          refine ⟨15917675298924482644991417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10611783532616321763327611 15917675298924482644991417)
          ·
            refine ⟨11938256474193361983743563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15917675298924482644991417 11938256474193361983743563)
            ·
              refine ⟨17907384711290042975615345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11938256474193361983743563 17907384711290042975615345)
              ·
                refine ⟨13430538533467532231711509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17907384711290042975615345 13430538533467532231711509)
                ·
                  refine ⟨629556493756290573361477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 13430538533467532231711509 629556493756290573361477)
                  ·
                    refine ⟨118041842579304482505277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 629556493756290573361477 118041842579304482505277)
                    ·
                      rfl

theorem cell23_689657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 2, 6, 4].length) (baseStart_689657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_689657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_689657 prefixEnd_689657 := by exact prefixLift 689657
  have htrace : WordTrace (prefixWord ++ tailWord_689657) baseStart_689657 baseEnd_689657 := by
    simpa [prefixWord, tailWord_689657, baseEnd_689657] using wordTrace_append hprefix tailTrace_689657
  have hstable : (prefixWord ++ tailWord_689657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_689657).length < 2 ^ (prefixWord ++ tailWord_689657).sum := by decide
  have hdescent : baseEnd_689657 < baseStart_689657 := by decide
  rcases family_descends (prefixWord ++ tailWord_689657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_689678 : List Nat := [4, 1, 1, 2, 4, 2, 2, 1, 1, 5]
def baseStart_689678 : Nat := 118140960795 + 689678 * 2 ^ 59
def prefixEnd_689678 : Nat := 4983230072969 + 3 ^ 40 * 689678 * 2
def baseEnd_689678 : Nat := 118045436943885955117745

theorem tailTrace_689678 : CollatzResearch.WordTrace tailWord_689678 prefixEnd_689678 118045436943885955117745 := by
  unfold tailWord_689678
  simp only [CollatzResearch.WordTrace]
  refine ⟨3144327899427733558744711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 16769748796947912313305125 3144327899427733558744711)
  ·
    refine ⟨4716491849141600338117067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3144327899427733558744711 4716491849141600338117067)
    ·
      refine ⟨7074737773712400507175601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4716491849141600338117067 7074737773712400507175601)
      ·
        refine ⟨5306053330284300380381701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7074737773712400507175601 5306053330284300380381701)
        ·
          refine ⟨994884999428306321321569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5306053330284300380381701 994884999428306321321569)
          ·
            refine ⟨746163749571229740991177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 994884999428306321321569 746163749571229740991177)
            ·
              refine ⟨559622812178422305743383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 746163749571229740991177 559622812178422305743383)
              ·
                refine ⟨839434218267633458615075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 559622812178422305743383 839434218267633458615075)
                ·
                  refine ⟨1259151327401450187922613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 839434218267633458615075 1259151327401450187922613)
                  ·
                    refine ⟨118045436943885955117745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1259151327401450187922613 118045436943885955117745)
                    ·
                      rfl

theorem cell23_689678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 2, 2, 1, 1, 5].length) (baseStart_689678 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_689678 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_689678 prefixEnd_689678 := by exact prefixLift 689678
  have htrace : WordTrace (prefixWord ++ tailWord_689678) baseStart_689678 baseEnd_689678 := by
    simpa [prefixWord, tailWord_689678, baseEnd_689678] using wordTrace_append hprefix tailTrace_689678
  have hstable : (prefixWord ++ tailWord_689678).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_689678).length < 2 ^ (prefixWord ++ tailWord_689678).sum := by decide
  have hdescent : baseEnd_689678 < baseStart_689678 := by decide
  rcases family_descends (prefixWord ++ tailWord_689678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_689727 : List Nat := [1, 1, 2, 2, 3, 3, 1, 1, 2, 2, 5]
def baseStart_689727 : Nat := 118140960795 + 689727 * 2 ^ 59
def prefixEnd_689727 : Nat := 4983230072969 + 3 ^ 40 * 689727 * 2
def baseEnd_689727 : Nat := 354161471383728173640509

theorem tailTrace_689727 : CollatzResearch.WordTrace tailWord_689727 prefixEnd_689727 354161471383728173640509 := by
  unfold tailWord_689727
  simp only [CollatzResearch.WordTrace]
  refine ⟨25156410372244349838491435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16770940248162899892327623 25156410372244349838491435)
  ·
    refine ⟨37734615558366524757737153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25156410372244349838491435 37734615558366524757737153)
    ·
      refine ⟨28300961668774893568302865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37734615558366524757737153 28300961668774893568302865)
      ·
        refine ⟨21225721251581170176227149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28300961668774893568302865 21225721251581170176227149)
        ·
          refine ⟨7959645469342938816085181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21225721251581170176227149 7959645469342938816085181)
          ·
            refine ⟨2984867051003602056031943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7959645469342938816085181 2984867051003602056031943)
            ·
              refine ⟨4477300576505403084047915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2984867051003602056031943 4477300576505403084047915)
              ·
                refine ⟨6715950864758104626071873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4477300576505403084047915 6715950864758104626071873)
                ·
                  refine ⟨5036963148568578469553905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6715950864758104626071873 5036963148568578469553905)
                  ·
                    refine ⟨3777722361426433852165429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5036963148568578469553905 3777722361426433852165429)
                    ·
                      refine ⟨354161471383728173640509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3777722361426433852165429 354161471383728173640509)
                      ·
                        rfl

theorem cell23_689727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 1, 1, 2, 2, 5].length) (baseStart_689727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_689727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_689727 prefixEnd_689727 := by exact prefixLift 689727
  have htrace : WordTrace (prefixWord ++ tailWord_689727) baseStart_689727 baseEnd_689727 := by
    simpa [prefixWord, tailWord_689727, baseEnd_689727] using wordTrace_append hprefix tailTrace_689727
  have hstable : (prefixWord ++ tailWord_689727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_689727).length < 2 ^ (prefixWord ++ tailWord_689727).sum := by decide
  have hdescent : baseEnd_689727 < baseStart_689727 := by decide
  rcases family_descends (prefixWord ++ tailWord_689727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_689765 : List Nat := [1, 3, 1, 3, 3, 3, 2, 1, 2, 1, 3]
def baseStart_689765 : Nat := 118140960795 + 689765 * 2 ^ 59
def prefixEnd_689765 : Nat := 4983230072969 + 3 ^ 40 * 689765 * 2
def baseEnd_689765 : Nat := 354180983648599024965335

theorem tailTrace_689765 : CollatzResearch.WordTrace tailWord_689765 prefixEnd_689765 354180983648599024965335 := by
  unfold tailWord_689765
  simp only [CollatzResearch.WordTrace]
  refine ⟨25157796346106682328374749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16771864230737788218916499 25157796346106682328374749)
  ·
    refine ⟨9434173629790005873140531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25157796346106682328374749 9434173629790005873140531)
    ·
      refine ⟨14151260444685008809710797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9434173629790005873140531 14151260444685008809710797)
      ·
        refine ⟨5306722666756878303641549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14151260444685008809710797 5306722666756878303641549)
        ·
          refine ⟨1990021000033829363865581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5306722666756878303641549 1990021000033829363865581)
          ·
            refine ⟨746257875012686011449593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1990021000033829363865581 746257875012686011449593)
            ·
              refine ⟨559693406259514508587195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 746257875012686011449593 559693406259514508587195)
              ·
                refine ⟨839540109389271762880793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 559693406259514508587195 839540109389271762880793)
                ·
                  refine ⟨629655082041953822160595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 839540109389271762880793 629655082041953822160595)
                  ·
                    refine ⟨944482623062930733240893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 629655082041953822160595 944482623062930733240893)
                    ·
                      refine ⟨354180983648599024965335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 944482623062930733240893 354180983648599024965335)
                      ·
                        rfl

theorem cell23_689765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 3, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 3, 2, 1, 2, 1, 3].length) (baseStart_689765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_689765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_689765 prefixEnd_689765 := by exact prefixLift 689765
  have htrace : WordTrace (prefixWord ++ tailWord_689765) baseStart_689765 baseEnd_689765 := by
    simpa [prefixWord, tailWord_689765, baseEnd_689765] using wordTrace_append hprefix tailTrace_689765
  have hstable : (prefixWord ++ tailWord_689765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_689765).length < 2 ^ (prefixWord ++ tailWord_689765).sum := by decide
  have hdescent : baseEnd_689765 < baseStart_689765 := by decide
  rcases family_descends (prefixWord ++ tailWord_689765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_689777 : List Nat := [1, 2, 2, 2, 1, 1, 1, 6, 7]
def baseStart_689777 : Nat := 118140960795 + 689777 * 2 ^ 59
def prefixEnd_689777 : Nat := 4983230072969 + 3 ^ 40 * 689777 * 2
def baseEnd_689777 : Nat := 39354127268494775335031

theorem tailTrace_689777 : CollatzResearch.WordTrace tailWord_689777 prefixEnd_689777 39354127268494775335031 := by
  unfold tailWord_689777
  simp only [CollatzResearch.WordTrace]
  refine ⟨25158234022063208377811585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16772156014708805585207723 25158234022063208377811585)
  ·
    refine ⟨18868675516547406283358689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25158234022063208377811585 18868675516547406283358689)
    ·
      refine ⟨14151506637410554712519017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18868675516547406283358689 14151506637410554712519017)
      ·
        refine ⟨10613629978057916034389263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14151506637410554712519017 10613629978057916034389263)
        ·
          refine ⟨15920444967086874051583895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10613629978057916034389263 15920444967086874051583895)
          ·
            refine ⟨23880667450630311077375843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15920444967086874051583895 23880667450630311077375843)
            ·
              refine ⟨35821001175945466616063765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23880667450630311077375843 35821001175945466616063765)
              ·
                refine ⟨1679109430122443747627989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 35821001175945466616063765 1679109430122443747627989)
                ·
                  refine ⟨39354127268494775335031, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1679109430122443747627989 39354127268494775335031)
                  ·
                    rfl

theorem cell23_689777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 6, 7].length) (baseStart_689777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_689777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_689777 prefixEnd_689777 := by exact prefixLift 689777
  have htrace : WordTrace (prefixWord ++ tailWord_689777) baseStart_689777 baseEnd_689777 := by
    simpa [prefixWord, tailWord_689777, baseEnd_689777] using wordTrace_append hprefix tailTrace_689777
  have hstable : (prefixWord ++ tailWord_689777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_689777).length < 2 ^ (prefixWord ++ tailWord_689777).sum := by decide
  have hdescent : baseEnd_689777 < baseStart_689777 := by decide
  rcases family_descends (prefixWord ++ tailWord_689777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_689804 : List Nat := [2, 2, 1, 2, 1, 1, 4, 2, 2, 3, 3]
def baseStart_689804 : Nat := 118140960795 + 689804 * 2 ^ 59
def prefixEnd_689804 : Nat := 4983230072969 + 3 ^ 40 * 689804 * 2
def baseEnd_689804 : Nat := 354201009394124372377655

theorem tailTrace_689804 : CollatzResearch.WordTrace tailWord_689804 prefixEnd_689804 354201009394124372377655 := by
  unfold tailWord_689804
  simp only [CollatzResearch.WordTrace]
  refine ⟨12579609396482695994522233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16772812528643594659362977 12579609396482695994522233)
  ·
    refine ⟨9434707047362021995891675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12579609396482695994522233 9434707047362021995891675)
    ·
      refine ⟨14152060571043032993837513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9434707047362021995891675 14152060571043032993837513)
      ·
        refine ⟨10614045428282274745378135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14152060571043032993837513 10614045428282274745378135)
        ·
          refine ⟨15921068142423412118067203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10614045428282274745378135 15921068142423412118067203)
          ·
            refine ⟨23881602213635118177100805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15921068142423412118067203 23881602213635118177100805)
            ·
              refine ⟨4477800415056584658206401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23881602213635118177100805 4477800415056584658206401)
              ·
                refine ⟨3358350311292438493654801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4477800415056584658206401 3358350311292438493654801)
                ·
                  refine ⟨2518762733469328870241101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3358350311292438493654801 2518762733469328870241101)
                  ·
                    refine ⟨944536025050998326340413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2518762733469328870241101 944536025050998326340413)
                    ·
                      refine ⟨354201009394124372377655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 944536025050998326340413 354201009394124372377655)
                      ·
                        rfl

theorem cell23_689804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 4, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 4, 2, 2, 3, 3].length) (baseStart_689804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_689804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_689804 prefixEnd_689804 := by exact prefixLift 689804
  have htrace : WordTrace (prefixWord ++ tailWord_689804) baseStart_689804 baseEnd_689804 := by
    simpa [prefixWord, tailWord_689804, baseEnd_689804] using wordTrace_append hprefix tailTrace_689804
  have hstable : (prefixWord ++ tailWord_689804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_689804).length < 2 ^ (prefixWord ++ tailWord_689804).sum := by decide
  have hdescent : baseEnd_689804 < baseStart_689804 := by decide
  rcases family_descends (prefixWord ++ tailWord_689804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_689817 : List Nat := [1, 2, 1, 2, 1, 2, 2, 3, 1, 1, 7]
def baseStart_689817 : Nat := 118140960795 + 689817 * 2 ^ 59
def prefixEnd_689817 : Nat := 4983230072969 + 3 ^ 40 * 689817 * 2
def baseEnd_689817 : Nat := 354207684642632821515095

theorem tailTrace_689817 : CollatzResearch.WordTrace tailWord_689817 prefixEnd_689817 354207684642632821515095 := by
  unfold tailWord_689817
  simp only [CollatzResearch.WordTrace]
  refine ⟨25159692941918295209267705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16773128627945530139511803 25159692941918295209267705)
  ·
    refine ⟨18869769706438721406950779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25159692941918295209267705 18869769706438721406950779)
    ·
      refine ⟨28304654559658082110426169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18869769706438721406950779 28304654559658082110426169)
      ·
        refine ⟨21228490919743561582819627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28304654559658082110426169 21228490919743561582819627)
        ·
          refine ⟨31842736379615342374229441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21228490919743561582819627 31842736379615342374229441)
          ·
            refine ⟨23882052284711506780672081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31842736379615342374229441 23882052284711506780672081)
            ·
              refine ⟨17911539213533630085504061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23882052284711506780672081 17911539213533630085504061)
              ·
                refine ⟨6716827205075111282064023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17911539213533630085504061 6716827205075111282064023)
                ·
                  refine ⟨10075240807612666923096035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6716827205075111282064023 10075240807612666923096035)
                  ·
                    refine ⟨15112861211419000384644053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10075240807612666923096035 15112861211419000384644053)
                    ·
                      refine ⟨354207684642632821515095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 15112861211419000384644053 354207684642632821515095)
                      ·
                        rfl

theorem cell23_689817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 3, 1, 1, 7].length) (baseStart_689817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_689817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_689817 prefixEnd_689817 := by exact prefixLift 689817
  have htrace : WordTrace (prefixWord ++ tailWord_689817) baseStart_689817 baseEnd_689817 := by
    simpa [prefixWord, tailWord_689817, baseEnd_689817] using wordTrace_append hprefix tailTrace_689817
  have hstable : (prefixWord ++ tailWord_689817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_689817).length < 2 ^ (prefixWord ++ tailWord_689817).sum := by decide
  have hdescent : baseEnd_689817 < baseStart_689817 := by decide
  rcases family_descends (prefixWord ++ tailWord_689817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_689905 : List Nat := [1, 2, 2, 2, 2, 5, 1, 3, 1, 4]
def baseStart_689905 : Nat := 118140960795 + 689905 * 2 ^ 59
def prefixEnd_689905 : Nat := 4983230072969 + 3 ^ 40 * 689905 * 2
def baseEnd_689905 : Nat := 118084290313409492404897

theorem tailTrace_689905 : CollatzResearch.WordTrace tailWord_689905 prefixEnd_689905 118084290313409492404897 := by
  unfold tailWord_689905
  simp only [CollatzResearch.WordTrace]
  refine ⟨25162902565599486238471169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16775268377066324158980779 25162902565599486238471169)
  ·
    refine ⟨18872176924199614678853377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25162902565599486238471169 18872176924199614678853377)
    ·
      refine ⟨14154132693149711009140033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18872176924199614678853377 14154132693149711009140033)
      ·
        refine ⟨10615599519862283256855025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14154132693149711009140033 10615599519862283256855025)
        ·
          refine ⟨7961699639896712442641269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10615599519862283256855025 7961699639896712442641269)
          ·
            refine ⟨746409341240316791497619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 7961699639896712442641269 746409341240316791497619)
            ·
              refine ⟨1119614011860475187246429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 746409341240316791497619 1119614011860475187246429)
              ·
                refine ⟨419855254447678195217411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1119614011860475187246429 419855254447678195217411)
                ·
                  refine ⟨629782881671517292826117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 419855254447678195217411 629782881671517292826117)
                  ·
                    refine ⟨118084290313409492404897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 629782881671517292826117 118084290313409492404897)
                    ·
                      rfl

theorem cell23_689905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 5, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 5, 1, 3, 1, 4].length) (baseStart_689905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_689905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_689905 prefixEnd_689905 := by exact prefixLift 689905
  have htrace : WordTrace (prefixWord ++ tailWord_689905) baseStart_689905 baseEnd_689905 := by
    simpa [prefixWord, tailWord_689905, baseEnd_689905] using wordTrace_append hprefix tailTrace_689905
  have hstable : (prefixWord ++ tailWord_689905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_689905).length < 2 ^ (prefixWord ++ tailWord_689905).sum := by decide
  have hdescent : baseEnd_689905 < baseStart_689905 := by decide
  rcases family_descends (prefixWord ++ tailWord_689905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_689911 : List Nat := [1, 1, 3, 1, 1, 1, 4, 2, 5, 1, 3]
def baseStart_689911 : Nat := 118140960795 + 689911 * 2 ^ 59
def prefixEnd_689911 : Nat := 4983230072969 + 3 ^ 40 * 689911 * 2
def baseEnd_689911 : Nat := 354255951824155453739663

theorem tailTrace_689911 : CollatzResearch.WordTrace tailWord_689911 prefixEnd_689911 354255951824155453739663 := by
  unfold tailWord_689911
  simp only [CollatzResearch.WordTrace]
  refine ⟨25163121403577749263189587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16775414269051832842126391 25163121403577749263189587)
  ·
    refine ⟨37744682105366623894784381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25163121403577749263189587 37744682105366623894784381)
    ·
      refine ⟨14154255789512483960544143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37744682105366623894784381 14154255789512483960544143)
      ·
        refine ⟨21231383684268725940816215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14154255789512483960544143 21231383684268725940816215)
        ·
          refine ⟨31847075526403088911224323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21231383684268725940816215 31847075526403088911224323)
          ·
            refine ⟨47770613289604633366836485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31847075526403088911224323 47770613289604633366836485)
            ·
              refine ⟨8956989991800868756281841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 47770613289604633366836485 8956989991800868756281841)
              ·
                refine ⟨6717742493850651567211381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8956989991800868756281841 6717742493850651567211381)
                ·
                  refine ⟨629788358798498584426067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 6717742493850651567211381 629788358798498584426067)
                  ·
                    refine ⟨944682538197747876639101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 629788358798498584426067 944682538197747876639101)
                    ·
                      refine ⟨354255951824155453739663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 944682538197747876639101 354255951824155453739663)
                      ·
                        rfl

theorem cell23_689911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 4, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 4, 2, 5, 1, 3].length) (baseStart_689911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_689911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_689911 prefixEnd_689911 := by exact prefixLift 689911
  have htrace : WordTrace (prefixWord ++ tailWord_689911) baseStart_689911 baseEnd_689911 := by
    simpa [prefixWord, tailWord_689911, baseEnd_689911] using wordTrace_append hprefix tailTrace_689911
  have hstable : (prefixWord ++ tailWord_689911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_689911).length < 2 ^ (prefixWord ++ tailWord_689911).sum := by decide
  have hdescent : baseEnd_689911 < baseStart_689911 := by decide
  rcases family_descends (prefixWord ++ tailWord_689911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_689914 : List Nat := [3, 1, 1, 1, 1, 3, 1, 2, 5, 5]
def baseStart_689914 : Nat := 118140960795 + 689914 * 2 ^ 59
def prefixEnd_689914 : Nat := 4983230072969 + 3 ^ 40 * 689914 * 2
def baseEnd_689914 : Nat := 118085830755372980667383

theorem tailTrace_689914 : CollatzResearch.WordTrace tailWord_689914 prefixEnd_689914 118085830755372980667383 := by
  unfold tailWord_689914
  simp only [CollatzResearch.WordTrace]
  refine ⟨6290807705641720193887199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16775487215044587183699197 6290807705641720193887199)
  ·
    refine ⟨9436211558462580290830799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6290807705641720193887199 9436211558462580290830799)
    ·
      refine ⟨14154317337693870436246199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9436211558462580290830799 14154317337693870436246199)
      ·
        refine ⟨21231476006540805654369299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14154317337693870436246199 21231476006540805654369299)
        ·
          refine ⟨31847214009811208481553949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21231476006540805654369299 31847214009811208481553949)
          ·
            refine ⟨11942705253679203180582731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31847214009811208481553949 11942705253679203180582731)
            ·
              refine ⟨17914057880518804770874097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11942705253679203180582731 17914057880518804770874097)
              ·
                refine ⟨13435543410389103578155573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17914057880518804770874097 13435543410389103578155573)
                ·
                  refine ⟨1259582194723978460452085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 13435543410389103578155573 1259582194723978460452085)
                  ·
                    refine ⟨118085830755372980667383, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1259582194723978460452085 118085830755372980667383)
                    ·
                      rfl

theorem cell23_689914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 2, 5, 5].length) (baseStart_689914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_689914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_689914 prefixEnd_689914 := by exact prefixLift 689914
  have htrace : WordTrace (prefixWord ++ tailWord_689914) baseStart_689914 baseEnd_689914 := by
    simpa [prefixWord, tailWord_689914, baseEnd_689914] using wordTrace_append hprefix tailTrace_689914
  have hstable : (prefixWord ++ tailWord_689914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_689914).length < 2 ^ (prefixWord ++ tailWord_689914).sum := by decide
  have hdescent : baseEnd_689914 < baseStart_689914 := by decide
  rcases family_descends (prefixWord ++ tailWord_689914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_689922 : List Nat := [3, 4, 1, 1, 1, 1, 5, 2, 1, 4]
def baseStart_689922 : Nat := 118140960795 + 689922 * 2 ^ 59
def prefixEnd_689922 : Nat := 4983230072969 + 3 ^ 40 * 689922 * 2
def baseEnd_689922 : Nat := 118087200037118303567371

theorem tailTrace_689922 : CollatzResearch.WordTrace tailWord_689922 prefixEnd_689922 118087200037118303567371 := by
  unfold tailWord_689922
  simp only [CollatzResearch.WordTrace]
  refine ⟨6290880651634474535460005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16775681737691932094560013 6290880651634474535460005)
  ·
    refine ⟨1179540122181463975398751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6290880651634474535460005 1179540122181463975398751)
    ·
      refine ⟨1769310183272195963098127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1179540122181463975398751 1769310183272195963098127)
      ·
        refine ⟨2653965274908293944647191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1769310183272195963098127 2653965274908293944647191)
        ·
          refine ⟨3980947912362440916970787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2653965274908293944647191 3980947912362440916970787)
          ·
            refine ⟨5971421868543661375456181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3980947912362440916970787 5971421868543661375456181)
            ·
              refine ⟨559820800175968253949017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 5971421868543661375456181 559820800175968253949017)
              ·
                refine ⟨419865600131976190461763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 559820800175968253949017 419865600131976190461763)
                ·
                  refine ⟨629798400197964285692645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 419865600131976190461763 629798400197964285692645)
                  ·
                    refine ⟨118087200037118303567371, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 629798400197964285692645 118087200037118303567371)
                    ·
                      rfl

theorem cell23_689922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 5, 2, 1, 4].length) (baseStart_689922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_689922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_689922 prefixEnd_689922 := by exact prefixLift 689922
  have htrace : WordTrace (prefixWord ++ tailWord_689922) baseStart_689922 baseEnd_689922 := by
    simpa [prefixWord, tailWord_689922, baseEnd_689922] using wordTrace_append hprefix tailTrace_689922
  have hstable : (prefixWord ++ tailWord_689922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_689922).length < 2 ^ (prefixWord ++ tailWord_689922).sum := by decide
  have hdescent : baseEnd_689922 < baseStart_689922 := by decide
  rcases family_descends (prefixWord ++ tailWord_689922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_689951 : List Nat := [1, 1, 2, 4, 2, 1, 3, 1, 3, 1, 4]
def baseStart_689951 : Nat := 118140960795 + 689951 * 2 ^ 59
def prefixEnd_689951 : Nat := 4983230072969 + 3 ^ 40 * 689951 * 2
def baseEnd_689951 : Nat := 354276491050335297239479

theorem tailTrace_689951 : CollatzResearch.WordTrace tailWord_689951 prefixEnd_689951 354276491050335297239479 := by
  unfold tailWord_689951
  simp only [CollatzResearch.WordTrace]
  refine ⟨25164580323432836094645707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16776386882288557396430471 25164580323432836094645707)
  ·
    refine ⟨37746870485149254141968561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25164580323432836094645707 37746870485149254141968561)
    ·
      refine ⟨28310152863861940606476421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37746870485149254141968561 28310152863861940606476421)
      ·
        refine ⟨5308153661974113863714329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 28310152863861940606476421 5308153661974113863714329)
        ·
          refine ⟨3981115246480585397785747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5308153661974113863714329 3981115246480585397785747)
          ·
            refine ⟨5971672869720878096678621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3981115246480585397785747 5971672869720878096678621)
            ·
              refine ⟨2239377326145329286254483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5971672869720878096678621 2239377326145329286254483)
              ·
                refine ⟨3359065989217993929381725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2239377326145329286254483 3359065989217993929381725)
                ·
                  refine ⟨1259649745956747723518147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3359065989217993929381725 1259649745956747723518147)
                  ·
                    refine ⟨1889474618935121585277221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1259649745956747723518147 1889474618935121585277221)
                    ·
                      refine ⟨354276491050335297239479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1889474618935121585277221 354276491050335297239479)
                      ·
                        rfl

theorem cell23_689951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 3, 1, 3, 1, 4].length) (baseStart_689951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_689951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_689951 prefixEnd_689951 := by exact prefixLift 689951
  have htrace : WordTrace (prefixWord ++ tailWord_689951) baseStart_689951 baseEnd_689951 := by
    simpa [prefixWord, tailWord_689951, baseEnd_689951] using wordTrace_append hprefix tailTrace_689951
  have hstable : (prefixWord ++ tailWord_689951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_689951).length < 2 ^ (prefixWord ++ tailWord_689951).sum := by decide
  have hdescent : baseEnd_689951 < baseStart_689951 := by decide
  rcases family_descends (prefixWord ++ tailWord_689951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_689978 : List Nat := [3, 1, 1, 1, 5, 1, 1, 4, 2, 4]
def baseStart_689978 : Nat := 118140960795 + 689978 * 2 ^ 59
def prefixEnd_689978 : Nat := 4983230072969 + 3 ^ 40 * 689978 * 2
def baseEnd_689978 : Nat := 118096785009335563867285

theorem tailTrace_689978 : CollatzResearch.WordTrace tailWord_689978 prefixEnd_689978 118096785009335563867285 := by
  unfold tailWord_689978
  simp only [CollatzResearch.WordTrace]
  refine ⟨6291391273583754926469647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16777043396223346470585725 6291391273583754926469647)
  ·
    refine ⟨9437086910375632389704471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6291391273583754926469647 9437086910375632389704471)
    ·
      refine ⟨14155630365563448584556707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9437086910375632389704471 14155630365563448584556707)
      ·
        refine ⟨21233445548345172876835061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14155630365563448584556707 21233445548345172876835061)
        ·
          refine ⟨1990635520157359957203287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 21233445548345172876835061 1990635520157359957203287)
          ·
            refine ⟨2985953280236039935804931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1990635520157359957203287 2985953280236039935804931)
            ·
              refine ⟨4478929920354059903707397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2985953280236039935804931 4478929920354059903707397)
              ·
                refine ⟨839799360066386231945137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4478929920354059903707397 839799360066386231945137)
                ·
                  refine ⟨629849520049789673958853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 839799360066386231945137 629849520049789673958853)
                  ·
                    refine ⟨118096785009335563867285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 629849520049789673958853 118096785009335563867285)
                    ·
                      rfl

theorem cell23_689978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 1, 4, 2, 4].length) (baseStart_689978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_689978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_689978 prefixEnd_689978 := by exact prefixLift 689978
  have htrace : WordTrace (prefixWord ++ tailWord_689978) baseStart_689978 baseEnd_689978 := by
    simpa [prefixWord, tailWord_689978, baseEnd_689978] using wordTrace_append hprefix tailTrace_689978
  have hstable : (prefixWord ++ tailWord_689978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_689978).length < 2 ^ (prefixWord ++ tailWord_689978).sum := by decide
  have hdescent : baseEnd_689978 < baseStart_689978 := by decide
  rcases family_descends (prefixWord ++ tailWord_689978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_690019 : List Nat := [1, 1, 1, 5, 4, 1, 2, 3, 1, 2, 2]
def baseStart_690019 : Nat := 118140960795 + 690019 * 2 ^ 59
def prefixEnd_690019 : Nat := 4983230072969 + 3 ^ 40 * 690019 * 2
def baseEnd_690019 : Nat := 354311407734841031189167

theorem tailTrace_690019 : CollatzResearch.WordTrace tailWord_690019 prefixEnd_690019 354311407734841031189167 := by
  unfold tailWord_690019
  simp only [CollatzResearch.WordTrace]
  refine ⟨25167060487186483708121111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16778040324790989138747407 25167060487186483708121111)
  ·
    refine ⟨37750590730779725562181667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25167060487186483708121111 37750590730779725562181667)
    ·
      refine ⟨56625886096169588343272501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37750590730779725562181667 56625886096169588343272501)
      ·
        refine ⟨5308676821515898907181797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 56625886096169588343272501 5308676821515898907181797)
        ·
          refine ⟨995376904034231045096587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5308676821515898907181797 995376904034231045096587)
          ·
            refine ⟨1493065356051346567644881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 995376904034231045096587 1493065356051346567644881)
            ·
              refine ⟨1119799017038509925733661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1493065356051346567644881 1119799017038509925733661)
              ·
                refine ⟨419924631389441222150123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1119799017038509925733661 419924631389441222150123)
                ·
                  refine ⟨629886947084161833225185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 419924631389441222150123 629886947084161833225185)
                  ·
                    refine ⟨472415210313121374918889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 629886947084161833225185 472415210313121374918889)
                    ·
                      refine ⟨354311407734841031189167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 472415210313121374918889 354311407734841031189167)
                      ·
                        rfl

theorem cell23_690019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 1, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 1, 2, 3, 1, 2, 2].length) (baseStart_690019 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_690019 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_690019 prefixEnd_690019 := by exact prefixLift 690019
  have htrace : WordTrace (prefixWord ++ tailWord_690019) baseStart_690019 baseEnd_690019 := by
    simpa [prefixWord, tailWord_690019, baseEnd_690019] using wordTrace_append hprefix tailTrace_690019
  have hstable : (prefixWord ++ tailWord_690019).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_690019).length < 2 ^ (prefixWord ++ tailWord_690019).sum := by decide
  have hdescent : baseEnd_690019 < baseStart_690019 := by decide
  rcases family_descends (prefixWord ++ tailWord_690019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_690051 : List Nat := [1, 1, 1, 3, 4, 2, 2, 1, 2, 6]
def baseStart_690051 : Nat := 118140960795 + 690051 * 2 ^ 59
def prefixEnd_690051 : Nat := 4983230072969 + 3 ^ 40 * 690051 * 2
def baseEnd_690051 : Nat := 118109279705261635329673

theorem tailTrace_690051 : CollatzResearch.WordTrace tailWord_690051 prefixEnd_690051 118109279705261635329673 := by
  unfold tailWord_690051
  simp only [CollatzResearch.WordTrace]
  refine ⟨25168227623070553173286007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16778818415380368782190671 25168227623070553173286007)
  ·
    refine ⟨37752341434605829759929011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25168227623070553173286007 37752341434605829759929011)
    ·
      refine ⟨56628512151908744639893517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37752341434605829759929011 56628512151908744639893517)
      ·
        refine ⟨21235692056965779239960069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 56628512151908744639893517 21235692056965779239960069)
        ·
          refine ⟨3981692260681083607492513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21235692056965779239960069 3981692260681083607492513)
          ·
            refine ⟨2986269195510812705619385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3981692260681083607492513 2986269195510812705619385)
            ·
              refine ⟨2239701896633109529214539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2986269195510812705619385 2239701896633109529214539)
              ·
                refine ⟨3359552844949664293821809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2239701896633109529214539 3359552844949664293821809)
                ·
                  refine ⟨2519664633712248220366357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3359552844949664293821809 2519664633712248220366357)
                  ·
                    refine ⟨118109279705261635329673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2519664633712248220366357 118109279705261635329673)
                    ·
                      rfl

theorem cell23_690051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 2, 1, 2, 6].length) (baseStart_690051 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_690051 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_690051 prefixEnd_690051 := by exact prefixLift 690051
  have htrace : WordTrace (prefixWord ++ tailWord_690051) baseStart_690051 baseEnd_690051 := by
    simpa [prefixWord, tailWord_690051, baseEnd_690051] using wordTrace_append hprefix tailTrace_690051
  have hstable : (prefixWord ++ tailWord_690051).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_690051).length < 2 ^ (prefixWord ++ tailWord_690051).sum := by decide
  have hdescent : baseEnd_690051 < baseStart_690051 := by decide
  rcases family_descends (prefixWord ++ tailWord_690051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_690070 : List Nat := [5, 3, 1, 1, 2, 2, 1, 3, 1, 2, 2]
def baseStart_690070 : Nat := 118140960795 + 690070 * 2 ^ 59
def prefixEnd_690070 : Nat := 4983230072969 + 3 ^ 40 * 690070 * 2
def baseEnd_690070 : Nat := 354337595248220331651433

theorem tailTrace_690070 : CollatzResearch.WordTrace tailWord_690070 prefixEnd_690070 354337595248220331651433 := by
  unfold tailWord_690070
  simp only [CollatzResearch.WordTrace]
  refine ⟨1573057538125107463639229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 16779280406667812945485109 1573057538125107463639229)
  ·
    refine ⟨589896576796915298864711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1573057538125107463639229 589896576796915298864711)
    ·
      refine ⟨884844865195372948297067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 589896576796915298864711 884844865195372948297067)
      ·
        refine ⟨1327267297793059422445601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 884844865195372948297067 1327267297793059422445601)
        ·
          refine ⟨995450473344794566834201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1327267297793059422445601 995450473344794566834201)
          ·
            refine ⟨746587855008595925125651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 995450473344794566834201 746587855008595925125651)
            ·
              refine ⟨1119881782512893887688477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 746587855008595925125651 1119881782512893887688477)
              ·
                refine ⟨419955668442335207883179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1119881782512893887688477 419955668442335207883179)
                ·
                  refine ⟨629933502663502811824769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 419955668442335207883179 629933502663502811824769)
                  ·
                    refine ⟨472450126997627108868577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 629933502663502811824769 472450126997627108868577)
                    ·
                      refine ⟨354337595248220331651433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 472450126997627108868577 354337595248220331651433)
                      ·
                        rfl

theorem cell23_690070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 2, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 2, 1, 3, 1, 2, 2].length) (baseStart_690070 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_690070 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_690070 prefixEnd_690070 := by exact prefixLift 690070
  have htrace : WordTrace (prefixWord ++ tailWord_690070) baseStart_690070 baseEnd_690070 := by
    simpa [prefixWord, tailWord_690070, baseEnd_690070] using wordTrace_append hprefix tailTrace_690070
  have hstable : (prefixWord ++ tailWord_690070).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_690070).length < 2 ^ (prefixWord ++ tailWord_690070).sum := by decide
  have hdescent : baseEnd_690070 < baseStart_690070 := by decide
  rcases family_descends (prefixWord ++ tailWord_690070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_690098 : List Nat := [3, 2, 1, 1, 1, 1, 1, 8, 5]
def baseStart_690098 : Nat := 118140960795 + 690098 * 2 ^ 59
def prefixEnd_690098 : Nat := 4983230072969 + 3 ^ 40 * 690098 * 2
def baseEnd_690098 : Nat := 39372441411838469122367

theorem tailTrace_690098 : CollatzResearch.WordTrace tailWord_690098 prefixEnd_690098 39372441411838469122367 := by
  unfold tailWord_690098
  simp only [CollatzResearch.WordTrace]
  refine ⟨6292485463475070050061737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16779961235933520133497965 6292485463475070050061737)
  ·
    refine ⟨4719364097606302537546303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6292485463475070050061737 4719364097606302537546303)
    ·
      refine ⟨7079046146409453806319455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4719364097606302537546303 7079046146409453806319455)
      ·
        refine ⟨10618569219614180709479183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7079046146409453806319455 10618569219614180709479183)
        ·
          refine ⟨15927853829421271064218775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10618569219614180709479183 15927853829421271064218775)
          ·
            refine ⟨23891780744131906596328163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15927853829421271064218775 23891780744131906596328163)
            ·
              refine ⟨35837671116197859894492245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23891780744131906596328163 35837671116197859894492245)
              ·
                refine ⟨419972708392943670638581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 35837671116197859894492245 419972708392943670638581)
                ·
                  refine ⟨39372441411838469122367, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 419972708392943670638581 39372441411838469122367)
                  ·
                    rfl

theorem cell23_690098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 8, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 8, 5].length) (baseStart_690098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_690098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_690098 prefixEnd_690098 := by exact prefixLift 690098
  have htrace : WordTrace (prefixWord ++ tailWord_690098) baseStart_690098 baseEnd_690098 := by
    simpa [prefixWord, tailWord_690098, baseEnd_690098] using wordTrace_append hprefix tailTrace_690098
  have hstable : (prefixWord ++ tailWord_690098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_690098).length < 2 ^ (prefixWord ++ tailWord_690098).sum := by decide
  have hdescent : baseEnd_690098 < baseStart_690098 := by decide
  rcases family_descends (prefixWord ++ tailWord_690098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_690109 : List Nat := [1, 4, 1, 2, 3, 1, 4, 1, 2, 2, 2]
def baseStart_690109 : Nat := 118140960795 + 690109 * 2 ^ 59
def prefixEnd_690109 : Nat := 4983230072969 + 3 ^ 40 * 690109 * 2
def baseEnd_690109 : Nat := 354357620993745679063753

theorem tailTrace_690109 : CollatzResearch.WordTrace tailWord_690109 prefixEnd_690109 354357620993745679063753 := by
  unfold tailWord_690109
  simp only [CollatzResearch.WordTrace]
  refine ⟨25170343056860429078897381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16780228704573619385931587 25170343056860429078897381)
  ·
    refine ⟨4719439323161330452293259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 25170343056860429078897381 4719439323161330452293259)
    ·
      refine ⟨7079158984741995678439889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4719439323161330452293259 7079158984741995678439889)
      ·
        refine ⟨5309369238556496758829917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7079158984741995678439889 5309369238556496758829917)
        ·
          refine ⟨1991013464458686284561219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5309369238556496758829917 1991013464458686284561219)
          ·
            refine ⟨2986520196688029426841829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1991013464458686284561219 2986520196688029426841829)
            ·
              refine ⟨559972536879005517532843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2986520196688029426841829 559972536879005517532843)
              ·
                refine ⟨839958805318508276299265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 559972536879005517532843 839958805318508276299265)
                ·
                  refine ⟨629969103988881207224449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 839958805318508276299265 629969103988881207224449)
                  ·
                    refine ⟨472476827991660905418337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 629969103988881207224449 472476827991660905418337)
                    ·
                      refine ⟨354357620993745679063753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 472476827991660905418337 354357620993745679063753)
                      ·
                        rfl

theorem cell23_690109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 4, 1, 2, 2, 2].length) (baseStart_690109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_690109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_690109 prefixEnd_690109 := by exact prefixLift 690109
  have htrace : WordTrace (prefixWord ++ tailWord_690109) baseStart_690109 baseEnd_690109 := by
    simpa [prefixWord, tailWord_690109, baseEnd_690109] using wordTrace_append hprefix tailTrace_690109
  have hstable : (prefixWord ++ tailWord_690109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_690109).length < 2 ^ (prefixWord ++ tailWord_690109).sum := by decide
  have hdescent : baseEnd_690109 < baseStart_690109 := by decide
  rcases family_descends (prefixWord ++ tailWord_690109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_690111 : List Nat := [1, 1, 2, 2, 2, 1, 3, 2, 4, 5]
def baseStart_690111 : Nat := 118140960795 + 690111 * 2 ^ 59
def prefixEnd_690111 : Nat := 4983230072969 + 3 ^ 40 * 690111 * 2
def baseEnd_690111 : Nat := 118119549318351557079581

theorem tailTrace_690111 : CollatzResearch.WordTrace tailWord_690111 prefixEnd_690111 118119549318351557079581 := by
  unfold tailWord_690111
  simp only [CollatzResearch.WordTrace]
  refine ⟨25170416002853183420470187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16780277335235455613646791 25170416002853183420470187)
  ·
    refine ⟨37755624004279775130705281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25170416002853183420470187 37755624004279775130705281)
    ·
      refine ⟨28316718003209831348028961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37755624004279775130705281 28316718003209831348028961)
      ·
        refine ⟨21237538502407373511021721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28316718003209831348028961 21237538502407373511021721)
        ·
          refine ⟨15928153876805530133266291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21237538502407373511021721 15928153876805530133266291)
          ·
            refine ⟨23892230815208295199899437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15928153876805530133266291 23892230815208295199899437)
            ·
              refine ⟨8959586555703110699962289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23892230815208295199899437 8959586555703110699962289)
              ·
                refine ⟨6719689916777333024971717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8959586555703110699962289 6719689916777333024971717)
                ·
                  refine ⟨1259941859395749942182197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6719689916777333024971717 1259941859395749942182197)
                  ·
                    refine ⟨118119549318351557079581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1259941859395749942182197 118119549318351557079581)
                    ·
                      rfl

theorem cell23_690111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 3, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 3, 2, 4, 5].length) (baseStart_690111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_690111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_690111 prefixEnd_690111 := by exact prefixLift 690111
  have htrace : WordTrace (prefixWord ++ tailWord_690111) baseStart_690111 baseEnd_690111 := by
    simpa [prefixWord, tailWord_690111, baseEnd_690111] using wordTrace_append hprefix tailTrace_690111
  have hstable : (prefixWord ++ tailWord_690111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_690111).length < 2 ^ (prefixWord ++ tailWord_690111).sum := by decide
  have hdescent : baseEnd_690111 < baseStart_690111 := by decide
  rcases family_descends (prefixWord ++ tailWord_690111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_690148 : List Nat := [2, 3, 1, 1, 1, 1, 3, 4, 2, 1, 4]
def baseStart_690148 : Nat := 118140960795 + 690148 * 2 ^ 59
def prefixEnd_690148 : Nat := 4983230072969 + 3 ^ 40 * 690148 * 2
def baseEnd_690148 : Nat := 354377646739271026476073

theorem tailTrace_690148 : CollatzResearch.WordTrace tailWord_690148 prefixEnd_690148 354377646739271026476073 := by
  unfold tailWord_690148
  simp only [CollatzResearch.WordTrace]
  refine ⟨12585882751859569369783549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16781177002479425826378065 12585882751859569369783549)
  ·
    refine ⟨4719706031947338513668831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12585882751859569369783549 4719706031947338513668831)
    ·
      refine ⟨7079559047921007770503247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4719706031947338513668831 7079559047921007770503247)
      ·
        refine ⟨10619338571881511655754871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7079559047921007770503247 10619338571881511655754871)
        ·
          refine ⟨15929007857822267483632307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10619338571881511655754871 15929007857822267483632307)
          ·
            refine ⟨23893511786733401225448461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15929007857822267483632307 23893511786733401225448461)
            ·
              refine ⟨8960066920025025459543173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23893511786733401225448461 8960066920025025459543173)
              ·
                refine ⟨1680012547504692273664345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8960066920025025459543173 1680012547504692273664345)
                ·
                  refine ⟨1260009410628519205248259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1680012547504692273664345 1260009410628519205248259)
                  ·
                    refine ⟨1890014115942778807872389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1260009410628519205248259 1890014115942778807872389)
                    ·
                      refine ⟨354377646739271026476073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1890014115942778807872389 354377646739271026476073)
                      ·
                        rfl

theorem cell23_690148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 3, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 3, 4, 2, 1, 4].length) (baseStart_690148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_690148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_690148 prefixEnd_690148 := by exact prefixLift 690148
  have htrace : WordTrace (prefixWord ++ tailWord_690148) baseStart_690148 baseEnd_690148 := by
    simpa [prefixWord, tailWord_690148, baseEnd_690148] using wordTrace_append hprefix tailTrace_690148
  have hstable : (prefixWord ++ tailWord_690148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_690148).length < 2 ^ (prefixWord ++ tailWord_690148).sum := by decide
  have hdescent : baseEnd_690148 < baseStart_690148 := by decide
  rcases family_descends (prefixWord ++ tailWord_690148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_690168 : List Nat := [2, 1, 2, 1, 1, 3, 2, 2, 4, 2, 3]
def baseStart_690168 : Nat := 118140960795 + 690168 * 2 ^ 59
def prefixEnd_690168 : Nat := 4983230072969 + 3 ^ 40 * 690168 * 2
def baseEnd_690168 : Nat := 354387916352360948225981

theorem tailTrace_690168 : CollatzResearch.WordTrace tailWord_690168 prefixEnd_690168 354387916352360948225981 := by
  unfold tailWord_690168
  simp only [CollatzResearch.WordTrace]
  refine ⟨12586247481823341077647579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16781663309097788103530105 12586247481823341077647579)
  ·
    refine ⟨18879371222735011616471369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12586247481823341077647579 18879371222735011616471369)
    ·
      refine ⟨14159528417051258712353527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18879371222735011616471369 14159528417051258712353527)
      ·
        refine ⟨21239292625576888068530291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14159528417051258712353527 21239292625576888068530291)
        ·
          refine ⟨31858938938365332102795437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21239292625576888068530291 31858938938365332102795437)
          ·
            refine ⟨11947102101886999538548289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31858938938365332102795437 11947102101886999538548289)
            ·
              refine ⟨8960326576415249653911217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11947102101886999538548289 8960326576415249653911217)
              ·
                refine ⟨6720244932311437240433413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8960326576415249653911217 6720244932311437240433413)
                ·
                  refine ⟨1260045924808394482581265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6720244932311437240433413 1260045924808394482581265)
                  ·
                    refine ⟨945034443606295861935949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1260045924808394482581265 945034443606295861935949)
                    ·
                      refine ⟨354387916352360948225981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 945034443606295861935949 354387916352360948225981)
                      ·
                        rfl

theorem cell23_690168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 2, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 2, 2, 4, 2, 3].length) (baseStart_690168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_690168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_690168 prefixEnd_690168 := by exact prefixLift 690168
  have htrace : WordTrace (prefixWord ++ tailWord_690168) baseStart_690168 baseEnd_690168 := by
    simpa [prefixWord, tailWord_690168, baseEnd_690168] using wordTrace_append hprefix tailTrace_690168
  have hstable : (prefixWord ++ tailWord_690168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_690168).length < 2 ^ (prefixWord ++ tailWord_690168).sum := by decide
  have hdescent : baseEnd_690168 < baseStart_690168 := by decide
  rcases family_descends (prefixWord ++ tailWord_690168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_690205 : List Nat := [1, 4, 2, 2, 2, 1, 3, 2, 6]
def baseStart_690205 : Nat := 118140960795 + 690205 * 2 ^ 59
def prefixEnd_690205 : Nat := 4983230072969 + 3 ^ 40 * 690205 * 2
def baseEnd_690205 : Nat := 39378546126286367051479

theorem tailTrace_690205 : CollatzResearch.WordTrace tailWord_690205 prefixEnd_690205 39378546126286367051479 := by
  unfold tailWord_690205
  simp only [CollatzResearch.WordTrace]
  refine ⟨25173844464512637474392069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16782562976341758316261379 25173844464512637474392069)
  ·
    refine ⟨4720095837096119526448513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 25173844464512637474392069 4720095837096119526448513)
    ·
      refine ⟨3540071877822089644836385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4720095837096119526448513 3540071877822089644836385)
      ·
        refine ⟨2655053908366567233627289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3540071877822089644836385 2655053908366567233627289)
        ·
          refine ⟨1991290431274925425220467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2655053908366567233627289 1991290431274925425220467)
          ·
            refine ⟨2986935646912388137830701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1991290431274925425220467 2986935646912388137830701)
            ·
              refine ⟨1120100867592145551686513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2986935646912388137830701 1120100867592145551686513)
              ·
                refine ⟨840075650694109163764885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1120100867592145551686513 840075650694109163764885)
                ·
                  refine ⟨39378546126286367051479, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 840075650694109163764885 39378546126286367051479)
                  ·
                    rfl

theorem cell23_690205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 3, 2, 6].length) (baseStart_690205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_690205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_690205 prefixEnd_690205 := by exact prefixLift 690205
  have htrace : WordTrace (prefixWord ++ tailWord_690205) baseStart_690205 baseEnd_690205 := by
    simpa [prefixWord, tailWord_690205, baseEnd_690205] using wordTrace_append hprefix tailTrace_690205
  have hstable : (prefixWord ++ tailWord_690205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_690205).length < 2 ^ (prefixWord ++ tailWord_690205).sum := by decide
  have hdescent : baseEnd_690205 < baseStart_690205 := by decide
  rcases family_descends (prefixWord ++ tailWord_690205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_690222 : List Nat := [4, 1, 3, 1, 1, 3, 3, 1, 6]
def baseStart_690222 : Nat := 118140960795 + 690222 * 2 ^ 59
def prefixEnd_690222 : Nat := 4983230072969 + 3 ^ 40 * 690222 * 2
def baseEnd_690222 : Nat := 39379516034189304105637

theorem tailTrace_690222 : CollatzResearch.WordTrace tailWord_690222 prefixEnd_690222 39379516034189304105637 := by
  unfold tailWord_690222
  simp only [CollatzResearch.WordTrace]
  refine ⟨3146808063181381172220115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 16782976336967366251840613 3146808063181381172220115)
  ·
    refine ⟨4720212094772071758330173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3146808063181381172220115 4720212094772071758330173)
    ·
      refine ⟨1770079535539526909373815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4720212094772071758330173 1770079535539526909373815)
      ·
        refine ⟨2655119303309290364060723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1770079535539526909373815 2655119303309290364060723)
        ·
          refine ⟨3982678954963935546091085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2655119303309290364060723 3982678954963935546091085)
          ·
            refine ⟨1493504608111475829784157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3982678954963935546091085 1493504608111475829784157)
            ·
              refine ⟨560064228041803436169059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1493504608111475829784157 560064228041803436169059)
              ·
                refine ⟨840096342062705154253589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 560064228041803436169059 840096342062705154253589)
                ·
                  refine ⟨39379516034189304105637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 840096342062705154253589 39379516034189304105637)
                  ·
                    rfl

theorem cell23_690222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 3, 3, 1, 6].length) (baseStart_690222 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_690222 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_690222 prefixEnd_690222 := by exact prefixLift 690222
  have htrace : WordTrace (prefixWord ++ tailWord_690222) baseStart_690222 baseEnd_690222 := by
    simpa [prefixWord, tailWord_690222, baseEnd_690222] using wordTrace_append hprefix tailTrace_690222
  have hstable : (prefixWord ++ tailWord_690222).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_690222).length < 2 ^ (prefixWord ++ tailWord_690222).sum := by decide
  have hdescent : baseEnd_690222 < baseStart_690222 := by decide
  rcases family_descends (prefixWord ++ tailWord_690222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_690225 : List Nat := [1, 2, 2, 3, 1, 3, 1, 2, 1, 5, 2]
def baseStart_690225 : Nat := 118140960795 + 690225 * 2 ^ 59
def prefixEnd_690225 : Nat := 4983230072969 + 3 ^ 40 * 690225 * 2
def baseEnd_690225 : Nat := 354417184749667225213219

theorem tailTrace_690225 : CollatzResearch.WordTrace tailWord_690225 prefixEnd_690225 354417184749667225213219 := by
  unfold tailWord_690225
  simp only [CollatzResearch.WordTrace]
  refine ⟨25174573924440180890120129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16783049282960120593413419 25174573924440180890120129)
  ·
    refine ⟨18880930443330135667590097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25174573924440180890120129 18880930443330135667590097)
    ·
      refine ⟨14160697832497601750692573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18880930443330135667590097 14160697832497601750692573)
      ·
        refine ⟨5310261687186600656509715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14160697832497601750692573 5310261687186600656509715)
        ·
          refine ⟨7965392530779900984764573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5310261687186600656509715 7965392530779900984764573)
          ·
            refine ⟨2987022199042462869286715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7965392530779900984764573 2987022199042462869286715)
            ·
              refine ⟨4480533298563694303930073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2987022199042462869286715 4480533298563694303930073)
              ·
                refine ⟨3360399973922770727947555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4480533298563694303930073 3360399973922770727947555)
                ·
                  refine ⟨5040599960884156091921333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3360399973922770727947555 5040599960884156091921333)
                  ·
                    refine ⟨472556246332889633617625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5040599960884156091921333 472556246332889633617625)
                    ·
                      refine ⟨354417184749667225213219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 472556246332889633617625 354417184749667225213219)
                      ·
                        rfl

theorem cell23_690225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 1, 2, 1, 5, 2].length) (baseStart_690225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_690225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_690225 prefixEnd_690225 := by exact prefixLift 690225
  have htrace : WordTrace (prefixWord ++ tailWord_690225) baseStart_690225 baseEnd_690225 := by
    simpa [prefixWord, tailWord_690225, baseEnd_690225] using wordTrace_append hprefix tailTrace_690225
  have hstable : (prefixWord ++ tailWord_690225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_690225).length < 2 ^ (prefixWord ++ tailWord_690225).sum := by decide
  have hdescent : baseEnd_690225 < baseStart_690225 := by decide
  rcases family_descends (prefixWord ++ tailWord_690225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_690265 : List Nat := [1, 2, 1, 2, 2, 1, 4, 4, 2, 4]
def baseStart_690265 : Nat := 118140960795 + 690265 * 2 ^ 59
def prefixEnd_690265 : Nat := 4983230072969 + 3 ^ 40 * 690265 * 2
def baseEnd_690265 : Nat := 118145907991949022904345

theorem tailTrace_690265 : CollatzResearch.WordTrace tailWord_690265 prefixEnd_690265 118145907991949022904345 := by
  unfold tailWord_690265
  simp only [CollatzResearch.WordTrace]
  refine ⟨25176032844295267721576249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16784021896196845147717499 25176032844295267721576249)
  ·
    refine ⟨18882024633221450791182187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25176032844295267721576249 18882024633221450791182187)
    ·
      refine ⟨28323036949832176186773281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18882024633221450791182187 28323036949832176186773281)
      ·
        refine ⟨21242277712374132140079961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28323036949832176186773281 21242277712374132140079961)
        ·
          refine ⟨15931708284280599105059971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21242277712374132140079961 15931708284280599105059971)
          ·
            refine ⟨23897562426420898657589957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15931708284280599105059971 23897562426420898657589957)
            ·
              refine ⟨4480792954953918498298117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23897562426420898657589957 4480792954953918498298117)
              ·
                refine ⟨840148679053859718430897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4480792954953918498298117 840148679053859718430897)
                ·
                  refine ⟨630111509290394788823173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 840148679053859718430897 630111509290394788823173)
                  ·
                    refine ⟨118145907991949022904345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 630111509290394788823173 118145907991949022904345)
                    ·
                      rfl

theorem cell23_690265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 4, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 4, 4, 2, 4].length) (baseStart_690265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_690265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_690265 prefixEnd_690265 := by exact prefixLift 690265
  have htrace : WordTrace (prefixWord ++ tailWord_690265) baseStart_690265 baseEnd_690265 := by
    simpa [prefixWord, tailWord_690265, baseEnd_690265] using wordTrace_append hprefix tailTrace_690265
  have hstable : (prefixWord ++ tailWord_690265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_690265).length < 2 ^ (prefixWord ++ tailWord_690265).sum := by decide
  have hdescent : baseEnd_690265 < baseStart_690265 := by decide
  rcases family_descends (prefixWord ++ tailWord_690265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_690285 : List Nat := [1, 5, 1, 1, 2, 1, 2, 3, 1, 2, 4]
def baseStart_690285 : Nat := 118140960795 + 690285 * 2 ^ 59
def prefixEnd_690285 : Nat := 4983230072969 + 3 ^ 40 * 690285 * 2
def baseEnd_690285 : Nat := 354447993588936990462943

theorem tailTrace_690285 : CollatzResearch.WordTrace tailWord_690285 prefixEnd_690285 354447993588936990462943 := by
  unfold tailWord_690285
  simp only [CollatzResearch.WordTrace]
  refine ⟨25176762304222811137304309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16784508202815207424869539 25176762304222811137304309)
  ·
    refine ⟨2360321466020888544122279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 25176762304222811137304309 2360321466020888544122279)
    ·
      refine ⟨3540482199031332816183419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2360321466020888544122279 3540482199031332816183419)
      ·
        refine ⟨5310723298546999224275129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3540482199031332816183419 5310723298546999224275129)
        ·
          refine ⟨3983042473910249418206347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5310723298546999224275129 3983042473910249418206347)
          ·
            refine ⟨5974563710865374127309521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3983042473910249418206347 5974563710865374127309521)
            ·
              refine ⟨4480922783149030595482141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5974563710865374127309521 4480922783149030595482141)
              ·
                refine ⟨1680346043680886473305803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4480922783149030595482141 1680346043680886473305803)
                ·
                  refine ⟨2520519065521329709958705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1680346043680886473305803 2520519065521329709958705)
                  ·
                    refine ⟨1890389299140997282469029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2520519065521329709958705 1890389299140997282469029)
                    ·
                      refine ⟨354447993588936990462943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1890389299140997282469029 354447993588936990462943)
                      ·
                        rfl

theorem cell23_690285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 2, 3, 1, 2, 4].length) (baseStart_690285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_690285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_690285 prefixEnd_690285 := by exact prefixLift 690285
  have htrace : WordTrace (prefixWord ++ tailWord_690285) baseStart_690285 baseEnd_690285 := by
    simpa [prefixWord, tailWord_690285, baseEnd_690285] using wordTrace_append hprefix tailTrace_690285
  have hstable : (prefixWord ++ tailWord_690285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_690285).length < 2 ^ (prefixWord ++ tailWord_690285).sum := by decide
  have hdescent : baseEnd_690285 < baseStart_690285 := by decide
  rcases family_descends (prefixWord ++ tailWord_690285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_690309 : List Nat := [1, 3, 1, 1, 5, 2, 3, 1, 1, 2, 3]
def baseStart_690309 : Nat := 118140960795 + 690309 * 2 ^ 59
def prefixEnd_690309 : Nat := 4983230072969 + 3 ^ 40 * 690309 * 2
def baseEnd_690309 : Nat := 354460317124644896562833

theorem tailTrace_690309 : CollatzResearch.WordTrace tailWord_690309 prefixEnd_690309 354460317124644896562833 := by
  unfold tailWord_690309
  simp only [CollatzResearch.WordTrace]
  refine ⟨25177637656135863236177981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16785091770757242157451987 25177637656135863236177981)
  ·
    refine ⟨9441614121050948713566743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25177637656135863236177981 9441614121050948713566743)
    ·
      refine ⟨14162421181576423070350115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9441614121050948713566743 14162421181576423070350115)
      ·
        refine ⟨21243631772364634605525173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14162421181576423070350115 21243631772364634605525173)
        ·
          refine ⟨1991590478659184494267985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 21243631772364634605525173 1991590478659184494267985)
          ·
            refine ⟨1493692858994388370700989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1991590478659184494267985 1493692858994388370700989)
            ·
              refine ⟨560134822122895639012871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1493692858994388370700989 560134822122895639012871)
              ·
                refine ⟨840202233184343458519307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 560134822122895639012871 840202233184343458519307)
                ·
                  refine ⟨1260303349776515187778961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 840202233184343458519307 1260303349776515187778961)
                  ·
                    refine ⟨945227512332386390834221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1260303349776515187778961 945227512332386390834221)
                    ·
                      refine ⟨354460317124644896562833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 945227512332386390834221 354460317124644896562833)
                      ·
                        rfl

theorem cell23_690309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 2, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 2, 3, 1, 1, 2, 3].length) (baseStart_690309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_690309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_690309 prefixEnd_690309 := by exact prefixLift 690309
  have htrace : WordTrace (prefixWord ++ tailWord_690309) baseStart_690309 baseEnd_690309 := by
    simpa [prefixWord, tailWord_690309, baseEnd_690309] using wordTrace_append hprefix tailTrace_690309
  have hstable : (prefixWord ++ tailWord_690309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_690309).length < 2 ^ (prefixWord ++ tailWord_690309).sum := by decide
  have hdescent : baseEnd_690309 < baseStart_690309 := by decide
  rcases family_descends (prefixWord ++ tailWord_690309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_690332 : List Nat := [2, 2, 3, 2, 1, 1, 1, 1, 5, 3, 2]
def baseStart_690332 : Nat := 118140960795 + 690332 * 2 ^ 59
def prefixEnd_690332 : Nat := 4983230072969 + 3 ^ 40 * 690332 * 2
def baseEnd_690332 : Nat := 354472127179698306575227

theorem tailTrace_690332 : CollatzResearch.WordTrace tailWord_690332 prefixEnd_690332 354472127179698306575227 := by
  unfold tailWord_690332
  simp only [CollatzResearch.WordTrace]
  refine ⟨12589238267526269082132625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16785651023368358776176833 12589238267526269082132625)
  ·
    refine ⟨9441928700644701811599469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12589238267526269082132625 9441928700644701811599469)
    ·
      refine ⟨3540723262741763179349801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9441928700644701811599469 3540723262741763179349801)
      ·
        refine ⟨2655542447056322384512351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3540723262741763179349801 2655542447056322384512351)
        ·
          refine ⟨3983313670584483576768527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2655542447056322384512351 3983313670584483576768527)
          ·
            refine ⟨5974970505876725365152791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3983313670584483576768527 5974970505876725365152791)
            ·
              refine ⟨8962455758815088047729187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5974970505876725365152791 8962455758815088047729187)
              ·
                refine ⟨13443683638222632071593781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8962455758815088047729187 13443683638222632071593781)
                ·
                  refine ⟨1260345341083371756711917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 13443683638222632071593781 1260345341083371756711917)
                  ·
                    refine ⟨472629502906264408766969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1260345341083371756711917 472629502906264408766969)
                    ·
                      refine ⟨354472127179698306575227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 472629502906264408766969 354472127179698306575227)
                      ·
                        rfl

theorem cell23_690332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 1, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 1, 1, 5, 3, 2].length) (baseStart_690332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_690332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_690332 prefixEnd_690332 := by exact prefixLift 690332
  have htrace : WordTrace (prefixWord ++ tailWord_690332) baseStart_690332 baseEnd_690332 := by
    simpa [prefixWord, tailWord_690332, baseEnd_690332] using wordTrace_append hprefix tailTrace_690332
  have hstable : (prefixWord ++ tailWord_690332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_690332).length < 2 ^ (prefixWord ++ tailWord_690332).sum := by decide
  have hdescent : baseEnd_690332 < baseStart_690332 := by decide
  rcases family_descends (prefixWord ++ tailWord_690332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_690349 : List Nat := [1, 5, 2, 1, 2, 1, 2, 1, 3, 3, 2]
def baseStart_690349 : Nat := 118140960795 + 690349 * 2 ^ 59
def prefixEnd_690349 : Nat := 4983230072969 + 3 ^ 40 * 690349 * 2
def baseEnd_690349 : Nat := 354480856350824740062649

theorem tailTrace_690349 : CollatzResearch.WordTrace tailWord_690349 prefixEnd_690349 354480856350824740062649 := by
  unfold tailWord_690349
  simp only [CollatzResearch.WordTrace]
  refine ⟨25179096575990950067634101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16786064383993966711756067 25179096575990950067634101)
  ·
    refine ⟨2360540303999151568840697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 25179096575990950067634101 2360540303999151568840697)
    ·
      refine ⟨1770405227999363676630523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2360540303999151568840697 1770405227999363676630523)
      ·
        refine ⟨2655607841999045514945785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1770405227999363676630523 2655607841999045514945785)
        ·
          refine ⟨1991705881499284136209339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2655607841999045514945785 1991705881499284136209339)
          ·
            refine ⟨2987558822248926204314009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1991705881499284136209339 2987558822248926204314009)
            ·
              refine ⟨2240669116686694653235507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2987558822248926204314009 2240669116686694653235507)
              ·
                refine ⟨3361003675030041979853261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2240669116686694653235507 3361003675030041979853261)
                ·
                  refine ⟨1260376378136265742444973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3361003675030041979853261 1260376378136265742444973)
                  ·
                    refine ⟨472641141801099653416865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1260376378136265742444973 472641141801099653416865)
                    ·
                      refine ⟨354480856350824740062649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 472641141801099653416865 354480856350824740062649)
                      ·
                        rfl

theorem cell23_690349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 2, 1, 3, 3, 2].length) (baseStart_690349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_690349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_690349 prefixEnd_690349 := by exact prefixLift 690349
  have htrace : WordTrace (prefixWord ++ tailWord_690349) baseStart_690349 baseEnd_690349 := by
    simpa [prefixWord, tailWord_690349, baseEnd_690349] using wordTrace_append hprefix tailTrace_690349
  have hstable : (prefixWord ++ tailWord_690349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_690349).length < 2 ^ (prefixWord ++ tailWord_690349).sum := by decide
  have hdescent : baseEnd_690349 < baseStart_690349 := by decide
  rcases family_descends (prefixWord ++ tailWord_690349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_690362 : List Nat := [3, 1, 1, 1, 2, 2, 4, 2, 1, 4, 2]
def baseStart_690362 : Nat := 118140960795 + 690362 * 2 ^ 59
def prefixEnd_690362 : Nat := 4983230072969 + 3 ^ 40 * 690362 * 2
def baseEnd_690362 : Nat := 354487531599333189200089

theorem tailTrace_690362 : CollatzResearch.WordTrace tailWord_690362 prefixEnd_690362 354487531599333189200089 := by
  unfold tailWord_690362
  simp only [CollatzResearch.WordTrace]
  refine ⟨6294892681235963321964335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16786380483295902191904893 6294892681235963321964335)
  ·
    refine ⟨9442339021853944982946503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6294892681235963321964335 9442339021853944982946503)
    ·
      refine ⟨14163508532780917474419755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9442339021853944982946503 14163508532780917474419755)
      ·
        refine ⟨21245262799171376211629633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14163508532780917474419755 21245262799171376211629633)
        ·
          refine ⟨15933947099378532158722225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21245262799171376211629633 15933947099378532158722225)
          ·
            refine ⟨11950460324533899119041669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15933947099378532158722225 11950460324533899119041669)
            ·
              refine ⟨2240711310850106084820313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11950460324533899119041669 2240711310850106084820313)
              ·
                refine ⟨1680533483137579563615235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2240711310850106084820313 1680533483137579563615235)
                ·
                  refine ⟨2520800224706369345422853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1680533483137579563615235 2520800224706369345422853)
                  ·
                    refine ⟨472650042132444252266785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2520800224706369345422853 472650042132444252266785)
                    ·
                      refine ⟨354487531599333189200089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 472650042132444252266785 354487531599333189200089)
                      ·
                        rfl

theorem cell23_690362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 4, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 4, 2, 1, 4, 2].length) (baseStart_690362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_690362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_690362 prefixEnd_690362 := by exact prefixLift 690362
  have htrace : WordTrace (prefixWord ++ tailWord_690362) baseStart_690362 baseEnd_690362 := by
    simpa [prefixWord, tailWord_690362, baseEnd_690362] using wordTrace_append hprefix tailTrace_690362
  have hstable : (prefixWord ++ tailWord_690362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_690362).length < 2 ^ (prefixWord ++ tailWord_690362).sum := by decide
  have hdescent : baseEnd_690362 < baseStart_690362 := by decide
  rcases family_descends (prefixWord ++ tailWord_690362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_690366 : List Nat := [4, 2, 1, 1, 4, 1, 1, 3, 1, 3, 2]
def baseStart_690366 : Nat := 118140960795 + 690366 * 2 ^ 59
def prefixEnd_690366 : Nat := 4983230072969 + 3 ^ 40 * 690366 * 2
def baseEnd_690366 : Nat := 354489585521951173550071

theorem tailTrace_690366 : CollatzResearch.WordTrace tailWord_690366 prefixEnd_690366 354489585521951173550071 := by
  unfold tailWord_690366
  simp only [CollatzResearch.WordTrace]
  refine ⟨3147464577116170246375369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 16786477744619574647335301 3147464577116170246375369)
  ·
    refine ⟨2360598432837127684781527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3147464577116170246375369 2360598432837127684781527)
    ·
      refine ⟨3540897649255691527172291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2360598432837127684781527 3540897649255691527172291)
      ·
        refine ⟨5311346473883537290758437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3540897649255691527172291 5311346473883537290758437)
        ·
          refine ⟨995877463853163242017207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5311346473883537290758437 995877463853163242017207)
          ·
            refine ⟨1493816195779744863025811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 995877463853163242017207 1493816195779744863025811)
            ·
              refine ⟨2240724293669617294538717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1493816195779744863025811 2240724293669617294538717)
              ·
                refine ⟨840271610126106485452019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2240724293669617294538717 840271610126106485452019)
                ·
                  refine ⟨1260407415189159728178029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 840271610126106485452019 1260407415189159728178029)
                  ·
                    refine ⟨472652780695934898066761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1260407415189159728178029 472652780695934898066761)
                    ·
                      refine ⟨354489585521951173550071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 472652780695934898066761 354489585521951173550071)
                      ·
                        rfl

theorem cell23_690366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 1, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 1, 1, 3, 1, 3, 2].length) (baseStart_690366 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_690366 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_690366 prefixEnd_690366 := by exact prefixLift 690366
  have htrace : WordTrace (prefixWord ++ tailWord_690366) baseStart_690366 baseEnd_690366 := by
    simpa [prefixWord, tailWord_690366, baseEnd_690366] using wordTrace_append hprefix tailTrace_690366
  have hstable : (prefixWord ++ tailWord_690366).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_690366).length < 2 ^ (prefixWord ++ tailWord_690366).sum := by decide
  have hdescent : baseEnd_690366 < baseStart_690366 := by decide
  rcases family_descends (prefixWord ++ tailWord_690366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_690415 : List Nat := [1, 1, 2, 1, 6, 1, 2, 1, 1, 7]
def baseStart_690415 : Nat := 118140960795 + 690415 * 2 ^ 59
def prefixEnd_690415 : Nat := 4983230072969 + 3 ^ 40 * 690415 * 2
def baseEnd_690415 : Nat := 118171582024673827279115

theorem tailTrace_690415 : CollatzResearch.WordTrace tailWord_690415 prefixEnd_690415 118171582024673827279115 := by
  unfold tailWord_690415
  simp only [CollatzResearch.WordTrace]
  refine ⟨25181503793751843339536699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16787669195834562226357799 25181503793751843339536699)
  ·
    refine ⟨37772255690627765009305049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25181503793751843339536699 37772255690627765009305049)
    ·
      refine ⟨28329191767970823756978787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37772255690627765009305049 28329191767970823756978787)
      ·
        refine ⟨42493787651956235635468181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28329191767970823756978787 42493787651956235635468181)
        ·
          refine ⟨1991896296185448545412571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 42493787651956235635468181 1991896296185448545412571)
          ·
            refine ⟨2987844444278172818118857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1991896296185448545412571 2987844444278172818118857)
            ·
              refine ⟨2240883333208629613589143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2987844444278172818118857 2240883333208629613589143)
              ·
                refine ⟨3361324999812944420383715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2240883333208629613589143 3361324999812944420383715)
                ·
                  refine ⟨5041987499719416630575573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3361324999812944420383715 5041987499719416630575573)
                  ·
                    refine ⟨118171582024673827279115, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 5041987499719416630575573 118171582024673827279115)
                    ·
                      rfl

theorem cell23_690415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 2, 1, 1, 7].length) (baseStart_690415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_690415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_690415 prefixEnd_690415 := by exact prefixLift 690415
  have htrace : WordTrace (prefixWord ++ tailWord_690415) baseStart_690415 baseEnd_690415 := by
    simpa [prefixWord, tailWord_690415, baseEnd_690415] using wordTrace_append hprefix tailTrace_690415
  have hstable : (prefixWord ++ tailWord_690415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_690415).length < 2 ^ (prefixWord ++ tailWord_690415).sum := by decide
  have hdescent : baseEnd_690415 < baseStart_690415 := by decide
  rcases family_descends (prefixWord ++ tailWord_690415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_690436 : List Nat := [2, 3, 2, 2, 3, 1, 3, 2, 5]
def baseStart_690436 : Nat := 118140960795 + 690436 * 2 ^ 59
def prefixEnd_690436 : Nat := 4983230072969 + 3 ^ 40 * 690436 * 2
def baseEnd_690436 : Nat := 39391725463085099963861

theorem tailTrace_690436 : CollatzResearch.WordTrace tailWord_690436 prefixEnd_690436 39391725463085099963861 := by
  unfold tailWord_690436
  simp only [CollatzResearch.WordTrace]
  refine ⟨12591134863337881963025581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16788179817783842617367441 12591134863337881963025581)
  ·
    refine ⟨4721675573751705736134593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12591134863337881963025581 4721675573751705736134593)
    ·
      refine ⟨3541256680313779302100945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4721675573751705736134593 3541256680313779302100945)
      ·
        refine ⟨2655942510235334476575709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3541256680313779302100945 2655942510235334476575709)
        ·
          refine ⟨995978441338250428715891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2655942510235334476575709 995978441338250428715891)
          ·
            refine ⟨1493967662007375643073837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 995978441338250428715891 1493967662007375643073837)
            ·
              refine ⟨560237873252765866152689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1493967662007375643073837 560237873252765866152689)
              ·
                refine ⟨420178404939574399614517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 560237873252765866152689 420178404939574399614517)
                ·
                  refine ⟨39391725463085099963861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 420178404939574399614517 39391725463085099963861)
                  ·
                    rfl

theorem cell23_690436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 1, 3, 2, 5].length) (baseStart_690436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_690436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_690436 prefixEnd_690436 := by exact prefixLift 690436
  have htrace : WordTrace (prefixWord ++ tailWord_690436) baseStart_690436 baseEnd_690436 := by
    simpa [prefixWord, tailWord_690436, baseEnd_690436] using wordTrace_append hprefix tailTrace_690436
  have hstable : (prefixWord ++ tailWord_690436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_690436).length < 2 ^ (prefixWord ++ tailWord_690436).sum := by decide
  have hdescent : baseEnd_690436 < baseStart_690436 := by decide
  rcases family_descends (prefixWord ++ tailWord_690436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_690465 : List Nat := [1, 2, 3, 2, 1, 1, 2, 1, 2, 4, 4]
def baseStart_690465 : Nat := 118140960795 + 690465 * 2 ^ 59
def prefixEnd_690465 : Nat := 4983230072969 + 3 ^ 40 * 690465 * 2
def baseEnd_690465 : Nat := 354540420106746286212115

theorem tailTrace_690465 : CollatzResearch.WordTrace tailWord_690465 prefixEnd_690465 354540420106746286212115 := by
  unfold tailWord_690465
  simp only [CollatzResearch.WordTrace]
  refine ⟨25183327443570701878856849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16788884962380467919237899 25183327443570701878856849)
  ·
    refine ⟨18887495582678026409142637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25183327443570701878856849 18887495582678026409142637)
    ·
      refine ⟨7082810843504259903428489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18887495582678026409142637 7082810843504259903428489)
      ·
        refine ⟨5312108132628194927571367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7082810843504259903428489 5312108132628194927571367)
        ·
          refine ⟨7968162198942292391357051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5312108132628194927571367 7968162198942292391357051)
          ·
            refine ⟨11952243298413438587035577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7968162198942292391357051 11952243298413438587035577)
            ·
              refine ⟨8964182473810078940276683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11952243298413438587035577 8964182473810078940276683)
              ·
                refine ⟨13446273710715118410415025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8964182473810078940276683 13446273710715118410415025)
                ·
                  refine ⟨10084705283036338807811269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13446273710715118410415025 10084705283036338807811269)
                  ·
                    refine ⟨1890882240569313526464613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10084705283036338807811269 1890882240569313526464613)
                    ·
                      refine ⟨354540420106746286212115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1890882240569313526464613 354540420106746286212115)
                      ·
                        rfl

theorem cell23_690465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 2, 1, 2, 4, 4].length) (baseStart_690465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_690465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_690465 prefixEnd_690465 := by exact prefixLift 690465
  have htrace : WordTrace (prefixWord ++ tailWord_690465) baseStart_690465 baseEnd_690465 := by
    simpa [prefixWord, tailWord_690465, baseEnd_690465] using wordTrace_append hprefix tailTrace_690465
  have hstable : (prefixWord ++ tailWord_690465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_690465).length < 2 ^ (prefixWord ++ tailWord_690465).sum := by decide
  have hdescent : baseEnd_690465 < baseStart_690465 := by decide
  rcases family_descends (prefixWord ++ tailWord_690465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_690469 : List Nat := [1, 3, 1, 2, 5, 1, 2, 1, 2, 1, 4]
def baseStart_690469 : Nat := 118140960795 + 690469 * 2 ^ 59
def prefixEnd_690469 : Nat := 4983230072969 + 3 ^ 40 * 690469 * 2
def baseEnd_690469 : Nat := 354542474029364270562097

theorem tailTrace_690469 : CollatzResearch.WordTrace tailWord_690469 prefixEnd_690469 354542474029364270562097 := by
  unfold tailWord_690469
  simp only [CollatzResearch.WordTrace]
  refine ⟨25183473335556210562002461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16788982223704140374668307 25183473335556210562002461)
  ·
    refine ⟨9443802500833578960750923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25183473335556210562002461 9443802500833578960750923)
    ·
      refine ⟨14165703751250368441126385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9443802500833578960750923 14165703751250368441126385)
      ·
        refine ⟨10624277813437776330844789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14165703751250368441126385 10624277813437776330844789)
        ·
          refine ⟨996026045009791531016699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 10624277813437776330844789 996026045009791531016699)
          ·
            refine ⟨1494039067514687296525049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 996026045009791531016699 1494039067514687296525049)
            ·
              refine ⟨1120529300636015472393787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1494039067514687296525049 1120529300636015472393787)
              ·
                refine ⟨1680793950954023208590681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1120529300636015472393787 1680793950954023208590681)
                ·
                  refine ⟨1260595463215517406443011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1680793950954023208590681 1260595463215517406443011)
                  ·
                    refine ⟨1890893194823276109664517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1260595463215517406443011 1890893194823276109664517)
                    ·
                      refine ⟨354542474029364270562097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1890893194823276109664517 354542474029364270562097)
                      ·
                        rfl

theorem cell23_690469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 1, 2, 1, 2, 1, 4].length) (baseStart_690469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_690469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_690469 prefixEnd_690469 := by exact prefixLift 690469
  have htrace : WordTrace (prefixWord ++ tailWord_690469) baseStart_690469 baseEnd_690469 := by
    simpa [prefixWord, tailWord_690469, baseEnd_690469] using wordTrace_append hprefix tailTrace_690469
  have hstable : (prefixWord ++ tailWord_690469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_690469).length < 2 ^ (prefixWord ++ tailWord_690469).sum := by decide
  have hdescent : baseEnd_690469 < baseStart_690469 := by decide
  rcases family_descends (prefixWord ++ tailWord_690469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_690489 : List Nat := [1, 2, 1, 6, 1, 1, 2, 2, 2, 2, 3]
def baseStart_690489 : Nat := 118140960795 + 690489 * 2 ^ 59
def prefixEnd_690489 : Nat := 4983230072969 + 3 ^ 40 * 690489 * 2
def baseEnd_690489 : Nat := 354552743642454192312005

theorem tailTrace_690489 : CollatzResearch.WordTrace tailWord_690489 prefixEnd_690489 354552743642454192312005 := by
  unfold tailWord_690489
  simp only [CollatzResearch.WordTrace]
  refine ⟨25184202795483753977730521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16789468530322502651820347 25184202795483753977730521)
  ·
    refine ⟨18888152096612815483297891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25184202795483753977730521 18888152096612815483297891)
    ·
      refine ⟨28332228144919223224946837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18888152096612815483297891 28332228144919223224946837)
      ·
        refine ⟨1328073194293088588669383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 28332228144919223224946837 1328073194293088588669383)
        ·
          refine ⟨1992109791439632883004075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1328073194293088588669383 1992109791439632883004075)
          ·
            refine ⟨2988164687159449324506113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1992109791439632883004075 2988164687159449324506113)
            ·
              refine ⟨2241123515369586993379585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2988164687159449324506113 2241123515369586993379585)
              ·
                refine ⟨1680842636527190245034689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2241123515369586993379585 1680842636527190245034689)
                ·
                  refine ⟨1260631977395392683776017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1680842636527190245034689 1260631977395392683776017)
                  ·
                    refine ⟨945473983046544512832013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1260631977395392683776017 945473983046544512832013)
                    ·
                      refine ⟨354552743642454192312005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 945473983046544512832013 354552743642454192312005)
                      ·
                        rfl

theorem cell23_690489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 2, 2, 2, 2, 3].length) (baseStart_690489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_690489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_690489 prefixEnd_690489 := by exact prefixLift 690489
  have htrace : WordTrace (prefixWord ++ tailWord_690489) baseStart_690489 baseEnd_690489 := by
    simpa [prefixWord, tailWord_690489, baseEnd_690489] using wordTrace_append hprefix tailTrace_690489
  have hstable : (prefixWord ++ tailWord_690489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_690489).length < 2 ^ (prefixWord ++ tailWord_690489).sum := by decide
  have hdescent : baseEnd_690489 < baseStart_690489 := by decide
  rcases family_descends (prefixWord ++ tailWord_690489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_690492 : List Nat := [2, 2, 2, 2, 1, 2, 4, 2, 6]
def baseStart_690492 : Nat := 118140960795 + 690492 * 2 ^ 59
def prefixEnd_690492 : Nat := 4983230072969 + 3 ^ 40 * 690492 * 2
def baseEnd_690492 : Nat := 39394920453824186730499

theorem tailTrace_690492 : CollatzResearch.WordTrace tailWord_690492 prefixEnd_690492 39394920453824186730499 := by
  unfold tailWord_690492
  simp only [CollatzResearch.WordTrace]
  refine ⟨12592156107236442745044865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16789541476315256993393153 12592156107236442745044865)
  ·
    refine ⟨9444117080427332058783649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12592156107236442745044865 9444117080427332058783649)
    ·
      refine ⟨7083087810320499044087737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9444117080427332058783649 7083087810320499044087737)
      ·
        refine ⟨5312315857740374283065803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7083087810320499044087737 5312315857740374283065803)
        ·
          refine ⟨7968473786610561424598705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5312315857740374283065803 7968473786610561424598705)
          ·
            refine ⟨5976355339957921068449029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7968473786610561424598705 5976355339957921068449029)
            ·
              refine ⟨1120566626242110200334193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5976355339957921068449029 1120566626242110200334193)
              ·
                refine ⟨840424969681582650250645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1120566626242110200334193 840424969681582650250645)
                ·
                  refine ⟨39394920453824186730499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 840424969681582650250645 39394920453824186730499)
                  ·
                    rfl

theorem cell23_690492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 4, 2, 6].length) (baseStart_690492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_690492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_690492 prefixEnd_690492 := by exact prefixLift 690492
  have htrace : WordTrace (prefixWord ++ tailWord_690492) baseStart_690492 baseEnd_690492 := by
    simpa [prefixWord, tailWord_690492, baseEnd_690492] using wordTrace_append hprefix tailTrace_690492
  have hstable : (prefixWord ++ tailWord_690492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_690492).length < 2 ^ (prefixWord ++ tailWord_690492).sum := by decide
  have hdescent : baseEnd_690492 < baseStart_690492 := by decide
  rcases family_descends (prefixWord ++ tailWord_690492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_690495 : List Nat := [1, 1, 2, 2, 4, 1, 2, 1, 1, 2, 6]
def baseStart_690495 : Nat := 118140960795 + 690495 * 2 ^ 59
def prefixEnd_690495 : Nat := 4983230072969 + 3 ^ 40 * 690495 * 2
def baseEnd_690495 : Nat := 354555824526381168836977

theorem tailTrace_690495 : CollatzResearch.WordTrace tailWord_690495 prefixEnd_690495 354555824526381168836977 := by
  unfold tailWord_690495
  simp only [CollatzResearch.WordTrace]
  refine ⟨25184421633462017002448939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16789614422308011334965959 25184421633462017002448939)
  ·
    refine ⟨37776632450193025503673409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25184421633462017002448939 37776632450193025503673409)
    ·
      refine ⟨28332474337644769127755057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37776632450193025503673409 28332474337644769127755057)
      ·
        refine ⟨21249355753233576845816293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28332474337644769127755057 21249355753233576845816293)
        ·
          refine ⟨3984254203731295658590555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21249355753233576845816293 3984254203731295658590555)
          ·
            refine ⟨5976381305596943487885833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3984254203731295658590555 5976381305596943487885833)
            ·
              refine ⟨4482285979197707615914375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5976381305596943487885833 4482285979197707615914375)
              ·
                refine ⟨6723428968796561423871563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4482285979197707615914375 6723428968796561423871563)
                ·
                  refine ⟨10085143453194842135807345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6723428968796561423871563 10085143453194842135807345)
                  ·
                    refine ⟨7563857589896131601855509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10085143453194842135807345 7563857589896131601855509)
                    ·
                      refine ⟨354555824526381168836977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 7563857589896131601855509 354555824526381168836977)
                      ·
                        rfl

theorem cell23_690495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 2, 1, 1, 2, 6].length) (baseStart_690495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_690495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_690495 prefixEnd_690495 := by exact prefixLift 690495
  have htrace : WordTrace (prefixWord ++ tailWord_690495) baseStart_690495 baseEnd_690495 := by
    simpa [prefixWord, tailWord_690495, baseEnd_690495] using wordTrace_append hprefix tailTrace_690495
  have hstable : (prefixWord ++ tailWord_690495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_690495).length < 2 ^ (prefixWord ++ tailWord_690495).sum := by decide
  have hdescent : baseEnd_690495 < baseStart_690495 := by decide
  rcases family_descends (prefixWord ++ tailWord_690495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_690519 : List Nat := [1, 1, 3, 2, 3, 1, 3, 2, 3, 1, 3]
def baseStart_690519 : Nat := 118140960795 + 690519 * 2 ^ 59
def prefixEnd_690519 : Nat := 4983230072969 + 3 ^ 40 * 690519 * 2
def baseEnd_690519 : Nat := 354568148062089074936867

theorem tailTrace_690519 : CollatzResearch.WordTrace tailWord_690519 prefixEnd_690519 354568148062089074936867 := by
  unfold tailWord_690519
  simp only [CollatzResearch.WordTrace]
  refine ⟨25185296985375069101322611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16790197990250046067548407 25185296985375069101322611)
  ·
    refine ⟨37777945478062603651983917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25185296985375069101322611 37777945478062603651983917)
    ·
      refine ⟨14166729554273476369493969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37777945478062603651983917 14166729554273476369493969)
      ·
        refine ⟨10625047165705107277120477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14166729554273476369493969 10625047165705107277120477)
        ·
          refine ⟨3984392687139415228920179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10625047165705107277120477 3984392687139415228920179)
          ·
            refine ⟨5976589030709122843380269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3984392687139415228920179 5976589030709122843380269)
            ·
              refine ⟨2241220886515921066267601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5976589030709122843380269 2241220886515921066267601)
              ·
                refine ⟨1680915664886940799700701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2241220886515921066267601 1680915664886940799700701)
                ·
                  refine ⟨630343374332602799887763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1680915664886940799700701 630343374332602799887763)
                  ·
                    refine ⟨945515061498904199831645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 630343374332602799887763 945515061498904199831645)
                    ·
                      refine ⟨354568148062089074936867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 945515061498904199831645 354568148062089074936867)
                      ·
                        rfl

theorem cell23_690519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 3, 2, 3, 1, 3].length) (baseStart_690519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_690519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_690519 prefixEnd_690519 := by exact prefixLift 690519
  have htrace : WordTrace (prefixWord ++ tailWord_690519) baseStart_690519 baseEnd_690519 := by
    simpa [prefixWord, tailWord_690519, baseEnd_690519] using wordTrace_append hprefix tailTrace_690519
  have hstable : (prefixWord ++ tailWord_690519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_690519).length < 2 ^ (prefixWord ++ tailWord_690519).sum := by decide
  have hdescent : baseEnd_690519 < baseStart_690519 := by decide
  rcases family_descends (prefixWord ++ tailWord_690519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_690522 : List Nat := [3, 1, 1, 2, 1, 2, 1, 6, 1, 5]
def baseStart_690522 : Nat := 118140960795 + 690522 * 2 ^ 59
def prefixEnd_690522 : Nat := 4983230072969 + 3 ^ 40 * 690522 * 2
def baseEnd_690522 : Nat := 118189896168017521066451

theorem tailTrace_690522 : CollatzResearch.WordTrace tailWord_690522 prefixEnd_690522 118189896168017521066451 := by
  unfold tailWord_690522
  simp only [CollatzResearch.WordTrace]
  refine ⟨6296351601091050153420455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16790270936242800409121213 6296351601091050153420455)
  ·
    refine ⟨9444527401636575230130683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6296351601091050153420455 9444527401636575230130683)
    ·
      refine ⟨14166791102454862845196025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9444527401636575230130683 14166791102454862845196025)
      ·
        refine ⟨10625093326841147133897019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14166791102454862845196025 10625093326841147133897019)
        ·
          refine ⟨15937639990261720700845529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10625093326841147133897019 15937639990261720700845529)
          ·
            refine ⟨11953229992696290525634147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15937639990261720700845529 11953229992696290525634147)
            ·
              refine ⟨17929844989044435788451221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11953229992696290525634147 17929844989044435788451221)
              ·
                refine ⟨840461483861457927583651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 17929844989044435788451221 840461483861457927583651)
                ·
                  refine ⟨1260692225792186891375477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 840461483861457927583651 1260692225792186891375477)
                  ·
                    refine ⟨118189896168017521066451, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1260692225792186891375477 118189896168017521066451)
                    ·
                      rfl

theorem cell23_690522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 6, 1, 5].length) (baseStart_690522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_690522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_690522 prefixEnd_690522 := by exact prefixLift 690522
  have htrace : WordTrace (prefixWord ++ tailWord_690522) baseStart_690522 baseEnd_690522 := by
    simpa [prefixWord, tailWord_690522, baseEnd_690522] using wordTrace_append hprefix tailTrace_690522
  have hstable : (prefixWord ++ tailWord_690522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_690522).length < 2 ^ (prefixWord ++ tailWord_690522).sum := by decide
  have hdescent : baseEnd_690522 < baseStart_690522 := by decide
  rcases family_descends (prefixWord ++ tailWord_690522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_690559 : List Nat := [1, 1, 2, 2, 1, 1, 2, 2, 7, 2, 2]
def baseStart_690559 : Nat := 118140960795 + 690559 * 2 ^ 59
def prefixEnd_690559 : Nat := 4983230072969 + 3 ^ 40 * 690559 * 2
def baseEnd_690559 : Nat := 354588687288268918436683

theorem tailTrace_690559 : CollatzResearch.WordTrace tailWord_690559 prefixEnd_690559 354588687288268918436683 := by
  unfold tailWord_690559
  simp only [CollatzResearch.WordTrace]
  refine ⟨25186755905230155932778731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16791170603486770621852487 25186755905230155932778731)
  ·
    refine ⟨37780133857845233899168097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25186755905230155932778731 37780133857845233899168097)
    ·
      refine ⟨28335100393383925424376073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37780133857845233899168097 28335100393383925424376073)
      ·
        refine ⟨21251325295037944068282055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28335100393383925424376073 21251325295037944068282055)
        ·
          refine ⟨31876987942556916102423083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21251325295037944068282055 31876987942556916102423083)
          ·
            refine ⟨47815481913835374153634625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31876987942556916102423083 47815481913835374153634625)
            ·
              refine ⟨35861611435376530615225969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47815481913835374153634625 35861611435376530615225969)
              ·
                refine ⟨26896208576532397961419477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35861611435376530615225969 26896208576532397961419477)
                ·
                  refine ⟨630379888512478077220769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 26896208576532397961419477 630379888512478077220769)
                  ·
                    refine ⟨472784916384358557915577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 630379888512478077220769 472784916384358557915577)
                    ·
                      refine ⟨354588687288268918436683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 472784916384358557915577 354588687288268918436683)
                      ·
                        rfl

theorem cell23_690559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 2, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 2, 7, 2, 2].length) (baseStart_690559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_690559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_690559 prefixEnd_690559 := by exact prefixLift 690559
  have htrace : WordTrace (prefixWord ++ tailWord_690559) baseStart_690559 baseEnd_690559 := by
    simpa [prefixWord, tailWord_690559, baseEnd_690559] using wordTrace_append hprefix tailTrace_690559
  have hstable : (prefixWord ++ tailWord_690559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_690559).length < 2 ^ (prefixWord ++ tailWord_690559).sum := by decide
  have hdescent : baseEnd_690559 < baseStart_690559 := by decide
  rcases family_descends (prefixWord ++ tailWord_690559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_690565 : List Nat := [1, 3, 1, 1, 3, 1, 1, 12]
def baseStart_690565 : Nat := 118140960795 + 690565 * 2 ^ 59
def prefixEnd_690565 : Nat := 4983230072969 + 3 ^ 40 * 690565 * 2
def baseEnd_690565 : Nat := 13133028450822070183765

theorem tailTrace_690565 : CollatzResearch.WordTrace tailWord_690565 prefixEnd_690565 13133028450822070183765 := by
  unfold tailWord_690565
  simp only [CollatzResearch.WordTrace]
  refine ⟨25186974743208418957497149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16791316495472279304998099 25186974743208418957497149)
  ·
    refine ⟨9445115528703157109061431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25186974743208418957497149 9445115528703157109061431)
    ·
      refine ⟨14167673293054735663592147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9445115528703157109061431 14167673293054735663592147)
      ·
        refine ⟨21251509939582103495388221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14167673293054735663592147 21251509939582103495388221)
        ·
          refine ⟨7969316227343288810770583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21251509939582103495388221 7969316227343288810770583)
          ·
            refine ⟨11953974341014933216155875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7969316227343288810770583 11953974341014933216155875)
            ·
              refine ⟨17930961511522399824233813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11953974341014933216155875 17930961511522399824233813)
              ·
                refine ⟨13133028450822070183765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 12 17930961511522399824233813 13133028450822070183765)
                ·
                  rfl

theorem cell23_690565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 12].length) (baseStart_690565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_690565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_690565 prefixEnd_690565 := by exact prefixLift 690565
  have htrace : WordTrace (prefixWord ++ tailWord_690565) baseStart_690565 baseEnd_690565 := by
    simpa [prefixWord, tailWord_690565, baseEnd_690565] using wordTrace_append hprefix tailTrace_690565
  have hstable : (prefixWord ++ tailWord_690565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_690565).length < 2 ^ (prefixWord ++ tailWord_690565).sum := by decide
  have hdescent : baseEnd_690565 < baseStart_690565 := by decide
  rcases family_descends (prefixWord ++ tailWord_690565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_690569 : List Nat := [1, 2, 1, 1, 6, 3, 1, 1, 1, 6]
def baseStart_690569 : Nat := 118140960795 + 690569 * 2 ^ 59
def prefixEnd_690569 : Nat := 4983230072969 + 3 ^ 40 * 690569 * 2
def baseEnd_690569 : Nat := 118197940698271293103879

theorem tailTrace_690569 : CollatzResearch.WordTrace tailWord_690569 prefixEnd_690569 118197940698271293103879 := by
  unfold tailWord_690569
  simp only [CollatzResearch.WordTrace]
  refine ⟨25187120635193927640642761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16791413756795951760428507 25187120635193927640642761)
  ·
    refine ⟨18890340476395445730482071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25187120635193927640642761 18890340476395445730482071)
    ·
      refine ⟨28335510714593168595723107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18890340476395445730482071 28335510714593168595723107)
      ·
        refine ⟨42503266071889752893584661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28335510714593168595723107 42503266071889752893584661)
        ·
          refine ⟨1992340597119832166886781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 42503266071889752893584661 1992340597119832166886781)
          ·
            refine ⟨747127723919937062582543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1992340597119832166886781 747127723919937062582543)
            ·
              refine ⟨1120691585879905593873815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 747127723919937062582543 1120691585879905593873815)
              ·
                refine ⟨1681037378819858390810723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1120691585879905593873815 1681037378819858390810723)
                ·
                  refine ⟨2521556068229787586216085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1681037378819858390810723 2521556068229787586216085)
                  ·
                    refine ⟨118197940698271293103879, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2521556068229787586216085 118197940698271293103879)
                    ·
                      rfl

theorem cell23_690569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 3, 1, 1, 1, 6].length) (baseStart_690569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_690569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_690569 prefixEnd_690569 := by exact prefixLift 690569
  have htrace : WordTrace (prefixWord ++ tailWord_690569) baseStart_690569 baseEnd_690569 := by
    simpa [prefixWord, tailWord_690569, baseEnd_690569] using wordTrace_append hprefix tailTrace_690569
  have hstable : (prefixWord ++ tailWord_690569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_690569).length < 2 ^ (prefixWord ++ tailWord_690569).sum := by decide
  have hdescent : baseEnd_690569 < baseStart_690569 := by decide
  rcases family_descends (prefixWord ++ tailWord_690569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_690572 : List Nat := [2, 2, 1, 2, 1, 5, 1, 1, 1, 1, 6]
def baseStart_690572 : Nat := 118140960795 + 690572 * 2 ^ 59
def prefixEnd_690572 : Nat := 4983230072969 + 3 ^ 40 * 690572 * 2
def baseEnd_690572 : Nat := 354595362536777367574123

theorem tailTrace_690572 : CollatzResearch.WordTrace tailWord_690572 prefixEnd_690572 354595362536777367574123 := by
  unfold tailWord_690572
  simp only [CollatzResearch.WordTrace]
  refine ⟨12593615027091529576500985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16791486702788706102001313 12593615027091529576500985)
  ·
    refine ⟨9445211270318647182375739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12593615027091529576500985 9445211270318647182375739)
    ·
      refine ⟨14167816905477970773563609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9445211270318647182375739 14167816905477970773563609)
      ·
        refine ⟨10625862679108478080172707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14167816905477970773563609 10625862679108478080172707)
        ·
          refine ⟨15938794018662717120259061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10625862679108478080172707 15938794018662717120259061)
          ·
            refine ⟨1494261939249629730024287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 15938794018662717120259061 1494261939249629730024287)
            ·
              refine ⟨2241392908874444595036431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1494261939249629730024287 2241392908874444595036431)
              ·
                refine ⟨3362089363311666892554647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2241392908874444595036431 3362089363311666892554647)
                ·
                  refine ⟨5043134044967500338831971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3362089363311666892554647 5043134044967500338831971)
                  ·
                    refine ⟨7564701067451250508247957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5043134044967500338831971 7564701067451250508247957)
                    ·
                      refine ⟨354595362536777367574123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 7564701067451250508247957 354595362536777367574123)
                      ·
                        rfl

theorem cell23_690572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 5, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 5, 1, 1, 1, 1, 6].length) (baseStart_690572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_690572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_690572 prefixEnd_690572 := by exact prefixLift 690572
  have htrace : WordTrace (prefixWord ++ tailWord_690572) baseStart_690572 baseEnd_690572 := by
    simpa [prefixWord, tailWord_690572, baseEnd_690572] using wordTrace_append hprefix tailTrace_690572
  have hstable : (prefixWord ++ tailWord_690572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_690572).length < 2 ^ (prefixWord ++ tailWord_690572).sum := by decide
  have hdescent : baseEnd_690572 < baseStart_690572 := by decide
  rcases family_descends (prefixWord ++ tailWord_690572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_690610 : List Nat := [3, 2, 1, 1, 1, 1, 7, 2, 1, 2, 2]
def baseStart_690610 : Nat := 118140960795 + 690610 * 2 ^ 59
def prefixEnd_690610 : Nat := 4983230072969 + 3 ^ 40 * 690610 * 2
def baseEnd_690610 : Nat := 354614874801648218898949

theorem tailTrace_690610 : CollatzResearch.WordTrace tailWord_690610 prefixEnd_690610 354614874801648218898949 := by
  unfold tailWord_690610
  simp only [CollatzResearch.WordTrace]
  refine ⟨6297154007011347910721321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16792410685363594428590189 6297154007011347910721321)
  ·
    refine ⟨4722865505258510933040991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6297154007011347910721321 4722865505258510933040991)
    ·
      refine ⟨7084298257887766399561487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4722865505258510933040991 7084298257887766399561487)
      ·
        refine ⟨10626447386831649599342231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7084298257887766399561487 10626447386831649599342231)
        ·
          refine ⟨15939671080247474399013347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10626447386831649599342231 15939671080247474399013347)
          ·
            refine ⟨23909506620371211598520021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15939671080247474399013347 23909506620371211598520021)
            ·
              refine ⟨560379061414950271840313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 23909506620371211598520021 560379061414950271840313)
              ·
                refine ⟨420284296061212703880235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 560379061414950271840313 420284296061212703880235)
                ·
                  refine ⟨630426444091819055820353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 420284296061212703880235 630426444091819055820353)
                  ·
                    refine ⟨472819833068864291865265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 630426444091819055820353 472819833068864291865265)
                    ·
                      refine ⟨354614874801648218898949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 472819833068864291865265 354614874801648218898949)
                      ·
                        rfl

theorem cell23_690610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 7, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 7, 2, 1, 2, 2].length) (baseStart_690610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_690610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_690610 prefixEnd_690610 := by exact prefixLift 690610
  have htrace : WordTrace (prefixWord ++ tailWord_690610) baseStart_690610 baseEnd_690610 := by
    simpa [prefixWord, tailWord_690610, baseEnd_690610] using wordTrace_append hprefix tailTrace_690610
  have hstable : (prefixWord ++ tailWord_690610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_690610).length < 2 ^ (prefixWord ++ tailWord_690610).sum := by decide
  have hdescent : baseEnd_690610 < baseStart_690610 := by decide
  rcases family_descends (prefixWord ++ tailWord_690610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_690672 : List Nat := [2, 1, 1, 1, 3, 3, 2, 3, 7]
def baseStart_690672 : Nat := 118140960795 + 690672 * 2 ^ 59
def prefixEnd_690672 : Nat := 4983230072969 + 3 ^ 40 * 690672 * 2
def baseEnd_690672 : Nat := 39405190066914108480407

theorem tailTrace_690672 : CollatzResearch.WordTrace tailWord_690672 prefixEnd_690672 39405190066914108480407 := by
  unfold tailWord_690672
  simp only [CollatzResearch.WordTrace]
  refine ⟨12595438676910388115821135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16793918235880517487761513 12595438676910388115821135)
  ·
    refine ⟨18893158015365582173731703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12595438676910388115821135 18893158015365582173731703)
    ·
      refine ⟨28339737023048373260597555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18893158015365582173731703 28339737023048373260597555)
      ·
        refine ⟨42509605534572559890896333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28339737023048373260597555 42509605534572559890896333)
        ·
          refine ⟨15941102075464709959086125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42509605534572559890896333 15941102075464709959086125)
          ·
            refine ⟨5977913278299266234657297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15941102075464709959086125 5977913278299266234657297)
            ·
              refine ⟨4483434958724449675992973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5977913278299266234657297 4483434958724449675992973)
              ·
                refine ⟨1681288109521668628497365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4483434958724449675992973 1681288109521668628497365)
                ·
                  refine ⟨39405190066914108480407, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1681288109521668628497365 39405190066914108480407)
                  ·
                    rfl

theorem cell23_690672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 2, 3, 7].length) (baseStart_690672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_690672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_690672 prefixEnd_690672 := by exact prefixLift 690672
  have htrace : WordTrace (prefixWord ++ tailWord_690672) baseStart_690672 baseEnd_690672 := by
    simpa [prefixWord, tailWord_690672, baseEnd_690672] using wordTrace_append hprefix tailTrace_690672
  have hstable : (prefixWord ++ tailWord_690672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_690672).length < 2 ^ (prefixWord ++ tailWord_690672).sum := by decide
  have hdescent : baseEnd_690672 < baseStart_690672 := by decide
  rcases family_descends (prefixWord ++ tailWord_690672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_690689 : List Nat := [1, 2, 4, 1, 3, 2, 1, 2, 7]
def baseStart_690689 : Nat := 118140960795 + 690689 * 2 ^ 59
def prefixEnd_690689 : Nat := 4983230072969 + 3 ^ 40 * 690689 * 2
def baseEnd_690689 : Nat := 39406159974817045534565

theorem tailTrace_690689 : CollatzResearch.WordTrace tailWord_690689 prefixEnd_690689 39406159974817045534565 := by
  unfold tailWord_690689
  simp only [CollatzResearch.WordTrace]
  refine ⟨25191497394759188135011121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16794331596506125423340747 25191497394759188135011121)
  ·
    refine ⟨18893623046069391101258341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25191497394759188135011121 18893623046069391101258341)
    ·
      refine ⟨3542554321138010831485939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18893623046069391101258341 3542554321138010831485939)
      ·
        refine ⟨5313831481707016247228909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3542554321138010831485939 5313831481707016247228909)
        ·
          refine ⟨1992686805640131092710841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5313831481707016247228909 1992686805640131092710841)
          ·
            refine ⟨1494515104230098319533131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1992686805640131092710841 1494515104230098319533131)
            ·
              refine ⟨2241772656345147479299697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1494515104230098319533131 2241772656345147479299697)
              ·
                refine ⟨1681329492258860609474773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2241772656345147479299697 1681329492258860609474773)
                ·
                  refine ⟨39406159974817045534565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1681329492258860609474773 39406159974817045534565)
                  ·
                    rfl

theorem cell23_690689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 2, 1, 2, 7].length) (baseStart_690689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_690689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_690689 prefixEnd_690689 := by exact prefixLift 690689
  have htrace : WordTrace (prefixWord ++ tailWord_690689) baseStart_690689 baseEnd_690689 := by
    simpa [prefixWord, tailWord_690689, baseEnd_690689] using wordTrace_append hprefix tailTrace_690689
  have hstable : (prefixWord ++ tailWord_690689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_690689).length < 2 ^ (prefixWord ++ tailWord_690689).sum := by decide
  have hdescent : baseEnd_690689 < baseStart_690689 := by decide
  rcases family_descends (prefixWord ++ tailWord_690689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_690796 : List Nat := [2, 2, 1, 1, 3, 1, 6, 1, 6]
def baseStart_690796 : Nat := 118140960795 + 690796 * 2 ^ 59
def prefixEnd_690796 : Nat := 4983230072969 + 3 ^ 40 * 690796 * 2
def baseEnd_690796 : Nat := 39412264689264943463677

theorem tailTrace_690796 : CollatzResearch.WordTrace tailWord_690796 prefixEnd_690796 39412264689264943463677 := by
  unfold tailWord_690796
  simp only [CollatzResearch.WordTrace]
  refine ⟨12597700002685772704578121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16796933336914363606104161 12597700002685772704578121)
  ·
    refine ⟨9448275002014329528433591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12597700002685772704578121 9448275002014329528433591)
    ·
      refine ⟨14172412503021494292650387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9448275002014329528433591 14172412503021494292650387)
      ·
        refine ⟨21258618754532241438975581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14172412503021494292650387 21258618754532241438975581)
        ·
          refine ⟨7971982032949590539615843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21258618754532241438975581 7971982032949590539615843)
          ·
            refine ⟨11957973049424385809423765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7971982032949590539615843 11957973049424385809423765)
            ·
              refine ⟨560529986691768084816739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 11957973049424385809423765 560529986691768084816739)
              ·
                refine ⟨840794980037652127225109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 560529986691768084816739 840794980037652127225109)
                ·
                  refine ⟨39412264689264943463677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 840794980037652127225109 39412264689264943463677)
                  ·
                    rfl

theorem cell23_690796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 6].length) (baseStart_690796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_690796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_690796 prefixEnd_690796 := by exact prefixLift 690796
  have htrace : WordTrace (prefixWord ++ tailWord_690796) baseStart_690796 baseEnd_690796 := by
    simpa [prefixWord, tailWord_690796, baseEnd_690796] using wordTrace_append hprefix tailTrace_690796
  have hstable : (prefixWord ++ tailWord_690796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_690796).length < 2 ^ (prefixWord ++ tailWord_690796).sum := by decide
  have hdescent : baseEnd_690796 < baseStart_690796 := by decide
  rcases family_descends (prefixWord ++ tailWord_690796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_690839 : List Nat := [1, 1, 3, 3, 2, 1, 1, 2, 3, 6]
def baseStart_690839 : Nat := 118140960795 + 690839 * 2 ^ 59
def prefixEnd_690839 : Nat := 4983230072969 + 3 ^ 40 * 690839 * 2
def baseEnd_690839 : Nat := 118244153957175940978465

theorem tailTrace_690839 : CollatzResearch.WordTrace tailWord_690839 prefixEnd_690839 118244153957175940978465 := by
  unfold tailWord_690839
  simp only [CollatzResearch.WordTrace]
  refine ⟨25196968344215763752971571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16797978896143842501981047 25196968344215763752971571)
  ·
    refine ⟨37795452516323645629457357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25196968344215763752971571 37795452516323645629457357)
    ·
      refine ⟨14173294693621367111046509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37795452516323645629457357 14173294693621367111046509)
      ·
        refine ⟨5314985510108012666642441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14173294693621367111046509 5314985510108012666642441)
        ·
          refine ⟨3986239132581009499981831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5314985510108012666642441 3986239132581009499981831)
          ·
            refine ⟨5979358698871514249972747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3986239132581009499981831 5979358698871514249972747)
            ·
              refine ⟨8969038048307271374959121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5979358698871514249972747 8969038048307271374959121)
              ·
                refine ⟨6726778536230453531219341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8969038048307271374959121 6726778536230453531219341)
                ·
                  refine ⟨2522541951086420074207253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6726778536230453531219341 2522541951086420074207253)
                  ·
                    refine ⟨118244153957175940978465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2522541951086420074207253 118244153957175940978465)
                    ·
                      rfl

theorem cell23_690839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 1, 2, 3, 6].length) (baseStart_690839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_690839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_690839 prefixEnd_690839 := by exact prefixLift 690839
  have htrace : WordTrace (prefixWord ++ tailWord_690839) baseStart_690839 baseEnd_690839 := by
    simpa [prefixWord, tailWord_690839, baseEnd_690839] using wordTrace_append hprefix tailTrace_690839
  have hstable : (prefixWord ++ tailWord_690839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_690839).length < 2 ^ (prefixWord ++ tailWord_690839).sum := by decide
  have hdescent : baseEnd_690839 < baseStart_690839 := by decide
  rcases family_descends (prefixWord ++ tailWord_690839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_690840 : List Nat := [2, 1, 2, 4, 1, 1, 3, 4, 1, 1, 3]
def baseStart_690840 : Nat := 118140960795 + 690840 * 2 ^ 59
def prefixEnd_690840 : Nat := 4983230072969 + 3 ^ 40 * 690840 * 2
def baseEnd_690840 : Nat := 354732975352182319022891

theorem tailTrace_690840 : CollatzResearch.WordTrace tailWord_690840 prefixEnd_690840 354732975352182319022891 := by
  unfold tailWord_690840
  simp only [CollatzResearch.WordTrace]
  refine ⟨12598502408606070461878987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16798003211474760615838649 12598502408606070461878987)
  ·
    refine ⟨18897753612909105692818481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12598502408606070461878987 18897753612909105692818481)
    ·
      refine ⟨14173315209681829269613861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18897753612909105692818481 14173315209681829269613861)
      ·
        refine ⟨2657496601815342988052599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14173315209681829269613861 2657496601815342988052599)
        ·
          refine ⟨3986244902723014482078899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2657496601815342988052599 3986244902723014482078899)
          ·
            refine ⟨5979367354084521723118349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3986244902723014482078899 5979367354084521723118349)
            ·
              refine ⟨2242262757781695646169381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5979367354084521723118349 2242262757781695646169381)
              ·
                refine ⟨420424267084067933656759, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2242262757781695646169381 420424267084067933656759)
                ·
                  refine ⟨630636400626101900485139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 420424267084067933656759 630636400626101900485139)
                  ·
                    refine ⟨945954600939152850727709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 630636400626101900485139 945954600939152850727709)
                    ·
                      refine ⟨354732975352182319022891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 945954600939152850727709 354732975352182319022891)
                      ·
                        rfl

theorem cell23_690840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 3, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 3, 4, 1, 1, 3].length) (baseStart_690840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_690840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_690840 prefixEnd_690840 := by exact prefixLift 690840
  have htrace : WordTrace (prefixWord ++ tailWord_690840) baseStart_690840 baseEnd_690840 := by
    simpa [prefixWord, tailWord_690840, baseEnd_690840] using wordTrace_append hprefix tailTrace_690840
  have hstable : (prefixWord ++ tailWord_690840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_690840).length < 2 ^ (prefixWord ++ tailWord_690840).sum := by decide
  have hdescent : baseEnd_690840 < baseStart_690840 := by decide
  rcases family_descends (prefixWord ++ tailWord_690840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_690863 : List Nat := [1, 1, 2, 1, 2, 5, 1, 1, 5, 2, 2]
def baseStart_690863 : Nat := 118140960795 + 690863 * 2 ^ 59
def prefixEnd_690863 : Nat := 4983230072969 + 3 ^ 40 * 690863 * 2
def baseEnd_690863 : Nat := 354744785407235729035285

theorem tailTrace_690863 : CollatzResearch.WordTrace tailWord_690863 prefixEnd_690863 354744785407235729035285 := by
  unfold tailWord_690863
  simp only [CollatzResearch.WordTrace]
  refine ⟨25197843696128815851845243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16798562464085877234563495 25197843696128815851845243)
  ·
    refine ⟨37796765544193223777767865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25197843696128815851845243 37796765544193223777767865)
    ·
      refine ⟨28347574158144917833325899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37796765544193223777767865 28347574158144917833325899)
      ·
        refine ⟨42521361237217376749988849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28347574158144917833325899 42521361237217376749988849)
        ·
          refine ⟨31891020927913032562491637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42521361237217376749988849 31891020927913032562491637)
          ·
            refine ⟨2989783211991846802733591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 31891020927913032562491637 2989783211991846802733591)
            ·
              refine ⟨4484674817987770204100387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2989783211991846802733591 4484674817987770204100387)
              ·
                refine ⟨6727012226981655306150581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4484674817987770204100387 6727012226981655306150581)
                ·
                  refine ⟨630657396279530184951617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 6727012226981655306150581 630657396279530184951617)
                  ·
                    refine ⟨472993047209647638713713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 630657396279530184951617 472993047209647638713713)
                    ·
                      refine ⟨354744785407235729035285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 472993047209647638713713 354744785407235729035285)
                      ·
                        rfl

theorem cell23_690863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 1, 1, 5, 2, 2].length) (baseStart_690863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_690863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_690863 prefixEnd_690863 := by exact prefixLift 690863
  have htrace : WordTrace (prefixWord ++ tailWord_690863) baseStart_690863 baseEnd_690863 := by
    simpa [prefixWord, tailWord_690863, baseEnd_690863] using wordTrace_append hprefix tailTrace_690863
  have hstable : (prefixWord ++ tailWord_690863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_690863).length < 2 ^ (prefixWord ++ tailWord_690863).sum := by decide
  have hdescent : baseEnd_690863 < baseStart_690863 := by decide
  rcases family_descends (prefixWord ++ tailWord_690863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_690876 : List Nat := [2, 2, 2, 3, 1, 1, 1, 4, 1, 2, 4]
def baseStart_690876 : Nat := 118140960795 + 690876 * 2 ^ 59
def prefixEnd_690876 : Nat := 4983230072969 + 3 ^ 40 * 690876 * 2
def baseEnd_690876 : Nat := 354751460655744178172725

theorem tailTrace_690876 : CollatzResearch.WordTrace tailWord_690876 prefixEnd_690876 354751460655744178172725 := by
  unfold tailWord_690876
  simp only [CollatzResearch.WordTrace]
  refine ⟨12599158922540859536034241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16798878563387812714712321 12599158922540859536034241)
  ·
    refine ⟨9449369191905644652025681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12599158922540859536034241 9449369191905644652025681)
    ·
      refine ⟨7087026893929233489019261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9449369191905644652025681 7087026893929233489019261)
      ·
        refine ⟨2657635085223462558382223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7087026893929233489019261 2657635085223462558382223)
        ·
          refine ⟨3986452627835193837573335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2657635085223462558382223 3986452627835193837573335)
          ·
            refine ⟨5979678941752790756360003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3986452627835193837573335 5979678941752790756360003)
            ·
              refine ⟨8969518412629186134540005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5979678941752790756360003 8969518412629186134540005)
              ·
                refine ⟨1681784702367972400226251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8969518412629186134540005 1681784702367972400226251)
                ·
                  refine ⟨2522677053551958600339377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1681784702367972400226251 2522677053551958600339377)
                  ·
                    refine ⟨1892007790163968950254533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2522677053551958600339377 1892007790163968950254533)
                    ·
                      refine ⟨354751460655744178172725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1892007790163968950254533 354751460655744178172725)
                      ·
                        rfl

theorem cell23_690876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 1, 4, 1, 2, 4].length) (baseStart_690876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_690876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_690876 prefixEnd_690876 := by exact prefixLift 690876
  have htrace : WordTrace (prefixWord ++ tailWord_690876) baseStart_690876 baseEnd_690876 := by
    simpa [prefixWord, tailWord_690876, baseEnd_690876] using wordTrace_append hprefix tailTrace_690876
  have hstable : (prefixWord ++ tailWord_690876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_690876).length < 2 ^ (prefixWord ++ tailWord_690876).sum := by decide
  have hdescent : baseEnd_690876 < baseStart_690876 := by decide
  rcases family_descends (prefixWord ++ tailWord_690876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_690880 : List Nat := [2, 1, 1, 2, 4, 4, 2, 1, 1, 1, 4]
def baseStart_690880 : Nat := 118140960795 + 690880 * 2 ^ 59
def prefixEnd_690880 : Nat := 4983230072969 + 3 ^ 40 * 690880 * 2
def baseEnd_690880 : Nat := 354753514578362162522707

theorem tailTrace_690880 : CollatzResearch.WordTrace tailWord_690880 prefixEnd_690880 354753514578362162522707 := by
  unfold tailWord_690880
  simp only [CollatzResearch.WordTrace]
  refine ⟨12599231868533613877607047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16798975824711485170142729 12599231868533613877607047)
  ·
    refine ⟨18898847802800420816410571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12599231868533613877607047 18898847802800420816410571)
    ·
      refine ⟨28348271704200631224615857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18898847802800420816410571 28348271704200631224615857)
      ·
        refine ⟨21261203778150473418461893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28348271704200631224615857 21261203778150473418461893)
        ·
          refine ⟨3986475708403213765961605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21261203778150473418461893 3986475708403213765961605)
          ·
            refine ⟨747464195325602581117801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3986475708403213765961605 747464195325602581117801)
            ·
              refine ⟨560598146494201935838351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 747464195325602581117801 560598146494201935838351)
              ·
                refine ⟨840897219741302903757527, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 560598146494201935838351 840897219741302903757527)
                ·
                  refine ⟨1261345829611954355636291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 840897219741302903757527 1261345829611954355636291)
                  ·
                    refine ⟨1892018744417931533454437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1261345829611954355636291 1892018744417931533454437)
                    ·
                      refine ⟨354753514578362162522707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1892018744417931533454437 354753514578362162522707)
                      ·
                        rfl

theorem cell23_690880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 4, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 4, 2, 1, 1, 1, 4].length) (baseStart_690880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_690880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_690880 prefixEnd_690880 := by exact prefixLift 690880
  have htrace : WordTrace (prefixWord ++ tailWord_690880) baseStart_690880 baseEnd_690880 := by
    simpa [prefixWord, tailWord_690880, baseEnd_690880] using wordTrace_append hprefix tailTrace_690880
  have hstable : (prefixWord ++ tailWord_690880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_690880).length < 2 ^ (prefixWord ++ tailWord_690880).sum := by decide
  have hdescent : baseEnd_690880 < baseStart_690880 := by decide
  rcases family_descends (prefixWord ++ tailWord_690880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_690890 : List Nat := [3, 1, 2, 1, 4, 3, 1, 2, 2, 4]
def baseStart_690890 : Nat := 118140960795 + 690890 * 2 ^ 59
def prefixEnd_690890 : Nat := 4983230072969 + 3 ^ 40 * 690890 * 2
def baseEnd_690890 : Nat := 118252883128302374465887

theorem tailTrace_690890 : CollatzResearch.WordTrace tailWord_690890 prefixEnd_690890 118252883128302374465887 := by
  unfold tailWord_690890
  simp only [CollatzResearch.WordTrace]
  refine ⟨6299707116757749865769531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16799218978020666308718749 6299707116757749865769531)
  ·
    refine ⟨9449560675136624798654297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6299707116757749865769531 9449560675136624798654297)
    ·
      refine ⟨7087170506352468598990723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9449560675136624798654297 7087170506352468598990723)
      ·
        refine ⟨10630755759528702898486085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7087170506352468598990723 10630755759528702898486085)
        ·
          refine ⟨1993266704911631793466141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10630755759528702898486085 1993266704911631793466141)
          ·
            refine ⟨747475014341861922549803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1993266704911631793466141 747475014341861922549803)
            ·
              refine ⟨1121212521512792883824705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 747475014341861922549803 1121212521512792883824705)
              ·
                refine ⟨840909391134594662868529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1121212521512792883824705 840909391134594662868529)
                ·
                  refine ⟨630682043350945997151397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 840909391134594662868529 630682043350945997151397)
                  ·
                    refine ⟨118252883128302374465887, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 630682043350945997151397 118252883128302374465887)
                    ·
                      rfl

theorem cell23_690890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 3, 1, 2, 2, 4].length) (baseStart_690890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_690890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_690890 prefixEnd_690890 := by exact prefixLift 690890
  have htrace : WordTrace (prefixWord ++ tailWord_690890) baseStart_690890 baseEnd_690890 := by
    simpa [prefixWord, tailWord_690890, baseEnd_690890] using wordTrace_append hprefix tailTrace_690890
  have hstable : (prefixWord ++ tailWord_690890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_690890).length < 2 ^ (prefixWord ++ tailWord_690890).sum := by decide
  have hdescent : baseEnd_690890 < baseStart_690890 := by decide
  rcases family_descends (prefixWord ++ tailWord_690890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_690913 : List Nat := [1, 2, 3, 1, 4, 1, 3, 1, 1, 3, 3]
def baseStart_690913 : Nat := 118140960795 + 690913 * 2 ^ 59
def prefixEnd_690913 : Nat := 4983230072969 + 3 ^ 40 * 690913 * 2
def baseEnd_690913 : Nat := 354770459439960533410055

theorem tailTrace_690913 : CollatzResearch.WordTrace tailWord_690913 prefixEnd_690913 354770459439960533410055 := by
  unfold tailWord_690913
  simp only [CollatzResearch.WordTrace]
  refine ⟨25199667345947674391165393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16799778230631782927443595 25199667345947674391165393)
  ·
    refine ⟨18899750509460755793374045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25199667345947674391165393 18899750509460755793374045)
    ·
      refine ⟨7087406441047783422515267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18899750509460755793374045 7087406441047783422515267)
      ·
        refine ⟨10631109661571675133772901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7087406441047783422515267 10631109661571675133772901)
        ·
          refine ⟨1993333061544689087582419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10631109661571675133772901 1993333061544689087582419)
          ·
            refine ⟨2989999592317033631373629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1993333061544689087582419 2989999592317033631373629)
            ·
              refine ⟨1121249847118887611765111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2989999592317033631373629 1121249847118887611765111)
              ·
                refine ⟨1681874770678331417647667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1121249847118887611765111 1681874770678331417647667)
                ·
                  refine ⟨2522812156017497126471501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1681874770678331417647667 2522812156017497126471501)
                  ·
                    refine ⟨946054558506561422426813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2522812156017497126471501 946054558506561422426813)
                    ·
                      refine ⟨354770459439960533410055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 946054558506561422426813 354770459439960533410055)
                      ·
                        rfl

theorem cell23_690913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 3, 1, 1, 3, 3].length) (baseStart_690913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_690913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_690913 prefixEnd_690913 := by exact prefixLift 690913
  have htrace : WordTrace (prefixWord ++ tailWord_690913) baseStart_690913 baseEnd_690913 := by
    simpa [prefixWord, tailWord_690913, baseEnd_690913] using wordTrace_append hprefix tailTrace_690913
  have hstable : (prefixWord ++ tailWord_690913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_690913).length < 2 ^ (prefixWord ++ tailWord_690913).sum := by decide
  have hdescent : baseEnd_690913 < baseStart_690913 := by decide
  rcases family_descends (prefixWord ++ tailWord_690913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_690920 : List Nat := [2, 1, 4, 1, 5, 1, 2, 7]
def baseStart_690920 : Nat := 118140960795 + 690920 * 2 ^ 59
def prefixEnd_690920 : Nat := 4983230072969 + 3 ^ 40 * 690920 * 2
def baseEnd_690920 : Nat := 13139779770538592815649

theorem tailTrace_690920 : CollatzResearch.WordTrace tailWord_690920 prefixEnd_690920 13139779770538592815649 := by
  unfold tailWord_690920
  simp only [CollatzResearch.WordTrace]
  refine ⟨12599961328461157293335107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16799948437948209724446809 12599961328461157293335107)
  ·
    refine ⟨18899941992691735940002661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12599961328461157293335107 18899941992691735940002661)
    ·
      refine ⟨3543739123629700488750499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18899941992691735940002661 3543739123629700488750499)
      ·
        refine ⟨5315608685444550733125749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3543739123629700488750499 5315608685444550733125749)
        ·
          refine ⟨498338314260426631230539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 5315608685444550733125749 498338314260426631230539)
          ·
            refine ⟨747507471390639946845809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 498338314260426631230539 747507471390639946845809)
            ·
              refine ⟨560630603542979960134357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 747507471390639946845809 560630603542979960134357)
              ·
                refine ⟨13139779770538592815649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 560630603542979960134357 13139779770538592815649)
                ·
                  rfl

theorem cell23_690920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 5, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 5, 1, 2, 7].length) (baseStart_690920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_690920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_690920 prefixEnd_690920 := by exact prefixLift 690920
  have htrace : WordTrace (prefixWord ++ tailWord_690920) baseStart_690920 baseEnd_690920 := by
    simpa [prefixWord, tailWord_690920, baseEnd_690920] using wordTrace_append hprefix tailTrace_690920
  have hstable : (prefixWord ++ tailWord_690920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_690920).length < 2 ^ (prefixWord ++ tailWord_690920).sum := by decide
  have hdescent : baseEnd_690920 < baseStart_690920 := by decide
  rcases family_descends (prefixWord ++ tailWord_690920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_690926 : List Nat := [4, 1, 2, 1, 1, 3, 1, 1, 2, 2, 5]
def baseStart_690926 : Nat := 118140960795 + 690926 * 2 ^ 59
def prefixEnd_690926 : Nat := 4983230072969 + 3 ^ 40 * 690926 * 2
def baseEnd_690926 : Nat := 354777134688468982547495

theorem tailTrace_690926 : CollatzResearch.WordTrace tailWord_690926 prefixEnd_690926 354777134688468982547495 := by
  unfold tailWord_690926
  simp only [CollatzResearch.WordTrace]
  refine ⟨3150017686862572201423579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 16800094329933718407592421 3150017686862572201423579)
  ·
    refine ⟨4725026530293858302135369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3150017686862572201423579 4725026530293858302135369)
    ·
      refine ⟨3543769897720393726601527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4725026530293858302135369 3543769897720393726601527)
      ·
        refine ⟨5315654846580590589902291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3543769897720393726601527 5315654846580590589902291)
        ·
          refine ⟨7973482269870885884853437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5315654846580590589902291 7973482269870885884853437)
          ·
            refine ⟨2990055851201582206820039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7973482269870885884853437 2990055851201582206820039)
            ·
              refine ⟨4485083776802373310230059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2990055851201582206820039 4485083776802373310230059)
              ·
                refine ⟨6727625665203559965345089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4485083776802373310230059 6727625665203559965345089)
                ·
                  refine ⟨5045719248902669974008817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6727625665203559965345089 5045719248902669974008817)
                  ·
                    refine ⟨3784289436677002480506613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5045719248902669974008817 3784289436677002480506613)
                    ·
                      refine ⟨354777134688468982547495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3784289436677002480506613 354777134688468982547495)
                      ·
                        rfl

theorem cell23_690926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 1, 1, 2, 2, 5].length) (baseStart_690926 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_690926 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_690926 prefixEnd_690926 := by exact prefixLift 690926
  have htrace : WordTrace (prefixWord ++ tailWord_690926) baseStart_690926 baseEnd_690926 := by
    simpa [prefixWord, tailWord_690926, baseEnd_690926] using wordTrace_append hprefix tailTrace_690926
  have hstable : (prefixWord ++ tailWord_690926).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_690926).length < 2 ^ (prefixWord ++ tailWord_690926).sum := by decide
  have hdescent : baseEnd_690926 < baseStart_690926 := by decide
  rcases family_descends (prefixWord ++ tailWord_690926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_690940 : List Nat := [2, 2, 2, 1, 3, 2, 2, 3, 1, 3, 2]
def baseStart_690940 : Nat := 118140960795 + 690940 * 2 ^ 59
def prefixEnd_690940 : Nat := 4983230072969 + 3 ^ 40 * 690940 * 2
def baseEnd_690940 : Nat := 354784323417631927772431

theorem tailTrace_690940 : CollatzResearch.WordTrace tailWord_690940 prefixEnd_690940 354784323417631927772431 := by
  unfold tailWord_690940
  simp only [CollatzResearch.WordTrace]
  refine ⟨12600326058424929001199137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16800434744566572001598849 12600326058424929001199137)
  ·
    refine ⟨9450244543818696750899353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12600326058424929001199137 9450244543818696750899353)
    ·
      refine ⟨7087683407864022563174515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9450244543818696750899353 7087683407864022563174515)
      ·
        refine ⟨10631525111796033844761773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7087683407864022563174515 10631525111796033844761773)
        ·
          refine ⟨3986821916923512691785665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10631525111796033844761773 3986821916923512691785665)
          ·
            refine ⟨2990116437692634518839249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3986821916923512691785665 2990116437692634518839249)
            ·
              refine ⟨2242587328269475889129437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2990116437692634518839249 2242587328269475889129437)
              ·
                refine ⟨840970248101053458423539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2242587328269475889129437 840970248101053458423539)
                ·
                  refine ⟨1261455372151580187635309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 840970248101053458423539 1261455372151580187635309)
                  ·
                    refine ⟨473045764556842570363241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1261455372151580187635309 473045764556842570363241)
                    ·
                      refine ⟨354784323417631927772431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 473045764556842570363241 354784323417631927772431)
                      ·
                        rfl

theorem cell23_690940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 2, 3, 1, 3, 2].length) (baseStart_690940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_690940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_690940 prefixEnd_690940 := by exact prefixLift 690940
  have htrace : WordTrace (prefixWord ++ tailWord_690940) baseStart_690940 baseEnd_690940 := by
    simpa [prefixWord, tailWord_690940, baseEnd_690940] using wordTrace_append hprefix tailTrace_690940
  have hstable : (prefixWord ++ tailWord_690940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_690940).length < 2 ^ (prefixWord ++ tailWord_690940).sum := by decide
  have hdescent : baseEnd_690940 < baseStart_690940 := by decide
  rcases family_descends (prefixWord ++ tailWord_690940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_690956 : List Nat := [2, 2, 1, 2, 2, 1, 1, 3, 2, 4, 3]
def baseStart_690956 : Nat := 118140960795 + 690956 * 2 ^ 59
def prefixEnd_690956 : Nat := 4983230072969 + 3 ^ 40 * 690956 * 2
def baseEnd_690956 : Nat := 354792539108103865172357

theorem tailTrace_690956 : CollatzResearch.WordTrace tailWord_690956 prefixEnd_690956 354792539108103865172357 := by
  unfold tailWord_690956
  simp only [CollatzResearch.WordTrace]
  refine ⟨12600617842395946367490361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16800823789861261823320481 12600617842395946367490361)
  ·
    refine ⟨9450463381796959775617771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12600617842395946367490361 9450463381796959775617771)
    ·
      refine ⟨14175695072695439663426657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9450463381796959775617771 14175695072695439663426657)
      ·
        refine ⟨10631771304521579747569993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14175695072695439663426657 10631771304521579747569993)
        ·
          refine ⟨7973828478391184810677495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10631771304521579747569993 7973828478391184810677495)
          ·
            refine ⟨11960742717586777216016243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7973828478391184810677495 11960742717586777216016243)
            ·
              refine ⟨17941114076380165824024365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11960742717586777216016243 17941114076380165824024365)
              ·
                refine ⟨6727917778642562184009137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17941114076380165824024365 6727917778642562184009137)
                ·
                  refine ⟨5045938333981921638006853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6727917778642562184009137 5045938333981921638006853)
                  ·
                    refine ⟨946113437621610307126285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5045938333981921638006853 946113437621610307126285)
                    ·
                      refine ⟨354792539108103865172357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 946113437621610307126285 354792539108103865172357)
                      ·
                        rfl

theorem cell23_690956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 3, 2, 4, 3].length) (baseStart_690956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_690956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_690956 prefixEnd_690956 := by exact prefixLift 690956
  have htrace : WordTrace (prefixWord ++ tailWord_690956) baseStart_690956 baseEnd_690956 := by
    simpa [prefixWord, tailWord_690956, baseEnd_690956] using wordTrace_append hprefix tailTrace_690956
  have hstable : (prefixWord ++ tailWord_690956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_690956).length < 2 ^ (prefixWord ++ tailWord_690956).sum := by decide
  have hdescent : baseEnd_690956 < baseStart_690956 := by decide
  rcases family_descends (prefixWord ++ tailWord_690956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_690993 : List Nat := [1, 2, 2, 3, 2, 1, 2, 5, 5]
def baseStart_690993 : Nat := 118140960795 + 690993 * 2 ^ 59
def prefixEnd_690993 : Nat := 4983230072969 + 3 ^ 40 * 690993 * 2
def baseEnd_690993 : Nat := 39423504210257802267743

theorem tailTrace_690993 : CollatzResearch.WordTrace tailWord_690993 prefixEnd_690993 39423504210257802267743 := by
  unfold tailWord_690993
  simp only [CollatzResearch.WordTrace]
  refine ⟨25202585185657848054077633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16801723457105232036051755 25202585185657848054077633)
  ·
    refine ⟨18901938889243386040558225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25202585185657848054077633 18901938889243386040558225)
    ·
      refine ⟨14176454166932539530418669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18901938889243386040558225 14176454166932539530418669)
      ·
        refine ⟨5316170312599702323907001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14176454166932539530418669 5316170312599702323907001)
        ·
          refine ⟨3987127734449776742930251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5316170312599702323907001 3987127734449776742930251)
          ·
            refine ⟨5980691601674665114395377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3987127734449776742930251 5980691601674665114395377)
            ·
              refine ⟨4485518701255998835796533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5980691601674665114395377 4485518701255998835796533)
              ·
                refine ⟨420517378242749890855925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4485518701255998835796533 420517378242749890855925)
                ·
                  refine ⟨39423504210257802267743, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 420517378242749890855925 39423504210257802267743)
                  ·
                    rfl

theorem cell23_690993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 2, 5, 5].length) (baseStart_690993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_690993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_690993 prefixEnd_690993 := by exact prefixLift 690993
  have htrace : WordTrace (prefixWord ++ tailWord_690993) baseStart_690993 baseEnd_690993 := by
    simpa [prefixWord, tailWord_690993, baseEnd_690993] using wordTrace_append hprefix tailTrace_690993
  have hstable : (prefixWord ++ tailWord_690993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_690993).length < 2 ^ (prefixWord ++ tailWord_690993).sum := by decide
  have hdescent : baseEnd_690993 < baseStart_690993 := by decide
  rcases family_descends (prefixWord ++ tailWord_690993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_691016 : List Nat := [2, 1, 3, 1, 1, 3, 1, 3, 1, 2, 5]
def baseStart_691016 : Nat := 118140960795 + 691016 * 2 ^ 59
def prefixEnd_691016 : Nat := 4983230072969 + 3 ^ 40 * 691016 * 2
def baseEnd_691016 : Nat := 354823347947373630422081

theorem tailTrace_691016 : CollatzResearch.WordTrace tailWord_691016 prefixEnd_691016 354823347947373630422081 := by
  unfold tailWord_691016
  simp only [CollatzResearch.WordTrace]
  refine ⟨12601712032287261491082451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16802282709716348654776601 12601712032287261491082451)
  ·
    refine ⟨18902568048430892236623677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12601712032287261491082451 18902568048430892236623677)
    ·
      refine ⟨7088463018161584588733879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18902568048430892236623677 7088463018161584588733879)
      ·
        refine ⟨10632694527242376883100819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7088463018161584588733879 10632694527242376883100819)
        ·
          refine ⟨15949041790863565324651229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10632694527242376883100819 15949041790863565324651229)
          ·
            refine ⟨5980890671573836996744211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15949041790863565324651229 5980890671573836996744211)
            ·
              refine ⟨8971336007360755495116317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5980890671573836996744211 8971336007360755495116317)
              ·
                refine ⟨3364251002760283310668619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8971336007360755495116317 3364251002760283310668619)
                ·
                  refine ⟨5046376504140424966002929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3364251002760283310668619 5046376504140424966002929)
                  ·
                    refine ⟨3784782378105318724502197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5046376504140424966002929 3784782378105318724502197)
                    ·
                      refine ⟨354823347947373630422081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3784782378105318724502197 354823347947373630422081)
                      ·
                        rfl

theorem cell23_691016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 1, 3, 1, 2, 5].length) (baseStart_691016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_691016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_691016 prefixEnd_691016 := by exact prefixLift 691016
  have htrace : WordTrace (prefixWord ++ tailWord_691016) baseStart_691016 baseEnd_691016 := by
    simpa [prefixWord, tailWord_691016, baseEnd_691016] using wordTrace_append hprefix tailTrace_691016
  have hstable : (prefixWord ++ tailWord_691016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_691016).length < 2 ^ (prefixWord ++ tailWord_691016).sum := by decide
  have hdescent : baseEnd_691016 < baseStart_691016 := by decide
  rcases family_descends (prefixWord ++ tailWord_691016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_691043 : List Nat := [1, 1, 1, 5, 3, 2, 1, 1, 1, 3, 4]
def baseStart_691043 : Nat := 118140960795 + 691043 * 2 ^ 59
def prefixEnd_691043 : Nat := 4983230072969 + 3 ^ 40 * 691043 * 2
def baseEnd_691043 : Nat := 354837211925045024784457

theorem tailTrace_691043 : CollatzResearch.WordTrace tailWord_691043 prefixEnd_691043 354837211925045024784457 := by
  unfold tailWord_691043
  simp only [CollatzResearch.WordTrace]
  refine ⟨25204408835476706593397783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16802939223651137728931855 25204408835476706593397783)
  ·
    refine ⟨37806613253215059890096675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25204408835476706593397783 37806613253215059890096675)
    ·
      refine ⟨56709919879822589835145013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37806613253215059890096675 56709919879822589835145013)
      ·
        refine ⟨5316554988733367797044845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 56709919879822589835145013 5316554988733367797044845)
        ·
          refine ⟨1993708120775012923891817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5316554988733367797044845 1993708120775012923891817)
          ·
            refine ⟨1495281090581259692918863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1993708120775012923891817 1495281090581259692918863)
            ·
              refine ⟨2242921635871889539378295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1495281090581259692918863 2242921635871889539378295)
              ·
                refine ⟨3364382453807834309067443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2242921635871889539378295 3364382453807834309067443)
                ·
                  refine ⟨5046573680711751463601165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3364382453807834309067443 5046573680711751463601165)
                  ·
                    refine ⟨1892465130266906798850437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5046573680711751463601165 1892465130266906798850437)
                    ·
                      refine ⟨354837211925045024784457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1892465130266906798850437 354837211925045024784457)
                      ·
                        rfl

theorem cell23_691043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 2, 1, 1, 1, 3, 4].length) (baseStart_691043 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_691043 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_691043 prefixEnd_691043 := by exact prefixLift 691043
  have htrace : WordTrace (prefixWord ++ tailWord_691043) baseStart_691043 baseEnd_691043 := by
    simpa [prefixWord, tailWord_691043, baseEnd_691043] using wordTrace_append hprefix tailTrace_691043
  have hstable : (prefixWord ++ tailWord_691043).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_691043).length < 2 ^ (prefixWord ++ tailWord_691043).sum := by decide
  have hdescent : baseEnd_691043 < baseStart_691043 := by decide
  rcases family_descends (prefixWord ++ tailWord_691043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_691053 : List Nat := [1, 5, 1, 1, 1, 1, 1, 1, 7, 4]
def baseStart_691053 : Nat := 118140960795 + 691053 * 2 ^ 59
def prefixEnd_691053 : Nat := 4983230072969 + 3 ^ 40 * 691053 * 2
def baseEnd_691053 : Nat := 118280782243863328553137

theorem tailTrace_691053 : CollatzResearch.WordTrace tailWord_691053 prefixEnd_691053 118280782243863328553137 := by
  unfold tailWord_691053
  simp only [CollatzResearch.WordTrace]
  refine ⟨25204773565440478301261813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16803182376960318867507875 25204773565440478301261813)
  ·
    refine ⟨2362947521760044840743295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 25204773565440478301261813 2362947521760044840743295)
    ·
      refine ⟨3544421282640067261114943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2362947521760044840743295 3544421282640067261114943)
      ·
        refine ⟨5316631923960100891672415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3544421282640067261114943 5316631923960100891672415)
        ·
          refine ⟨7974947885940151337508623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5316631923960100891672415 7974947885940151337508623)
          ·
            refine ⟨11962421828910227006262935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7974947885940151337508623 11962421828910227006262935)
            ·
              refine ⟨17943632743365340509394403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11962421828910227006262935 17943632743365340509394403)
              ·
                refine ⟨26915449115048010764091605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17943632743365340509394403 26915449115048010764091605)
                ·
                  refine ⟨630830838633937752283397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 26915449115048010764091605 630830838633937752283397)
                  ·
                    refine ⟨118280782243863328553137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 630830838633937752283397 118280782243863328553137)
                    ·
                      rfl

theorem cell23_691053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 1, 7, 4].length) (baseStart_691053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_691053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_691053 prefixEnd_691053 := by exact prefixLift 691053
  have htrace : WordTrace (prefixWord ++ tailWord_691053) baseStart_691053 baseEnd_691053 := by
    simpa [prefixWord, tailWord_691053, baseEnd_691053] using wordTrace_append hprefix tailTrace_691053
  have hstable : (prefixWord ++ tailWord_691053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_691053).length < 2 ^ (prefixWord ++ tailWord_691053).sum := by decide
  have hdescent : baseEnd_691053 < baseStart_691053 := by decide
  rcases family_descends (prefixWord ++ tailWord_691053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_691056 : List Nat := [2, 1, 1, 1, 4, 1, 3, 1, 2, 1, 6]
def baseStart_691056 : Nat := 118140960795 + 691056 * 2 ^ 59
def prefixEnd_691056 : Nat := 4983230072969 + 3 ^ 40 * 691056 * 2
def baseEnd_691056 : Nat := 354843887173553473921897

theorem tailTrace_691056 : CollatzResearch.WordTrace tailWord_691056 prefixEnd_691056 354843887173553473921897 := by
  unfold tailWord_691056
  simp only [CollatzResearch.WordTrace]
  refine ⟨12602441492214804906810511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16803255322953073209080681 12602441492214804906810511)
  ·
    refine ⟨18903662238322207360215767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12602441492214804906810511 18903662238322207360215767)
    ·
      refine ⟨28355493357483311040323651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18903662238322207360215767 28355493357483311040323651)
      ·
        refine ⟨42533240036224966560485477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28355493357483311040323651 42533240036224966560485477)
        ·
          refine ⟨7974982506792181230091027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 42533240036224966560485477 7974982506792181230091027)
          ·
            refine ⟨11962473760188271845136541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7974982506792181230091027 11962473760188271845136541)
            ·
              refine ⟨4485927660070601941926203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11962473760188271845136541 4485927660070601941926203)
              ·
                refine ⟨6728891490105902912889305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4485927660070601941926203 6728891490105902912889305)
                ·
                  refine ⟨5046668617579427184666979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6728891490105902912889305 5046668617579427184666979)
                  ·
                    refine ⟨7570002926369140777000469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5046668617579427184666979 7570002926369140777000469)
                    ·
                      refine ⟨354843887173553473921897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 7570002926369140777000469 354843887173553473921897)
                      ·
                        rfl

theorem cell23_691056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 3, 1, 2, 1, 6].length) (baseStart_691056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_691056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_691056 prefixEnd_691056 := by exact prefixLift 691056
  have htrace : WordTrace (prefixWord ++ tailWord_691056) baseStart_691056 baseEnd_691056 := by
    simpa [prefixWord, tailWord_691056, baseEnd_691056] using wordTrace_append hprefix tailTrace_691056
  have hstable : (prefixWord ++ tailWord_691056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_691056).length < 2 ^ (prefixWord ++ tailWord_691056).sum := by decide
  have hdescent : baseEnd_691056 < baseStart_691056 := by decide
  rcases family_descends (prefixWord ++ tailWord_691056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_691063 : List Nat := [1, 1, 3, 1, 1, 2, 1, 6, 2, 2, 3]
def baseStart_691063 : Nat := 118140960795 + 691063 * 2 ^ 59
def prefixEnd_691063 : Nat := 4983230072969 + 3 ^ 40 * 691063 * 2
def baseEnd_691063 : Nat := 354847481538134946534365

theorem tailTrace_691063 : CollatzResearch.WordTrace tailWord_691063 prefixEnd_691063 354847481538134946534365 := by
  unfold tailWord_691063
  simp only [CollatzResearch.WordTrace]
  refine ⟨25205138295404250009125843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16803425530269500006083895 25205138295404250009125843)
  ·
    refine ⟨37807707443106375013688765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25205138295404250009125843 37807707443106375013688765)
    ·
      refine ⟨14177890291164890630133287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37807707443106375013688765 14177890291164890630133287)
      ·
        refine ⟨21266835436747335945199931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14177890291164890630133287 21266835436747335945199931)
        ·
          refine ⟨31900253155121003917799897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21266835436747335945199931 31900253155121003917799897)
          ·
            refine ⟨23925189866340752938349923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31900253155121003917799897 23925189866340752938349923)
            ·
              refine ⟨35887784799511129407524885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23925189866340752938349923 35887784799511129407524885)
              ·
                refine ⟨1682239912477084190977729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 35887784799511129407524885 1682239912477084190977729)
                ·
                  refine ⟨1261679934357813143233297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1682239912477084190977729 1261679934357813143233297)
                  ·
                    refine ⟨946259950768359857424973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1261679934357813143233297 946259950768359857424973)
                    ·
                      refine ⟨354847481538134946534365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 946259950768359857424973 354847481538134946534365)
                      ·
                        rfl

theorem cell23_691063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 6, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 6, 2, 2, 3].length) (baseStart_691063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_691063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_691063 prefixEnd_691063 := by exact prefixLift 691063
  have htrace : WordTrace (prefixWord ++ tailWord_691063) baseStart_691063 baseEnd_691063 := by
    simpa [prefixWord, tailWord_691063, baseEnd_691063] using wordTrace_append hprefix tailTrace_691063
  have hstable : (prefixWord ++ tailWord_691063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_691063).length < 2 ^ (prefixWord ++ tailWord_691063).sum := by decide
  have hdescent : baseEnd_691063 < baseStart_691063 := by decide
  rcases family_descends (prefixWord ++ tailWord_691063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_691113 : List Nat := [1, 2, 1, 1, 1, 1, 5, 5, 1, 5]
def baseStart_691113 : Nat := 118140960795 + 691113 * 2 ^ 59
def prefixEnd_691113 : Nat := 4983230072969 + 3 ^ 40 * 691113 * 2
def baseEnd_691113 : Nat := 118291051856953250303045

theorem tailTrace_691113 : CollatzResearch.WordTrace tailWord_691113 prefixEnd_691113 118291051856953250303045 := by
  unfold tailWord_691113
  simp only [CollatzResearch.WordTrace]
  refine ⟨25206961945223108548445993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16804641296815405698963995 25206961945223108548445993)
  ·
    refine ⟨18905221458917331411334495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25206961945223108548445993 18905221458917331411334495)
    ·
      refine ⟨28357832188375997117001743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18905221458917331411334495 28357832188375997117001743)
      ·
        refine ⟨42536748282563995675502615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28357832188375997117001743 42536748282563995675502615)
        ·
          refine ⟨63805122423845993513253923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42536748282563995675502615 63805122423845993513253923)
          ·
            refine ⟨95707683635768990269880885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63805122423845993513253923 95707683635768990269880885)
            ·
              refine ⟨8972595340853342837801333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 95707683635768990269880885 8972595340853342837801333)
              ·
                refine ⟨841180813205000891043875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8972595340853342837801333 841180813205000891043875)
                ·
                  refine ⟨1261771219807501336565813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 841180813205000891043875 1261771219807501336565813)
                  ·
                    refine ⟨118291051856953250303045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1261771219807501336565813 118291051856953250303045)
                    ·
                      rfl

theorem cell23_691113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 5, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 5, 5, 1, 5].length) (baseStart_691113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_691113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_691113 prefixEnd_691113 := by exact prefixLift 691113
  have htrace : WordTrace (prefixWord ++ tailWord_691113) baseStart_691113 baseEnd_691113 := by
    simpa [prefixWord, tailWord_691113, baseEnd_691113] using wordTrace_append hprefix tailTrace_691113
  have hstable : (prefixWord ++ tailWord_691113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_691113).length < 2 ^ (prefixWord ++ tailWord_691113).sum := by decide
  have hdescent : baseEnd_691113 < baseStart_691113 := by decide
  rcases family_descends (prefixWord ++ tailWord_691113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_691127 : List Nat := [1, 1, 3, 1, 3, 1, 2, 6, 1, 1, 3]
def baseStart_691127 : Nat := 118140960795 + 691127 * 2 ^ 59
def prefixEnd_691127 : Nat := 4983230072969 + 3 ^ 40 * 691127 * 2
def baseEnd_691127 : Nat := 354880344300022696134071

theorem tailTrace_691127 : CollatzResearch.WordTrace tailWord_691127 prefixEnd_691127 354880344300022696134071 := by
  unfold tailWord_691127
  simp only [CollatzResearch.WordTrace]
  refine ⟨25207472567172388939455635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16804981711448259292970423 25207472567172388939455635)
  ·
    refine ⟨37811208850758583409183453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25207472567172388939455635 37811208850758583409183453)
    ·
      refine ⟨14179203319034468778443795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37811208850758583409183453 14179203319034468778443795)
      ·
        refine ⟨21268804978551703167665693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14179203319034468778443795 21268804978551703167665693)
        ·
          refine ⟨7975801866956888687874635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21268804978551703167665693 7975801866956888687874635)
          ·
            refine ⟨11963702800435333031811953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7975801866956888687874635 11963702800435333031811953)
            ·
              refine ⟨8972777100326499773858965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11963702800435333031811953 8972777100326499773858965)
              ·
                refine ⟨420598926577804676899639, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 8972777100326499773858965 420598926577804676899639)
                ·
                  refine ⟨630898389866707015349459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 420598926577804676899639 630898389866707015349459)
                  ·
                    refine ⟨946347584800060523024189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 630898389866707015349459 946347584800060523024189)
                    ·
                      refine ⟨354880344300022696134071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 946347584800060523024189 354880344300022696134071)
                      ·
                        rfl

theorem cell23_691127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 2, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 2, 6, 1, 1, 3].length) (baseStart_691127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_691127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_691127 prefixEnd_691127 := by exact prefixLift 691127
  have htrace : WordTrace (prefixWord ++ tailWord_691127) baseStart_691127 baseEnd_691127 := by
    simpa [prefixWord, tailWord_691127, baseEnd_691127] using wordTrace_append hprefix tailTrace_691127
  have hstable : (prefixWord ++ tailWord_691127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_691127).length < 2 ^ (prefixWord ++ tailWord_691127).sum := by decide
  have hdescent : baseEnd_691127 < baseStart_691127 := by decide
  rcases family_descends (prefixWord ++ tailWord_691127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_691150 : List Nat := [4, 1, 1, 1, 2, 4, 1, 1, 3, 1, 4]
def baseStart_691150 : Nat := 118140960795 + 691150 * 2 ^ 59
def prefixEnd_691150 : Nat := 4983230072969 + 3 ^ 40 * 691150 * 2
def baseEnd_691150 : Nat := 354892154355076106146465

theorem tailTrace_691150 : CollatzResearch.WordTrace tailWord_691150 prefixEnd_691150 354892154355076106146465 := by
  unfold tailWord_691150
  simp only [CollatzResearch.WordTrace]
  refine ⟨3151038930761132983442863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 16805540964059375911695269 3151038930761132983442863)
  ·
    refine ⟨4726558396141699475164295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3151038930761132983442863 4726558396141699475164295)
    ·
      refine ⟨7089837594212549212746443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4726558396141699475164295 7089837594212549212746443)
      ·
        refine ⟨10634756391318823819119665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7089837594212549212746443 10634756391318823819119665)
        ·
          refine ⟨7976067293489117864339749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10634756391318823819119665 7976067293489117864339749)
          ·
            refine ⟨1495512617529209599563703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7976067293489117864339749 1495512617529209599563703)
            ·
              refine ⟨2243268926293814399345555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1495512617529209599563703 2243268926293814399345555)
              ·
                refine ⟨3364903389440721599018333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2243268926293814399345555 3364903389440721599018333)
                ·
                  refine ⟨1261838771040270599631875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3364903389440721599018333 1261838771040270599631875)
                  ·
                    refine ⟨1892758156560405899447813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1261838771040270599631875 1892758156560405899447813)
                    ·
                      refine ⟨354892154355076106146465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1892758156560405899447813 354892154355076106146465)
                      ·
                        rfl

theorem cell23_691150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 4, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 4, 1, 1, 3, 1, 4].length) (baseStart_691150 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_691150 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_691150 prefixEnd_691150 := by exact prefixLift 691150
  have htrace : WordTrace (prefixWord ++ tailWord_691150) baseStart_691150 baseEnd_691150 := by
    simpa [prefixWord, tailWord_691150, baseEnd_691150] using wordTrace_append hprefix tailTrace_691150
  have hstable : (prefixWord ++ tailWord_691150).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_691150).length < 2 ^ (prefixWord ++ tailWord_691150).sum := by decide
  have hdescent : baseEnd_691150 < baseStart_691150 := by decide
  rcases family_descends (prefixWord ++ tailWord_691150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_691154 : List Nat := [3, 2, 2, 3, 1, 2, 2, 1, 2, 3, 2]
def baseStart_691154 : Nat := 118140960795 + 691154 * 2 ^ 59
def prefixEnd_691154 : Nat := 4983230072969 + 3 ^ 40 * 691154 * 2
def baseEnd_691154 : Nat := 354894208277694090496447

theorem tailTrace_691154 : CollatzResearch.WordTrace tailWord_691154 prefixEnd_691154 354894208277694090496447 := by
  unfold tailWord_691154
  simp only [CollatzResearch.WordTrace]
  refine ⟨6302114334518643137672129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16805638225383048367125677 6302114334518643137672129)
  ·
    refine ⟨4726585750888982353254097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6302114334518643137672129 4726585750888982353254097)
    ·
      refine ⟨3544939313166736764940573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4726585750888982353254097 3544939313166736764940573)
      ·
        refine ⟨1329352242437526286852715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3544939313166736764940573 1329352242437526286852715)
        ·
          refine ⟨1994028363656289430279073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1329352242437526286852715 1994028363656289430279073)
          ·
            refine ⟨1495521272742217072709305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1994028363656289430279073 1495521272742217072709305)
            ·
              refine ⟨1121640954556662804531979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1495521272742217072709305 1121640954556662804531979)
              ·
                refine ⟨1682461431834994206797969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1121640954556662804531979 1682461431834994206797969)
                ·
                  refine ⟨1261846073876245655098477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1682461431834994206797969 1261846073876245655098477)
                  ·
                    refine ⟨473192277703592120661929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1261846073876245655098477 473192277703592120661929)
                    ·
                      refine ⟨354894208277694090496447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 473192277703592120661929 354894208277694090496447)
                      ·
                        rfl

theorem cell23_691154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 2, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 2, 2, 1, 2, 3, 2].length) (baseStart_691154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_691154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_691154 prefixEnd_691154 := by exact prefixLift 691154
  have htrace : WordTrace (prefixWord ++ tailWord_691154) baseStart_691154 baseEnd_691154 := by
    simpa [prefixWord, tailWord_691154, baseEnd_691154] using wordTrace_append hprefix tailTrace_691154
  have hstable : (prefixWord ++ tailWord_691154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_691154).length < 2 ^ (prefixWord ++ tailWord_691154).sum := by decide
  have hdescent : baseEnd_691154 < baseStart_691154 := by decide
  rcases family_descends (prefixWord ++ tailWord_691154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_691173 : List Nat := [1, 3, 1, 6, 12]
def baseStart_691173 : Nat := 118140960795 + 691173 * 2 ^ 59
def prefixEnd_691173 : Nat := 4983230072969 + 3 ^ 40 * 691173 * 2
def baseEnd_691173 : Nat := 486836713868490419971

theorem tailTrace_691173 : CollatzResearch.WordTrace tailWord_691173 prefixEnd_691173 486836713868490419971 := by
  unfold tailWord_691173
  simp only [CollatzResearch.WordTrace]
  refine ⟨25209150325005738795630173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16806100216670492530420115 25209150325005738795630173)
  ·
    refine ⟨9453431371877152048361315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25209150325005738795630173 9453431371877152048361315)
    ·
      refine ⟨14180147057815728072541973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9453431371877152048361315 14180147057815728072541973)
      ·
        refine ⟨664694393335112253400405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 14180147057815728072541973 664694393335112253400405)
        ·
          refine ⟨486836713868490419971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 12 664694393335112253400405 486836713868490419971)
          ·
            rfl

theorem cell23_691173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 12].length) (baseStart_691173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_691173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_691173 prefixEnd_691173 := by exact prefixLift 691173
  have htrace : WordTrace (prefixWord ++ tailWord_691173) baseStart_691173 baseEnd_691173 := by
    simpa [prefixWord, tailWord_691173, baseEnd_691173] using wordTrace_append hprefix tailTrace_691173
  have hstable : (prefixWord ++ tailWord_691173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_691173).length < 2 ^ (prefixWord ++ tailWord_691173).sum := by decide
  have hdescent : baseEnd_691173 < baseStart_691173 := by decide
  rcases family_descends (prefixWord ++ tailWord_691173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_691190 : List Nat := [5, 1, 1, 1, 3, 1, 3, 8]
def baseStart_691190 : Nat := 118140960795 + 691190 * 2 ^ 59
def prefixEnd_691190 : Nat := 4983230072969 + 3 ^ 40 * 691190 * 2
def baseEnd_691190 : Nat := 13144914577083553690603

theorem tailTrace_691190 : CollatzResearch.WordTrace tailWord_691190 prefixEnd_691190 13144914577083553690603 := by
  unfold tailWord_691190
  simp only [CollatzResearch.WordTrace]
  refine ⟨1575610647871509418687439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 16806513577296100465999349 1575610647871509418687439)
  ·
    refine ⟨2363415971807264128031159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1575610647871509418687439 2363415971807264128031159)
    ·
      refine ⟨3545123957710896192046739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2363415971807264128031159 3545123957710896192046739)
      ·
        refine ⟨5317685936566344288070109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3545123957710896192046739 5317685936566344288070109)
        ·
          refine ⟨1994132226212379108026291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5317685936566344288070109 1994132226212379108026291)
          ·
            refine ⟨2991198339318568662039437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1994132226212379108026291 2991198339318568662039437)
            ·
              refine ⟨1121699377244463248264789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2991198339318568662039437 1121699377244463248264789)
              ·
                refine ⟨13144914577083553690603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1121699377244463248264789 13144914577083553690603)
                ·
                  rfl

theorem cell23_691190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 3, 8].length) (baseStart_691190 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_691190 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_691190 prefixEnd_691190 := by exact prefixLift 691190
  have htrace : WordTrace (prefixWord ++ tailWord_691190) baseStart_691190 baseEnd_691190 := by
    simpa [prefixWord, tailWord_691190, baseEnd_691190] using wordTrace_append hprefix tailTrace_691190
  have hstable : (prefixWord ++ tailWord_691190).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_691190).length < 2 ^ (prefixWord ++ tailWord_691190).sum := by decide
  have hdescent : baseEnd_691190 < baseStart_691190 := by decide
  rcases family_descends (prefixWord ++ tailWord_691190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_691234 : List Nat := [3, 3, 1, 1, 1, 3, 3, 2, 2, 1, 3]
def baseStart_691234 : Nat := 118140960795 + 691234 * 2 ^ 59
def prefixEnd_691234 : Nat := 4983230072969 + 3 ^ 40 * 691234 * 2
def baseEnd_691234 : Nat := 354935286730053777496079

theorem tailTrace_691234 : CollatzResearch.WordTrace tailWord_691234 prefixEnd_691234 354935286730053777496079 := by
  unfold tailWord_691234
  simp only [CollatzResearch.WordTrace]
  refine ⟨6302843794446186553400189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16807583451856497475733837 6302843794446186553400189)
  ·
    refine ⟨2363566422917319957525071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6302843794446186553400189 2363566422917319957525071)
    ·
      refine ⟨3545349634375979936287607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2363566422917319957525071 3545349634375979936287607)
      ·
        refine ⟨5318024451563969904431411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3545349634375979936287607 5318024451563969904431411)
        ·
          refine ⟨7977036677345954856647117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5318024451563969904431411 7977036677345954856647117)
          ·
            refine ⟨2991388754004733071242669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7977036677345954856647117 2991388754004733071242669)
            ·
              refine ⟨1121770782751774901716001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2991388754004733071242669 1121770782751774901716001)
              ·
                refine ⟨841328087063831176287001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1121770782751774901716001 841328087063831176287001)
                ·
                  refine ⟨630996065297873382215251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 841328087063831176287001 630996065297873382215251)
                  ·
                    refine ⟨946494097946810073322877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 630996065297873382215251 946494097946810073322877)
                    ·
                      refine ⟨354935286730053777496079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 946494097946810073322877 354935286730053777496079)
                      ·
                        rfl

theorem cell23_691234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 3, 2, 2, 1, 3].length) (baseStart_691234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_691234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_691234 prefixEnd_691234 := by exact prefixLift 691234
  have htrace : WordTrace (prefixWord ++ tailWord_691234) baseStart_691234 baseEnd_691234 := by
    simpa [prefixWord, tailWord_691234, baseEnd_691234] using wordTrace_append hprefix tailTrace_691234
  have hstable : (prefixWord ++ tailWord_691234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_691234).length < 2 ^ (prefixWord ++ tailWord_691234).sum := by decide
  have hdescent : baseEnd_691234 < baseStart_691234 := by decide
  rcases family_descends (prefixWord ++ tailWord_691234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_691277 : List Nat := [1, 6, 1, 1, 1, 3, 1, 1, 2, 1, 5]
def baseStart_691277 : Nat := 118140960795 + 691277 * 2 ^ 59
def prefixEnd_691277 : Nat := 4983230072969 + 3 ^ 40 * 691277 * 2
def baseEnd_691277 : Nat := 354957366398197109258381

theorem tailTrace_691277 : CollatzResearch.WordTrace tailWord_691277 prefixEnd_691277 354957366398197109258381 := by
  unfold tailWord_691277
  simp only [CollatzResearch.WordTrace]
  refine ⟨25212943516628964557416085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16808629011085976371610723 25212943516628964557416085)
  ·
    refine ⟨1181856727341982713628879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 25212943516628964557416085 1181856727341982713628879)
    ·
      refine ⟨1772785091012974070443319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1181856727341982713628879 1772785091012974070443319)
      ·
        refine ⟨2659177636519461105664979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1772785091012974070443319 2659177636519461105664979)
        ·
          refine ⟨3988766454779191658497469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2659177636519461105664979 3988766454779191658497469)
          ·
            refine ⟨1495787420542196871936551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3988766454779191658497469 1495787420542196871936551)
            ·
              refine ⟨2243681130813295307904827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1495787420542196871936551 2243681130813295307904827)
              ·
                refine ⟨3365521696219942961857241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2243681130813295307904827 3365521696219942961857241)
                ·
                  refine ⟨2524141272164957221392931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3365521696219942961857241 2524141272164957221392931)
                  ·
                    refine ⟨3786211908247435832089397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2524141272164957221392931 3786211908247435832089397)
                    ·
                      refine ⟨354957366398197109258381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3786211908247435832089397 354957366398197109258381)
                      ·
                        rfl

theorem cell23_691277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 3, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 3, 1, 1, 2, 1, 5].length) (baseStart_691277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_691277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_691277 prefixEnd_691277 := by exact prefixLift 691277
  have htrace : WordTrace (prefixWord ++ tailWord_691277) baseStart_691277 baseEnd_691277 := by
    simpa [prefixWord, tailWord_691277, baseEnd_691277] using wordTrace_append hprefix tailTrace_691277
  have hstable : (prefixWord ++ tailWord_691277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_691277).length < 2 ^ (prefixWord ++ tailWord_691277).sum := by decide
  have hdescent : baseEnd_691277 < baseStart_691277 := by decide
  rcases family_descends (prefixWord ++ tailWord_691277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_691290 : List Nat := [3, 1, 1, 2, 1, 1, 2, 4, 2, 3, 3]
def baseStart_691290 : Nat := 118140960795 + 691290 * 2 ^ 59
def prefixEnd_691290 : Nat := 4983230072969 + 3 ^ 40 * 691290 * 2
def baseEnd_691290 : Nat := 354964041646705558395821

theorem tailTrace_691290 : CollatzResearch.WordTrace tailWord_691290 prefixEnd_691290 354964041646705558395821 := by
  unfold tailWord_691290
  simp only [CollatzResearch.WordTrace]
  refine ⟨6303354416395466944409831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16808945110387911851759549 6303354416395466944409831)
  ·
    refine ⟨9455031624593200416614747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6303354416395466944409831 9455031624593200416614747)
    ·
      refine ⟨14182547436889800624922121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9455031624593200416614747 14182547436889800624922121)
      ·
        refine ⟨10636910577667350468691591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14182547436889800624922121 10636910577667350468691591)
        ·
          refine ⟨15955365866501025703037387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10636910577667350468691591 15955365866501025703037387)
          ·
            refine ⟨23933048799751538554556081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15955365866501025703037387 23933048799751538554556081)
            ·
              refine ⟨17949786599813653915917061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23933048799751538554556081 17949786599813653915917061)
              ·
                refine ⟨3365584987465060109234449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17949786599813653915917061 3365584987465060109234449)
                ·
                  refine ⟨2524188740598795081925837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3365584987465060109234449 2524188740598795081925837)
                  ·
                    refine ⟨946570777724548155722189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2524188740598795081925837 946570777724548155722189)
                    ·
                      refine ⟨354964041646705558395821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 946570777724548155722189 354964041646705558395821)
                      ·
                        rfl

theorem cell23_691290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 4, 2, 3, 3].length) (baseStart_691290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_691290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_691290 prefixEnd_691290 := by exact prefixLift 691290
  have htrace : WordTrace (prefixWord ++ tailWord_691290) baseStart_691290 baseEnd_691290 := by
    simpa [prefixWord, tailWord_691290, baseEnd_691290] using wordTrace_append hprefix tailTrace_691290
  have hstable : (prefixWord ++ tailWord_691290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_691290).length < 2 ^ (prefixWord ++ tailWord_691290).sum := by decide
  have hdescent : baseEnd_691290 < baseStart_691290 := by decide
  rcases family_descends (prefixWord ++ tailWord_691290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_691323 : List Nat := [1, 1, 1, 1, 1, 4, 1, 3, 2, 8]
def baseStart_691323 : Nat := 118140960795 + 691323 * 2 ^ 59
def prefixEnd_691323 : Nat := 4983230072969 + 3 ^ 40 * 691323 * 2
def baseEnd_691323 : Nat := 118326995502767976427723

theorem tailTrace_691323 : CollatzResearch.WordTrace tailWord_691323 prefixEnd_691323 118326995502767976427723 := by
  unfold tailWord_691323
  simp only [CollatzResearch.WordTrace]
  refine ⟨25214621274462314413590623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16809747516308209609060415 25214621274462314413590623)
  ·
    refine ⟨37821931911693471620385935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25214621274462314413590623 37821931911693471620385935)
    ·
      refine ⟨56732897867540207430578903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37821931911693471620385935 56732897867540207430578903)
      ·
        refine ⟨85099346801310311145868355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56732897867540207430578903 85099346801310311145868355)
        ·
          refine ⟨127649020201965466718802533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85099346801310311145868355 127649020201965466718802533)
          ·
            refine ⟨23934191287868525009775475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 127649020201965466718802533 23934191287868525009775475)
            ·
              refine ⟨35901286931802787514663213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23934191287868525009775475 35901286931802787514663213)
              ·
                refine ⟨13462982599426045317998705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35901286931802787514663213 13462982599426045317998705)
                ·
                  refine ⟨10097236949569533988499029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13462982599426045317998705 10097236949569533988499029)
                  ·
                    refine ⟨118326995502767976427723, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 10097236949569533988499029 118326995502767976427723)
                    ·
                      rfl

theorem cell23_691323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 3, 2, 8].length) (baseStart_691323 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_691323 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_691323 prefixEnd_691323 := by exact prefixLift 691323
  have htrace : WordTrace (prefixWord ++ tailWord_691323) baseStart_691323 baseEnd_691323 := by
    simpa [prefixWord, tailWord_691323, baseEnd_691323] using wordTrace_append hprefix tailTrace_691323
  have hstable : (prefixWord ++ tailWord_691323).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_691323).length < 2 ^ (prefixWord ++ tailWord_691323).sum := by decide
  have hdescent : baseEnd_691323 < baseStart_691323 := by decide
  rcases family_descends (prefixWord ++ tailWord_691323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_691357 : List Nat := [1, 4, 2, 1, 1, 2, 2, 3, 3, 4]
def baseStart_691357 : Nat := 118140960795 + 691357 * 2 ^ 59
def prefixEnd_691357 : Nat := 4983230072969 + 3 ^ 40 * 691357 * 2
def baseEnd_691357 : Nat := 118332814950185598752671

theorem tailTrace_691357 : CollatzResearch.WordTrace tailWord_691357 prefixEnd_691357 118332814950185598752671 := by
  unfold tailWord_691357
  simp only [CollatzResearch.WordTrace]
  refine ⟨25215861356339138220328325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16810574237559425480218883 25215861356339138220328325)
  ·
    refine ⟨4727974004313588416311561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 25215861356339138220328325 4727974004313588416311561)
    ·
      refine ⟨3545980503235191312233671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4727974004313588416311561 3545980503235191312233671)
      ·
        refine ⟨5318970754852786968350507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3545980503235191312233671 5318970754852786968350507)
        ·
          refine ⟨7978456132279180452525761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5318970754852786968350507 7978456132279180452525761)
          ·
            refine ⟨5983842099209385339394321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7978456132279180452525761 5983842099209385339394321)
            ·
              refine ⟨4487881574407039004545741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5983842099209385339394321 4487881574407039004545741)
              ·
                refine ⟨1682955590402639626704653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4487881574407039004545741 1682955590402639626704653)
                ·
                  refine ⟨631108346400989860014245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1682955590402639626704653 631108346400989860014245)
                  ·
                    refine ⟨118332814950185598752671, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 631108346400989860014245 118332814950185598752671)
                    ·
                      rfl

theorem cell23_691357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 2, 3, 3, 4].length) (baseStart_691357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_691357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_691357 prefixEnd_691357 := by exact prefixLift 691357
  have htrace : WordTrace (prefixWord ++ tailWord_691357) baseStart_691357 baseEnd_691357 := by
    simpa [prefixWord, tailWord_691357, baseEnd_691357] using wordTrace_append hprefix tailTrace_691357
  have hstable : (prefixWord ++ tailWord_691357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_691357).length < 2 ^ (prefixWord ++ tailWord_691357).sum := by decide
  have hdescent : baseEnd_691357 < baseStart_691357 := by decide
  rcases family_descends (prefixWord ++ tailWord_691357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_691364 : List Nat := [2, 3, 1, 2, 3, 2, 1, 1, 2, 4, 2]
def baseStart_691364 : Nat := 118140960795 + 691364 * 2 ^ 59
def prefixEnd_691364 : Nat := 4983230072969 + 3 ^ 40 * 691364 * 2
def baseEnd_691364 : Nat := 355002039215138268870481

theorem tailTrace_691364 : CollatzResearch.WordTrace tailWord_691364 prefixEnd_691364 355002039215138268870481 := by
  unfold tailWord_691364
  simp only [CollatzResearch.WordTrace]
  refine ⟨12608058333656889207916573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16810744444875852277222097 12608058333656889207916573)
  ·
    refine ⟨4728021875121333452968715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12608058333656889207916573 4728021875121333452968715)
    ·
      refine ⟨7092032812682000179453073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4728021875121333452968715 7092032812682000179453073)
      ·
        refine ⟨5319024609511500134589805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7092032812682000179453073 5319024609511500134589805)
        ·
          refine ⟨1994634228566812550471177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5319024609511500134589805 1994634228566812550471177)
          ·
            refine ⟨1495975671425109412853383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1994634228566812550471177 1495975671425109412853383)
            ·
              refine ⟨2243963507137664119280075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1495975671425109412853383 2243963507137664119280075)
              ·
                refine ⟨3365945260706496178920113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2243963507137664119280075 3365945260706496178920113)
                ·
                  refine ⟨2524458945529872134190085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3365945260706496178920113 2524458945529872134190085)
                  ·
                    refine ⟨473336052286851025160641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2524458945529872134190085 473336052286851025160641)
                    ·
                      refine ⟨355002039215138268870481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 473336052286851025160641 355002039215138268870481)
                      ·
                        rfl

theorem cell23_691364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 2, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 2, 1, 1, 2, 4, 2].length) (baseStart_691364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_691364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_691364 prefixEnd_691364 := by exact prefixLift 691364
  have htrace : WordTrace (prefixWord ++ tailWord_691364) baseStart_691364 baseEnd_691364 := by
    simpa [prefixWord, tailWord_691364, baseEnd_691364] using wordTrace_append hprefix tailTrace_691364
  have hstable : (prefixWord ++ tailWord_691364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_691364).length < 2 ^ (prefixWord ++ tailWord_691364).sum := by decide
  have hdescent : baseEnd_691364 < baseStart_691364 := by decide
  rcases family_descends (prefixWord ++ tailWord_691364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_691397 : List Nat := [1, 3, 1, 1, 1, 1, 3, 1, 7, 1, 3]
def baseStart_691397 : Nat := 118140960795 + 691397 * 2 ^ 59
def prefixEnd_691397 : Nat := 4983230072969 + 3 ^ 40 * 691397 * 2
def baseEnd_691397 : Nat := 355018984076736639757829

theorem tailTrace_691397 : CollatzResearch.WordTrace tailWord_691397 prefixEnd_691397 355018984076736639757829 := by
  unfold tailWord_691397
  simp only [CollatzResearch.WordTrace]
  refine ⟨25217320276194225051784445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16811546850796150034522963 25217320276194225051784445)
  ·
    refine ⟨9456495103572834394419167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25217320276194225051784445 9456495103572834394419167)
    ·
      refine ⟨14184742655359251591628751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9456495103572834394419167 14184742655359251591628751)
      ·
        refine ⟨21277113983038877387443127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14184742655359251591628751 21277113983038877387443127)
        ·
          refine ⟨31915670974558316081164691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21277113983038877387443127 31915670974558316081164691)
          ·
            refine ⟨47873506461837474121747037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31915670974558316081164691 47873506461837474121747037)
            ·
              refine ⟨17952564923189052795655139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 47873506461837474121747037 17952564923189052795655139)
              ·
                refine ⟨26928847384783579193482709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17952564923189052795655139 26928847384783579193482709)
                ·
                  refine ⟨631144860580865137347251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 26928847384783579193482709 631144860580865137347251)
                  ·
                    refine ⟨946717290871297706020877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 631144860580865137347251 946717290871297706020877)
                    ·
                      refine ⟨355018984076736639757829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 946717290871297706020877 355018984076736639757829)
                      ·
                        rfl

theorem cell23_691397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 1, 7, 1, 3].length) (baseStart_691397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_691397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_691397 prefixEnd_691397 := by exact prefixLift 691397
  have htrace : WordTrace (prefixWord ++ tailWord_691397) baseStart_691397 baseEnd_691397 := by
    simpa [prefixWord, tailWord_691397, baseEnd_691397] using wordTrace_append hprefix tailTrace_691397
  have hstable : (prefixWord ++ tailWord_691397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_691397).length < 2 ^ (prefixWord ++ tailWord_691397).sum := by decide
  have hdescent : baseEnd_691397 < baseStart_691397 := by decide
  rcases family_descends (prefixWord ++ tailWord_691397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_691421 : List Nat := [1, 4, 3, 2, 2, 1, 3, 1, 6]
def baseStart_691421 : Nat := 118140960795 + 691421 * 2 ^ 59
def prefixEnd_691421 : Nat := 4983230072969 + 3 ^ 40 * 691421 * 2
def baseEnd_691421 : Nat := 39447923068049393984191

theorem tailTrace_691421 : CollatzResearch.WordTrace tailWord_691421 prefixEnd_691421 39447923068049393984191 := by
  unfold tailWord_691421
  simp only [CollatzResearch.WordTrace]
  refine ⟨25218195628107277150658117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16812130418738184767105411 25218195628107277150658117)
  ·
    refine ⟨4728411680270114465748397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 25218195628107277150658117 4728411680270114465748397)
    ·
      refine ⟨1773154380101292924655649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4728411680270114465748397 1773154380101292924655649)
      ·
        refine ⟨1329865785075969693491737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1773154380101292924655649 1329865785075969693491737)
        ·
          refine ⟨997399338806977270118803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1329865785075969693491737 997399338806977270118803)
          ·
            refine ⟨1496099008210465905178205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 997399338806977270118803 1496099008210465905178205)
            ·
              refine ⟨561037128078924714441827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1496099008210465905178205 561037128078924714441827)
              ·
                refine ⟨841555692118387071662741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 561037128078924714441827 841555692118387071662741)
                ·
                  refine ⟨39447923068049393984191, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 841555692118387071662741 39447923068049393984191)
                  ·
                    rfl

theorem cell23_691421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 1, 3, 1, 6].length) (baseStart_691421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_691421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_691421 prefixEnd_691421 := by exact prefixLift 691421
  have htrace : WordTrace (prefixWord ++ tailWord_691421) baseStart_691421 baseEnd_691421 := by
    simpa [prefixWord, tailWord_691421, baseEnd_691421] using wordTrace_append hprefix tailTrace_691421
  have hstable : (prefixWord ++ tailWord_691421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_691421).length < 2 ^ (prefixWord ++ tailWord_691421).sum := by decide
  have hdescent : baseEnd_691421 < baseStart_691421 := by decide
  rcases family_descends (prefixWord ++ tailWord_691421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_691434 : List Nat := [3, 1, 3, 1, 1, 4, 2, 2, 1, 5]
def baseStart_691434 : Nat := 118140960795 + 691434 * 2 ^ 59
def prefixEnd_691434 : Nat := 4983230072969 + 3 ^ 40 * 691434 * 2
def baseEnd_691434 : Nat := 118345994286984331665053

theorem tailTrace_691434 : CollatzResearch.WordTrace tailWord_691434 prefixEnd_691434 118345994286984331665053 := by
  unfold tailWord_691434
  simp only [CollatzResearch.WordTrace]
  refine ⟨6304667444265045092720339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16812446518040120247254237 6304667444265045092720339)
  ·
    refine ⟨9457001166397567639080509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6304667444265045092720339 9457001166397567639080509)
    ·
      refine ⟨3546375437399087864655191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9457001166397567639080509 3546375437399087864655191)
      ·
        refine ⟨5319563156098631796982787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3546375437399087864655191 5319563156098631796982787)
        ·
          refine ⟨7979344734147947695474181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5319563156098631796982787 7979344734147947695474181)
          ·
            refine ⟨1496127137652740192901409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7979344734147947695474181 1496127137652740192901409)
            ·
              refine ⟨1122095353239555144676057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1496127137652740192901409 1122095353239555144676057)
              ·
                refine ⟨841571514929666358507043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1122095353239555144676057 841571514929666358507043)
                ·
                  refine ⟨1262357272394499537760565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 841571514929666358507043 1262357272394499537760565)
                  ·
                    refine ⟨118345994286984331665053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1262357272394499537760565 118345994286984331665053)
                    ·
                      rfl

theorem cell23_691434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 4, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 4, 2, 2, 1, 5].length) (baseStart_691434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_691434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_691434 prefixEnd_691434 := by exact prefixLift 691434
  have htrace : WordTrace (prefixWord ++ tailWord_691434) baseStart_691434 baseEnd_691434 := by
    simpa [prefixWord, tailWord_691434, baseEnd_691434] using wordTrace_append hprefix tailTrace_691434
  have hstable : (prefixWord ++ tailWord_691434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_691434).length < 2 ^ (prefixWord ++ tailWord_691434).sum := by decide
  have hdescent : baseEnd_691434 < baseStart_691434 := by decide
  rcases family_descends (prefixWord ++ tailWord_691434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_691457 : List Nat := [1, 2, 4, 1, 1, 3, 1, 3, 1, 1, 5]
def baseStart_691457 : Nat := 118140960795 + 691457 * 2 ^ 59
def prefixEnd_691457 : Nat := 4983230072969 + 3 ^ 40 * 691457 * 2
def baseEnd_691457 : Nat := 355049792916006405007553

theorem tailTrace_691457 : CollatzResearch.WordTrace tailWord_691457 prefixEnd_691457 355049792916006405007553 := by
  unfold tailWord_691457
  simp only [CollatzResearch.WordTrace]
  refine ⟨25219508655976855298968625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16813005770651236865979083 25219508655976855298968625)
  ·
    refine ⟨18914631491982641474226469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25219508655976855298968625 18914631491982641474226469)
    ·
      refine ⟨3546493404746745276417463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18914631491982641474226469 3546493404746745276417463)
      ·
        refine ⟨5319740107120117914626195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3546493404746745276417463 5319740107120117914626195)
        ·
          refine ⟨7979610160680176871939293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5319740107120117914626195 7979610160680176871939293)
          ·
            refine ⟨2992353810255066326977235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7979610160680176871939293 2992353810255066326977235)
            ·
              refine ⟨4488530715382599490465853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2992353810255066326977235 4488530715382599490465853)
              ·
                refine ⟨1683199018268474808924695, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4488530715382599490465853 1683199018268474808924695)
                ·
                  refine ⟨2524798527402712213387043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1683199018268474808924695 2524798527402712213387043)
                  ·
                    refine ⟨3787197791104068320080565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2524798527402712213387043 3787197791104068320080565)
                    ·
                      refine ⟨355049792916006405007553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3787197791104068320080565 355049792916006405007553)
                      ·
                        rfl

theorem cell23_691457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 1, 3, 1, 1, 5].length) (baseStart_691457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_691457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_691457 prefixEnd_691457 := by exact prefixLift 691457
  have htrace : WordTrace (prefixWord ++ tailWord_691457) baseStart_691457 baseEnd_691457 := by
    simpa [prefixWord, tailWord_691457, baseEnd_691457] using wordTrace_append hprefix tailTrace_691457
  have hstable : (prefixWord ++ tailWord_691457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_691457).length < 2 ^ (prefixWord ++ tailWord_691457).sum := by decide
  have hdescent : baseEnd_691457 < baseStart_691457 := by decide
  rcases family_descends (prefixWord ++ tailWord_691457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_691458 : List Nat := [3, 4, 1, 1, 3, 1, 1, 2, 2, 3, 2]
def baseStart_691458 : Nat := 118140960795 + 691458 * 2 ^ 59
def prefixEnd_691458 : Nat := 4983230072969 + 3 ^ 40 * 691458 * 2
def baseEnd_691458 : Nat := 355050306396660901095049

theorem tailTrace_691458 : CollatzResearch.WordTrace tailWord_691458 prefixEnd_691458 355050306396660901095049 := by
  unfold tailWord_691458
  simp only [CollatzResearch.WordTrace]
  refine ⟨6304886282243308117438757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16813030085982154979836685 6304886282243308117438757)
  ·
    refine ⟨1182166177920620272019767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6304886282243308117438757 1182166177920620272019767)
    ·
      refine ⟨1773249266880930408029651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1182166177920620272019767 1773249266880930408029651)
      ·
        refine ⟨2659873900321395612044477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1773249266880930408029651 2659873900321395612044477)
        ·
          refine ⟨997452712620523354516679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2659873900321395612044477 997452712620523354516679)
          ·
            refine ⟨1496179068930785031775019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 997452712620523354516679 1496179068930785031775019)
            ·
              refine ⟨2244268603396177547662529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1496179068930785031775019 2244268603396177547662529)
              ·
                refine ⟨1683201452547133160746897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2244268603396177547662529 1683201452547133160746897)
                ·
                  refine ⟨1262401089410349870560173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1683201452547133160746897 1262401089410349870560173)
                  ·
                    refine ⟨473400408528881201460065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1262401089410349870560173 473400408528881201460065)
                    ·
                      refine ⟨355050306396660901095049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 473400408528881201460065 355050306396660901095049)
                      ·
                        rfl

theorem cell23_691458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 1, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 1, 1, 2, 2, 3, 2].length) (baseStart_691458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_691458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_691458 prefixEnd_691458 := by exact prefixLift 691458
  have htrace : WordTrace (prefixWord ++ tailWord_691458) baseStart_691458 baseEnd_691458 := by
    simpa [prefixWord, tailWord_691458, baseEnd_691458] using wordTrace_append hprefix tailTrace_691458
  have hstable : (prefixWord ++ tailWord_691458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_691458).length < 2 ^ (prefixWord ++ tailWord_691458).sum := by decide
  have hdescent : baseEnd_691458 < baseStart_691458 := by decide
  rcases family_descends (prefixWord ++ tailWord_691458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_691488 : List Nat := [2, 1, 1, 5, 4, 1, 1, 2, 1, 1, 4]
def baseStart_691488 : Nat := 118140960795 + 691488 * 2 ^ 59
def prefixEnd_691488 : Nat := 4983230072969 + 3 ^ 40 * 691488 * 2
def baseEnd_691488 : Nat := 355065710816295783719911

theorem tailTrace_691488 : CollatzResearch.WordTrace tailWord_691488 prefixEnd_691488 355065710816295783719911 := by
  unfold tailWord_691488
  simp only [CollatzResearch.WordTrace]
  refine ⟨12610319659432273796673559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16813759545909698395564745 12610319659432273796673559)
  ·
    refine ⟨18915479489148410695010339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12610319659432273796673559 18915479489148410695010339)
    ·
      refine ⟨28373219233722616042515509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18915479489148410695010339 28373219233722616042515509)
      ·
        refine ⟨2659989303161495253985829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 28373219233722616042515509 2659989303161495253985829)
        ·
          refine ⟨498747994342780360122343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2659989303161495253985829 498747994342780360122343)
          ·
            refine ⟨748121991514170540183515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 498747994342780360122343 748121991514170540183515)
            ·
              refine ⟨1122182987271255810275273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 748121991514170540183515 1122182987271255810275273)
              ·
                refine ⟨841637240453441857706455, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1122182987271255810275273 841637240453441857706455)
                ·
                  refine ⟨1262455860680162786559683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 841637240453441857706455 1262455860680162786559683)
                  ·
                    refine ⟨1893683791020244179839525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1262455860680162786559683 1893683791020244179839525)
                    ·
                      refine ⟨355065710816295783719911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1893683791020244179839525 355065710816295783719911)
                      ·
                        rfl

theorem cell23_691488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 4, 1, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 4, 1, 1, 2, 1, 1, 4].length) (baseStart_691488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_691488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_691488 prefixEnd_691488 := by exact prefixLift 691488
  have htrace : WordTrace (prefixWord ++ tailWord_691488) baseStart_691488 baseEnd_691488 := by
    simpa [prefixWord, tailWord_691488, baseEnd_691488] using wordTrace_append hprefix tailTrace_691488
  have hstable : (prefixWord ++ tailWord_691488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_691488).length < 2 ^ (prefixWord ++ tailWord_691488).sum := by decide
  have hdescent : baseEnd_691488 < baseStart_691488 := by decide
  rcases family_descends (prefixWord ++ tailWord_691488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_691491 : List Nat := [1, 1, 1, 4, 2, 5, 1, 2, 1, 2, 3]
def baseStart_691491 : Nat := 118140960795 + 691491 * 2 ^ 59
def prefixEnd_691491 : Nat := 4983230072969 + 3 ^ 40 * 691491 * 2
def baseEnd_691491 : Nat := 355067251258259271982397

theorem tailTrace_691491 : CollatzResearch.WordTrace tailWord_691491 prefixEnd_691491 355067251258259271982397 := by
  unfold tailWord_691491
  simp only [CollatzResearch.WordTrace]
  refine ⟨25220748737853679105706327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16813832491902452737137551 25220748737853679105706327)
  ·
    refine ⟨37831123106780518658559491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25220748737853679105706327 37831123106780518658559491)
    ·
      refine ⟨56746684660170777987839237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37831123106780518658559491 56746684660170777987839237)
      ·
        refine ⟨10640003373782020872719857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 56746684660170777987839237 10640003373782020872719857)
        ·
          refine ⟨7980002530336515654539893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10640003373782020872719857 7980002530336515654539893)
          ·
            refine ⟨748125237219048342613115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 7980002530336515654539893 748125237219048342613115)
            ·
              refine ⟨1122187855828572513919673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 748125237219048342613115 1122187855828572513919673)
              ·
                refine ⟨841640891871429385439755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1122187855828572513919673 841640891871429385439755)
                ·
                  refine ⟨1262461337807144078159633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 841640891871429385439755 1262461337807144078159633)
                  ·
                    refine ⟨946846003355358058619725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1262461337807144078159633 946846003355358058619725)
                    ·
                      refine ⟨355067251258259271982397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 946846003355358058619725 355067251258259271982397)
                      ·
                        rfl

theorem cell23_691491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 5, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 5, 1, 2, 1, 2, 3].length) (baseStart_691491 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_691491 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_691491 prefixEnd_691491 := by exact prefixLift 691491
  have htrace : WordTrace (prefixWord ++ tailWord_691491) baseStart_691491 baseEnd_691491 := by
    simpa [prefixWord, tailWord_691491, baseEnd_691491] using wordTrace_append hprefix tailTrace_691491
  have hstable : (prefixWord ++ tailWord_691491).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_691491).length < 2 ^ (prefixWord ++ tailWord_691491).sum := by decide
  have hdescent : baseEnd_691491 < baseStart_691491 := by decide
  rcases family_descends (prefixWord ++ tailWord_691491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_691501 : List Nat := [1, 5, 3, 1, 1, 2, 1, 2, 1, 2, 4]
def baseStart_691501 : Nat := 118140960795 + 691501 * 2 ^ 59
def prefixEnd_691501 : Nat := 4983230072969 + 3 ^ 40 * 691501 * 2
def baseEnd_691501 : Nat := 355072386064804232857351

theorem tailTrace_691501 : CollatzResearch.WordTrace tailWord_691501 prefixEnd_691501 355072386064804232857351 := by
  unfold tailWord_691501
  simp only [CollatzResearch.WordTrace]
  refine ⟨25221113467817450813570357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16814075645211633875713571 25221113467817450813570357)
  ·
    refine ⟨2364479387607886013772221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 25221113467817450813570357 2364479387607886013772221)
    ·
      refine ⟨886679770352957255164583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2364479387607886013772221 886679770352957255164583)
      ·
        refine ⟨1330019655529435882746875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 886679770352957255164583 1330019655529435882746875)
        ·
          refine ⟨1995029483294153824120313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1330019655529435882746875 1995029483294153824120313)
          ·
            refine ⟨1496272112470615368090235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1995029483294153824120313 1496272112470615368090235)
            ·
              refine ⟨2244408168705923052135353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1496272112470615368090235 2244408168705923052135353)
              ·
                refine ⟨1683306126529442289101515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2244408168705923052135353 1683306126529442289101515)
                ·
                  refine ⟨2524959189794163433652273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1683306126529442289101515 2524959189794163433652273)
                  ·
                    refine ⟨1893719392345622575239205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2524959189794163433652273 1893719392345622575239205)
                    ·
                      refine ⟨355072386064804232857351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1893719392345622575239205 355072386064804232857351)
                      ·
                        rfl

theorem cell23_691501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 2, 1, 2, 1, 2, 4].length) (baseStart_691501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_691501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_691501 prefixEnd_691501 := by exact prefixLift 691501
  have htrace : WordTrace (prefixWord ++ tailWord_691501) baseStart_691501 baseEnd_691501 := by
    simpa [prefixWord, tailWord_691501, baseEnd_691501] using wordTrace_append hprefix tailTrace_691501
  have hstable : (prefixWord ++ tailWord_691501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_691501).length < 2 ^ (prefixWord ++ tailWord_691501).sum := by decide
  have hdescent : baseEnd_691501 < baseStart_691501 := by decide
  rcases family_descends (prefixWord ++ tailWord_691501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_691508 : List Nat := [2, 5, 1, 1, 1, 1, 5, 1, 1, 2, 3]
def baseStart_691508 : Nat := 118140960795 + 691508 * 2 ^ 59
def prefixEnd_691508 : Nat := 4983230072969 + 3 ^ 40 * 691508 * 2
def baseEnd_691508 : Nat := 355075980429385705469819

theorem tailTrace_691508 : CollatzResearch.WordTrace tailWord_691508 prefixEnd_691508 355075980429385705469819 := by
  unfold tailWord_691508
  simp only [CollatzResearch.WordTrace]
  refine ⟨12610684389396045504537589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16814245852528060672716785 12610684389396045504537589)
  ·
    refine ⟨1182251661505879266050399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 12610684389396045504537589 1182251661505879266050399)
    ·
      refine ⟨1773377492258818899075599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1182251661505879266050399 1773377492258818899075599)
      ·
        refine ⟨2660066238388228348613399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1773377492258818899075599 2660066238388228348613399)
        ·
          refine ⟨3990099357582342522920099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2660066238388228348613399 3990099357582342522920099)
          ·
            refine ⟨5985149036373513784380149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3990099357582342522920099 5985149036373513784380149)
            ·
              refine ⟨561107722160016917285639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 5985149036373513784380149 561107722160016917285639)
              ·
                refine ⟨841661583240025375928459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 561107722160016917285639 841661583240025375928459)
                ·
                  refine ⟨1262492374860038063892689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 841661583240025375928459 1262492374860038063892689)
                  ·
                    refine ⟨946869281145028547919517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1262492374860038063892689 946869281145028547919517)
                    ·
                      refine ⟨355075980429385705469819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 946869281145028547919517 355075980429385705469819)
                      ·
                        rfl

theorem cell23_691508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 5, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 5, 1, 1, 2, 3].length) (baseStart_691508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_691508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_691508 prefixEnd_691508 := by exact prefixLift 691508
  have htrace : WordTrace (prefixWord ++ tailWord_691508) baseStart_691508 baseEnd_691508 := by
    simpa [prefixWord, tailWord_691508, baseEnd_691508] using wordTrace_append hprefix tailTrace_691508
  have hstable : (prefixWord ++ tailWord_691508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_691508).length < 2 ^ (prefixWord ++ tailWord_691508).sum := by decide
  have hdescent : baseEnd_691508 < baseStart_691508 := by decide
  rcases family_descends (prefixWord ++ tailWord_691508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_691524 : List Nat := [2, 3, 4, 1, 1, 1, 1, 1, 2, 7]
def baseStart_691524 : Nat := 118140960795 + 691524 * 2 ^ 59
def prefixEnd_691524 : Nat := 4983230072969 + 3 ^ 40 * 691524 * 2
def baseEnd_691524 : Nat := 118361398706619214289915

theorem tailTrace_691524 : CollatzResearch.WordTrace tailWord_691524 prefixEnd_691524 118361398706619214289915 := by
  unfold tailWord_691524
  simp only [CollatzResearch.WordTrace]
  refine ⟨12610976173367062870828813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16814634897822750494438417 12610976173367062870828813)
  ·
    refine ⟨4729116065012648576560805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12610976173367062870828813 4729116065012648576560805)
    ·
      refine ⟨886709262189871608105151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4729116065012648576560805 886709262189871608105151)
      ·
        refine ⟨1330063893284807412157727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 886709262189871608105151 1330063893284807412157727)
        ·
          refine ⟨1995095839927211118236591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1330063893284807412157727 1995095839927211118236591)
          ·
            refine ⟨2992643759890816677354887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1995095839927211118236591 2992643759890816677354887)
            ·
              refine ⟨4488965639836225016032331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2992643759890816677354887 4488965639836225016032331)
              ·
                refine ⟨6733448459754337524048497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4488965639836225016032331 6733448459754337524048497)
                ·
                  refine ⟨5050086344815753143036373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6733448459754337524048497 5050086344815753143036373)
                  ·
                    refine ⟨118361398706619214289915, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 5050086344815753143036373 118361398706619214289915)
                    ·
                      rfl

theorem cell23_691524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 1, 1, 2, 7].length) (baseStart_691524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_691524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_691524 prefixEnd_691524 := by exact prefixLift 691524
  have htrace : WordTrace (prefixWord ++ tailWord_691524) baseStart_691524 baseEnd_691524 := by
    simpa [prefixWord, tailWord_691524, baseEnd_691524] using wordTrace_append hprefix tailTrace_691524
  have hstable : (prefixWord ++ tailWord_691524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_691524).length < 2 ^ (prefixWord ++ tailWord_691524).sum := by decide
  have hdescent : baseEnd_691524 < baseStart_691524 := by decide
  rcases family_descends (prefixWord ++ tailWord_691524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_691527 : List Nat := [1, 1, 4, 1, 2, 3, 1, 1, 2, 3, 4]
def baseStart_691527 : Nat := 118140960795 + 691527 * 2 ^ 59
def prefixEnd_691527 : Nat := 4983230072969 + 3 ^ 40 * 691527 * 2
def baseEnd_691527 : Nat := 355085736561821131132231

theorem tailTrace_691527 : CollatzResearch.WordTrace tailWord_691527 prefixEnd_691527 355085736561821131132231 := by
  unfold tailWord_691527
  simp only [CollatzResearch.WordTrace]
  refine ⟨25222061765723257254016835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16814707843815504836011223 25222061765723257254016835)
  ·
    refine ⟨37833092648584885881025253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25222061765723257254016835 37833092648584885881025253)
    ·
      refine ⟨7093704871609666102692235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 37833092648584885881025253 7093704871609666102692235)
      ·
        refine ⟨10640557307414499154038353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7093704871609666102692235 10640557307414499154038353)
        ·
          refine ⟨7980417980560874365528765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10640557307414499154038353 7980417980560874365528765)
          ·
            refine ⟨2992656742710327887073287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7980417980560874365528765 2992656742710327887073287)
            ·
              refine ⟨4488985114065491830609931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2992656742710327887073287 4488985114065491830609931)
              ·
                refine ⟨6733477671098237745914897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4488985114065491830609931 6733477671098237745914897)
                ·
                  refine ⟨5050108253323678309436173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6733477671098237745914897 5050108253323678309436173)
                  ·
                    refine ⟨1893790594996379366038565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5050108253323678309436173 1893790594996379366038565)
                    ·
                      refine ⟨355085736561821131132231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1893790594996379366038565 355085736561821131132231)
                      ·
                        rfl

theorem cell23_691527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 1, 1, 2, 3, 4].length) (baseStart_691527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_691527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_691527 prefixEnd_691527 := by exact prefixLift 691527
  have htrace : WordTrace (prefixWord ++ tailWord_691527) baseStart_691527 baseEnd_691527 := by
    simpa [prefixWord, tailWord_691527, baseEnd_691527] using wordTrace_append hprefix tailTrace_691527
  have hstable : (prefixWord ++ tailWord_691527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_691527).length < 2 ^ (prefixWord ++ tailWord_691527).sum := by decide
  have hdescent : baseEnd_691527 < baseStart_691527 := by decide
  rcases family_descends (prefixWord ++ tailWord_691527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_691537 : List Nat := [1, 2, 2, 1, 4, 1, 3, 1, 2, 6]
def baseStart_691537 : Nat := 118140960795 + 691537 * 2 ^ 59
def prefixEnd_691537 : Nat := 4983230072969 + 3 ^ 40 * 691537 * 2
def baseEnd_691537 : Nat := 118363623789455364002395

theorem tailTrace_691537 : CollatzResearch.WordTrace tailWord_691537 prefixEnd_691537 118363623789455364002395 := by
  unfold tailWord_691537
  simp only [CollatzResearch.WordTrace]
  refine ⟨25222426495687028961880865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16814950997124685974587243 25222426495687028961880865)
  ·
    refine ⟨18916819871765271721410649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25222426495687028961880865 18916819871765271721410649)
    ·
      refine ⟨14187614903823953791057987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18916819871765271721410649 14187614903823953791057987)
      ·
        refine ⟨21281422355735930686586981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14187614903823953791057987 21281422355735930686586981)
        ·
          refine ⟨3990266691700487003735059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21281422355735930686586981 3990266691700487003735059)
          ·
            refine ⟨5985400037550730505602589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3990266691700487003735059 5985400037550730505602589)
            ·
              refine ⟨2244525014081523939600971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5985400037550730505602589 2244525014081523939600971)
              ·
                refine ⟨3366787521122285909401457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2244525014081523939600971 3366787521122285909401457)
                ·
                  refine ⟨2525090640841714432051093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3366787521122285909401457 2525090640841714432051093)
                  ·
                    refine ⟨118363623789455364002395, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2525090640841714432051093 118363623789455364002395)
                    ·
                      rfl

theorem cell23_691537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 3, 1, 2, 6].length) (baseStart_691537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_691537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_691537 prefixEnd_691537 := by exact prefixLift 691537
  have htrace : WordTrace (prefixWord ++ tailWord_691537) baseStart_691537 baseEnd_691537 := by
    simpa [prefixWord, tailWord_691537, baseEnd_691537] using wordTrace_append hprefix tailTrace_691537
  have hstable : (prefixWord ++ tailWord_691537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_691537).length < 2 ^ (prefixWord ++ tailWord_691537).sum := by decide
  have hdescent : baseEnd_691537 < baseStart_691537 := by decide
  rcases family_descends (prefixWord ++ tailWord_691537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_691557 : List Nat := [1, 3, 1, 3, 1, 2, 1, 2, 1, 4, 4]
def baseStart_691557 : Nat := 118140960795 + 691557 * 2 ^ 59
def prefixEnd_691557 : Nat := 4983230072969 + 3 ^ 40 * 691557 * 2
def baseEnd_691557 : Nat := 355101140981456013757093

theorem tailTrace_691557 : CollatzResearch.WordTrace tailWord_691557 prefixEnd_691557 355101140981456013757093 := by
  unfold tailWord_691557
  simp only [CollatzResearch.WordTrace]
  refine ⟨25223155955614572377608925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16815437303743048251739283 25223155955614572377608925)
  ·
    refine ⟨9458683483355464641603347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25223155955614572377608925 9458683483355464641603347)
    ·
      refine ⟨14188025225033196962405021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9458683483355464641603347 14188025225033196962405021)
      ·
        refine ⟨5320509459387448860901883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14188025225033196962405021 5320509459387448860901883)
        ·
          refine ⟨7980764189081173291352825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5320509459387448860901883 7980764189081173291352825)
          ·
            refine ⟨5985573141810879968514619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7980764189081173291352825 5985573141810879968514619)
            ·
              refine ⟨8978359712716319952771929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5985573141810879968514619 8978359712716319952771929)
              ·
                refine ⟨6733769784537239964578947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8978359712716319952771929 6733769784537239964578947)
                ·
                  refine ⟨10100654676805859946868421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6733769784537239964578947 10100654676805859946868421)
                  ·
                    refine ⟨1893872751901098740037829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10100654676805859946868421 1893872751901098740037829)
                    ·
                      refine ⟨355101140981456013757093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1893872751901098740037829 355101140981456013757093)
                      ·
                        rfl

theorem cell23_691557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 1, 2, 1, 4, 4].length) (baseStart_691557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_691557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_691557 prefixEnd_691557 := by exact prefixLift 691557
  have htrace : WordTrace (prefixWord ++ tailWord_691557) baseStart_691557 baseEnd_691557 := by
    simpa [prefixWord, tailWord_691557, baseEnd_691557] using wordTrace_append hprefix tailTrace_691557
  have hstable : (prefixWord ++ tailWord_691557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_691557).length < 2 ^ (prefixWord ++ tailWord_691557).sum := by decide
  have hdescent : baseEnd_691557 < baseStart_691557 := by decide
  rcases family_descends (prefixWord ++ tailWord_691557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_691565 : List Nat := [1, 5, 1, 1, 1, 5, 2, 1, 1, 3, 2]
def baseStart_691565 : Nat := 118140960795 + 691565 * 2 ^ 59
def prefixEnd_691565 : Nat := 4983230072969 + 3 ^ 40 * 691565 * 2
def baseEnd_691565 : Nat := 355105248826691982457057

theorem tailTrace_691565 : CollatzResearch.WordTrace tailWord_691565 prefixEnd_691565 355105248826691982457057 := by
  unfold tailWord_691565
  simp only [CollatzResearch.WordTrace]
  refine ⟨25223447739585589743900149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16815631826390393162600099 25223447739585589743900149)
  ·
    refine ⟨2364698225586149038490639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 25223447739585589743900149 2364698225586149038490639)
    ·
      refine ⟨3547047338379223557735959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2364698225586149038490639 3547047338379223557735959)
      ·
        refine ⟨5320571007568835336603939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3547047338379223557735959 5320571007568835336603939)
        ·
          refine ⟨7980856511353253004905909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5320571007568835336603939 7980856511353253004905909)
          ·
            refine ⟨748205297939367469209929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 7980856511353253004905909 748205297939367469209929)
            ·
              refine ⟨561153973454525601907447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 748205297939367469209929 561153973454525601907447)
              ·
                refine ⟨841730960181788402861171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 561153973454525601907447 841730960181788402861171)
                ·
                  refine ⟨1262596440272682604291757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 841730960181788402861171 1262596440272682604291757)
                  ·
                    refine ⟨473473665102255976609409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1262596440272682604291757 473473665102255976609409)
                    ·
                      refine ⟨355105248826691982457057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 473473665102255976609409 355105248826691982457057)
                      ·
                        rfl

theorem cell23_691565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 5, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 5, 2, 1, 1, 3, 2].length) (baseStart_691565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_691565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_691565 prefixEnd_691565 := by exact prefixLift 691565
  have htrace : WordTrace (prefixWord ++ tailWord_691565) baseStart_691565 baseEnd_691565 := by
    simpa [prefixWord, tailWord_691565, baseEnd_691565] using wordTrace_append hprefix tailTrace_691565
  have hstable : (prefixWord ++ tailWord_691565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_691565).length < 2 ^ (prefixWord ++ tailWord_691565).sum := by decide
  have hdescent : baseEnd_691565 < baseStart_691565 := by decide
  rcases family_descends (prefixWord ++ tailWord_691565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_691607 : List Nat := [1, 1, 3, 3, 1, 1, 1, 2, 3, 2, 5]
def baseStart_691607 : Nat := 118140960795 + 691607 * 2 ^ 59
def prefixEnd_691607 : Nat := 4983230072969 + 3 ^ 40 * 691607 * 2
def baseEnd_691607 : Nat := 355126815014180818131863

theorem tailTrace_691607 : CollatzResearch.WordTrace tailWord_691607 prefixEnd_691607 355126815014180818131863 := by
  unfold tailWord_691607
  simp only [CollatzResearch.WordTrace]
  refine ⟨25224979605433430916929075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16816653070288953944619383 25224979605433430916929075)
  ·
    refine ⟨37837469408150146375393613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25224979605433430916929075 37837469408150146375393613)
    ·
      refine ⟨14189051028056304890772605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37837469408150146375393613 14189051028056304890772605)
      ·
        refine ⟨5320894135521114334039727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14189051028056304890772605 5320894135521114334039727)
        ·
          refine ⟨7981341203281671501059591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5320894135521114334039727 7981341203281671501059591)
          ·
            refine ⟨11972011804922507251589387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7981341203281671501059591 11972011804922507251589387)
            ·
              refine ⟨17958017707383760877384081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11972011804922507251589387 17958017707383760877384081)
              ·
                refine ⟨13468513280537820658038061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17958017707383760877384081 13468513280537820658038061)
                ·
                  refine ⟨5050692480201682746764273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13468513280537820658038061 5050692480201682746764273)
                  ·
                    refine ⟨3788019360151262060073205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5050692480201682746764273 3788019360151262060073205)
                    ·
                      refine ⟨355126815014180818131863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3788019360151262060073205 355126815014180818131863)
                      ·
                        rfl

theorem cell23_691607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 2, 3, 2, 5].length) (baseStart_691607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_691607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_691607 prefixEnd_691607 := by exact prefixLift 691607
  have htrace : WordTrace (prefixWord ++ tailWord_691607) baseStart_691607 baseEnd_691607 := by
    simpa [prefixWord, tailWord_691607, baseEnd_691607] using wordTrace_append hprefix tailTrace_691607
  have hstable : (prefixWord ++ tailWord_691607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_691607).length < 2 ^ (prefixWord ++ tailWord_691607).sum := by decide
  have hdescent : baseEnd_691607 < baseStart_691607 := by decide
  rcases family_descends (prefixWord ++ tailWord_691607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_691618 : List Nat := [3, 3, 1, 2, 1, 4, 1, 3, 5]
def baseStart_691618 : Nat := 118140960795 + 691618 * 2 ^ 59
def prefixEnd_691618 : Nat := 4983230072969 + 3 ^ 40 * 691618 * 2
def baseEnd_691618 : Nat := 39459162589042252788257

theorem tailTrace_691618 : CollatzResearch.WordTrace tailWord_691618 prefixEnd_691618 39459162589042252788257 := by
  unfold tailWord_691618
  simp only [CollatzResearch.WordTrace]
  refine ⟨6306345202098394948894877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 16816920538929053197053005 6306345202098394948894877)
  ·
    refine ⟨2364879450786898105835579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6306345202098394948894877 2364879450786898105835579)
    ·
      refine ⟨3547319176180347158753369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2364879450786898105835579 3547319176180347158753369)
      ·
        refine ⟨2660489382135260369065027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3547319176180347158753369 2660489382135260369065027)
        ·
          refine ⟨3990734073202890553597541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2660489382135260369065027 3990734073202890553597541)
          ·
            refine ⟨748262638725541978799539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3990734073202890553597541 748262638725541978799539)
            ·
              refine ⟨1122393958088312968199309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 748262638725541978799539 1122393958088312968199309)
              ·
                refine ⟨420897734283117363074741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1122393958088312968199309 420897734283117363074741)
                ·
                  refine ⟨39459162589042252788257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 420897734283117363074741 39459162589042252788257)
                  ·
                    rfl

theorem cell23_691618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 4, 1, 3, 5].length) (baseStart_691618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_691618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_691618 prefixEnd_691618 := by exact prefixLift 691618
  have htrace : WordTrace (prefixWord ++ tailWord_691618) baseStart_691618 baseEnd_691618 := by
    simpa [prefixWord, tailWord_691618, baseEnd_691618] using wordTrace_append hprefix tailTrace_691618
  have hstable : (prefixWord ++ tailWord_691618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_691618).length < 2 ^ (prefixWord ++ tailWord_691618).sum := by decide
  have hdescent : baseEnd_691618 < baseStart_691618 := by decide
  rcases family_descends (prefixWord ++ tailWord_691618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_691647 : List Nat := [1, 1, 2, 2, 2, 1, 1, 4, 2, 1, 6]
def baseStart_691647 : Nat := 118140960795 + 691647 * 2 ^ 59
def prefixEnd_691647 : Nat := 4983230072969 + 3 ^ 40 * 691647 * 2
def baseEnd_691647 : Nat := 355147354240360661631679

theorem tailTrace_691647 : CollatzResearch.WordTrace tailWord_691647 prefixEnd_691647 355147354240360661631679 := by
  unfold tailWord_691647
  simp only [CollatzResearch.WordTrace]
  refine ⟨25226438525288517748385195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16817625683525678498923463 25226438525288517748385195)
  ·
    refine ⟨37839657787932776622577793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25226438525288517748385195 37839657787932776622577793)
    ·
      refine ⟨28379743340949582466933345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37839657787932776622577793 28379743340949582466933345)
      ·
        refine ⟨21284807505712186850200009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28379743340949582466933345 21284807505712186850200009)
        ·
          refine ⟨15963605629284140137650007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21284807505712186850200009 15963605629284140137650007)
          ·
            refine ⟨23945408443926210206475011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15963605629284140137650007 23945408443926210206475011)
            ·
              refine ⟨35918112665889315309712517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23945408443926210206475011 35918112665889315309712517)
              ·
                refine ⟨6734646124854246620571097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 35918112665889315309712517 6734646124854246620571097)
                ·
                  refine ⟨5050984593640684965428323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6734646124854246620571097 5050984593640684965428323)
                  ·
                    refine ⟨7576476890461027448142485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5050984593640684965428323 7576476890461027448142485)
                    ·
                      refine ⟨355147354240360661631679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 7576476890461027448142485 355147354240360661631679)
                      ·
                        rfl

theorem cell23_691647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 4, 2, 1, 6].length) (baseStart_691647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_691647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_691647 prefixEnd_691647 := by exact prefixLift 691647
  have htrace : WordTrace (prefixWord ++ tailWord_691647) baseStart_691647 baseEnd_691647 := by
    simpa [prefixWord, tailWord_691647, baseEnd_691647] using wordTrace_append hprefix tailTrace_691647
  have hstable : (prefixWord ++ tailWord_691647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_691647).length < 2 ^ (prefixWord ++ tailWord_691647).sum := by decide
  have hdescent : baseEnd_691647 < baseStart_691647 := by decide
  rcases family_descends (prefixWord ++ tailWord_691647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_691668 : List Nat := [2, 4, 1, 2, 3, 1, 2, 1, 2, 1, 4]
def baseStart_691668 : Nat := 118140960795 + 691668 * 2 ^ 59
def prefixEnd_691668 : Nat := 4983230072969 + 3 ^ 40 * 691668 * 2
def baseEnd_691668 : Nat := 355158137334105079469083

theorem tailTrace_691668 : CollatzResearch.WordTrace tailWord_691668 prefixEnd_691668 355158137334105079469083 := by
  unfold tailWord_691668
  simp only [CollatzResearch.WordTrace]
  refine ⟨12613602229106219167449829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16818136305474958889933105 12613602229106219167449829)
  ·
    refine ⟨2365050417957416093896843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12613602229106219167449829 2365050417957416093896843)
    ·
      refine ⟨3547575626936124140845265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2365050417957416093896843 3547575626936124140845265)
      ·
        refine ⟨2660681720202093105633949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3547575626936124140845265 2660681720202093105633949)
        ·
          refine ⟨997755645075784914612731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2660681720202093105633949 997755645075784914612731)
          ·
            refine ⟨1496633467613677371919097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 997755645075784914612731 1496633467613677371919097)
            ·
              refine ⟨1122475100710258028939323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1496633467613677371919097 1122475100710258028939323)
              ·
                refine ⟨1683712651065387043408985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1122475100710258028939323 1683712651065387043408985)
                ·
                  refine ⟨1262784488299040282556739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1683712651065387043408985 1262784488299040282556739)
                  ·
                    refine ⟨1894176732448560423835109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1262784488299040282556739 1894176732448560423835109)
                    ·
                      refine ⟨355158137334105079469083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1894176732448560423835109 355158137334105079469083)
                      ·
                        rfl

theorem cell23_691668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 1, 2, 1, 2, 1, 4].length) (baseStart_691668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_691668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_691668 prefixEnd_691668 := by exact prefixLift 691668
  have htrace : WordTrace (prefixWord ++ tailWord_691668) baseStart_691668 baseEnd_691668 := by
    simpa [prefixWord, tailWord_691668, baseEnd_691668] using wordTrace_append hprefix tailTrace_691668
  have hstable : (prefixWord ++ tailWord_691668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_691668).length < 2 ^ (prefixWord ++ tailWord_691668).sum := by decide
  have hdescent : baseEnd_691668 < baseStart_691668 := by decide
  rcases family_descends (prefixWord ++ tailWord_691668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_691694 : List Nat := [4, 1, 2, 1, 2, 1, 2, 1, 1, 2, 6]
def baseStart_691694 : Nat := 118140960795 + 691694 * 2 ^ 59
def prefixEnd_691694 : Nat := 4983230072969 + 3 ^ 40 * 691694 * 2
def baseEnd_691694 : Nat := 355171487831121977743963

theorem tailTrace_691694 : CollatzResearch.WordTrace tailWord_691694 prefixEnd_691694 355171487831121977743963 := by
  unfold tailWord_691694
  simp only [CollatzResearch.WordTrace]
  refine ⟨3153519094514780596918267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 16818768504078829850230757 3153519094514780596918267)
  ·
    refine ⟨4730278641772170895377401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3153519094514780596918267 4730278641772170895377401)
    ·
      refine ⟨3547708981329128171533051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4730278641772170895377401 3547708981329128171533051)
      ·
        refine ⟨5321563471993692257299577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3547708981329128171533051 5321563471993692257299577)
        ·
          refine ⟨3991172603995269192974683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5321563471993692257299577 3991172603995269192974683)
          ·
            refine ⟨5986758905992903789462025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3991172603995269192974683 5986758905992903789462025)
            ·
              refine ⟨4490069179494677842096519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5986758905992903789462025 4490069179494677842096519)
              ·
                refine ⟨6735103769242016763144779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4490069179494677842096519 6735103769242016763144779)
                ·
                  refine ⟨10102655653863025144717169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6735103769242016763144779 10102655653863025144717169)
                  ·
                    refine ⟨7576991740397268858537877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10102655653863025144717169 7576991740397268858537877)
                    ·
                      refine ⟨355171487831121977743963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 7576991740397268858537877 355171487831121977743963)
                      ·
                        rfl

theorem cell23_691694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 2, 1, 1, 2, 6].length) (baseStart_691694 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_691694 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_691694 prefixEnd_691694 := by exact prefixLift 691694
  have htrace : WordTrace (prefixWord ++ tailWord_691694) baseStart_691694 baseEnd_691694 := by
    simpa [prefixWord, tailWord_691694, baseEnd_691694] using wordTrace_append hprefix tailTrace_691694
  have hstable : (prefixWord ++ tailWord_691694).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_691694).length < 2 ^ (prefixWord ++ tailWord_691694).sum := by decide
  have hdescent : baseEnd_691694 < baseStart_691694 := by decide
  rcases family_descends (prefixWord ++ tailWord_691694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_691704 : List Nat := [2, 1, 2, 1, 1, 5, 1, 2, 3, 5]
def baseStart_691704 : Nat := 118140960795 + 691704 * 2 ^ 59
def prefixEnd_691704 : Nat := 4983230072969 + 3 ^ 40 * 691704 * 2
def baseEnd_691704 : Nat := 118392207545888979539639

theorem tailTrace_691704 : CollatzResearch.WordTrace tailWord_691704 prefixEnd_691704 118392207545888979539639 := by
  unfold tailWord_691704
  simp only [CollatzResearch.WordTrace]
  refine ⟨12614258743041008241605083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16819011657388010988806777 12614258743041008241605083)
  ·
    refine ⟨18921388114561512362407625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12614258743041008241605083 18921388114561512362407625)
    ·
      refine ⟨14191041085921134271805719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18921388114561512362407625 14191041085921134271805719)
      ·
        refine ⟨21286561628881701407708579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14191041085921134271805719 21286561628881701407708579)
        ·
          refine ⟨31929842443322552111562869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21286561628881701407708579 31929842443322552111562869)
          ·
            refine ⟨2993422729061489260459019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 31929842443322552111562869 2993422729061489260459019)
            ·
              refine ⟨4490134093592233890688529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2993422729061489260459019 4490134093592233890688529)
              ·
                refine ⟨3367600570194175418016397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4490134093592233890688529 3367600570194175418016397)
                ·
                  refine ⟨1262850213822815781756149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3367600570194175418016397 1262850213822815781756149)
                  ·
                    refine ⟨118392207545888979539639, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1262850213822815781756149 118392207545888979539639)
                    ·
                      rfl

theorem cell23_691704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 1, 2, 3, 5].length) (baseStart_691704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_691704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_691704 prefixEnd_691704 := by exact prefixLift 691704
  have htrace : WordTrace (prefixWord ++ tailWord_691704) baseStart_691704 baseEnd_691704 := by
    simpa [prefixWord, tailWord_691704, baseEnd_691704] using wordTrace_append hprefix tailTrace_691704
  have hstable : (prefixWord ++ tailWord_691704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_691704).length < 2 ^ (prefixWord ++ tailWord_691704).sum := by decide
  have hdescent : baseEnd_691704 < baseStart_691704 := by decide
  rcases family_descends (prefixWord ++ tailWord_691704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_691808 : List Nat := [2, 1, 1, 3, 2, 1, 1, 6, 2, 1, 3]
def baseStart_691808 : Nat := 118140960795 + 691808 * 2 ^ 59
def prefixEnd_691808 : Nat := 4983230072969 + 3 ^ 40 * 691808 * 2
def baseEnd_691808 : Nat := 355230024625734531718439

theorem tailTrace_691808 : CollatzResearch.WordTrace tailWord_691808 prefixEnd_691808 355230024625734531718439 := by
  unfold tailWord_691808
  simp only [CollatzResearch.WordTrace]
  refine ⟨12616155338852621122498039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16821540451803494829997385 12616155338852621122498039)
  ·
    refine ⟨18924233008278931683747059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12616155338852621122498039 18924233008278931683747059)
    ·
      refine ⟨28386349512418397525620589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18924233008278931683747059 28386349512418397525620589)
      ·
        refine ⟨10644881067156899072107721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28386349512418397525620589 10644881067156899072107721)
        ·
          refine ⟨7983660800367674304080791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10644881067156899072107721 7983660800367674304080791)
          ·
            refine ⟨11975491200551511456121187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7983660800367674304080791 11975491200551511456121187)
            ·
              refine ⟨17963236800827267184181781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11975491200551511456121187 17963236800827267184181781)
              ·
                refine ⟨842026725038778149258521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 17963236800827267184181781 842026725038778149258521)
                ·
                  refine ⟨631520043779083611943891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 842026725038778149258521 631520043779083611943891)
                  ·
                    refine ⟨947280065668625417915837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 631520043779083611943891 947280065668625417915837)
                    ·
                      refine ⟨355230024625734531718439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 947280065668625417915837 355230024625734531718439)
                      ·
                        rfl

theorem cell23_691808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 6, 2, 1, 3].length) (baseStart_691808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_691808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_691808 prefixEnd_691808 := by exact prefixLift 691808
  have htrace : WordTrace (prefixWord ++ tailWord_691808) baseStart_691808 baseEnd_691808 := by
    simpa [prefixWord, tailWord_691808, baseEnd_691808] using wordTrace_append hprefix tailTrace_691808
  have hstable : (prefixWord ++ tailWord_691808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_691808).length < 2 ^ (prefixWord ++ tailWord_691808).sum := by decide
  have hdescent : baseEnd_691808 < baseStart_691808 := by decide
  rcases family_descends (prefixWord ++ tailWord_691808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_691901 : List Nat := [1, 4, 1, 2, 1, 2, 3, 1, 1, 7]
def baseStart_691901 : Nat := 118140960795 + 691901 * 2 ^ 59
def prefixEnd_691901 : Nat := 4983230072969 + 3 ^ 40 * 691901 * 2
def baseEnd_691901 : Nat := 118425926108867555951837

theorem tailTrace_691901 : CollatzResearch.WordTrace tailWord_691901 prefixEnd_691901 118425926108867555951837 := by
  unfold tailWord_691901
  simp only [CollatzResearch.WordTrace]
  refine ⟨25235702666368319128131557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 16823801777578879418754371 25235702666368319128131557)
  ·
    refine ⟨4731694249944059836524667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 25235702666368319128131557 4731694249944059836524667)
    ·
      refine ⟨7097541374916089754787001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4731694249944059836524667 7097541374916089754787001)
      ·
        refine ⟨5323156031187067316090251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7097541374916089754787001 5323156031187067316090251)
        ·
          refine ⟨7984734046780600974135377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5323156031187067316090251 7984734046780600974135377)
          ·
            refine ⟨5988550535085450730601533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7984734046780600974135377 5988550535085450730601533)
            ·
              refine ⟨2245706450657044023975575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5988550535085450730601533 2245706450657044023975575)
              ·
                refine ⟨3368559675985566035963363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2245706450657044023975575 3368559675985566035963363)
                ·
                  refine ⟨5052839513978349053945045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3368559675985566035963363 5052839513978349053945045)
                  ·
                    refine ⟨118425926108867555951837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 5052839513978349053945045 118425926108867555951837)
                    ·
                      rfl

theorem cell23_691901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 3, 1, 1, 7].length) (baseStart_691901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_691901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_691901 prefixEnd_691901 := by exact prefixLift 691901
  have htrace : WordTrace (prefixWord ++ tailWord_691901) baseStart_691901 baseEnd_691901 := by
    simpa [prefixWord, tailWord_691901, baseEnd_691901] using wordTrace_append hprefix tailTrace_691901
  have hstable : (prefixWord ++ tailWord_691901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_691901).length < 2 ^ (prefixWord ++ tailWord_691901).sum := by decide
  have hdescent : baseEnd_691901 < baseStart_691901 := by decide
  rcases family_descends (prefixWord ++ tailWord_691901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_691916 : List Nat := [2, 2, 1, 5, 3, 1, 1, 2, 2, 2, 2]
def baseStart_691916 : Nat := 118140960795 + 691916 * 2 ^ 59
def prefixEnd_691916 : Nat := 4983230072969 + 3 ^ 40 * 691916 * 2
def baseEnd_691916 : Nat := 355285480536420109167943

theorem tailTrace_691916 : CollatzResearch.WordTrace tailWord_691916 prefixEnd_691916 355285480536420109167943 := by
  unfold tailWord_691916
  simp only [CollatzResearch.WordTrace]
  refine ⟨12618124880656988344963801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 16824166507542651126618401 12618124880656988344963801)
  ·
    refine ⟨9463593660492741258722851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12618124880656988344963801 9463593660492741258722851)
    ·
      refine ⟨14195390490739111888084277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9463593660492741258722851 14195390490739111888084277)
      ·
        refine ⟨1330817858506791739507901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 14195390490739111888084277 1330817858506791739507901)
        ·
          refine ⟨499056696940046902315463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1330817858506791739507901 499056696940046902315463)
          ·
            refine ⟨748585045410070353473195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 499056696940046902315463 748585045410070353473195)
            ·
              refine ⟨1122877568115105530209793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 748585045410070353473195 1122877568115105530209793)
              ·
                refine ⟨842158176086329147657345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1122877568115105530209793 842158176086329147657345)
                ·
                  refine ⟨631618632064746860743009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 842158176086329147657345 631618632064746860743009)
                  ·
                    refine ⟨473713974048560145557257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 631618632064746860743009 473713974048560145557257)
                    ·
                      refine ⟨355285480536420109167943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 473713974048560145557257 355285480536420109167943)
                      ·
                        rfl

theorem cell23_691916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 3, 1, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 3, 1, 1, 2, 2, 2, 2].length) (baseStart_691916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_691916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_691916 prefixEnd_691916 := by exact prefixLift 691916
  have htrace : WordTrace (prefixWord ++ tailWord_691916) baseStart_691916 baseEnd_691916 := by
    simpa [prefixWord, tailWord_691916, baseEnd_691916] using wordTrace_append hprefix tailTrace_691916
  have hstable : (prefixWord ++ tailWord_691916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_691916).length < 2 ^ (prefixWord ++ tailWord_691916).sum := by decide
  have hdescent : baseEnd_691916 < baseStart_691916 := by decide
  rcases family_descends (prefixWord ++ tailWord_691916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
