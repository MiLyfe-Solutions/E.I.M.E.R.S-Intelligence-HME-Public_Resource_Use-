import V185TrunkScan23Chunk0616

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_3648852 : List Nat := [2, 4, 1, 1, 2, 1, 1, 2, 2, 4, 3]
def baseStart_3648852 : Nat := 118140960795 + 3648852 * 2 ^ 59
def prefixEnd_3648852 : Nat := 4983230072969 + 3 ^ 40 * 3648852 * 2
def baseEnd_3648852 : Nat := 1873614913119463083469241

theorem tailTrace_3648852 : CollatzResearch.WordTrace tailWord_3648852 prefixEnd_3648852 1873614913119463083469241 := by
  unfold tailWord_3648852
  simp only [CollatzResearch.WordTrace]
  refine ⟨66542282888419926576634405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88723043851226568768845873 66542282888419926576634405)
  ·
    refine ⟨12476678041578736233118951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 66542282888419926576634405 12476678041578736233118951)
    ·
      refine ⟨18715017062368104349678427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12476678041578736233118951 18715017062368104349678427)
      ·
        refine ⟨28072525593552156524517641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18715017062368104349678427 28072525593552156524517641)
        ·
          refine ⟨21054394195164117393388231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28072525593552156524517641 21054394195164117393388231)
          ·
            refine ⟨31581591292746176090082347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21054394195164117393388231 31581591292746176090082347)
            ·
              refine ⟨47372386939119264135123521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31581591292746176090082347 47372386939119264135123521)
              ·
                refine ⟨35529290204339448101342641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47372386939119264135123521 35529290204339448101342641)
                ·
                  refine ⟨26646967653254586076006981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35529290204339448101342641 26646967653254586076006981)
                  ·
                    refine ⟨4996306434985234889251309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26646967653254586076006981 4996306434985234889251309)
                    ·
                      refine ⟨1873614913119463083469241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4996306434985234889251309 1873614913119463083469241)
                      ·
                        rfl

theorem cell23_3648852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 2, 2, 4, 3].length) (baseStart_3648852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3648852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3648852 prefixEnd_3648852 := by exact prefixLift 3648852
  have htrace : WordTrace (prefixWord ++ tailWord_3648852) baseStart_3648852 baseEnd_3648852 := by
    simpa [prefixWord, tailWord_3648852, baseEnd_3648852] using wordTrace_append hprefix tailTrace_3648852
  have hstable : (prefixWord ++ tailWord_3648852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3648852).length < 2 ^ (prefixWord ++ tailWord_3648852).sum := by decide
  have hdescent : baseEnd_3648852 < baseStart_3648852 := by decide
  rcases family_descends (prefixWord ++ tailWord_3648852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3648855 : List Nat := [1, 1, 3, 2, 3, 2, 1, 1, 9]
def baseStart_3648855 : Nat := 118140960795 + 3648855 * 2 ^ 59
def prefixEnd_3648855 : Nat := 4983230072969 + 3 ^ 40 * 3648855 * 2
def baseEnd_3648855 : Nat := 208179605951269619081303

theorem tailTrace_3648855 : CollatzResearch.WordTrace tailWord_3648855 prefixEnd_3648855 208179605951269619081303 := by
  unfold tailWord_3648855
  simp only [CollatzResearch.WordTrace]
  refine ⟨133084675195828984665628019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88723116797219323110418679 133084675195828984665628019)
  ·
    refine ⟨199627012793743476998442029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133084675195828984665628019 199627012793743476998442029)
    ·
      refine ⟨74860129797653803874415761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 199627012793743476998442029 74860129797653803874415761)
      ·
        refine ⟨56145097348240352905811821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74860129797653803874415761 56145097348240352905811821)
        ·
          refine ⟨21054411505590132339679433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56145097348240352905811821 21054411505590132339679433)
          ·
            refine ⟨15790808629192599254759575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21054411505590132339679433 15790808629192599254759575)
            ·
              refine ⟨23686212943788898882139363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15790808629192599254759575 23686212943788898882139363)
              ·
                refine ⟨35529319415683348323209045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23686212943788898882139363 35529319415683348323209045)
                ·
                  refine ⟨208179605951269619081303, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 35529319415683348323209045 208179605951269619081303)
                  ·
                    rfl

theorem cell23_3648855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 1, 1, 9].length) (baseStart_3648855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3648855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3648855 prefixEnd_3648855 := by exact prefixLift 3648855
  have htrace : WordTrace (prefixWord ++ tailWord_3648855) baseStart_3648855 baseEnd_3648855 := by
    simpa [prefixWord, tailWord_3648855, baseEnd_3648855] using wordTrace_append hprefix tailTrace_3648855
  have hstable : (prefixWord ++ tailWord_3648855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3648855).length < 2 ^ (prefixWord ++ tailWord_3648855).sum := by decide
  have hdescent : baseEnd_3648855 < baseStart_3648855 := by decide
  rcases family_descends (prefixWord ++ tailWord_3648855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3648866 : List Nat := [3, 3, 2, 1, 1, 1, 2, 2, 4, 2, 2]
def baseStart_3648866 : Nat := 118140960795 + 3648866 * 2 ^ 59
def prefixEnd_3648866 : Nat := 4983230072969 + 3 ^ 40 * 3648866 * 2
def baseEnd_3648866 : Nat := 1873622101848626028694177

theorem tailTrace_3648866 : CollatzResearch.WordTrace tailWord_3648866 prefixEnd_3648866 1873622101848626028694177 := by
  unfold tailWord_3648866
  simp only [CollatzResearch.WordTrace]
  refine ⟨33271269099697283386069613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88723384265859422362852301 33271269099697283386069613)
  ·
    refine ⟨12476725912386481269776105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33271269099697283386069613 12476725912386481269776105)
    ·
      refine ⟨9357544434289860952332079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12476725912386481269776105 9357544434289860952332079)
      ·
        refine ⟨14036316651434791428498119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9357544434289860952332079 14036316651434791428498119)
        ·
          refine ⟨21054474977152187142747179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14036316651434791428498119 21054474977152187142747179)
          ·
            refine ⟨31581712465728280714120769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21054474977152187142747179 31581712465728280714120769)
            ·
              refine ⟨23686284349296210535590577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31581712465728280714120769 23686284349296210535590577)
              ·
                refine ⟨17764713261972157901692933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23686284349296210535590577 17764713261972157901692933)
                ·
                  refine ⟨3330883736619779606567425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17764713261972157901692933 3330883736619779606567425)
                  ·
                    refine ⟨2498162802464834704925569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3330883736619779606567425 2498162802464834704925569)
                    ·
                      refine ⟨1873622101848626028694177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2498162802464834704925569 1873622101848626028694177)
                      ·
                        rfl

theorem cell23_3648866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 2, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 2, 2, 4, 2, 2].length) (baseStart_3648866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3648866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3648866 prefixEnd_3648866 := by exact prefixLift 3648866
  have htrace : WordTrace (prefixWord ++ tailWord_3648866) baseStart_3648866 baseEnd_3648866 := by
    simpa [prefixWord, tailWord_3648866, baseEnd_3648866] using wordTrace_append hprefix tailTrace_3648866
  have hstable : (prefixWord ++ tailWord_3648866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3648866).length < 2 ^ (prefixWord ++ tailWord_3648866).sum := by decide
  have hdescent : baseEnd_3648866 < baseStart_3648866 := by decide
  rcases family_descends (prefixWord ++ tailWord_3648866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3648882 : List Nat := [3, 2, 1, 2, 1, 2, 1, 1, 4, 3, 3]
def baseStart_3648882 : Nat := 118140960795 + 3648882 * 2 ^ 59
def prefixEnd_3648882 : Nat := 4983230072969 + 3 ^ 40 * 3648882 * 2
def baseEnd_3648882 : Nat := 1873630317539097966094103

theorem tailTrace_3648882 : CollatzResearch.WordTrace tailWord_3648882 prefixEnd_3648882 1873630317539097966094103 := by
  unfold tailWord_3648882
  simp only [CollatzResearch.WordTrace]
  refine ⟨33271414991682792069215225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88723773311154112184573933 33271414991682792069215225)
  ·
    refine ⟨24953561243762094051911419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33271414991682792069215225 24953561243762094051911419)
    ·
      refine ⟨37430341865643141077867129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24953561243762094051911419 37430341865643141077867129)
      ·
        refine ⟨28072756399232355808400347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37430341865643141077867129 28072756399232355808400347)
        ·
          refine ⟨42109134598848533712600521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28072756399232355808400347 42109134598848533712600521)
          ·
            refine ⟨31581850949136400284450391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42109134598848533712600521 31581850949136400284450391)
            ·
              refine ⟨47372776423704600426675587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31581850949136400284450391 47372776423704600426675587)
              ·
                refine ⟨71059164635556900640013381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47372776423704600426675587 71059164635556900640013381)
                ·
                  refine ⟨13323593369166918870002509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 71059164635556900640013381 13323593369166918870002509)
                  ·
                    refine ⟨4996347513437594576250941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13323593369166918870002509 4996347513437594576250941)
                    ·
                      refine ⟨1873630317539097966094103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4996347513437594576250941 1873630317539097966094103)
                      ·
                        rfl

theorem cell23_3648882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 1, 1, 4, 3, 3].length) (baseStart_3648882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3648882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3648882 prefixEnd_3648882 := by exact prefixLift 3648882
  have htrace : WordTrace (prefixWord ++ tailWord_3648882) baseStart_3648882 baseEnd_3648882 := by
    simpa [prefixWord, tailWord_3648882, baseEnd_3648882] using wordTrace_append hprefix tailTrace_3648882
  have hstable : (prefixWord ++ tailWord_3648882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3648882).length < 2 ^ (prefixWord ++ tailWord_3648882).sum := by decide
  have hdescent : baseEnd_3648882 < baseStart_3648882 := by decide
  rcases family_descends (prefixWord ++ tailWord_3648882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3648922 : List Nat := [3, 1, 1, 4, 1, 1, 1, 3, 1, 3, 4]
def baseStart_3648922 : Nat := 118140960795 + 3648922 * 2 ^ 59
def prefixEnd_3648922 : Nat := 4983230072969 + 3 ^ 40 * 3648922 * 2
def baseEnd_3648922 : Nat := 1873650856765277809593919

theorem tailTrace_3648922 : CollatzResearch.WordTrace tailWord_3648922 prefixEnd_3648922 1873650856765277809593919 := by
  unfold tailWord_3648922
  simp only [CollatzResearch.WordTrace]
  refine ⟨33271779721646563777079255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88724745924390836738878013 33271779721646563777079255)
  ·
    refine ⟨49907669582469845665618883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33271779721646563777079255 49907669582469845665618883)
    ·
      refine ⟨74861504373704768498428325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49907669582469845665618883 74861504373704768498428325)
      ·
        refine ⟨14036532070069644093455311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 74861504373704768498428325 14036532070069644093455311)
        ·
          refine ⟨21054798105104466140182967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14036532070069644093455311 21054798105104466140182967)
          ·
            refine ⟨31582197157656699210274451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21054798105104466140182967 31582197157656699210274451)
            ·
              refine ⟨47373295736485048815411677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31582197157656699210274451 47373295736485048815411677)
              ·
                refine ⟨17764985901181893305779379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47373295736485048815411677 17764985901181893305779379)
                ·
                  refine ⟨26647478851772839958669069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17764985901181893305779379 26647478851772839958669069)
                  ·
                    refine ⟨9992804569414814984500901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26647478851772839958669069 9992804569414814984500901)
                    ·
                      refine ⟨1873650856765277809593919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9992804569414814984500901 1873650856765277809593919)
                      ·
                        rfl

theorem cell23_3648922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 1, 3, 1, 3, 4].length) (baseStart_3648922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3648922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3648922 prefixEnd_3648922 := by exact prefixLift 3648922
  have htrace : WordTrace (prefixWord ++ tailWord_3648922) baseStart_3648922 baseEnd_3648922 := by
    simpa [prefixWord, tailWord_3648922, baseEnd_3648922] using wordTrace_append hprefix tailTrace_3648922
  have hstable : (prefixWord ++ tailWord_3648922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3648922).length < 2 ^ (prefixWord ++ tailWord_3648922).sum := by decide
  have hdescent : baseEnd_3648922 < baseStart_3648922 := by decide
  rcases family_descends (prefixWord ++ tailWord_3648922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3648936 : List Nat := [2, 1, 6, 1, 2, 1, 1, 2, 2, 5]
def baseStart_3648936 : Nat := 118140960795 + 3648936 * 2 ^ 59
def prefixEnd_3648936 : Nat := 4983230072969 + 3 ^ 40 * 3648936 * 2
def baseEnd_3648936 : Nat := 624552681831480251606285

theorem tailTrace_3648936 : CollatzResearch.WordTrace tailWord_3648936 prefixEnd_3648936 624552681831480251606285 := by
  unfold tailWord_3648936
  simp only [CollatzResearch.WordTrace]
  refine ⟨66543814754267767749663331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88725086339023690332884441 66543814754267767749663331)
  ·
    refine ⟨99815722131401651624494997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66543814754267767749663331 99815722131401651624494997)
    ·
      refine ⟨4678861974909452419898203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 99815722131401651624494997 4678861974909452419898203)
      ·
        refine ⟨7018292962364178629847305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4678861974909452419898203 7018292962364178629847305)
        ·
          refine ⟨5263719721773133972385479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7018292962364178629847305 5263719721773133972385479)
          ·
            refine ⟨7895579582659700958578219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5263719721773133972385479 7895579582659700958578219)
            ·
              refine ⟨11843369373989551437867329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7895579582659700958578219 11843369373989551437867329)
              ·
                refine ⟨8882527030492163578400497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11843369373989551437867329 8882527030492163578400497)
                ·
                  refine ⟨6661895272869122683800373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8882527030492163578400497 6661895272869122683800373)
                  ·
                    refine ⟨624552681831480251606285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6661895272869122683800373 624552681831480251606285)
                    ·
                      rfl

theorem cell23_3648936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 1, 1, 2, 2, 5].length) (baseStart_3648936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3648936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3648936 prefixEnd_3648936 := by exact prefixLift 3648936
  have htrace : WordTrace (prefixWord ++ tailWord_3648936) baseStart_3648936 baseEnd_3648936 := by
    simpa [prefixWord, tailWord_3648936, baseEnd_3648936] using wordTrace_append hprefix tailTrace_3648936
  have hstable : (prefixWord ++ tailWord_3648936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3648936).length < 2 ^ (prefixWord ++ tailWord_3648936).sum := by decide
  have hdescent : baseEnd_3648936 < baseStart_3648936 := by decide
  rcases family_descends (prefixWord ++ tailWord_3648936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3649006 : List Nat := [4, 1, 2, 1, 2, 1, 2, 3, 3, 1, 3]
def baseStart_3649006 : Nat := 118140960795 + 3649006 * 2 ^ 59
def prefixEnd_3649006 : Nat := 4983230072969 + 3 ^ 40 * 3649006 * 2
def baseEnd_3649006 : Nat := 1873693989140255480943533

theorem tailTrace_3649006 : CollatzResearch.WordTrace tailWord_3649006 prefixEnd_3649006 1873693989140255480943533 := by
  unfold tailWord_3649006
  simp only [CollatzResearch.WordTrace]
  refine ⟨16636272827285242181796859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 88726788412187958302916581 16636272827285242181796859)
  ·
    refine ⟨24954409240927863272695289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16636272827285242181796859 24954409240927863272695289)
    ·
      refine ⟨18715806930695897454521467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24954409240927863272695289 18715806930695897454521467)
      ·
        refine ⟨28073710396043846181782201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18715806930695897454521467 28073710396043846181782201)
        ·
          refine ⟨21055282797032884636336651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28073710396043846181782201 21055282797032884636336651)
          ·
            refine ⟨31582924195549326954504977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21055282797032884636336651 31582924195549326954504977)
            ·
              refine ⟨23687193146661995215878733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31582924195549326954504977 23687193146661995215878733)
              ·
                refine ⟨8882697429998248205954525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23687193146661995215878733 8882697429998248205954525)
                ·
                  refine ⟨3331011536249343077232947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8882697429998248205954525 3331011536249343077232947)
                  ·
                    refine ⟨4996517304374014615849421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3331011536249343077232947 4996517304374014615849421)
                    ·
                      refine ⟨1873693989140255480943533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4996517304374014615849421 1873693989140255480943533)
                      ·
                        rfl

theorem cell23_3649006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 2, 3, 3, 1, 3].length) (baseStart_3649006 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3649006 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3649006 prefixEnd_3649006 := by exact prefixLift 3649006
  have htrace : WordTrace (prefixWord ++ tailWord_3649006) baseStart_3649006 baseEnd_3649006 := by
    simpa [prefixWord, tailWord_3649006, baseEnd_3649006] using wordTrace_append hprefix tailTrace_3649006
  have hstable : (prefixWord ++ tailWord_3649006).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3649006).length < 2 ^ (prefixWord ++ tailWord_3649006).sum := by decide
  have hdescent : baseEnd_3649006 < baseStart_3649006 := by decide
  rcases family_descends (prefixWord ++ tailWord_3649006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3649026 : List Nat := [3, 4, 1, 2, 1, 1, 2, 1, 3, 5]
def baseStart_3649026 : Nat := 118140960795 + 3649026 * 2 ^ 59
def prefixEnd_3649026 : Nat := 4983230072969 + 3 ^ 40 * 3649026 * 2
def baseEnd_3649026 : Nat := 624568086251115134231147

theorem tailTrace_3649026 : CollatzResearch.WordTrace tailWord_3649026 prefixEnd_3649026 624568086251115134231147 := by
  unfold tailWord_3649026
  simp only [CollatzResearch.WordTrace]
  refine ⟨33272728019552370217525733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88727274718806320580068621 33272728019552370217525733)
  ·
    refine ⟨6238636503666069415786075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 33272728019552370217525733 6238636503666069415786075)
    ·
      refine ⟨9357954755499104123679113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6238636503666069415786075 9357954755499104123679113)
      ·
        refine ⟨7018466066624328092759335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9357954755499104123679113 7018466066624328092759335)
        ·
          refine ⟨10527699099936492139139003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7018466066624328092759335 10527699099936492139139003)
          ·
            refine ⟨15791548649904738208708505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10527699099936492139139003 15791548649904738208708505)
            ·
              refine ⟨11843661487428553656531379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15791548649904738208708505 11843661487428553656531379)
              ·
                refine ⟨17765492231142830484797069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11843661487428553656531379 17765492231142830484797069)
                ·
                  refine ⟨6662059586678561431798901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17765492231142830484797069 6662059586678561431798901)
                  ·
                    refine ⟨624568086251115134231147, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6662059586678561431798901 624568086251115134231147)
                    ·
                      rfl

theorem cell23_3649026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 2, 1, 3, 5].length) (baseStart_3649026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3649026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3649026 prefixEnd_3649026 := by exact prefixLift 3649026
  have htrace : WordTrace (prefixWord ++ tailWord_3649026) baseStart_3649026 baseEnd_3649026 := by
    simpa [prefixWord, tailWord_3649026, baseEnd_3649026] using wordTrace_append hprefix tailTrace_3649026
  have hstable : (prefixWord ++ tailWord_3649026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3649026).length < 2 ^ (prefixWord ++ tailWord_3649026).sum := by decide
  have hdescent : baseEnd_3649026 < baseStart_3649026 := by decide
  rcases family_descends (prefixWord ++ tailWord_3649026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3649029 : List Nat := [1, 3, 1, 1, 2, 2, 1, 6, 1, 1, 4]
def baseStart_3649029 : Nat := 118140960795 + 3649029 * 2 ^ 59
def prefixEnd_3649029 : Nat := 4983230072969 + 3 ^ 40 * 3649029 * 2
def baseEnd_3649029 : Nat := 1873705799195308890955927

theorem tailTrace_3649029 : CollatzResearch.WordTrace tailWord_3649029 prefixEnd_3649029 1873705799195308890955927 := by
  unfold tailWord_3649029
  simp only [CollatzResearch.WordTrace]
  refine ⟨133091021497198612382462141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88727347664799074921641427 133091021497198612382462141)
  ·
    refine ⟨49909133061449479643423303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 133091021497198612382462141 49909133061449479643423303)
    ·
      refine ⟨74863699592174219465134955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49909133061449479643423303 74863699592174219465134955)
      ·
        refine ⟨112295549388261329197702433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74863699592174219465134955 112295549388261329197702433)
        ·
          refine ⟨84221662041195996898276825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 112295549388261329197702433 84221662041195996898276825)
          ·
            refine ⟨63166246530896997673707619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84221662041195996898276825 63166246530896997673707619)
            ·
              refine ⟨94749369796345496510561429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63166246530896997673707619 94749369796345496510561429)
              ·
                refine ⟨4441376709203695148932567, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 94749369796345496510561429 4441376709203695148932567)
                ·
                  refine ⟨6662065063805542723398851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4441376709203695148932567 6662065063805542723398851)
                  ·
                    refine ⟨9993097595708314085098277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6662065063805542723398851 9993097595708314085098277)
                    ·
                      refine ⟨1873705799195308890955927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9993097595708314085098277 1873705799195308890955927)
                      ·
                        rfl

theorem cell23_3649029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 6, 1, 1, 4].length) (baseStart_3649029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3649029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3649029 prefixEnd_3649029 := by exact prefixLift 3649029
  have htrace : WordTrace (prefixWord ++ tailWord_3649029) baseStart_3649029 baseEnd_3649029 := by
    simpa [prefixWord, tailWord_3649029, baseEnd_3649029] using wordTrace_append hprefix tailTrace_3649029
  have hstable : (prefixWord ++ tailWord_3649029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3649029).length < 2 ^ (prefixWord ++ tailWord_3649029).sum := by decide
  have hdescent : baseEnd_3649029 < baseStart_3649029 := by decide
  rcases family_descends (prefixWord ++ tailWord_3649029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3649052 : List Nat := [2, 2, 3, 1, 2, 1, 12]
def baseStart_3649052 : Nat := 118140960795 + 3649052 * 2 ^ 59
def prefixEnd_3649052 : Nat := 4983230072969 + 3 ^ 40 * 3649052 * 2
def baseEnd_3649052 : Nat := 23132316163584719765041

theorem tailTrace_3649052 : CollatzResearch.WordTrace tailWord_3649052 prefixEnd_3649052 23132316163584719765041 := by
  unfold tailWord_3649052
  simp only [CollatzResearch.WordTrace]
  refine ⟨66545930188057643655274705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88727906917410191540366273 66545930188057643655274705)
  ·
    refine ⟨49909447641043232741456029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66545930188057643655274705 49909447641043232741456029)
    ·
      refine ⟨18716042865391212278046011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49909447641043232741456029 18716042865391212278046011)
      ·
        refine ⟨28074064298086818417069017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18716042865391212278046011 28074064298086818417069017)
        ·
          refine ⟨21055548223565113812801763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28074064298086818417069017 21055548223565113812801763)
          ·
            refine ⟨31583322335347670719202645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21055548223565113812801763 31583322335347670719202645)
            ·
              refine ⟨23132316163584719765041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 31583322335347670719202645 23132316163584719765041)
              ·
                rfl

theorem cell23_3649052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 12].length) (baseStart_3649052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3649052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3649052 prefixEnd_3649052 := by exact prefixLift 3649052
  have htrace : WordTrace (prefixWord ++ tailWord_3649052) baseStart_3649052 baseEnd_3649052 := by
    simpa [prefixWord, tailWord_3649052, baseEnd_3649052] using wordTrace_append hprefix tailTrace_3649052
  have hstable : (prefixWord ++ tailWord_3649052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3649052).length < 2 ^ (prefixWord ++ tailWord_3649052).sum := by decide
  have hdescent : baseEnd_3649052 < baseStart_3649052 := by decide
  rcases family_descends (prefixWord ++ tailWord_3649052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3649056 : List Nat := [2, 1, 1, 6, 1, 2, 1, 1, 4, 4]
def baseStart_3649056 : Nat := 118140960795 + 3649056 * 2 ^ 59
def prefixEnd_3649056 : Nat := 4983230072969 + 3 ^ 40 * 3649056 * 2
def baseEnd_3649056 : Nat := 624573221057660095106101

theorem tailTrace_3649056 : CollatzResearch.WordTrace tailWord_3649056 prefixEnd_3649056 624573221057660095106101 := by
  unfold tailWord_3649056
  simp only [CollatzResearch.WordTrace]
  refine ⟨66546003134050397996847511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88728004178733863995796681 66546003134050397996847511)
  ·
    refine ⟨99819004701075596995271267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66546003134050397996847511 99819004701075596995271267)
    ·
      refine ⟨149728507051613395492906901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99819004701075596995271267 149728507051613395492906901)
      ·
        refine ⟨7018523768044377913730011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 149728507051613395492906901 7018523768044377913730011)
        ·
          refine ⟨10527785652066566870595017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7018523768044377913730011 10527785652066566870595017)
          ·
            refine ⟨7895839239049925152946263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10527785652066566870595017 7895839239049925152946263)
            ·
              refine ⟨11843758858574887729419395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7895839239049925152946263 11843758858574887729419395)
              ·
                refine ⟨17765638287862331594129093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11843758858574887729419395 17765638287862331594129093)
                ·
                  refine ⟨3331057178974187173899205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17765638287862331594129093 3331057178974187173899205)
                  ·
                    refine ⟨624573221057660095106101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3331057178974187173899205 624573221057660095106101)
                    ·
                      rfl

theorem cell23_3649056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 2, 1, 1, 4, 4].length) (baseStart_3649056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3649056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3649056 prefixEnd_3649056 := by exact prefixLift 3649056
  have htrace : WordTrace (prefixWord ++ tailWord_3649056) baseStart_3649056 baseEnd_3649056 := by
    simpa [prefixWord, tailWord_3649056, baseEnd_3649056] using wordTrace_append hprefix tailTrace_3649056
  have hstable : (prefixWord ++ tailWord_3649056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3649056).length < 2 ^ (prefixWord ++ tailWord_3649056).sum := by decide
  have hdescent : baseEnd_3649056 < baseStart_3649056 := by decide
  rcases family_descends (prefixWord ++ tailWord_3649056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3649130 : List Nat := [3, 1, 3, 2, 1, 2, 4, 1, 2, 1, 3]
def baseStart_3649130 : Nat := 118140960795 + 3649130 * 2 ^ 59
def prefixEnd_3649130 : Nat := 4983230072969 + 3 ^ 40 * 3649130 * 2
def baseEnd_3649130 : Nat := 1873757660741412995792963

theorem tailTrace_3649130 : CollatzResearch.WordTrace tailWord_3649130 prefixEnd_3649130 1873757660741412995792963 := by
  unfold tailWord_3649130
  simp only [CollatzResearch.WordTrace]
  refine ⟨33273676317458176657972211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88729803513221804421259229 33273676317458176657972211)
  ·
    refine ⟨49910514476187264986958317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33273676317458176657972211 49910514476187264986958317)
    ·
      refine ⟨18716442928570224370109369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49910514476187264986958317 18716442928570224370109369)
      ·
        refine ⟨14037332196427668277582027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18716442928570224370109369 14037332196427668277582027)
        ·
          refine ⟨21055998294641502416373041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14037332196427668277582027 21055998294641502416373041)
          ·
            refine ⟨15791998720981126812279781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21055998294641502416373041 15791998720981126812279781)
            ·
              refine ⟨2960999760183961277302459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15791998720981126812279781 2960999760183961277302459)
              ·
                refine ⟨4441499640275941915953689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2960999760183961277302459 4441499640275941915953689)
                ·
                  refine ⟨3331124730206956436965267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4441499640275941915953689 3331124730206956436965267)
                  ·
                    refine ⟨4996687095310434655447901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3331124730206956436965267 4996687095310434655447901)
                    ·
                      refine ⟨1873757660741412995792963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4996687095310434655447901 1873757660741412995792963)
                      ·
                        rfl

theorem cell23_3649130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 4, 1, 2, 1, 3].length) (baseStart_3649130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3649130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3649130 prefixEnd_3649130 := by exact prefixLift 3649130
  have htrace : WordTrace (prefixWord ++ tailWord_3649130) baseStart_3649130 baseEnd_3649130 := by
    simpa [prefixWord, tailWord_3649130, baseEnd_3649130] using wordTrace_append hprefix tailTrace_3649130
  have hstable : (prefixWord ++ tailWord_3649130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3649130).length < 2 ^ (prefixWord ++ tailWord_3649130).sum := by decide
  have hdescent : baseEnd_3649130 < baseStart_3649130 := by decide
  rcases family_descends (prefixWord ++ tailWord_3649130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3649153 : List Nat := [1, 2, 4, 2, 1, 3, 1, 2, 1, 4, 2]
def baseStart_3649153 : Nat := 118140960795 + 3649153 * 2 ^ 59
def prefixEnd_3649153 : Nat := 4983230072969 + 3 ^ 40 * 3649153 * 2
def baseEnd_3649153 : Nat := 1873769470796466405805357

theorem tailTrace_3649153 : CollatzResearch.WordTrace tailWord_3649153 prefixEnd_3649153 1873769470796466405805357 := by
  unfold tailWord_3649153
  simp only [CollatzResearch.WordTrace]
  refine ⟨133095544148749381559976113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88730362765832921039984075 133095544148749381559976113)
  ·
    refine ⟨99821658111562036169982085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133095544148749381559976113 99821658111562036169982085)
    ·
      refine ⟨18716560895917881781871641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 99821658111562036169982085 18716560895917881781871641)
      ·
        refine ⟨14037420671938411336403731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18716560895917881781871641 14037420671938411336403731)
        ·
          refine ⟨21056131007907617004605597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14037420671938411336403731 21056131007907617004605597)
          ·
            refine ⟨7896049127965356376727099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21056131007907617004605597 7896049127965356376727099)
            ·
              refine ⟨11844073691948034565090649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7896049127965356376727099 11844073691948034565090649)
              ·
                refine ⟨8883055268961025923817987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11844073691948034565090649 8883055268961025923817987)
                ·
                  refine ⟨13324582903441538885726981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8883055268961025923817987 13324582903441538885726981)
                  ·
                    refine ⟨2498359294395288541073809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13324582903441538885726981 2498359294395288541073809)
                    ·
                      refine ⟨1873769470796466405805357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2498359294395288541073809 1873769470796466405805357)
                      ·
                        rfl

theorem cell23_3649153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 3, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 3, 1, 2, 1, 4, 2].length) (baseStart_3649153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3649153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3649153 prefixEnd_3649153 := by exact prefixLift 3649153
  have htrace : WordTrace (prefixWord ++ tailWord_3649153) baseStart_3649153 baseEnd_3649153 := by
    simpa [prefixWord, tailWord_3649153, baseEnd_3649153] using wordTrace_append hprefix tailTrace_3649153
  have hstable : (prefixWord ++ tailWord_3649153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3649153).length < 2 ^ (prefixWord ++ tailWord_3649153).sum := by decide
  have hdescent : baseEnd_3649153 < baseStart_3649153 := by decide
  rcases family_descends (prefixWord ++ tailWord_3649153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3649183 : List Nat := [1, 1, 2, 7, 1, 1, 1, 1, 2, 2, 4]
def baseStart_3649183 : Nat := 118140960795 + 3649183 * 2 ^ 59
def prefixEnd_3649183 : Nat := 4983230072969 + 3 ^ 40 * 3649183 * 2
def baseEnd_3649183 : Nat := 1873784875216101288430219

theorem tailTrace_3649183 : CollatzResearch.WordTrace tailWord_3649183 prefixEnd_3649183 1873784875216101288430219 := by
  unfold tailWord_3649183
  simp only [CollatzResearch.WordTrace]
  refine ⟨133096638338640696683568203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88731092225760464455712135 133096638338640696683568203)
  ·
    refine ⟨199644957507961045025352305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133096638338640696683568203 199644957507961045025352305)
    ·
      refine ⟨149733718130970783769014229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 199644957507961045025352305 149733718130970783769014229)
      ·
        refine ⟨3509384018694627744586271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 149733718130970783769014229 3509384018694627744586271)
        ·
          refine ⟨5264076028041941616879407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3509384018694627744586271 5264076028041941616879407)
          ·
            refine ⟨7896114042062912425319111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5264076028041941616879407 7896114042062912425319111)
            ·
              refine ⟨11844171063094368637978667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7896114042062912425319111 11844171063094368637978667)
              ·
                refine ⟨17766256594641552956968001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11844171063094368637978667 17766256594641552956968001)
                ·
                  refine ⟨13324692445981164717726001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17766256594641552956968001 13324692445981164717726001)
                  ·
                    refine ⟨9993519334485873538294501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13324692445981164717726001 9993519334485873538294501)
                    ·
                      refine ⟨1873784875216101288430219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9993519334485873538294501 1873784875216101288430219)
                      ·
                        rfl

theorem cell23_3649183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 1, 1, 1, 2, 2, 4].length) (baseStart_3649183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3649183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3649183 prefixEnd_3649183 := by exact prefixLift 3649183
  have htrace : WordTrace (prefixWord ++ tailWord_3649183) baseStart_3649183 baseEnd_3649183 := by
    simpa [prefixWord, tailWord_3649183, baseEnd_3649183] using wordTrace_append hprefix tailTrace_3649183
  have hstable : (prefixWord ++ tailWord_3649183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3649183).length < 2 ^ (prefixWord ++ tailWord_3649183).sum := by decide
  have hdescent : baseEnd_3649183 < baseStart_3649183 := by decide
  rcases family_descends (prefixWord ++ tailWord_3649183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3649189 : List Nat := [1, 3, 1, 2, 1, 2, 2, 2, 4, 5]
def baseStart_3649189 : Nat := 118140960795 + 3649189 * 2 ^ 59
def prefixEnd_3649189 : Nat := 4983230072969 + 3 ^ 40 * 3649189 * 2
def baseEnd_3649189 : Nat := 624595985366676088318397

theorem tailTrace_3649189 : CollatzResearch.WordTrace tailWord_3649189 prefixEnd_3649189 624595985366676088318397 := by
  unfold tailWord_3649189
  simp only [CollatzResearch.WordTrace]
  refine ⟨133096857176618959708286621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88731238117745973138857747 133096857176618959708286621)
  ·
    refine ⟨49911321441232109890607483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 133096857176618959708286621 49911321441232109890607483)
    ·
      refine ⟨74866982161848164835911225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49911321441232109890607483 74866982161848164835911225)
      ·
        refine ⟨56150236621386123626933419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74866982161848164835911225 56150236621386123626933419)
        ·
          refine ⟨84225354932079185440400129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56150236621386123626933419 84225354932079185440400129)
          ·
            refine ⟨63169016199059389080300097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84225354932079185440400129 63169016199059389080300097)
            ·
              refine ⟨47376762149294541810225073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63169016199059389080300097 47376762149294541810225073)
              ·
                refine ⟨35532571611970906357668805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47376762149294541810225073 35532571611970906357668805)
                ·
                  refine ⟨6662357177244544942062901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35532571611970906357668805 6662357177244544942062901)
                  ·
                    refine ⟨624595985366676088318397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6662357177244544942062901 624595985366676088318397)
                    ·
                      rfl

theorem cell23_3649189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 2, 2, 4, 5].length) (baseStart_3649189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3649189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3649189 prefixEnd_3649189 := by exact prefixLift 3649189
  have htrace : WordTrace (prefixWord ++ tailWord_3649189) baseStart_3649189 baseEnd_3649189 := by
    simpa [prefixWord, tailWord_3649189, baseEnd_3649189] using wordTrace_append hprefix tailTrace_3649189
  have hstable : (prefixWord ++ tailWord_3649189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3649189).length < 2 ^ (prefixWord ++ tailWord_3649189).sum := by decide
  have hdescent : baseEnd_3649189 < baseStart_3649189 := by decide
  rcases family_descends (prefixWord ++ tailWord_3649189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3649239 : List Nat := [1, 1, 3, 2, 1, 3, 1, 2, 2, 1, 6]
def baseStart_3649239 : Nat := 118140960795 + 3649239 * 2 ^ 59
def prefixEnd_3649239 : Nat := 4983230072969 + 3 ^ 40 * 3649239 * 2
def baseEnd_3649239 : Nat := 1873813630132753069329961

theorem tailTrace_3649239 : CollatzResearch.WordTrace tailWord_3649239 prefixEnd_3649239 1873813630132753069329961 := by
  unfold tailWord_3649239
  simp only [CollatzResearch.WordTrace]
  refine ⟨133098680826437818247606771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88732453884291878831737847 133098680826437818247606771)
  ·
    refine ⟨199648021239656727371410157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133098680826437818247606771 199648021239656727371410157)
    ·
      refine ⟨74868007964871272764278809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 199648021239656727371410157 74868007964871272764278809)
      ·
        refine ⟨56151005973653454573209107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74868007964871272764278809 56151005973653454573209107)
        ·
          refine ⟨84226508960480181859813661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56151005973653454573209107 84226508960480181859813661)
          ·
            refine ⟨31584940860180068197430123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 84226508960480181859813661 31584940860180068197430123)
            ·
              refine ⟨47377411290270102296145185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31584940860180068197430123 47377411290270102296145185)
              ·
                refine ⟨35533058467702576722108889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47377411290270102296145185 35533058467702576722108889)
                ·
                  refine ⟨26649793850776932541581667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35533058467702576722108889 26649793850776932541581667)
                  ·
                    refine ⟨39974690776165398812372501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26649793850776932541581667 39974690776165398812372501)
                    ·
                      refine ⟨1873813630132753069329961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 39974690776165398812372501 1873813630132753069329961)
                      ·
                        rfl

theorem cell23_3649239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 1, 2, 2, 1, 6].length) (baseStart_3649239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3649239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3649239 prefixEnd_3649239 := by exact prefixLift 3649239
  have htrace : WordTrace (prefixWord ++ tailWord_3649239) baseStart_3649239 baseEnd_3649239 := by
    simpa [prefixWord, tailWord_3649239, baseEnd_3649239] using wordTrace_append hprefix tailTrace_3649239
  have hstable : (prefixWord ++ tailWord_3649239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3649239).length < 2 ^ (prefixWord ++ tailWord_3649239).sum := by decide
  have hdescent : baseEnd_3649239 < baseStart_3649239 := by decide
  rcases family_descends (prefixWord ++ tailWord_3649239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3649287 : List Nat := [1, 1, 4, 4, 3, 1, 1, 1, 3, 4]
def baseStart_3649287 : Nat := 118140960795 + 3649287 * 2 ^ 59
def prefixEnd_3649287 : Nat := 4983230072969 + 3 ^ 40 * 3649287 * 2
def baseEnd_3649287 : Nat := 624612759068056293843247

theorem tailTrace_3649287 : CollatzResearch.WordTrace tailWord_3649287 prefixEnd_3649287 624612759068056293843247 := by
  unfold tailWord_3649287
  simp only [CollatzResearch.WordTrace]
  refine ⟨133100431530263922445354115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88733621020175948296902743 133100431530263922445354115)
  ·
    refine ⟨199650647295395883668031173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133100431530263922445354115 199650647295395883668031173)
    ·
      refine ⟨37434496367886728187755845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 199650647295395883668031173 37434496367886728187755845)
      ·
        refine ⟨7018968068978761535204221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 37434496367886728187755845 7018968068978761535204221)
        ·
          refine ⟨2632113025867035575701583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7018968068978761535204221 2632113025867035575701583)
          ·
            refine ⟨3948169538800553363552375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2632113025867035575701583 3948169538800553363552375)
            ·
              refine ⟨5922254308200830045328563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3948169538800553363552375 5922254308200830045328563)
              ·
                refine ⟨8883381462301245067992845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5922254308200830045328563 8883381462301245067992845)
                ·
                  refine ⟨3331268048362966900497317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8883381462301245067992845 3331268048362966900497317)
                  ·
                    refine ⟨624612759068056293843247, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3331268048362966900497317 624612759068056293843247)
                    ·
                      rfl

theorem cell23_3649287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 3, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 3, 1, 1, 1, 3, 4].length) (baseStart_3649287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3649287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3649287 prefixEnd_3649287 := by exact prefixLift 3649287
  have htrace : WordTrace (prefixWord ++ tailWord_3649287) baseStart_3649287 baseEnd_3649287 := by
    simpa [prefixWord, tailWord_3649287, baseEnd_3649287] using wordTrace_append hprefix tailTrace_3649287
  have hstable : (prefixWord ++ tailWord_3649287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3649287).length < 2 ^ (prefixWord ++ tailWord_3649287).sum := by decide
  have hdescent : baseEnd_3649287 < baseStart_3649287 := by decide
  rcases family_descends (prefixWord ++ tailWord_3649287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3649289 : List Nat := [1, 2, 1, 1, 3, 2, 1, 2, 2, 1, 7]
def baseStart_3649289 : Nat := 118140960795 + 3649289 * 2 ^ 59
def prefixEnd_3649289 : Nat := 4983230072969 + 3 ^ 40 * 3649289 * 2
def baseEnd_3649289 : Nat := 1873839304165477873704731

theorem tailTrace_3649289 : CollatzResearch.WordTrace tailWord_3649289 prefixEnd_3649289 1873839304165477873704731 := by
  unfold tailWord_3649289
  simp only [CollatzResearch.WordTrace]
  refine ⟨133100504476256676786926921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88733669650837784524617947 133100504476256676786926921)
  ·
    refine ⟨99825378357192507590195191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133100504476256676786926921 99825378357192507590195191)
    ·
      refine ⟨149738067535788761385292787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99825378357192507590195191 149738067535788761385292787)
      ·
        refine ⟨224607101303683142077939181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149738067535788761385292787 224607101303683142077939181)
        ·
          refine ⟨84227662988881178279227193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 224607101303683142077939181 84227662988881178279227193)
          ·
            refine ⟨63170747241660883709420395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84227662988881178279227193 63170747241660883709420395)
            ·
              refine ⟨94756120862491325564130593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63170747241660883709420395 94756120862491325564130593)
              ·
                refine ⟨71067090646868494173097945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 94756120862491325564130593 71067090646868494173097945)
                ·
                  refine ⟨53300317985151370629823459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 71067090646868494173097945 53300317985151370629823459)
                  ·
                    refine ⟨79950476977727055944735189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 53300317985151370629823459 79950476977727055944735189)
                    ·
                      refine ⟨1873839304165477873704731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 79950476977727055944735189 1873839304165477873704731)
                      ·
                        rfl

theorem cell23_3649289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 2, 2, 1, 7].length) (baseStart_3649289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3649289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3649289 prefixEnd_3649289 := by exact prefixLift 3649289
  have htrace : WordTrace (prefixWord ++ tailWord_3649289) baseStart_3649289 baseEnd_3649289 := by
    simpa [prefixWord, tailWord_3649289, baseEnd_3649289] using wordTrace_append hprefix tailTrace_3649289
  have hstable : (prefixWord ++ tailWord_3649289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3649289).length < 2 ^ (prefixWord ++ tailWord_3649289).sum := by decide
  have hdescent : baseEnd_3649289 < baseStart_3649289 := by decide
  rcases family_descends (prefixWord ++ tailWord_3649289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3649313 : List Nat := [1, 2, 3, 2, 1, 3, 3, 2, 1, 5]
def baseStart_3649313 : Nat := 118140960795 + 3649313 * 2 ^ 59
def prefixEnd_3649313 : Nat := 4983230072969 + 3 ^ 40 * 3649313 * 2
def baseEnd_3649313 : Nat := 624617209233728593268207

theorem tailTrace_3649313 : CollatzResearch.WordTrace tailWord_3649313 prefixEnd_3649313 624617209233728593268207 := by
  unfold tailWord_3649313
  simp only [CollatzResearch.WordTrace]
  refine ⟨133101379828169728885800593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88734253218779819257200395 133101379828169728885800593)
  ·
    refine ⟨99826034871127296664350445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133101379828169728885800593 99826034871127296664350445)
    ·
      refine ⟨37434763076672736249131417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 99826034871127296664350445 37434763076672736249131417)
      ·
        refine ⟨28076072307504552186848563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37434763076672736249131417 28076072307504552186848563)
        ·
          refine ⟨42114108461256828280272845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28076072307504552186848563 42114108461256828280272845)
          ·
            refine ⟨15792790672971310605102317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42114108461256828280272845 15792790672971310605102317)
            ·
              refine ⟨5922296502364241476913369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15792790672971310605102317 5922296502364241476913369)
              ·
                refine ⟨4441722376773181107685027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5922296502364241476913369 4441722376773181107685027)
                ·
                  refine ⟨6662583565159771661527541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4441722376773181107685027 6662583565159771661527541)
                  ·
                    refine ⟨624617209233728593268207, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6662583565159771661527541 624617209233728593268207)
                    ·
                      rfl

theorem cell23_3649313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 3, 2, 1, 5].length) (baseStart_3649313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3649313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3649313 prefixEnd_3649313 := by exact prefixLift 3649313
  have htrace : WordTrace (prefixWord ++ tailWord_3649313) baseStart_3649313 baseEnd_3649313 := by
    simpa [prefixWord, tailWord_3649313, baseEnd_3649313] using wordTrace_append hprefix tailTrace_3649313
  have hstable : (prefixWord ++ tailWord_3649313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3649313).length < 2 ^ (prefixWord ++ tailWord_3649313).sum := by decide
  have hdescent : baseEnd_3649313 < baseStart_3649313 := by decide
  rcases family_descends (prefixWord ++ tailWord_3649313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3649320 : List Nat := [2, 1, 5, 1, 1, 2, 1, 3, 2, 3, 2]
def baseStart_3649320 : Nat := 118140960795 + 3649320 * 2 ^ 59
def prefixEnd_3649320 : Nat := 4983230072969 + 3 ^ 40 * 3649320 * 2
def baseEnd_3649320 : Nat := 1873855222065767252417089

theorem tailTrace_3649320 : CollatzResearch.WordTrace tailWord_3649320 prefixEnd_3649320 1873855222065767252417089 := by
  unfold tailWord_3649320
  simp only [CollatzResearch.WordTrace]
  refine ⟨66550817569572184540652707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88734423426096246054203609 66550817569572184540652707)
  ·
    refine ⟨99826226354358276810979061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66550817569572184540652707 99826226354358276810979061)
    ·
      refine ⟨9358708720721088451029287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 99826226354358276810979061 9358708720721088451029287)
      ·
        refine ⟨14038063081081632676543931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9358708720721088451029287 14038063081081632676543931)
        ·
          refine ⟨21057094621622449014815897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14038063081081632676543931 21057094621622449014815897)
          ·
            refine ⟨15792820966216836761111923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21057094621622449014815897 15792820966216836761111923)
            ·
              refine ⟨23689231449325255141667885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15792820966216836761111923 23689231449325255141667885)
              ·
                refine ⟨8883461793496970678125457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23689231449325255141667885 8883461793496970678125457)
                ·
                  refine ⟨6662596345122728008594093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8883461793496970678125457 6662596345122728008594093)
                  ·
                    refine ⟨2498473629421023003222785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6662596345122728008594093 2498473629421023003222785)
                    ·
                      refine ⟨1873855222065767252417089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2498473629421023003222785 1873855222065767252417089)
                      ·
                        rfl

theorem cell23_3649320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 1, 3, 2, 3, 2].length) (baseStart_3649320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3649320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3649320 prefixEnd_3649320 := by exact prefixLift 3649320
  have htrace : WordTrace (prefixWord ++ tailWord_3649320) baseStart_3649320 baseEnd_3649320 := by
    simpa [prefixWord, tailWord_3649320, baseEnd_3649320] using wordTrace_append hprefix tailTrace_3649320
  have hstable : (prefixWord ++ tailWord_3649320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3649320).length < 2 ^ (prefixWord ++ tailWord_3649320).sum := by decide
  have hdescent : baseEnd_3649320 < baseStart_3649320 := by decide
  rcases family_descends (prefixWord ++ tailWord_3649320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3649330 : List Nat := [3, 2, 1, 1, 3, 3, 3, 1, 1, 5]
def baseStart_3649330 : Nat := 118140960795 + 3649330 * 2 ^ 59
def prefixEnd_3649330 : Nat := 4983230072969 + 3 ^ 40 * 3649330 * 2
def baseEnd_3649330 : Nat := 624620118957437404430681

theorem tailTrace_3649330 : CollatzResearch.WordTrace tailWord_3649330 prefixEnd_3649330 624620118957437404430681 := by
  unfold tailWord_3649330
  simp only [CollatzResearch.WordTrace]
  refine ⟨33275499967277035197292361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88734666579405427192779629 33275499967277035197292361)
  ·
    refine ⟨24956624975457776397969271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33275499967277035197292361 24956624975457776397969271)
    ·
      refine ⟨37434937463186664596953907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24956624975457776397969271 37434937463186664596953907)
      ·
        refine ⟨56152406194779996895430861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37434937463186664596953907 56152406194779996895430861)
        ·
          refine ⟨21057152323042498835786573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56152406194779996895430861 21057152323042498835786573)
          ·
            refine ⟨7896432121140937063419965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21057152323042498835786573 7896432121140937063419965)
            ·
              refine ⟨2961162045427851398782487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7896432121140937063419965 2961162045427851398782487)
              ·
                refine ⟨4441743068141777098173731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2961162045427851398782487 4441743068141777098173731)
                ·
                  refine ⟨6662614602212665647260597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4441743068141777098173731 6662614602212665647260597)
                  ·
                    refine ⟨624620118957437404430681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6662614602212665647260597 624620118957437404430681)
                    ·
                      rfl

theorem cell23_3649330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 3, 3, 1, 1, 5].length) (baseStart_3649330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3649330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3649330 prefixEnd_3649330 := by exact prefixLift 3649330
  have htrace : WordTrace (prefixWord ++ tailWord_3649330) baseStart_3649330 baseEnd_3649330 := by
    simpa [prefixWord, tailWord_3649330, baseEnd_3649330] using wordTrace_append hprefix tailTrace_3649330
  have hstable : (prefixWord ++ tailWord_3649330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3649330).length < 2 ^ (prefixWord ++ tailWord_3649330).sum := by decide
  have hdescent : baseEnd_3649330 < baseStart_3649330 := by decide
  rcases family_descends (prefixWord ++ tailWord_3649330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3649367 : List Nat := [1, 1, 3, 2, 5, 1, 1, 2, 3, 2, 2]
def baseStart_3649367 : Nat := 118140960795 + 3649367 * 2 ^ 59
def prefixEnd_3649367 : Nat := 4983230072969 + 3 ^ 40 * 3649367 * 2
def baseEnd_3649367 : Nat := 1873879355656528568529373

theorem tailTrace_3649367 : CollatzResearch.WordTrace tailWord_3649367 prefixEnd_3649367 1873879355656528568529373 := by
  unfold tailWord_3649367
  simp only [CollatzResearch.WordTrace]
  refine ⟨133103349369974096108266355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88735566246649397405510903 133103349369974096108266355)
  ·
    refine ⟨199655024054961144162399533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133103349369974096108266355 199655024054961144162399533)
    ·
      refine ⟨74870634020610429060899825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 199655024054961144162399533 74870634020610429060899825)
      ·
        refine ⟨56152975515457821795674869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74870634020610429060899825 56152975515457821795674869)
        ·
          refine ⟨5264341454574170793344519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 56152975515457821795674869 5264341454574170793344519)
          ·
            refine ⟨7896512181861256190016779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5264341454574170793344519 7896512181861256190016779)
            ·
              refine ⟨11844768272791884285025169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7896512181861256190016779 11844768272791884285025169)
              ·
                refine ⟨8883576204593913213768877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11844768272791884285025169 8883576204593913213768877)
                ·
                  refine ⟨3331341076722717455163329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8883576204593913213768877 3331341076722717455163329)
                  ·
                    refine ⟨2498505807542038091372497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3331341076722717455163329 2498505807542038091372497)
                    ·
                      refine ⟨1873879355656528568529373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2498505807542038091372497 1873879355656528568529373)
                      ·
                        rfl

theorem cell23_3649367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 1, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 1, 1, 2, 3, 2, 2].length) (baseStart_3649367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3649367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3649367 prefixEnd_3649367 := by exact prefixLift 3649367
  have htrace : WordTrace (prefixWord ++ tailWord_3649367) baseStart_3649367 baseEnd_3649367 := by
    simpa [prefixWord, tailWord_3649367, baseEnd_3649367] using wordTrace_append hprefix tailTrace_3649367
  have hstable : (prefixWord ++ tailWord_3649367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3649367).length < 2 ^ (prefixWord ++ tailWord_3649367).sum := by decide
  have hdescent : baseEnd_3649367 < baseStart_3649367 := by decide
  rcases family_descends (prefixWord ++ tailWord_3649367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3649383 : List Nat := [1, 1, 5, 1, 2, 1, 1, 4, 1, 3, 3]
def baseStart_3649383 : Nat := 118140960795 + 3649383 * 2 ^ 59
def prefixEnd_3649383 : Nat := 4983230072969 + 3 ^ 40 * 3649383 * 2
def baseEnd_3649383 : Nat := 1873887571347000505929299

theorem tailTrace_3649383 : CollatzResearch.WordTrace tailWord_3649383 prefixEnd_3649383 1873887571347000505929299 := by
  unfold tailWord_3649383
  simp only [CollatzResearch.WordTrace]
  refine ⟨133103932937916130840848803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88735955291944087227232535 133103932937916130840848803)
  ·
    refine ⟨199655899406874196261273205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133103932937916130840848803 199655899406874196261273205)
    ·
      refine ⟨18717740569394455899494363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 199655899406874196261273205 18717740569394455899494363)
      ·
        refine ⟨28076610854091683849241545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18717740569394455899494363 28076610854091683849241545)
        ·
          refine ⟨21057458140568762886931159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28076610854091683849241545 21057458140568762886931159)
          ·
            refine ⟨31586187210853144330396739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21057458140568762886931159 31586187210853144330396739)
            ·
              refine ⟨47379280816279716495595109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31586187210853144330396739 47379280816279716495595109)
              ·
                refine ⟨8883615153052446842924083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 47379280816279716495595109 8883615153052446842924083)
                ·
                  refine ⟨13325422729578670264386125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8883615153052446842924083 13325422729578670264386125)
                  ·
                    refine ⟨4997033523592001349144797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13325422729578670264386125 4997033523592001349144797)
                    ·
                      refine ⟨1873887571347000505929299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4997033523592001349144797 1873887571347000505929299)
                      ·
                        rfl

theorem cell23_3649383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 1, 4, 1, 3, 3].length) (baseStart_3649383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3649383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3649383 prefixEnd_3649383 := by exact prefixLift 3649383
  have htrace : WordTrace (prefixWord ++ tailWord_3649383) baseStart_3649383 baseEnd_3649383 := by
    simpa [prefixWord, tailWord_3649383, baseEnd_3649383] using wordTrace_append hprefix tailTrace_3649383
  have hstable : (prefixWord ++ tailWord_3649383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3649383).length < 2 ^ (prefixWord ++ tailWord_3649383).sum := by decide
  have hdescent : baseEnd_3649383 < baseStart_3649383 := by decide
  rcases family_descends (prefixWord ++ tailWord_3649383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3649384 : List Nat := [2, 1, 4, 2, 1, 1, 4, 3, 1, 2, 2]
def baseStart_3649384 : Nat := 118140960795 + 3649384 * 2 ^ 59
def prefixEnd_3649384 : Nat := 4983230072969 + 3 ^ 40 * 3649384 * 2
def baseEnd_3649384 : Nat := 1873888084827655002016795

theorem tailTrace_3649384 : CollatzResearch.WordTrace tailWord_3649384 prefixEnd_3649384 1873888084827655002016795 := by
  unfold tailWord_3649384
  simp only [CollatzResearch.WordTrace]
  refine ⟨66551984705456254005817603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88735979607275005341090137 66551984705456254005817603)
  ·
    refine ⟨99827977058184381008726405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66551984705456254005817603 99827977058184381008726405)
    ·
      refine ⟨18717745698409571439136201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 99827977058184381008726405 18717745698409571439136201)
      ·
        refine ⟨14038309273807178579352151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18717745698409571439136201 14038309273807178579352151)
        ·
          refine ⟨21057463910710767869028227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14038309273807178579352151 21057463910710767869028227)
          ·
            refine ⟨31586195866066151803542341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21057463910710767869028227 31586195866066151803542341)
            ·
              refine ⟨5922411724887403463164189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31586195866066151803542341 5922411724887403463164189)
              ·
                refine ⟨2220904396832776298686571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5922411724887403463164189 2220904396832776298686571)
                ·
                  refine ⟨3331356595249164448029857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2220904396832776298686571 3331356595249164448029857)
                  ·
                    refine ⟨2498517446436873336022393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3331356595249164448029857 2498517446436873336022393)
                    ·
                      refine ⟨1873888084827655002016795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2498517446436873336022393 1873888084827655002016795)
                      ·
                        rfl

theorem cell23_3649384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 4, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 4, 3, 1, 2, 2].length) (baseStart_3649384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3649384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3649384 prefixEnd_3649384 := by exact prefixLift 3649384
  have htrace : WordTrace (prefixWord ++ tailWord_3649384) baseStart_3649384 baseEnd_3649384 := by
    simpa [prefixWord, tailWord_3649384, baseEnd_3649384] using wordTrace_append hprefix tailTrace_3649384
  have hstable : (prefixWord ++ tailWord_3649384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3649384).length < 2 ^ (prefixWord ++ tailWord_3649384).sum := by decide
  have hdescent : baseEnd_3649384 < baseStart_3649384 := by decide
  rcases family_descends (prefixWord ++ tailWord_3649384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3649417 : List Nat := [1, 2, 1, 1, 5, 1, 5, 1, 2, 1, 3]
def baseStart_3649417 : Nat := 118140960795 + 3649417 * 2 ^ 59
def prefixEnd_3649417 : Nat := 4983230072969 + 3 ^ 40 * 3649417 * 2
def baseEnd_3649417 : Nat := 1873905029689253372904143

theorem tailTrace_3649417 : CollatzResearch.WordTrace tailWord_3649417 prefixEnd_3649417 1873905029689253372904143 := by
  unfold tailWord_3649417
  simp only [CollatzResearch.WordTrace]
  refine ⟨133105173019792954647586505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88736782013195303098391003 133105173019792954647586505)
  ·
    refine ⟨99828879764844715985689879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133105173019792954647586505 99828879764844715985689879)
    ·
      refine ⟨149743319647267073978534819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99828879764844715985689879 149743319647267073978534819)
      ·
        refine ⟨224614979470900610967802229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149743319647267073978534819 224614979470900610967802229)
        ·
          refine ⟨21057654325396932278231459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 224614979470900610967802229 21057654325396932278231459)
          ·
            refine ⟨31586481488095398417347189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21057654325396932278231459 31586481488095398417347189)
            ·
              refine ⟨2961232639508943601626299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 31586481488095398417347189 2961232639508943601626299)
              ·
                refine ⟨4441848959263415402439449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2961232639508943601626299 4441848959263415402439449)
                ·
                  refine ⟨3331386719447561551829587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4441848959263415402439449 3331386719447561551829587)
                  ·
                    refine ⟨4997080079171342327744381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3331386719447561551829587 4997080079171342327744381)
                    ·
                      refine ⟨1873905029689253372904143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4997080079171342327744381 1873905029689253372904143)
                      ·
                        rfl

theorem cell23_3649417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 5, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 5, 1, 2, 1, 3].length) (baseStart_3649417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3649417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3649417 prefixEnd_3649417 := by exact prefixLift 3649417
  have htrace : WordTrace (prefixWord ++ tailWord_3649417) baseStart_3649417 baseEnd_3649417 := by
    simpa [prefixWord, tailWord_3649417, baseEnd_3649417] using wordTrace_append hprefix tailTrace_3649417
  have hstable : (prefixWord ++ tailWord_3649417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3649417).length < 2 ^ (prefixWord ++ tailWord_3649417).sum := by decide
  have hdescent : baseEnd_3649417 < baseStart_3649417 := by decide
  rcases family_descends (prefixWord ++ tailWord_3649417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3649457 : List Nat := [1, 2, 2, 4, 2, 1, 2, 1, 4, 2, 2]
def baseStart_3649457 : Nat := 118140960795 + 3649457 * 2 ^ 59
def prefixEnd_3649457 : Nat := 4983230072969 + 3 ^ 40 * 3649457 * 2
def baseEnd_3649457 : Nat := 1873925568915433216403959

theorem tailTrace_3649457 : CollatzResearch.WordTrace tailWord_3649457 prefixEnd_3649457 1873925568915433216403959 := by
  unfold tailWord_3649457
  simp only [CollatzResearch.WordTrace]
  refine ⟨133106631939648041479042625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88737754626432027652695083 133106631939648041479042625)
  ·
    refine ⟨99829973954736031109281969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133106631939648041479042625 99829973954736031109281969)
    ·
      refine ⟨74872480466052023331961477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99829973954736031109281969 74872480466052023331961477)
      ·
        refine ⟨14038590087384754374742777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 74872480466052023331961477 14038590087384754374742777)
        ·
          refine ⟨10528942565538565781057083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14038590087384754374742777 10528942565538565781057083)
          ·
            refine ⟨15793413848307848671585625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10528942565538565781057083 15793413848307848671585625)
            ·
              refine ⟨11845060386230886503689219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15793413848307848671585625 11845060386230886503689219)
              ·
                refine ⟨17767590579346329755533829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11845060386230886503689219 17767590579346329755533829)
                ·
                  refine ⟨3331423233627436829162593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17767590579346329755533829 3331423233627436829162593)
                  ·
                    refine ⟨2498567425220577621871945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3331423233627436829162593 2498567425220577621871945)
                    ·
                      refine ⟨1873925568915433216403959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2498567425220577621871945 1873925568915433216403959)
                      ·
                        rfl

theorem cell23_3649457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 2, 1, 4, 2, 2].length) (baseStart_3649457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3649457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3649457 prefixEnd_3649457 := by exact prefixLift 3649457
  have htrace : WordTrace (prefixWord ++ tailWord_3649457) baseStart_3649457 baseEnd_3649457 := by
    simpa [prefixWord, tailWord_3649457, baseEnd_3649457] using wordTrace_append hprefix tailTrace_3649457
  have hstable : (prefixWord ++ tailWord_3649457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3649457).length < 2 ^ (prefixWord ++ tailWord_3649457).sum := by decide
  have hdescent : baseEnd_3649457 < baseStart_3649457 := by decide
  rcases family_descends (prefixWord ++ tailWord_3649457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3649466 : List Nat := [3, 1, 1, 1, 2, 1, 2, 1, 2, 1, 8]
def baseStart_3649466 : Nat := 118140960795 + 3649466 * 2 ^ 59
def prefixEnd_3649466 : Nat := 4983230072969 + 3 ^ 40 * 3649466 * 2
def baseEnd_3649466 : Nat := 1873930190241323681191417

theorem tailTrace_3649466 : CollatzResearch.WordTrace tailWord_3649466 prefixEnd_3649466 1873930190241323681191417 := by
  unfold tailWord_3649466
  simp only [CollatzResearch.WordTrace]
  refine ⟨33276740049153859004030063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88737973464410290677413501 33276740049153859004030063)
  ·
    refine ⟨49915110073730788506045095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33276740049153859004030063 49915110073730788506045095)
    ·
      refine ⟨74872665110596182759067643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49915110073730788506045095 74872665110596182759067643)
      ·
        refine ⟨112308997665894274138601465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74872665110596182759067643 112308997665894274138601465)
        ·
          refine ⟨84231748249420705603951099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 112308997665894274138601465 84231748249420705603951099)
          ·
            refine ⟨126347622374131058405926649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84231748249420705603951099 126347622374131058405926649)
            ·
              refine ⟨94760716780598293804444987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 126347622374131058405926649 94760716780598293804444987)
              ·
                refine ⟨142141075170897440706667481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 94760716780598293804444987 142141075170897440706667481)
                ·
                  refine ⟨106605806378173080530000611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 142141075170897440706667481 106605806378173080530000611)
                  ·
                    refine ⟨159908709567259620795000917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 106605806378173080530000611 159908709567259620795000917)
                    ·
                      refine ⟨1873930190241323681191417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 159908709567259620795000917 1873930190241323681191417)
                      ·
                        rfl

theorem cell23_3649466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 1, 2, 1, 8].length) (baseStart_3649466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3649466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3649466 prefixEnd_3649466 := by exact prefixLift 3649466
  have htrace : WordTrace (prefixWord ++ tailWord_3649466) baseStart_3649466 baseEnd_3649466 := by
    simpa [prefixWord, tailWord_3649466, baseEnd_3649466] using wordTrace_append hprefix tailTrace_3649466
  have hstable : (prefixWord ++ tailWord_3649466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3649466).length < 2 ^ (prefixWord ++ tailWord_3649466).sum := by decide
  have hdescent : baseEnd_3649466 < baseStart_3649466 := by decide
  rcases family_descends (prefixWord ++ tailWord_3649466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3649468 : List Nat := [2, 2, 2, 5, 2, 1, 2, 1, 2, 1, 3]
def baseStart_3649468 : Nat := 118140960795 + 3649468 * 2 ^ 59
def prefixEnd_3649468 : Nat := 4983230072969 + 3 ^ 40 * 3649468 * 2
def baseEnd_3649468 : Nat := 1873931217202632673366409

theorem tailTrace_3649468 : CollatzResearch.WordTrace tailWord_3649468 prefixEnd_3649468 1873931217202632673366409 := by
  unfold tailWord_3649468
  simp only [CollatzResearch.WordTrace]
  refine ⟨66553516571304095178846529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88738022095072126905128705 66553516571304095178846529)
  ·
    refine ⟨49915137428478071384134897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66553516571304095178846529 49915137428478071384134897)
    ·
      refine ⟨37436353071358553538101173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49915137428478071384134897 37436353071358553538101173)
      ·
        refine ⟨3509658100439864394196985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 37436353071358553538101173 3509658100439864394196985)
        ·
          refine ⟨2632243575329898295647739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3509658100439864394196985 2632243575329898295647739)
          ·
            refine ⟨3948365362994847443471609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2632243575329898295647739 3948365362994847443471609)
            ·
              refine ⟨2961274022246135582603707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3948365362994847443471609 2961274022246135582603707)
              ·
                refine ⟨4441911033369203373905561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2961274022246135582603707 4441911033369203373905561)
                ·
                  refine ⟨3331433275026902530429171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4441911033369203373905561 3331433275026902530429171)
                  ·
                    refine ⟨4997149912540353795643757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3331433275026902530429171 4997149912540353795643757)
                    ·
                      refine ⟨1873931217202632673366409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4997149912540353795643757 1873931217202632673366409)
                      ·
                        rfl

theorem cell23_3649468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 2, 1, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 2, 1, 2, 1, 2, 1, 3].length) (baseStart_3649468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3649468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3649468 prefixEnd_3649468 := by exact prefixLift 3649468
  have htrace : WordTrace (prefixWord ++ tailWord_3649468) baseStart_3649468 baseEnd_3649468 := by
    simpa [prefixWord, tailWord_3649468, baseEnd_3649468] using wordTrace_append hprefix tailTrace_3649468
  have hstable : (prefixWord ++ tailWord_3649468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3649468).length < 2 ^ (prefixWord ++ tailWord_3649468).sum := by decide
  have hdescent : baseEnd_3649468 < baseStart_3649468 := by decide
  rcases family_descends (prefixWord ++ tailWord_3649468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3649503 : List Nat := [1, 1, 2, 3, 4, 1, 1, 2, 1, 2, 5]
def baseStart_3649503 : Nat := 118140960795 + 3649503 * 2 ^ 59
def prefixEnd_3649503 : Nat := 4983230072969 + 3 ^ 40 * 3649503 * 2
def baseEnd_3649503 : Nat := 1873949189025540036428747

theorem tailTrace_3649503 : CollatzResearch.WordTrace tailWord_3649503 prefixEnd_3649503 1873949189025540036428747 := by
  unfold tailWord_3649503
  simp only [CollatzResearch.WordTrace]
  refine ⟨133108309697481391335217163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88738873131654260890144775 133108309697481391335217163)
  ·
    refine ⟨199662464546222087002825745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133108309697481391335217163 199662464546222087002825745)
    ·
      refine ⟨149746848409666565252119309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 199662464546222087002825745 149746848409666565252119309)
      ·
        refine ⟨56155068153624961969544741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 149746848409666565252119309 56155068153624961969544741)
        ·
          refine ⟨10529075278804680369289639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 56155068153624961969544741 10529075278804680369289639)
          ·
            refine ⟨15793612918207020553934459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10529075278804680369289639 15793612918207020553934459)
            ·
              refine ⟨23690419377310530830901689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15793612918207020553934459 23690419377310530830901689)
              ·
                refine ⟨17767814532982898123176267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23690419377310530830901689 17767814532982898123176267)
                ·
                  refine ⟨26651721799474347184764401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17767814532982898123176267 26651721799474347184764401)
                  ·
                    refine ⟨19988791349605760388573301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26651721799474347184764401 19988791349605760388573301)
                    ·
                      refine ⟨1873949189025540036428747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19988791349605760388573301 1873949189025540036428747)
                      ·
                        rfl

theorem cell23_3649503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 1, 2, 1, 2, 5].length) (baseStart_3649503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3649503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3649503 prefixEnd_3649503 := by exact prefixLift 3649503
  have htrace : WordTrace (prefixWord ++ tailWord_3649503) baseStart_3649503 baseEnd_3649503 := by
    simpa [prefixWord, tailWord_3649503, baseEnd_3649503] using wordTrace_append hprefix tailTrace_3649503
  have hstable : (prefixWord ++ tailWord_3649503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3649503).length < 2 ^ (prefixWord ++ tailWord_3649503).sum := by decide
  have hdescent : baseEnd_3649503 < baseStart_3649503 := by decide
  rcases family_descends (prefixWord ++ tailWord_3649503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3649523 : List Nat := [1, 1, 1, 2, 2, 2, 1, 2, 7, 4]
def baseStart_3649523 : Nat := 118140960795 + 3649523 * 2 ^ 59
def prefixEnd_3649523 : Nat := 4983230072969 + 3 ^ 40 * 3649523 * 2
def baseEnd_3649523 : Nat := 624653152879543319392885

theorem tailTrace_3649523 : CollatzResearch.WordTrace tailWord_3649523 prefixEnd_3649523 624653152879543319392885 := by
  unfold tailWord_3649523
  simp only [CollatzResearch.WordTrace]
  refine ⟨133109039157408934750945223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88739359438272623167296815 133109039157408934750945223)
  ·
    refine ⟨199663558736113402126417835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133109039157408934750945223 199663558736113402126417835)
    ·
      refine ⟨299495338104170103189626753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 199663558736113402126417835 299495338104170103189626753)
      ·
        refine ⟨224621503578127577392220065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 299495338104170103189626753 224621503578127577392220065)
        ·
          refine ⟨168466127683595683044165049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 224621503578127577392220065 168466127683595683044165049)
          ·
            refine ⟨126349595762696762283123787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 168466127683595683044165049 126349595762696762283123787)
            ·
              refine ⟨189524393644045143424685681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 126349595762696762283123787 189524393644045143424685681)
              ·
                refine ⟨142143295233033857568514261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 189524393644045143424685681 142143295233033857568514261)
                ·
                  refine ⟨3331483482024231036762053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 142143295233033857568514261 3331483482024231036762053)
                  ·
                    refine ⟨624653152879543319392885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3331483482024231036762053 624653152879543319392885)
                    ·
                      rfl

theorem cell23_3649523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 2, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 2, 7, 4].length) (baseStart_3649523 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3649523 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3649523 prefixEnd_3649523 := by exact prefixLift 3649523
  have htrace : WordTrace (prefixWord ++ tailWord_3649523) baseStart_3649523 baseEnd_3649523 := by
    simpa [prefixWord, tailWord_3649523, baseEnd_3649523] using wordTrace_append hprefix tailTrace_3649523
  have hstable : (prefixWord ++ tailWord_3649523).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3649523).length < 2 ^ (prefixWord ++ tailWord_3649523).sum := by decide
  have hdescent : baseEnd_3649523 < baseStart_3649523 := by decide
  rcases family_descends (prefixWord ++ tailWord_3649523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3649550 : List Nat := [4, 1, 1, 2, 2, 1, 3, 1, 1, 4, 3]
def baseStart_3649550 : Nat := 118140960795 + 3649550 * 2 ^ 59
def prefixEnd_3649550 : Nat := 4983230072969 + 3 ^ 40 * 3649550 * 2
def baseEnd_3649550 : Nat := 1873973322616301352541031

theorem tailTrace_3649550 : CollatzResearch.WordTrace tailWord_3649550 prefixEnd_3649550 1873973322616301352541031 := by
  unfold tailWord_3649550
  simp only [CollatzResearch.WordTrace]
  refine ⟨16638752991038889795272263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 88740015952207412241452069 16638752991038889795272263)
  ·
    refine ⟨24958129486558334692908395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16638752991038889795272263 24958129486558334692908395)
    ·
      refine ⟨37437194229837502039362593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24958129486558334692908395 37437194229837502039362593)
      ·
        refine ⟨28077895672378126529521945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37437194229837502039362593 28077895672378126529521945)
        ·
          refine ⟨21058421754283594897141459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28077895672378126529521945 21058421754283594897141459)
          ·
            refine ⟨31587632631425392345712189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21058421754283594897141459 31587632631425392345712189)
            ·
              refine ⟨11845362236784522129642071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31587632631425392345712189 11845362236784522129642071)
              ·
                refine ⟨17768043355176783194463107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11845362236784522129642071 17768043355176783194463107)
                ·
                  refine ⟨26652065032765174791694661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17768043355176783194463107 26652065032765174791694661)
                  ·
                    refine ⟨4997262193643470273442749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26652065032765174791694661 4997262193643470273442749)
                    ·
                      refine ⟨1873973322616301352541031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4997262193643470273442749 1873973322616301352541031)
                      ·
                        rfl

theorem cell23_3649550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 3, 1, 1, 4, 3].length) (baseStart_3649550 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3649550 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3649550 prefixEnd_3649550 := by exact prefixLift 3649550
  have htrace : WordTrace (prefixWord ++ tailWord_3649550) baseStart_3649550 baseEnd_3649550 := by
    simpa [prefixWord, tailWord_3649550, baseEnd_3649550] using wordTrace_append hprefix tailTrace_3649550
  have hstable : (prefixWord ++ tailWord_3649550).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3649550).length < 2 ^ (prefixWord ++ tailWord_3649550).sum := by decide
  have hdescent : baseEnd_3649550 < baseStart_3649550 := by decide
  rcases family_descends (prefixWord ++ tailWord_3649550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3649573 : List Nat := [1, 3, 1, 2, 2, 3, 1, 1, 1, 2, 6]
def baseStart_3649573 : Nat := 118140960795 + 3649573 * 2 ^ 59
def prefixEnd_3649573 : Nat := 4983230072969 + 3 ^ 40 * 3649573 * 2
def baseEnd_3649573 : Nat := 1873985132671354762553425

theorem tailTrace_3649573 : CollatzResearch.WordTrace tailWord_3649573 prefixEnd_3649573 1873985132671354762553425 := by
  unfold tailWord_3649573
  simp only [CollatzResearch.WordTrace]
  refine ⟨133110862807227793290265373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88740575204818528860176915 133110862807227793290265373)
  ·
    refine ⟨49916573552710422483849515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 133110862807227793290265373 49916573552710422483849515)
    ·
      refine ⟨74874860329065633725774273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49916573552710422483849515 74874860329065633725774273)
      ·
        refine ⟨56156145246799225294330705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74874860329065633725774273 56156145246799225294330705)
        ·
          refine ⟨42117108935099418970748029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56156145246799225294330705 42117108935099418970748029)
          ·
            refine ⟨15793915850662282114030511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42117108935099418970748029 15793915850662282114030511)
            ·
              refine ⟨23690873775993423171045767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15793915850662282114030511 23690873775993423171045767)
              ·
                refine ⟨35536310663990134756568651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23690873775993423171045767 35536310663990134756568651)
                ·
                  refine ⟨53304465995985202134852977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35536310663990134756568651 53304465995985202134852977)
                  ·
                    refine ⟨39978349496988901601139733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 53304465995985202134852977 39978349496988901601139733)
                    ·
                      refine ⟨1873985132671354762553425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 39978349496988901601139733 1873985132671354762553425)
                      ·
                        rfl

theorem cell23_3649573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 1, 1, 1, 2, 6].length) (baseStart_3649573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3649573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3649573 prefixEnd_3649573 := by exact prefixLift 3649573
  have htrace : WordTrace (prefixWord ++ tailWord_3649573) baseStart_3649573 baseEnd_3649573 := by
    simpa [prefixWord, tailWord_3649573, baseEnd_3649573] using wordTrace_append hprefix tailTrace_3649573
  have hstable : (prefixWord ++ tailWord_3649573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3649573).length < 2 ^ (prefixWord ++ tailWord_3649573).sum := by decide
  have hdescent : baseEnd_3649573 < baseStart_3649573 := by decide
  rcases family_descends (prefixWord ++ tailWord_3649573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3649583 : List Nat := [1, 1, 2, 1, 2, 1, 1, 6, 3, 5]
def baseStart_3649583 : Nat := 118140960795 + 3649583 * 2 ^ 59
def prefixEnd_3649583 : Nat := 4983230072969 + 3 ^ 40 * 3649583 * 2
def baseEnd_3649583 : Nat := 624663422492633241142793

theorem tailTrace_3649583 : CollatzResearch.WordTrace tailWord_3649583 prefixEnd_3649583 624663422492633241142793 := by
  unfold tailWord_3649583
  simp only [CollatzResearch.WordTrace]
  refine ⟨133111227537191564998129403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88740818358127709998752935 133111227537191564998129403)
  ·
    refine ⟨199666841305787347497194105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133111227537191564998129403 199666841305787347497194105)
    ·
      refine ⟨149750130979340510622895579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 199666841305787347497194105 149750130979340510622895579)
      ·
        refine ⟨224625196469010765934343369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149750130979340510622895579 224625196469010765934343369)
        ·
          refine ⟨168468897351758074450757527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 224625196469010765934343369 168468897351758074450757527)
          ·
            refine ⟨252703346027637111676136291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 168468897351758074450757527 252703346027637111676136291)
            ·
              refine ⟨379055019041455667514204437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 252703346027637111676136291 379055019041455667514204437)
              ·
                refine ⟨17768204017568234414728333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 379055019041455667514204437 17768204017568234414728333)
                ·
                  refine ⟨6663076506588087905523125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17768204017568234414728333 6663076506588087905523125)
                  ·
                    refine ⟨624663422492633241142793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6663076506588087905523125 624663422492633241142793)
                    ·
                      rfl

theorem cell23_3649583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 6, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 6, 3, 5].length) (baseStart_3649583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3649583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3649583 prefixEnd_3649583 := by exact prefixLift 3649583
  have htrace : WordTrace (prefixWord ++ tailWord_3649583) baseStart_3649583 baseEnd_3649583 := by
    simpa [prefixWord, tailWord_3649583, baseEnd_3649583] using wordTrace_append hprefix tailTrace_3649583
  have hstable : (prefixWord ++ tailWord_3649583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3649583).length < 2 ^ (prefixWord ++ tailWord_3649583).sum := by decide
  have hdescent : baseEnd_3649583 < baseStart_3649583 := by decide
  rcases family_descends (prefixWord ++ tailWord_3649583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3649590 : List Nat := [5, 1, 2, 1, 1, 1, 1, 2, 1, 2, 6]
def baseStart_3649590 : Nat := 118140960795 + 3649590 * 2 ^ 59
def prefixEnd_3649590 : Nat := 4983230072969 + 3 ^ 40 * 3649590 * 2
def baseEnd_3649590 : Nat := 1873993861842481196040847

theorem tailTrace_3649590 : CollatzResearch.WordTrace tailWord_3649590 prefixEnd_3649590 1873993861842481196040847 := by
  unfold tailWord_3649590
  simp only [CollatzResearch.WordTrace]
  refine ⟨8319467678010387824602139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 88740988565444136795756149 8319467678010387824602139)
  ·
    refine ⟨12479201517015581736903209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8319467678010387824602139 12479201517015581736903209)
    ·
      refine ⟨9359401137761686302677407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12479201517015581736903209 9359401137761686302677407)
      ·
        refine ⟨14039101706642529454016111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9359401137761686302677407 14039101706642529454016111)
        ·
          refine ⟨21058652559963794181024167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14039101706642529454016111 21058652559963794181024167)
          ·
            refine ⟨31587978839945691271536251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21058652559963794181024167 31587978839945691271536251)
            ·
              refine ⟨47381968259918536907304377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31587978839945691271536251 47381968259918536907304377)
              ·
                refine ⟨35536476194938902680478283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47381968259918536907304377 35536476194938902680478283)
                ·
                  refine ⟨53304714292408354020717425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35536476194938902680478283 53304714292408354020717425)
                  ·
                    refine ⟨39978535719306265515538069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 53304714292408354020717425 39978535719306265515538069)
                    ·
                      refine ⟨1873993861842481196040847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 39978535719306265515538069 1873993861842481196040847)
                      ·
                        rfl

theorem cell23_3649590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 1, 2, 1, 2, 6].length) (baseStart_3649590 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3649590 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3649590 prefixEnd_3649590 := by exact prefixLift 3649590
  have htrace : WordTrace (prefixWord ++ tailWord_3649590) baseStart_3649590 baseEnd_3649590 := by
    simpa [prefixWord, tailWord_3649590, baseEnd_3649590] using wordTrace_append hprefix tailTrace_3649590
  have hstable : (prefixWord ++ tailWord_3649590).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3649590).length < 2 ^ (prefixWord ++ tailWord_3649590).sum := by decide
  have hdescent : baseEnd_3649590 < baseStart_3649590 := by decide
  rcases family_descends (prefixWord ++ tailWord_3649590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3649597 : List Nat := [1, 4, 1, 3, 1, 1, 1, 4, 3, 1, 3]
def baseStart_3649597 : Nat := 118140960795 + 3649597 * 2 ^ 59
def prefixEnd_3649597 : Nat := 4983230072969 + 3 ^ 40 * 3649597 * 2
def baseEnd_3649597 : Nat := 1873997456207062668653315

theorem tailTrace_3649597 : CollatzResearch.WordTrace tailWord_3649597 prefixEnd_3649597 1873997456207062668653315 := by
  unfold tailWord_3649597
  simp only [CollatzResearch.WordTrace]
  refine ⟨133111738159140845389139045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88741158772760563592759363 133111738159140845389139045)
  ·
    refine ⟨24958450904838908510463571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 133111738159140845389139045 24958450904838908510463571)
    ·
      refine ⟨37437676357258362765695357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24958450904838908510463571 37437676357258362765695357)
      ·
        refine ⟨14039128633971886037135759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37437676357258362765695357 14039128633971886037135759)
        ·
          refine ⟨21058692950957829055703639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14039128633971886037135759 21058692950957829055703639)
          ·
            refine ⟨31588039426436743583555459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21058692950957829055703639 31588039426436743583555459)
            ·
              refine ⟨47382059139655115375333189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31588039426436743583555459 47382059139655115375333189)
              ·
                refine ⟨8884136088685334132874973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 47382059139655115375333189 8884136088685334132874973)
                ·
                  refine ⟨3331551033257000299828115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8884136088685334132874973 3331551033257000299828115)
                  ·
                    refine ⟨4997326549885500449742173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3331551033257000299828115 4997326549885500449742173)
                    ·
                      refine ⟨1873997456207062668653315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4997326549885500449742173 1873997456207062668653315)
                      ·
                        rfl

theorem cell23_3649597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 1, 4, 3, 1, 3].length) (baseStart_3649597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3649597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3649597 prefixEnd_3649597 := by exact prefixLift 3649597
  have htrace : WordTrace (prefixWord ++ tailWord_3649597) baseStart_3649597 baseEnd_3649597 := by
    simpa [prefixWord, tailWord_3649597, baseEnd_3649597] using wordTrace_append hprefix tailTrace_3649597
  have hstable : (prefixWord ++ tailWord_3649597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3649597).length < 2 ^ (prefixWord ++ tailWord_3649597).sum := by decide
  have hdescent : baseEnd_3649597 < baseStart_3649597 := by decide
  rcases family_descends (prefixWord ++ tailWord_3649597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3649600 : List Nat := [2, 1, 1, 2, 2, 4, 1, 4, 1, 5]
def baseStart_3649600 : Nat := 118140960795 + 3649600 * 2 ^ 59
def prefixEnd_3649600 : Nat := 4983230072969 + 3 ^ 40 * 3649600 * 2
def baseEnd_3649600 : Nat := 624666332216342052305267

theorem tailTrace_3649600 : CollatzResearch.WordTrace tailWord_3649600 prefixEnd_3649600 624666332216342052305267 := by
  unfold tailWord_3649600
  simp only [CollatzResearch.WordTrace]
  refine ⟨66555923789064988450749127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88741231718753317934332169 66555923789064988450749127)
  ·
    refine ⟨99833885683597482676123691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66555923789064988450749127 99833885683597482676123691)
    ·
      refine ⟨149750828525396224014185537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99833885683597482676123691 149750828525396224014185537)
      ·
        refine ⟨112313121394047168010639153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 149750828525396224014185537 112313121394047168010639153)
        ·
          refine ⟨84234841045535376007979365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 112313121394047168010639153 84234841045535376007979365)
          ·
            refine ⟨15794032696037883001496131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 84234841045535376007979365 15794032696037883001496131)
            ·
              refine ⟨23691049044056824502244197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15794032696037883001496131 23691049044056824502244197)
              ·
                refine ⟨4442071695760654594170787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23691049044056824502244197 4442071695760654594170787)
                ·
                  refine ⟨6663107543640981891256181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4442071695760654594170787 6663107543640981891256181)
                  ·
                    refine ⟨624666332216342052305267, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6663107543640981891256181 624666332216342052305267)
                    ·
                      rfl

theorem cell23_3649600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 1, 4, 1, 5].length) (baseStart_3649600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3649600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3649600 prefixEnd_3649600 := by exact prefixLift 3649600
  have htrace : WordTrace (prefixWord ++ tailWord_3649600) baseStart_3649600 baseEnd_3649600 := by
    simpa [prefixWord, tailWord_3649600, baseEnd_3649600] using wordTrace_append hprefix tailTrace_3649600
  have hstable : (prefixWord ++ tailWord_3649600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3649600).length < 2 ^ (prefixWord ++ tailWord_3649600).sum := by decide
  have hdescent : baseEnd_3649600 < baseStart_3649600 := by decide
  rcases family_descends (prefixWord ++ tailWord_3649600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3649607 : List Nat := [1, 1, 4, 1, 3, 1, 2, 3, 2, 3, 2]
def baseStart_3649607 : Nat := 118140960795 + 3649607 * 2 ^ 59
def prefixEnd_3649607 : Nat := 4983230072969 + 3 ^ 40 * 3649607 * 2
def baseEnd_3649607 : Nat := 1874002591013607629528269

theorem tailTrace_3649607 : CollatzResearch.WordTrace tailWord_3649607 prefixEnd_3649607 1874002591013607629528269 := by
  unfold tailWord_3649607
  simp only [CollatzResearch.WordTrace]
  refine ⟨133112102889104617097003075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88741401926069744731335383 133112102889104617097003075)
  ·
    refine ⟨199668154333656925645504613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133112102889104617097003075 199668154333656925645504613)
    ·
      refine ⟨37437778937560673558532115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 199668154333656925645504613 37437778937560673558532115)
      ·
        refine ⟨56156668406341010337798173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37437778937560673558532115 56156668406341010337798173)
        ·
          refine ⟨21058750652377878876674315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56156668406341010337798173 21058750652377878876674315)
          ·
            refine ⟨31588125978566818315011473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21058750652377878876674315 31588125978566818315011473)
            ·
              refine ⟨23691094483925113736258605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31588125978566818315011473 23691094483925113736258605)
              ·
                refine ⟨8884160431471917651096977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23691094483925113736258605 8884160431471917651096977)
                ·
                  refine ⟨6663120323603938238322733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8884160431471917651096977 6663120323603938238322733)
                  ·
                    refine ⟨2498670121351476839371025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6663120323603938238322733 2498670121351476839371025)
                    ·
                      refine ⟨1874002591013607629528269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2498670121351476839371025 1874002591013607629528269)
                      ·
                        rfl

theorem cell23_3649607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 2, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 2, 3, 2, 3, 2].length) (baseStart_3649607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3649607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3649607 prefixEnd_3649607 := by exact prefixLift 3649607
  have htrace : WordTrace (prefixWord ++ tailWord_3649607) baseStart_3649607 baseEnd_3649607 := by
    simpa [prefixWord, tailWord_3649607, baseEnd_3649607] using wordTrace_append hprefix tailTrace_3649607
  have hstable : (prefixWord ++ tailWord_3649607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3649607).length < 2 ^ (prefixWord ++ tailWord_3649607).sum := by decide
  have hdescent : baseEnd_3649607 < baseStart_3649607 := by decide
  rcases family_descends (prefixWord ++ tailWord_3649607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3649620 : List Nat := [2, 4, 1, 1, 1, 1, 1, 2, 5, 1, 4]
def baseStart_3649620 : Nat := 118140960795 + 3649620 * 2 ^ 59
def prefixEnd_3649620 : Nat := 4983230072969 + 3 ^ 40 * 3649620 * 2
def baseEnd_3649620 : Nat := 1874009266262116078665709

theorem tailTrace_3649620 : CollatzResearch.WordTrace tailWord_3649620 prefixEnd_3649620 1874009266262116078665709 := by
  unfold tailWord_3649620
  simp only [CollatzResearch.WordTrace]
  refine ⟨66556288519028760158613157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88741718025371680211484209 66556288519028760158613157)
  ·
    refine ⟨12479304097317892529739967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 66556288519028760158613157 12479304097317892529739967)
    ·
      refine ⟨18718956145976838794609951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12479304097317892529739967 18718956145976838794609951)
      ·
        refine ⟨28078434218965258191914927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18718956145976838794609951 28078434218965258191914927)
        ·
          refine ⟨42117651328447887287872391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28078434218965258191914927 42117651328447887287872391)
          ·
            refine ⟨63176476992671830931808587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42117651328447887287872391 63176476992671830931808587)
            ·
              refine ⟨94764715489007746397712881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63176476992671830931808587 94764715489007746397712881)
              ·
                refine ⟨71073536616755809798284661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 94764715489007746397712881 71073536616755809798284661)
                ·
                  refine ⟨6663144057820857168589187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 71073536616755809798284661 6663144057820857168589187)
                  ·
                    refine ⟨9994716086731285752883781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6663144057820857168589187 9994716086731285752883781)
                    ·
                      refine ⟨1874009266262116078665709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9994716086731285752883781 1874009266262116078665709)
                      ·
                        rfl

theorem cell23_3649620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 2, 5, 1, 4].length) (baseStart_3649620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3649620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3649620 prefixEnd_3649620 := by exact prefixLift 3649620
  have htrace : WordTrace (prefixWord ++ tailWord_3649620) baseStart_3649620 baseEnd_3649620 := by
    simpa [prefixWord, tailWord_3649620, baseEnd_3649620] using wordTrace_append hprefix tailTrace_3649620
  have hstable : (prefixWord ++ tailWord_3649620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3649620).length < 2 ^ (prefixWord ++ tailWord_3649620).sum := by decide
  have hdescent : baseEnd_3649620 < baseStart_3649620 := by decide
  rcases family_descends (prefixWord ++ tailWord_3649620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3649647 : List Nat := [1, 1, 2, 1, 3, 5, 1, 3, 2, 4]
def baseStart_3649647 : Nat := 118140960795 + 3649647 * 2 ^ 59
def prefixEnd_3649647 : Nat := 4983230072969 + 3 ^ 40 * 3649647 * 2
def baseEnd_3649647 : Nat := 624674376746595824342695

theorem tailTrace_3649647 : CollatzResearch.WordTrace tailWord_3649647 prefixEnd_3649647 624674376746595824342695 := by
  unfold tailWord_3649647
  simp only [CollatzResearch.WordTrace]
  refine ⟨133113561808959703928459195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88742374539306469285639463 133113561808959703928459195)
  ·
    refine ⟨199670342713439555892688793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133113561808959703928459195 199670342713439555892688793)
    ·
      refine ⟨149752757035079666919516595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 199670342713439555892688793 149752757035079666919516595)
      ·
        refine ⟨224629135552619500379274893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149752757035079666919516595 224629135552619500379274893)
        ·
          refine ⟨84235925832232312642228085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 224629135552619500379274893 84235925832232312642228085)
          ·
            refine ⟨7897118046771779310208883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 84235925832232312642228085 7897118046771779310208883)
            ·
              refine ⟨11845677070157668965313325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7897118046771779310208883 11845677070157668965313325)
              ·
                refine ⟨4442128901309125861992497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11845677070157668965313325 4442128901309125861992497)
                ·
                  refine ⟨3331596675981844396494373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4442128901309125861992497 3331596675981844396494373)
                  ·
                    refine ⟨624674376746595824342695, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3331596675981844396494373 624674376746595824342695)
                    ·
                      rfl

theorem cell23_3649647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 5, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 5, 1, 3, 2, 4].length) (baseStart_3649647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3649647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3649647 prefixEnd_3649647 := by exact prefixLift 3649647
  have htrace : WordTrace (prefixWord ++ tailWord_3649647) baseStart_3649647 baseEnd_3649647 := by
    simpa [prefixWord, tailWord_3649647, baseEnd_3649647] using wordTrace_append hprefix tailTrace_3649647
  have hstable : (prefixWord ++ tailWord_3649647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3649647).length < 2 ^ (prefixWord ++ tailWord_3649647).sum := by decide
  have hdescent : baseEnd_3649647 < baseStart_3649647 := by decide
  rcases family_descends (prefixWord ++ tailWord_3649647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3649650 : List Nat := [3, 2, 1, 2, 2, 2, 2, 1, 1, 1, 6]
def baseStart_3649650 : Nat := 118140960795 + 3649650 * 2 ^ 59
def prefixEnd_3649650 : Nat := 4983230072969 + 3 ^ 40 * 3649650 * 2
def baseEnd_3649650 : Nat := 1874024670681750961290571

theorem tailTrace_3649650 : CollatzResearch.WordTrace tailWord_3649650 prefixEnd_3649650 1874024670681750961290571 := by
  unfold tailWord_3649650
  simp only [CollatzResearch.WordTrace]
  refine ⟨33278417806987208860204601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88742447485299223627212269 33278417806987208860204601)
  ·
    refine ⟨24958813355240406645153451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33278417806987208860204601 24958813355240406645153451)
    ·
      refine ⟨37438220032860609967730177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24958813355240406645153451 37438220032860609967730177)
      ·
        refine ⟨28078665024645457475797633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37438220032860609967730177 28078665024645457475797633)
        ·
          refine ⟨21058998768484093106848225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28078665024645457475797633 21058998768484093106848225)
          ·
            refine ⟨15794249076363069830136169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21058998768484093106848225 15794249076363069830136169)
            ·
              refine ⟨11845686807272302372602127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15794249076363069830136169 11845686807272302372602127)
              ·
                refine ⟨17768530210908453558903191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11845686807272302372602127 17768530210908453558903191)
                ·
                  refine ⟨26652795316362680338354787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17768530210908453558903191 26652795316362680338354787)
                  ·
                    refine ⟨39979192974544020507532181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26652795316362680338354787 39979192974544020507532181)
                    ·
                      refine ⟨1874024670681750961290571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 39979192974544020507532181 1874024670681750961290571)
                      ·
                        rfl

theorem cell23_3649650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 2, 1, 1, 1, 6].length) (baseStart_3649650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3649650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3649650 prefixEnd_3649650 := by exact prefixLift 3649650
  have htrace : WordTrace (prefixWord ++ tailWord_3649650) baseStart_3649650 baseEnd_3649650 := by
    simpa [prefixWord, tailWord_3649650, baseEnd_3649650] using wordTrace_append hprefix tailTrace_3649650
  have hstable : (prefixWord ++ tailWord_3649650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3649650).length < 2 ^ (prefixWord ++ tailWord_3649650).sum := by decide
  have hdescent : baseEnd_3649650 < baseStart_3649650 := by decide
  rcases family_descends (prefixWord ++ tailWord_3649650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3649654 : List Nat := [5, 1, 1, 2, 1, 2, 3, 2, 1, 1, 4]
def baseStart_3649654 : Nat := 118140960795 + 3649654 * 2 ^ 59
def prefixEnd_3649654 : Nat := 4983230072969 + 3 ^ 40 * 3649654 * 2
def baseEnd_3649654 : Nat := 1874026724604368945640553

theorem tailTrace_3649654 : CollatzResearch.WordTrace tailWord_3649654 prefixEnd_3649654 1874026724604368945640553 := by
  unfold tailWord_3649654
  simp only [CollatzResearch.WordTrace]
  refine ⟨8319613569995896507747751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 88742544746622896082642677 8319613569995896507747751)
  ·
    refine ⟨12479420354993844761621627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8319613569995896507747751 12479420354993844761621627)
    ·
      refine ⟨18719130532490767142432441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12479420354993844761621627 18719130532490767142432441)
      ·
        refine ⟨14039347899368075356824331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18719130532490767142432441 14039347899368075356824331)
        ·
          refine ⟨21059021849052113035236497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14039347899368075356824331 21059021849052113035236497)
          ·
            refine ⟨15794266386789084776427373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21059021849052113035236497 15794266386789084776427373)
            ·
              refine ⟨5922849895045906791160265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15794266386789084776427373 5922849895045906791160265)
              ·
                refine ⟨4442137421284430093370199, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5922849895045906791160265 4442137421284430093370199)
                ·
                  refine ⟨6663206131926645140055299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4442137421284430093370199 6663206131926645140055299)
                  ·
                    refine ⟨9994809197889967710082949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6663206131926645140055299 9994809197889967710082949)
                    ·
                      refine ⟨1874026724604368945640553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9994809197889967710082949 1874026724604368945640553)
                      ·
                        rfl

theorem cell23_3649654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 3, 2, 1, 1, 4].length) (baseStart_3649654 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3649654 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3649654 prefixEnd_3649654 := by exact prefixLift 3649654
  have htrace : WordTrace (prefixWord ++ tailWord_3649654) baseStart_3649654 baseEnd_3649654 := by
    simpa [prefixWord, tailWord_3649654, baseEnd_3649654] using wordTrace_append hprefix tailTrace_3649654
  have hstable : (prefixWord ++ tailWord_3649654).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3649654).length < 2 ^ (prefixWord ++ tailWord_3649654).sum := by decide
  have hdescent : baseEnd_3649654 < baseStart_3649654 := by decide
  rcases family_descends (prefixWord ++ tailWord_3649654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3649657 : List Nat := [1, 2, 1, 3, 4, 2, 1, 1, 3, 2, 3]
def baseStart_3649657 : Nat := 118140960795 + 3649657 * 2 ^ 59
def prefixEnd_3649657 : Nat := 4983230072969 + 3 ^ 40 * 3649657 * 2
def baseEnd_3649657 : Nat := 1874028265046332433903039

theorem tailTrace_3649657 : CollatzResearch.WordTrace tailWord_3649657 prefixEnd_3649657 1874028265046332433903039 := by
  unfold tailWord_3649657
  simp only [CollatzResearch.WordTrace]
  refine ⟨133113926538923475636323225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88742617692615650424215483 133113926538923475636323225)
  ·
    refine ⟨99835444904192606727242419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133113926538923475636323225 99835444904192606727242419)
    ·
      refine ⟨149753167356288910090863629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99835444904192606727242419 149753167356288910090863629)
      ·
        refine ⟨56157437758608341284073861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 149753167356288910090863629 56157437758608341284073861)
        ·
          refine ⟨10529519579739063990763849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 56157437758608341284073861 10529519579739063990763849)
          ·
            refine ⟨7897139684804297993072887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10529519579739063990763849 7897139684804297993072887)
            ·
              refine ⟨11845709527206446989609331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7897139684804297993072887 11845709527206446989609331)
              ·
                refine ⟨17768564290809670484413997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11845709527206446989609331 17768564290809670484413997)
                ·
                  refine ⟨6663211609053626431655249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17768564290809670484413997 6663211609053626431655249)
                  ·
                    refine ⟨4997408706790219823741437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6663211609053626431655249 4997408706790219823741437)
                    ·
                      refine ⟨1874028265046332433903039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4997408706790219823741437 1874028265046332433903039)
                      ·
                        rfl

theorem cell23_3649657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 2, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 2, 1, 1, 3, 2, 3].length) (baseStart_3649657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3649657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3649657 prefixEnd_3649657 := by exact prefixLift 3649657
  have htrace : WordTrace (prefixWord ++ tailWord_3649657) baseStart_3649657 baseEnd_3649657 := by
    simpa [prefixWord, tailWord_3649657, baseEnd_3649657] using wordTrace_append hprefix tailTrace_3649657
  have hstable : (prefixWord ++ tailWord_3649657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3649657).length < 2 ^ (prefixWord ++ tailWord_3649657).sum := by decide
  have hdescent : baseEnd_3649657 < baseStart_3649657 := by decide
  rcases family_descends (prefixWord ++ tailWord_3649657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3649688 : List Nat := [2, 1, 2, 4, 3, 1, 1, 4, 1, 2, 2]
def baseStart_3649688 : Nat := 118140960795 + 3649688 * 2 ^ 59
def prefixEnd_3649688 : Nat := 4983230072969 + 3 ^ 40 * 3649688 * 2
def baseEnd_3649688 : Nat := 1874044182946621812615397

theorem tailTrace_3649688 : CollatzResearch.WordTrace tailWord_3649688 prefixEnd_3649688 1874044182946621812615397 := by
  unfold tailWord_3649688
  simp only [CollatzResearch.WordTrace]
  refine ⟨66557528600905583965350859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88743371467874111953801145 66557528600905583965350859)
  ·
    refine ⟨99836292901358375948026289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66557528600905583965350859 99836292901358375948026289)
    ·
      refine ⟨74877219676018781961019717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99836292901358375948026289 74877219676018781961019717)
      ·
        refine ⟨14039478689253521617691197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 74877219676018781961019717 14039478689253521617691197)
        ·
          refine ⟨5264804508470070606634199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14039478689253521617691197 5264804508470070606634199)
          ·
            refine ⟨7897206762705105909951299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5264804508470070606634199 7897206762705105909951299)
            ·
              refine ⟨11845810144057658864926949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7897206762705105909951299 11845810144057658864926949)
              ·
                refine ⟨2221089402010811037173803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11845810144057658864926949 2221089402010811037173803)
                ·
                  refine ⟨3331634103016216555760705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2221089402010811037173803 3331634103016216555760705)
                  ·
                    refine ⟨2498725577262162416820529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3331634103016216555760705 2498725577262162416820529)
                    ·
                      refine ⟨1874044182946621812615397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2498725577262162416820529 1874044182946621812615397)
                      ·
                        rfl

theorem cell23_3649688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 1, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 1, 1, 4, 1, 2, 2].length) (baseStart_3649688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3649688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3649688 prefixEnd_3649688 := by exact prefixLift 3649688
  have htrace : WordTrace (prefixWord ++ tailWord_3649688) baseStart_3649688 baseEnd_3649688 := by
    simpa [prefixWord, tailWord_3649688, baseEnd_3649688] using wordTrace_append hprefix tailTrace_3649688
  have hstable : (prefixWord ++ tailWord_3649688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3649688).length < 2 ^ (prefixWord ++ tailWord_3649688).sum := by decide
  have hdescent : baseEnd_3649688 < baseStart_3649688 := by decide
  rcases family_descends (prefixWord ++ tailWord_3649688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3649694 : List Nat := [4, 3, 1, 1, 3, 2, 1, 8]
def baseStart_3649694 : Nat := 118140960795 + 3649694 * 2 ^ 59
def prefixEnd_3649694 : Nat := 4983230072969 + 3 ^ 40 * 3649694 * 2
def baseEnd_3649694 : Nat := 69409157919649955153347

theorem tailTrace_3649694 : CollatzResearch.WordTrace tailWord_3649694 prefixEnd_3649694 69409157919649955153347 := by
  unfold tailWord_3649694
  simp only [CollatzResearch.WordTrace]
  refine ⟨16639409504973678869427517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 88743517359859620636946757 16639409504973678869427517)
  ·
    refine ⟨6239778564365129576035319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16639409504973678869427517 6239778564365129576035319)
    ·
      refine ⟨9359667846547694364052979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6239778564365129576035319 9359667846547694364052979)
      ·
        refine ⟨14039501769821541546079469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9359667846547694364052979 14039501769821541546079469)
        ·
          refine ⟨5264813163683078079779801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14039501769821541546079469 5264813163683078079779801)
          ·
            refine ⟨3948609872762308559834851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5264813163683078079779801 3948609872762308559834851)
            ·
              refine ⟨5922914809143462839752277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3948609872762308559834851 5922914809143462839752277)
              ·
                refine ⟨69409157919649955153347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5922914809143462839752277 69409157919649955153347)
                ·
                  rfl

theorem cell23_3649694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 2, 1, 8].length) (baseStart_3649694 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3649694 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3649694 prefixEnd_3649694 := by exact prefixLift 3649694
  have htrace : WordTrace (prefixWord ++ tailWord_3649694) baseStart_3649694 baseEnd_3649694 := by
    simpa [prefixWord, tailWord_3649694, baseEnd_3649694] using wordTrace_append hprefix tailTrace_3649694
  have hstable : (prefixWord ++ tailWord_3649694).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3649694).length < 2 ^ (prefixWord ++ tailWord_3649694).sum := by decide
  have hdescent : baseEnd_3649694 < baseStart_3649694 := by decide
  rcases family_descends (prefixWord ++ tailWord_3649694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3649714 : List Nat := [3, 2, 1, 1, 1, 3, 2, 4, 1, 3, 2]
def baseStart_3649714 : Nat := 118140960795 + 3649714 * 2 ^ 59
def prefixEnd_3649714 : Nat := 4983230072969 + 3 ^ 40 * 3649714 * 2
def baseEnd_3649714 : Nat := 1874057533443638710890277

theorem tailTrace_3649714 : CollatzResearch.WordTrace tailWord_3649714 prefixEnd_3649714 1874057533443638710890277 := by
  unfold tailWord_3649714
  simp only [CollatzResearch.WordTrace]
  refine ⟨33279001374929243592787049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88744003666477982914098797 33279001374929243592787049)
  ·
    refine ⟨24959251031196932694590287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33279001374929243592787049 24959251031196932694590287)
    ·
      refine ⟨37438876546795399041885431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24959251031196932694590287 37438876546795399041885431)
      ·
        refine ⟨56158314820193098562828147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37438876546795399041885431 56158314820193098562828147)
        ·
          refine ⟨84237472230289647844242221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56158314820193098562828147 84237472230289647844242221)
          ·
            refine ⟨31589052086358617941590833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 84237472230289647844242221 31589052086358617941590833)
            ·
              refine ⟨23691789064768963456193125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31589052086358617941590833 23691789064768963456193125)
              ·
                refine ⟨4442210449644180648036211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23691789064768963456193125 4442210449644180648036211)
                ·
                  refine ⟨6663315674466270972054317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4442210449644180648036211 6663315674466270972054317)
                  ·
                    refine ⟨2498743377924851614520369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6663315674466270972054317 2498743377924851614520369)
                    ·
                      refine ⟨1874057533443638710890277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2498743377924851614520369 1874057533443638710890277)
                      ·
                        rfl

theorem cell23_3649714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 2, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 2, 4, 1, 3, 2].length) (baseStart_3649714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3649714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3649714 prefixEnd_3649714 := by exact prefixLift 3649714
  have htrace : WordTrace (prefixWord ++ tailWord_3649714) baseStart_3649714 baseEnd_3649714 := by
    simpa [prefixWord, tailWord_3649714, baseEnd_3649714] using wordTrace_append hprefix tailTrace_3649714
  have hstable : (prefixWord ++ tailWord_3649714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3649714).length < 2 ^ (prefixWord ++ tailWord_3649714).sum := by decide
  have hdescent : baseEnd_3649714 < baseStart_3649714 := by decide
  rcases family_descends (prefixWord ++ tailWord_3649714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3649767 : List Nat := [1, 1, 5, 3, 1, 1, 2, 2, 7]
def baseStart_3649767 : Nat := 118140960795 + 3649767 * 2 ^ 59
def prefixEnd_3649767 : Nat := 4983230072969 + 3 ^ 40 * 3649767 * 2
def baseEnd_3649767 : Nat := 208231638657591889280837

theorem tailTrace_3649767 : CollatzResearch.WordTrace tailWord_3649767 prefixEnd_3649767 208231638657591889280837 := by
  unfold tailWord_3649767
  simp only [CollatzResearch.WordTrace]
  refine ⟨133117938568524964422827555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88745292379016642948551703 133117938568524964422827555)
  ·
    refine ⟨199676907852787446634241333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133117938568524964422827555 199676907852787446634241333)
    ·
      refine ⟨18719710111198823121960125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 199676907852787446634241333 18719710111198823121960125)
      ·
        refine ⟨7019891291699558670735047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18719710111198823121960125 7019891291699558670735047)
        ·
          refine ⟨10529836937549338006102571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7019891291699558670735047 10529836937549338006102571)
          ·
            refine ⟨15794755406324007009153857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10529836937549338006102571 15794755406324007009153857)
            ·
              refine ⟨11846066554743005256865393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15794755406324007009153857 11846066554743005256865393)
              ·
                refine ⟨8884549916057253942649045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11846066554743005256865393 8884549916057253942649045)
                ·
                  refine ⟨208231638657591889280837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8884549916057253942649045 208231638657591889280837)
                  ·
                    rfl

theorem cell23_3649767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 2, 2, 7].length) (baseStart_3649767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3649767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3649767 prefixEnd_3649767 := by exact prefixLift 3649767
  have htrace : WordTrace (prefixWord ++ tailWord_3649767) baseStart_3649767 baseEnd_3649767 := by
    simpa [prefixWord, tailWord_3649767, baseEnd_3649767] using wordTrace_append hprefix tailTrace_3649767
  have hstable : (prefixWord ++ tailWord_3649767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3649767).length < 2 ^ (prefixWord ++ tailWord_3649767).sum := by decide
  have hdescent : baseEnd_3649767 < baseStart_3649767 := by decide
  rcases family_descends (prefixWord ++ tailWord_3649767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3649827 : List Nat := [1, 1, 1, 4, 2, 2, 2, 1, 5, 4]
def baseStart_3649827 : Nat := 118140960795 + 3649827 * 2 ^ 59
def prefixEnd_3649827 : Nat := 4983230072969 + 3 ^ 40 * 3649827 * 2
def baseEnd_3649827 : Nat := 624705185585865589592419

theorem tailTrace_3649827 : CollatzResearch.WordTrace tailWord_3649827 prefixEnd_3649827 624705185585865589592419 := by
  unfold tailWord_3649827
  simp only [CollatzResearch.WordTrace]
  refine ⟨133120126948307594670011735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88746751298871729780007823 133120126948307594670011735)
  ·
    refine ⟨199680190422461392005017603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133120126948307594670011735 199680190422461392005017603)
    ·
      refine ⟨299520285633692088007526405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 199680190422461392005017603 299520285633692088007526405)
      ·
        refine ⟨56160053556317266501411201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 299520285633692088007526405 56160053556317266501411201)
        ·
          refine ⟨42120040167237949876058401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56160053556317266501411201 42120040167237949876058401)
          ·
            refine ⟨31590030125428462407043801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42120040167237949876058401 31590030125428462407043801)
            ·
              refine ⟨23692522594071346805282851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31590030125428462407043801 23692522594071346805282851)
              ·
                refine ⟨35538783891107020207924277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23692522594071346805282851 35538783891107020207924277)
                ·
                  refine ⟨3331760989791283144492901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 35538783891107020207924277 3331760989791283144492901)
                  ·
                    refine ⟨624705185585865589592419, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3331760989791283144492901 624705185585865589592419)
                    ·
                      rfl

theorem cell23_3649827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 2, 1, 5, 4].length) (baseStart_3649827 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3649827 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3649827 prefixEnd_3649827 := by exact prefixLift 3649827
  have htrace : WordTrace (prefixWord ++ tailWord_3649827) baseStart_3649827 baseEnd_3649827 := by
    simpa [prefixWord, tailWord_3649827, baseEnd_3649827] using wordTrace_append hprefix tailTrace_3649827
  have hstable : (prefixWord ++ tailWord_3649827).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3649827).length < 2 ^ (prefixWord ++ tailWord_3649827).sum := by decide
  have hdescent : baseEnd_3649827 < baseStart_3649827 := by decide
  rcases family_descends (prefixWord ++ tailWord_3649827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3649840 : List Nat := [2, 1, 1, 1, 2, 2, 2, 4, 8]
def baseStart_3649840 : Nat := 118140960795 + 3649840 * 2 ^ 59
def prefixEnd_3649840 : Nat := 4983230072969 + 3 ^ 40 * 3649840 * 2
def baseEnd_3649840 : Nat := 208235803556233913101633

theorem tailTrace_3649840 : CollatzResearch.WordTrace tailWord_3649840 prefixEnd_3649840 208235803556233913101633 := by
  unfold tailWord_3649840
  simp only [CollatzResearch.WordTrace]
  refine ⟨66560300548630248945117487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88747067398173665260156649 66560300548630248945117487)
  ·
    refine ⟨99840450822945373417676231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66560300548630248945117487 99840450822945373417676231)
    ·
      refine ⟨149760676234418060126514347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99840450822945373417676231 149760676234418060126514347)
      ·
        refine ⟨224641014351627090189771521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149760676234418060126514347 224641014351627090189771521)
        ·
          refine ⟨168480760763720317642328641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 224641014351627090189771521 168480760763720317642328641)
          ·
            refine ⟨126360570572790238231746481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 168480760763720317642328641 126360570572790238231746481)
            ·
              refine ⟨94770427929592678673809861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 126360570572790238231746481 94770427929592678673809861)
              ·
                refine ⟨17769455236798627251339349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 94770427929592678673809861 17769455236798627251339349)
                ·
                  refine ⟨208235803556233913101633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 17769455236798627251339349 208235803556233913101633)
                  ·
                    rfl

theorem cell23_3649840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 4, 8].length) (baseStart_3649840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3649840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3649840 prefixEnd_3649840 := by exact prefixLift 3649840
  have htrace : WordTrace (prefixWord ++ tailWord_3649840) baseStart_3649840 baseEnd_3649840 := by
    simpa [prefixWord, tailWord_3649840, baseEnd_3649840] using wordTrace_append hprefix tailTrace_3649840
  have hstable : (prefixWord ++ tailWord_3649840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3649840).length < 2 ^ (prefixWord ++ tailWord_3649840).sum := by decide
  have hdescent : baseEnd_3649840 < baseStart_3649840 := by decide
  rcases family_descends (prefixWord ++ tailWord_3649840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3649887 : List Nat := [1, 1, 2, 3, 1, 2, 4, 1, 3, 5]
def baseStart_3649887 : Nat := 118140960795 + 3649887 * 2 ^ 59
def prefixEnd_3649887 : Nat := 4983230072969 + 3 ^ 40 * 3649887 * 2
def baseEnd_3649887 : Nat := 624715455198955511342327

theorem tailTrace_3649887 : CollatzResearch.WordTrace tailWord_3649887 prefixEnd_3649887 624715455198955511342327 := by
  unfold tailWord_3649887
  simp only [CollatzResearch.WordTrace]
  refine ⟨133122315328090224917195915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88748210218726816611463943 133122315328090224917195915)
  ·
    refine ⟨199683472992135337375793873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133122315328090224917195915 199683472992135337375793873)
    ·
      refine ⟨149762604744101503031845405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 199683472992135337375793873 149762604744101503031845405)
      ·
        refine ⟨56160976779038063636942027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 149762604744101503031845405 56160976779038063636942027)
        ·
          refine ⟨84241465168557095455413041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56160976779038063636942027 84241465168557095455413041)
          ·
            refine ⟨63181098876417821591559781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84241465168557095455413041 63181098876417821591559781)
            ·
              refine ⟨11846456039328341548417459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 63181098876417821591559781 11846456039328341548417459)
              ·
                refine ⟨17769684058992512322626189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11846456039328341548417459 17769684058992512322626189)
                ·
                  refine ⟨6663631522122192120984821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17769684058992512322626189 6663631522122192120984821)
                  ·
                    refine ⟨624715455198955511342327, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6663631522122192120984821 624715455198955511342327)
                    ·
                      rfl

theorem cell23_3649887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 4, 1, 3, 5].length) (baseStart_3649887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3649887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3649887 prefixEnd_3649887 := by exact prefixLift 3649887
  have htrace : WordTrace (prefixWord ++ tailWord_3649887) baseStart_3649887 baseEnd_3649887 := by
    simpa [prefixWord, tailWord_3649887, baseEnd_3649887] using wordTrace_append hprefix tailTrace_3649887
  have hstable : (prefixWord ++ tailWord_3649887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3649887).length < 2 ^ (prefixWord ++ tailWord_3649887).sum := by decide
  have hdescent : baseEnd_3649887 < baseStart_3649887 := by decide
  rcases family_descends (prefixWord ++ tailWord_3649887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3649888 : List Nat := [2, 1, 1, 3, 6, 1, 1, 1, 2, 2, 3]
def baseStart_3649888 : Nat := 118140960795 + 3649888 * 2 ^ 59
def prefixEnd_3649888 : Nat := 4983230072969 + 3 ^ 40 * 3649888 * 2
def baseEnd_3649888 : Nat := 1874146879077521030114477

theorem tailTrace_3649888 : CollatzResearch.WordTrace tailWord_3649888 prefixEnd_3649888 1874146879077521030114477 := by
  unfold tailWord_3649888
  simp only [CollatzResearch.WordTrace]
  refine ⟨66561175900543301043991159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88748234534057734725321545 66561175900543301043991159)
  ·
    refine ⟨99841763850814951565986739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66561175900543301043991159 99841763850814951565986739)
    ·
      refine ⟨149762645776222427348980109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99841763850814951565986739 149762645776222427348980109)
      ·
        refine ⟨56160992166083410255867541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 149762645776222427348980109 56160992166083410255867541)
        ·
          refine ⟨2632546507785159855743791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 56160992166083410255867541 2632546507785159855743791)
          ·
            refine ⟨3948819761677739783615687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2632546507785159855743791 3948819761677739783615687)
            ·
              refine ⟨5923229642516609675423531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3948819761677739783615687 5923229642516609675423531)
              ·
                refine ⟨8884844463774914513135297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5923229642516609675423531 8884844463774914513135297)
                ·
                  refine ⟨6663633347831185884851473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8884844463774914513135297 6663633347831185884851473)
                  ·
                    refine ⟨4997725010873389413638605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6663633347831185884851473 4997725010873389413638605)
                    ·
                      refine ⟨1874146879077521030114477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4997725010873389413638605 1874146879077521030114477)
                      ·
                        rfl

theorem cell23_3649888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 6, 1, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 6, 1, 1, 1, 2, 2, 3].length) (baseStart_3649888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3649888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3649888 prefixEnd_3649888 := by exact prefixLift 3649888
  have htrace : WordTrace (prefixWord ++ tailWord_3649888) baseStart_3649888 baseEnd_3649888 := by
    simpa [prefixWord, tailWord_3649888, baseEnd_3649888] using wordTrace_append hprefix tailTrace_3649888
  have hstable : (prefixWord ++ tailWord_3649888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3649888).length < 2 ^ (prefixWord ++ tailWord_3649888).sum := by decide
  have hdescent : baseEnd_3649888 < baseStart_3649888 := by decide
  rcases family_descends (prefixWord ++ tailWord_3649888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3649904 : List Nat := [2, 1, 1, 1, 4, 4, 1, 3, 1, 5]
def baseStart_3649904 : Nat := 118140960795 + 3649904 * 2 ^ 59
def prefixEnd_3649904 : Nat := 4983230072969 + 3 ^ 40 * 3649904 * 2
def baseEnd_3649904 : Nat := 624718364922664322504801

theorem tailTrace_3649904 : CollatzResearch.WordTrace tailWord_3649904 prefixEnd_3649904 624718364922664322504801 := by
  unfold tailWord_3649904
  simp only [CollatzResearch.WordTrace]
  refine ⟨66561467684514318410282383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88748623579352424547043177 66561467684514318410282383)
  ·
    refine ⟨99842201526771477615423575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66561467684514318410282383 99842201526771477615423575)
    ·
      refine ⟨149763302290157216423135363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99842201526771477615423575 149763302290157216423135363)
      ·
        refine ⟨224644953435235824634703045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149763302290157216423135363 224644953435235824634703045)
        ·
          refine ⟨42120928769106717119006821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 224644953435235824634703045 42120928769106717119006821)
          ·
            refine ⟨7897674144207509459813779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 42120928769106717119006821 7897674144207509459813779)
            ·
              refine ⟨11846511216311264189720669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7897674144207509459813779 11846511216311264189720669)
              ·
                refine ⟨4442441706116724071145251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11846511216311264189720669 4442441706116724071145251)
                ·
                  refine ⟨6663662559175086106717877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4442441706116724071145251 6663662559175086106717877)
                  ·
                    refine ⟨624718364922664322504801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6663662559175086106717877 624718364922664322504801)
                    ·
                      rfl

theorem cell23_3649904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 4, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 4, 1, 3, 1, 5].length) (baseStart_3649904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3649904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3649904 prefixEnd_3649904 := by exact prefixLift 3649904
  have htrace : WordTrace (prefixWord ++ tailWord_3649904) baseStart_3649904 baseEnd_3649904 := by
    simpa [prefixWord, tailWord_3649904, baseEnd_3649904] using wordTrace_append hprefix tailTrace_3649904
  have hstable : (prefixWord ++ tailWord_3649904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3649904).length < 2 ^ (prefixWord ++ tailWord_3649904).sum := by decide
  have hdescent : baseEnd_3649904 < baseStart_3649904 := by decide
  rcases family_descends (prefixWord ++ tailWord_3649904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3649954 : List Nat := [3, 3, 1, 2, 1, 1, 2, 1, 3, 2, 4]
def baseStart_3649954 : Nat := 118140960795 + 3649954 * 2 ^ 59
def prefixEnd_3649954 : Nat := 4983230072969 + 3 ^ 40 * 3649954 * 2
def baseEnd_3649954 : Nat := 1874180768800717771889173

theorem tailTrace_3649954 : CollatzResearch.WordTrace tailWord_3649954 prefixEnd_3649954 1874180768800717771889173 := by
  unfold tailWord_3649954
  simp only [CollatzResearch.WordTrace]
  refine ⟨33281189754711873839971229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88749839345898330239923277 33281189754711873839971229)
  ·
    refine ⟨12480446158016952689989211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33281189754711873839971229 12480446158016952689989211)
    ·
      refine ⟨18720669237025429034983817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12480446158016952689989211 18720669237025429034983817)
      ·
        refine ⟨14040501927769071776237863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18720669237025429034983817 14040501927769071776237863)
        ·
          refine ⟨21060752891653607664356795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14040501927769071776237863 21060752891653607664356795)
          ·
            refine ⟨31591129337480411496535193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21060752891653607664356795 31591129337480411496535193)
            ·
              refine ⟨23693347003110308622401395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31591129337480411496535193 23693347003110308622401395)
              ·
                refine ⟨35540020504665462933602093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23693347003110308622401395 35540020504665462933602093)
                ·
                  refine ⟨13327507689249548600100785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35540020504665462933602093 13327507689249548600100785)
                  ·
                    refine ⟨9995630766937161450075589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13327507689249548600100785 9995630766937161450075589)
                    ·
                      refine ⟨1874180768800717771889173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9995630766937161450075589 1874180768800717771889173)
                      ·
                        rfl

theorem cell23_3649954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 2, 1, 3, 2, 4].length) (baseStart_3649954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3649954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3649954 prefixEnd_3649954 := by exact prefixLift 3649954
  have htrace : WordTrace (prefixWord ++ tailWord_3649954) baseStart_3649954 baseEnd_3649954 := by
    simpa [prefixWord, tailWord_3649954, baseEnd_3649954] using wordTrace_append hprefix tailTrace_3649954
  have hstable : (prefixWord ++ tailWord_3649954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3649954).length < 2 ^ (prefixWord ++ tailWord_3649954).sum := by decide
  have hdescent : baseEnd_3649954 < baseStart_3649954 := by decide
  rcases family_descends (prefixWord ++ tailWord_3649954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3649962 : List Nat := [3, 1, 6, 1, 1, 1, 1, 2, 2, 3, 2]
def baseStart_3649962 : Nat := 118140960795 + 3649962 * 2 ^ 59
def prefixEnd_3649962 : Nat := 4983230072969 + 3 ^ 40 * 3649962 * 2
def baseEnd_3649962 : Nat := 1874184876645953740589137

theorem tailTrace_3649962 : CollatzResearch.WordTrace tailWord_3649962 prefixEnd_3649962 1874184876645953740589137 := by
  unfold tailWord_3649962
  simp only [CollatzResearch.WordTrace]
  refine ⟨33281262700704628181544035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88750033868545675150784093 33281262700704628181544035)
  ·
    refine ⟨49921894051056942272316053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33281262700704628181544035 49921894051056942272316053)
    ·
      refine ⟨2340088783643294169014815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 49921894051056942272316053 2340088783643294169014815)
      ·
        refine ⟨3510133175464941253522223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2340088783643294169014815 3510133175464941253522223)
        ·
          refine ⟨5265199763197411880283335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3510133175464941253522223 5265199763197411880283335)
          ·
            refine ⟨7897799644796117820425003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5265199763197411880283335 7897799644796117820425003)
            ·
              refine ⟨11846699467194176730637505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7897799644796117820425003 11846699467194176730637505)
              ·
                refine ⟨8885024600395632547978129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11846699467194176730637505 8885024600395632547978129)
                ·
                  refine ⟨6663768450296724410983597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8885024600395632547978129 6663768450296724410983597)
                  ·
                    refine ⟨2498913168861271654118849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6663768450296724410983597 2498913168861271654118849)
                    ·
                      refine ⟨1874184876645953740589137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2498913168861271654118849 1874184876645953740589137)
                      ·
                        rfl

theorem cell23_3649962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 1, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 1, 1, 2, 2, 3, 2].length) (baseStart_3649962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3649962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3649962 prefixEnd_3649962 := by exact prefixLift 3649962
  have htrace : WordTrace (prefixWord ++ tailWord_3649962) baseStart_3649962 baseEnd_3649962 := by
    simpa [prefixWord, tailWord_3649962, baseEnd_3649962] using wordTrace_append hprefix tailTrace_3649962
  have hstable : (prefixWord ++ tailWord_3649962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3649962).length < 2 ^ (prefixWord ++ tailWord_3649962).sum := by decide
  have hdescent : baseEnd_3649962 < baseStart_3649962 := by decide
  rcases family_descends (prefixWord ++ tailWord_3649962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3649984 : List Nat := [2, 1, 1, 2, 3, 1, 1, 1, 2, 7, 2]
def baseStart_3649984 : Nat := 118140960795 + 3649984 * 2 ^ 59
def prefixEnd_3649984 : Nat := 4983230072969 + 3 ^ 40 * 3649984 * 2
def baseEnd_3649984 : Nat := 1874196173220352654514035

theorem tailTrace_3649984 : CollatzResearch.WordTrace tailWord_3649984 prefixEnd_3649984 1874196173220352654514035 := by
  unfold tailWord_3649984
  simp only [CollatzResearch.WordTrace]
  refine ⟨66562926604369405241738503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88750568805825873655651337 66562926604369405241738503)
  ·
    refine ⟨99844389906554107862607755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66562926604369405241738503 99844389906554107862607755)
    ·
      refine ⟨149766584859831161793911633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99844389906554107862607755 149766584859831161793911633)
      ·
        refine ⟨112324938644873371345433725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 149766584859831161793911633 112324938644873371345433725)
        ·
          refine ⟨42121851991827514254537647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 112324938644873371345433725 42121851991827514254537647)
          ·
            refine ⟨63182777987741271381806471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42121851991827514254537647 63182777987741271381806471)
            ·
              refine ⟨94774166981611907072709707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63182777987741271381806471 94774166981611907072709707)
              ·
                refine ⟨142161250472417860609064561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 94774166981611907072709707 142161250472417860609064561)
                ·
                  refine ⟨106620937854313395456798421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 142161250472417860609064561 106620937854313395456798421)
                  ·
                    refine ⟨2498928230960470206018713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 106620937854313395456798421 2498928230960470206018713)
                    ·
                      refine ⟨1874196173220352654514035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2498928230960470206018713 1874196173220352654514035)
                      ·
                        rfl

theorem cell23_3649984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 1, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 1, 2, 7, 2].length) (baseStart_3649984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3649984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3649984 prefixEnd_3649984 := by exact prefixLift 3649984
  have htrace : WordTrace (prefixWord ++ tailWord_3649984) baseStart_3649984 baseEnd_3649984 := by
    simpa [prefixWord, tailWord_3649984, baseEnd_3649984] using wordTrace_append hprefix tailTrace_3649984
  have hstable : (prefixWord ++ tailWord_3649984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3649984).length < 2 ^ (prefixWord ++ tailWord_3649984).sum := by decide
  have hdescent : baseEnd_3649984 < baseStart_3649984 := by decide
  rcases family_descends (prefixWord ++ tailWord_3649984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3650007 : List Nat := [1, 1, 3, 2, 1, 1, 1, 1, 6, 6]
def baseStart_3650007 : Nat := 118140960795 + 3650007 * 2 ^ 59
def prefixEnd_3650007 : Nat := 4983230072969 + 3 ^ 40 * 3650007 * 2
def baseEnd_3650007 : Nat := 624735994425135354842143

theorem tailTrace_3650007 : CollatzResearch.WordTrace tailWord_3650007 prefixEnd_3650007 624735994425135354842143 := by
  unfold tailWord_3650007
  simp only [CollatzResearch.WordTrace]
  refine ⟨133126692087655485411564275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88751128058436990274376183 133126692087655485411564275)
  ·
    refine ⟨199690038131483228117346413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133126692087655485411564275 199690038131483228117346413)
    ·
      refine ⟨74883764299306210544004905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 199690038131483228117346413 74883764299306210544004905)
      ·
        refine ⟨56162823224479657908003679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74883764299306210544004905 56162823224479657908003679)
        ·
          refine ⟨84244234836719486862005519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56162823224479657908003679 84244234836719486862005519)
          ·
            refine ⟨126366352255079230293008279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84244234836719486862005519 126366352255079230293008279)
            ·
              refine ⟨189549528382618845439512419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 126366352255079230293008279 189549528382618845439512419)
              ·
                refine ⟨284324292573928268159268629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 189549528382618845439512419 284324292573928268159268629)
                ·
                  refine ⟨13327701214402887569965717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 284324292573928268159268629 13327701214402887569965717)
                  ·
                    refine ⟨624735994425135354842143, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13327701214402887569965717 624735994425135354842143)
                    ·
                      rfl

theorem cell23_3650007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 1, 6, 6].length) (baseStart_3650007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3650007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3650007 prefixEnd_3650007 := by exact prefixLift 3650007
  have htrace : WordTrace (prefixWord ++ tailWord_3650007) baseStart_3650007 baseEnd_3650007 := by
    simpa [prefixWord, tailWord_3650007, baseEnd_3650007] using wordTrace_append hprefix tailTrace_3650007
  have hstable : (prefixWord ++ tailWord_3650007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3650007).length < 2 ^ (prefixWord ++ tailWord_3650007).sum := by decide
  have hdescent : baseEnd_3650007 < baseStart_3650007 := by decide
  rcases family_descends (prefixWord ++ tailWord_3650007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3650088 : List Nat := [2, 1, 5, 2, 1, 1, 2, 4, 5]
def baseStart_3650088 : Nat := 118140960795 + 3650088 * 2 ^ 59
def prefixEnd_3650088 : Nat := 4983230072969 + 3 ^ 40 * 3650088 * 2
def baseEnd_3650088 : Nat := 208249952800935583068173

theorem tailTrace_3650088 : CollatzResearch.WordTrace tailWord_3650088 prefixEnd_3650088 208249952800935583068173 := by
  unfold tailWord_3650088
  simp only [CollatzResearch.WordTrace]
  refine ⟨66564823200181018122631459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88753097600241357496841945 66564823200181018122631459)
  ·
    refine ⟨99847234800271527183947189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66564823200181018122631459 99847234800271527183947189)
    ·
      refine ⟨9360678262525455673495049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 99847234800271527183947189 9360678262525455673495049)
      ·
        refine ⟨7020508696894091755121287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9360678262525455673495049 7020508696894091755121287)
        ·
          refine ⟨10530763045341137632681931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7020508696894091755121287 10530763045341137632681931)
          ·
            refine ⟨15796144568011706449022897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10530763045341137632681931 15796144568011706449022897)
            ·
              refine ⟨11847108426008779836767173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15796144568011706449022897 11847108426008779836767173)
              ·
                refine ⟨2221332829876646219393845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11847108426008779836767173 2221332829876646219393845)
                ·
                  refine ⟨208249952800935583068173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2221332829876646219393845 208249952800935583068173)
                  ·
                    rfl

theorem cell23_3650088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 2, 4, 5].length) (baseStart_3650088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3650088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3650088 prefixEnd_3650088 := by exact prefixLift 3650088
  have htrace : WordTrace (prefixWord ++ tailWord_3650088) baseStart_3650088 baseEnd_3650088 := by
    simpa [prefixWord, tailWord_3650088, baseEnd_3650088] using wordTrace_append hprefix tailTrace_3650088
  have hstable : (prefixWord ++ tailWord_3650088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3650088).length < 2 ^ (prefixWord ++ tailWord_3650088).sum := by decide
  have hdescent : baseEnd_3650088 < baseStart_3650088 := by decide
  rcases family_descends (prefixWord ++ tailWord_3650088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3650104 : List Nat := [2, 1, 2, 1, 4, 1, 1, 1, 3, 3, 4]
def baseStart_3650104 : Nat := 118140960795 + 3650104 * 2 ^ 59
def prefixEnd_3650104 : Nat := 4983230072969 + 3 ^ 40 * 3650104 * 2
def baseEnd_3650104 : Nat := 1874257790898892185013483

theorem tailTrace_3650104 : CollatzResearch.WordTrace tailWord_3650104 prefixEnd_3650104 1874257790898892185013483 := by
  unfold tailWord_3650104
  simp only [CollatzResearch.WordTrace]
  refine ⟨66565114984152035488922683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88753486645536047318563577 66565114984152035488922683)
  ·
    refine ⟨99847672476228053233384025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66565114984152035488922683 99847672476228053233384025)
    ·
      refine ⟨74885754357171039925038019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99847672476228053233384025 74885754357171039925038019)
      ·
        refine ⟨112328631535756559887557029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74885754357171039925038019 112328631535756559887557029)
        ·
          refine ⟨21061618412954354978916943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 112328631535756559887557029 21061618412954354978916943)
          ·
            refine ⟨31592427619431532468375415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21061618412954354978916943 31592427619431532468375415)
            ·
              refine ⟨47388641429147298702563123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31592427619431532468375415 47388641429147298702563123)
              ·
                refine ⟨71082962143720948053844685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47388641429147298702563123 71082962143720948053844685)
                ·
                  refine ⟨26656110803895355520191757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 71082962143720948053844685 26656110803895355520191757)
                  ·
                    refine ⟨9996041551460758320071909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26656110803895355520191757 9996041551460758320071909)
                    ·
                      refine ⟨1874257790898892185013483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9996041551460758320071909 1874257790898892185013483)
                      ·
                        rfl

theorem cell23_3650104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 1, 1, 3, 3, 4].length) (baseStart_3650104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3650104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3650104 prefixEnd_3650104 := by exact prefixLift 3650104
  have htrace : WordTrace (prefixWord ++ tailWord_3650104) baseStart_3650104 baseEnd_3650104 := by
    simpa [prefixWord, tailWord_3650104, baseEnd_3650104] using wordTrace_append hprefix tailTrace_3650104
  have hstable : (prefixWord ++ tailWord_3650104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3650104).length < 2 ^ (prefixWord ++ tailWord_3650104).sum := by decide
  have hdescent : baseEnd_3650104 < baseStart_3650104 := by decide
  rcases family_descends (prefixWord ++ tailWord_3650104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3650118 : List Nat := [6, 1, 1, 1, 2, 1, 2, 1, 1, 7]
def baseStart_3650118 : Nat := 118140960795 + 3650118 * 2 ^ 59
def prefixEnd_3650118 : Nat := 4983230072969 + 3 ^ 40 * 3650118 * 2
def baseEnd_3650118 : Nat := 624754993209351710079473

theorem tailTrace_3650118 : CollatzResearch.WordTrace tailWord_3650118 prefixEnd_3650118 624754993209351710079473 := by
  unfold tailWord_3650118
  simp only [CollatzResearch.WordTrace]
  refine ⟨4160335643445417230276719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 88753827060168900912570005 4160335643445417230276719)
  ·
    refine ⟨6240503465168125845415079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4160335643445417230276719 6240503465168125845415079)
    ·
      refine ⟨9360755197752188768122619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6240503465168125845415079 9360755197752188768122619)
      ·
        refine ⟨14041132796628283152183929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9360755197752188768122619 14041132796628283152183929)
        ·
          refine ⟨10530849597471212364137947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14041132796628283152183929 10530849597471212364137947)
          ·
            refine ⟨15796274396206818546206921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10530849597471212364137947 15796274396206818546206921)
            ·
              refine ⟨11847205797155113909655191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15796274396206818546206921 11847205797155113909655191)
              ·
                refine ⟨17770808695732670864482787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11847205797155113909655191 17770808695732670864482787)
                ·
                  refine ⟨26656213043599006296724181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17770808695732670864482787 26656213043599006296724181)
                  ·
                    refine ⟨624754993209351710079473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 26656213043599006296724181 624754993209351710079473)
                    ·
                      rfl

theorem cell23_3650118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 2, 1, 1, 7].length) (baseStart_3650118 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3650118 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3650118 prefixEnd_3650118 := by exact prefixLift 3650118
  have htrace : WordTrace (prefixWord ++ tailWord_3650118) baseStart_3650118 baseEnd_3650118 := by
    simpa [prefixWord, tailWord_3650118, baseEnd_3650118] using wordTrace_append hprefix tailTrace_3650118
  have hstable : (prefixWord ++ tailWord_3650118).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3650118).length < 2 ^ (prefixWord ++ tailWord_3650118).sum := by decide
  have hdescent : baseEnd_3650118 < baseStart_3650118 := by decide
  rcases family_descends (prefixWord ++ tailWord_3650118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3650144 : List Nat := [2, 1, 1, 3, 2, 1, 4, 1, 8]
def baseStart_3650144 : Nat := 118140960795 + 3650144 * 2 ^ 59
def prefixEnd_3650144 : Nat := 4983230072969 + 3 ^ 40 * 3650144 * 2
def baseEnd_3650144 : Nat := 208253147791674669834811

theorem tailTrace_3650144 : CollatzResearch.WordTrace tailWord_3650144 prefixEnd_3650144 208253147791674669834811 := by
  unfold tailWord_3650144
  simp only [CollatzResearch.WordTrace]
  refine ⟨66565844444079578904650743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88754459258772771872867657 66565844444079578904650743)
  ·
    refine ⟨99848766666119368356976115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66565844444079578904650743 99848766666119368356976115)
    ·
      refine ⟨149773149999179052535464173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99848766666119368356976115 149773149999179052535464173)
      ·
        refine ⟨56164931249692144700799065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 149773149999179052535464173 56164931249692144700799065)
        ·
          refine ⟨42123698437269108525599299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56164931249692144700799065 42123698437269108525599299)
          ·
            refine ⟨63185547655903662788398949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42123698437269108525599299 63185547655903662788398949)
            ·
              refine ⟨11847290185481936772824803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 63185547655903662788398949 11847290185481936772824803)
              ·
                refine ⟨17770935278222905159237205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11847290185481936772824803 17770935278222905159237205)
                ·
                  refine ⟨208253147791674669834811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 17770935278222905159237205 208253147791674669834811)
                  ·
                    rfl

theorem cell23_3650144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 4, 1, 8].length) (baseStart_3650144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3650144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3650144 prefixEnd_3650144 := by exact prefixLift 3650144
  have htrace : WordTrace (prefixWord ++ tailWord_3650144) baseStart_3650144 baseEnd_3650144 := by
    simpa [prefixWord, tailWord_3650144, baseEnd_3650144] using wordTrace_append hprefix tailTrace_3650144
  have hstable : (prefixWord ++ tailWord_3650144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3650144).length < 2 ^ (prefixWord ++ tailWord_3650144).sum := by decide
  have hdescent : baseEnd_3650144 < baseStart_3650144 := by decide
  rcases family_descends (prefixWord ++ tailWord_3650144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3650222 : List Nat := [4, 1, 4, 1, 1, 2, 1, 2, 3, 1, 3]
def baseStart_3650222 : Nat := 118140960795 + 3650222 * 2 ^ 59
def prefixEnd_3650222 : Nat := 4983230072969 + 3 ^ 40 * 3650222 * 2
def baseEnd_3650222 : Nat := 1874318381616122723337941

theorem tailTrace_3650222 : CollatzResearch.WordTrace tailWord_3650222 prefixEnd_3650222 1874318381616122723337941 := by
  unfold tailWord_3650222
  simp only [CollatzResearch.WordTrace]
  refine ⟨16641816722734572141330115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 88756355854584384753760613 16641816722734572141330115)
  ·
    refine ⟨24962725084101858211995173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16641816722734572141330115 24962725084101858211995173)
    ·
      refine ⟨4680510953269098414749095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24962725084101858211995173 4680510953269098414749095)
      ·
        refine ⟨7020766429903647622123643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4680510953269098414749095 7020766429903647622123643)
        ·
          refine ⟨10531149644855471433185465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7020766429903647622123643 10531149644855471433185465)
          ·
            refine ⟨7898362233641603574889099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10531149644855471433185465 7898362233641603574889099)
            ·
              refine ⟨11847543350462405362333649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7898362233641603574889099 11847543350462405362333649)
              ·
                refine ⟨8885657512846804021750237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11847543350462405362333649 8885657512846804021750237)
                ·
                  refine ⟨3332121567317551508156339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8885657512846804021750237 3332121567317551508156339)
                  ·
                    refine ⟨4998182350976327262234509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3332121567317551508156339 4998182350976327262234509)
                    ·
                      refine ⟨1874318381616122723337941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4998182350976327262234509 1874318381616122723337941)
                      ·
                        rfl

theorem cell23_3650222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 2, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 2, 1, 2, 3, 1, 3].length) (baseStart_3650222 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3650222 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3650222 prefixEnd_3650222 := by exact prefixLift 3650222
  have htrace : WordTrace (prefixWord ++ tailWord_3650222) baseStart_3650222 baseEnd_3650222 := by
    simpa [prefixWord, tailWord_3650222, baseEnd_3650222] using wordTrace_append hprefix tailTrace_3650222
  have hstable : (prefixWord ++ tailWord_3650222).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3650222).length < 2 ^ (prefixWord ++ tailWord_3650222).sum := by decide
  have hdescent : baseEnd_3650222 < baseStart_3650222 := by decide
  rcases family_descends (prefixWord ++ tailWord_3650222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3650238 : List Nat := [4, 2, 1, 1, 2, 1, 2, 2, 4, 4]
def baseStart_3650238 : Nat := 118140960795 + 3650238 * 2 ^ 59
def prefixEnd_3650238 : Nat := 4983230072969 + 3 ^ 40 * 3650238 * 2
def baseEnd_3650238 : Nat := 624775532435531553579289

theorem tailTrace_3650238 : CollatzResearch.WordTrace tailWord_3650238 prefixEnd_3650238 624775532435531553579289 := by
  unfold tailWord_3650238
  simp only [CollatzResearch.WordTrace]
  refine ⟨16641889668727326482902921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 88756744899879074575482245 16641889668727326482902921)
  ·
    refine ⟨12481417251545494862177191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16641889668727326482902921 12481417251545494862177191)
    ·
      refine ⟨18722125877318242293265787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12481417251545494862177191 18722125877318242293265787)
      ·
        refine ⟨28083188815977363439898681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18722125877318242293265787 28083188815977363439898681)
        ·
          refine ⟨21062391611983022579924011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28083188815977363439898681 21062391611983022579924011)
          ·
            refine ⟨31593587417974533869886017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21062391611983022579924011 31593587417974533869886017)
            ·
              refine ⟨23695190563480900402414513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31593587417974533869886017 23695190563480900402414513)
              ·
                refine ⟨17771392922610675301810885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23695190563480900402414513 17771392922610675301810885)
                ·
                  refine ⟨3332136172989501619089541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17771392922610675301810885 3332136172989501619089541)
                  ·
                    refine ⟨624775532435531553579289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3332136172989501619089541 624775532435531553579289)
                    ·
                      rfl

theorem cell23_3650238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 2, 2, 4, 4].length) (baseStart_3650238 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3650238 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3650238 prefixEnd_3650238 := by exact prefixLift 3650238
  have htrace : WordTrace (prefixWord ++ tailWord_3650238) baseStart_3650238 baseEnd_3650238 := by
    simpa [prefixWord, tailWord_3650238, baseEnd_3650238] using wordTrace_append hprefix tailTrace_3650238
  have hstable : (prefixWord ++ tailWord_3650238).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3650238).length < 2 ^ (prefixWord ++ tailWord_3650238).sum := by decide
  have hdescent : baseEnd_3650238 < baseStart_3650238 := by decide
  rcases family_descends (prefixWord ++ tailWord_3650238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3650275 : List Nat := [1, 1, 1, 7, 1, 3, 1, 1, 1, 2, 4]
def baseStart_3650275 : Nat := 118140960795 + 3650275 * 2 ^ 59
def prefixEnd_3650275 : Nat := 4983230072969 + 3 ^ 40 * 3650275 * 2
def baseEnd_3650275 : Nat := 1874345596090811015975197

theorem tailTrace_3650275 : CollatzResearch.WordTrace tailWord_3650275 prefixEnd_3650275 1874345596090811015975197 := by
  unfold tailWord_3650275
  simp only [CollatzResearch.WordTrace]
  refine ⟨133136466850684567182320279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88757644567123044788213519 133136466850684567182320279)
  ·
    refine ⟨199704700276026850773480419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133136466850684567182320279 199704700276026850773480419)
    ·
      refine ⟨299557050414040276160220629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 199704700276026850773480419 299557050414040276160220629)
      ·
        refine ⟨7020868369079068972505171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 299557050414040276160220629 7020868369079068972505171)
        ·
          refine ⟨10531302553618603458757757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7020868369079068972505171 10531302553618603458757757)
          ·
            refine ⟨3949238457606976297034159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10531302553618603458757757 3949238457606976297034159)
            ·
              refine ⟨5923857686410464445551239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3949238457606976297034159 5923857686410464445551239)
              ·
                refine ⟨8885786529615696668326859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5923857686410464445551239 8885786529615696668326859)
                ·
                  refine ⟨13328679794423545002490289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8885786529615696668326859 13328679794423545002490289)
                  ·
                    refine ⟨9996509845817658751867717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13328679794423545002490289 9996509845817658751867717)
                    ·
                      refine ⟨1874345596090811015975197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9996509845817658751867717 1874345596090811015975197)
                      ·
                        rfl

theorem cell23_3650275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 3, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 3, 1, 1, 1, 2, 4].length) (baseStart_3650275 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3650275 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3650275 prefixEnd_3650275 := by exact prefixLift 3650275
  have htrace : WordTrace (prefixWord ++ tailWord_3650275) baseStart_3650275 baseEnd_3650275 := by
    simpa [prefixWord, tailWord_3650275, baseEnd_3650275] using wordTrace_append hprefix tailTrace_3650275
  have hstable : (prefixWord ++ tailWord_3650275).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3650275).length < 2 ^ (prefixWord ++ tailWord_3650275).sum := by decide
  have hdescent : baseEnd_3650275 < baseStart_3650275 := by decide
  rcases family_descends (prefixWord ++ tailWord_3650275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3650338 : List Nat := [3, 3, 1, 1, 2, 2, 1, 2, 2, 1, 5]
def baseStart_3650338 : Nat := 118140960795 + 3650338 * 2 ^ 59
def prefixEnd_3650338 : Nat := 4983230072969 + 3 ^ 40 * 3650338 * 2
def baseEnd_3650338 : Nat := 1874377945372044269487407

theorem tailTrace_3650338 : CollatzResearch.WordTrace tailWord_3650338 prefixEnd_3650338 1874377945372044269487407 := by
  unfold tailWord_3650338
  simp only [CollatzResearch.WordTrace]
  refine ⟨33284691162364082235465917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88759176432970885961242445 33284691162364082235465917)
  ·
    refine ⟨12481759185886530838299719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33284691162364082235465917 12481759185886530838299719)
    ·
      refine ⟨18722638778829796257449579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12481759185886530838299719 18722638778829796257449579)
      ·
        refine ⟨28083958168244694386174369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18722638778829796257449579 28083958168244694386174369)
        ·
          refine ⟨21062968626183520789630777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28083958168244694386174369 21062968626183520789630777)
          ·
            refine ⟨15797226469637640592223083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21062968626183520789630777 15797226469637640592223083)
            ·
              refine ⟨23695839704456460888334625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15797226469637640592223083 23695839704456460888334625)
              ·
                refine ⟨17771879778342345666250969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23695839704456460888334625 17771879778342345666250969)
                ·
                  refine ⟨13328909833756759249688227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17771879778342345666250969 13328909833756759249688227)
                  ·
                    refine ⟨19993364750635138874532341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13328909833756759249688227 19993364750635138874532341)
                    ·
                      refine ⟨1874377945372044269487407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19993364750635138874532341 1874377945372044269487407)
                      ·
                        rfl

theorem cell23_3650338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 1, 2, 2, 1, 5].length) (baseStart_3650338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3650338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3650338 prefixEnd_3650338 := by exact prefixLift 3650338
  have htrace : WordTrace (prefixWord ++ tailWord_3650338) baseStart_3650338 baseEnd_3650338 := by
    simpa [prefixWord, tailWord_3650338, baseEnd_3650338] using wordTrace_append hprefix tailTrace_3650338
  have hstable : (prefixWord ++ tailWord_3650338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3650338).length < 2 ^ (prefixWord ++ tailWord_3650338).sum := by decide
  have hdescent : baseEnd_3650338 < baseStart_3650338 := by decide
  rcases family_descends (prefixWord ++ tailWord_3650338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3650341 : List Nat := [1, 3, 1, 2, 3, 1, 2, 1, 9]
def baseStart_3650341 : Nat := 118140960795 + 3650341 * 2 ^ 59
def prefixEnd_3650341 : Nat := 4983230072969 + 3 ^ 40 * 3650341 * 2
def baseEnd_3650341 : Nat := 208264387312667528638877

theorem tailTrace_3650341 : CollatzResearch.WordTrace tailWord_3650341 prefixEnd_3650341 208264387312667528638877 := by
  unfold tailWord_3650341
  simp only [CollatzResearch.WordTrace]
  refine ⟨133138874068445460454222877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88759249378963640302815251 133138874068445460454222877)
  ·
    refine ⟨49927077775667047670333579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 133138874068445460454222877 49927077775667047670333579)
    ·
      refine ⟨74890616663500571505500369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49927077775667047670333579 74890616663500571505500369)
      ·
        refine ⟨56167962497625428629125277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74890616663500571505500369 56167962497625428629125277)
        ·
          refine ⟨21062985936609535735921979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56167962497625428629125277 21062985936609535735921979)
          ·
            refine ⟨31594478904914303603882969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21062985936609535735921979 31594478904914303603882969)
            ·
              refine ⟨23695859178685727702912227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31594478904914303603882969 23695859178685727702912227)
              ·
                refine ⟨35543788768028591554368341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23695859178685727702912227 35543788768028591554368341)
                ·
                  refine ⟨208264387312667528638877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 35543788768028591554368341 208264387312667528638877)
                  ·
                    rfl

theorem cell23_3650341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 2, 1, 9].length) (baseStart_3650341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3650341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3650341 prefixEnd_3650341 := by exact prefixLift 3650341
  have htrace : WordTrace (prefixWord ++ tailWord_3650341) baseStart_3650341 baseEnd_3650341 := by
    simpa [prefixWord, tailWord_3650341, baseEnd_3650341] using wordTrace_append hprefix tailTrace_3650341
  have hstable : (prefixWord ++ tailWord_3650341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3650341).length < 2 ^ (prefixWord ++ tailWord_3650341).sum := by decide
  have hdescent : baseEnd_3650341 < baseStart_3650341 := by decide
  rcases family_descends (prefixWord ++ tailWord_3650341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3650356 : List Nat := [2, 5, 1, 1, 3, 1, 3, 1, 1, 3, 2]
def baseStart_3650356 : Nat := 118140960795 + 3650356 * 2 ^ 59
def prefixEnd_3650356 : Nat := 4983230072969 + 3 ^ 40 * 3650356 * 2
def baseEnd_3650356 : Nat := 1874387188023825199062325

theorem tailTrace_3650356 : CollatzResearch.WordTrace tailWord_3650356 prefixEnd_3650356 1874387188023825199062325 := by
  unfold tailWord_3650356
  simp only [CollatzResearch.WordTrace]
  refine ⟨66569710581695559008009461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88759614108927412010679281 66569710581695559008009461)
  ·
    refine ⟨6240910367033958657000887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 66569710581695559008009461 6240910367033958657000887)
    ·
      refine ⟨9361365550550937985501331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6240910367033958657000887 9361365550550937985501331)
      ·
        refine ⟨14042048325826406978251997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9361365550550937985501331 14042048325826406978251997)
        ·
          refine ⟨5265768122184902616844499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14042048325826406978251997 5265768122184902616844499)
          ·
            refine ⟨7898652183277353925266749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5265768122184902616844499 7898652183277353925266749)
            ·
              refine ⟨2961994568729007721975031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7898652183277353925266749 2961994568729007721975031)
              ·
                refine ⟨4442991853093511582962547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2961994568729007721975031 4442991853093511582962547)
                ·
                  refine ⟨6664487779640267374443821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4442991853093511582962547 6664487779640267374443821)
                  ·
                    refine ⟨2499182917365100265416433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6664487779640267374443821 2499182917365100265416433)
                    ·
                      refine ⟨1874387188023825199062325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2499182917365100265416433 1874387188023825199062325)
                      ·
                        rfl

theorem cell23_3650356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 1, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 1, 3, 1, 1, 3, 2].length) (baseStart_3650356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3650356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3650356 prefixEnd_3650356 := by exact prefixLift 3650356
  have htrace : WordTrace (prefixWord ++ tailWord_3650356) baseStart_3650356 baseEnd_3650356 := by
    simpa [prefixWord, tailWord_3650356, baseEnd_3650356] using wordTrace_append hprefix tailTrace_3650356
  have hstable : (prefixWord ++ tailWord_3650356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3650356).length < 2 ^ (prefixWord ++ tailWord_3650356).sum := by decide
  have hdescent : baseEnd_3650356 < baseStart_3650356 := by decide
  rcases family_descends (prefixWord ++ tailWord_3650356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3650385 : List Nat := [1, 2, 2, 1, 6, 1, 1, 1, 2, 3, 3]
def baseStart_3650385 : Nat := 118140960795 + 3650385 * 2 ^ 59
def prefixEnd_3650385 : Nat := 4983230072969 + 3 ^ 40 * 3650385 * 2
def baseEnd_3650385 : Nat := 1874402078962805585599691

theorem tailTrace_3650385 : CollatzResearch.WordTrace tailWord_3650385 prefixEnd_3650385 1874402078962805585599691 := by
  unfold tailWord_3650385
  simp only [CollatzResearch.WordTrace]
  refine ⟨133140478880286055968824609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88760319253524037312549739 133140478880286055968824609)
  ·
    refine ⟨99855359160214541976618457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133140478880286055968824609 99855359160214541976618457)
    ·
      refine ⟨74891519370160906482463843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99855359160214541976618457 74891519370160906482463843)
      ·
        refine ⟨112337279055241359723695765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74891519370160906482463843 112337279055241359723695765)
        ·
          refine ⟨5265809955714438737048239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 112337279055241359723695765 5265809955714438737048239)
          ·
            refine ⟨7898714933571658105572359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5265809955714438737048239 7898714933571658105572359)
            ·
              refine ⟨11848072400357487158358539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7898714933571658105572359 11848072400357487158358539)
              ·
                refine ⟨17772108600536230737537809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11848072400357487158358539 17772108600536230737537809)
                ·
                  refine ⟨13329081450402173053153357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17772108600536230737537809 13329081450402173053153357)
                  ·
                    refine ⟨4998405543900814894932509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13329081450402173053153357 4998405543900814894932509)
                    ·
                      refine ⟨1874402078962805585599691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4998405543900814894932509 1874402078962805585599691)
                      ·
                        rfl

theorem cell23_3650385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 1, 1, 1, 2, 3, 3].length) (baseStart_3650385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3650385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3650385 prefixEnd_3650385 := by exact prefixLift 3650385
  have htrace : WordTrace (prefixWord ++ tailWord_3650385) baseStart_3650385 baseEnd_3650385 := by
    simpa [prefixWord, tailWord_3650385, baseEnd_3650385] using wordTrace_append hprefix tailTrace_3650385
  have hstable : (prefixWord ++ tailWord_3650385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3650385).length < 2 ^ (prefixWord ++ tailWord_3650385).sum := by decide
  have hdescent : baseEnd_3650385 < baseStart_3650385 := by decide
  rcases family_descends (prefixWord ++ tailWord_3650385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3650401 : List Nat := [1, 2, 3, 1, 1, 1, 2, 1, 1, 10]
def baseStart_3650401 : Nat := 118140960795 + 3650401 * 2 ^ 59
def prefixEnd_3650401 : Nat := 4983230072969 + 3 ^ 40 * 3650401 * 2
def baseEnd_3650401 : Nat := 624803431551092507666539

theorem tailTrace_3650401 : CollatzResearch.WordTrace tailWord_3650401 prefixEnd_3650401 624803431551092507666539 := by
  unfold tailWord_3650401
  simp only [CollatzResearch.WordTrace]
  refine ⟨133141062448228090701407057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88760708298818727134271371 133141062448228090701407057)
  ·
    refine ⟨99855796836171068026055293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133141062448228090701407057 99855796836171068026055293)
    ·
      refine ⟨37445923813564150509770735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 99855796836171068026055293 37445923813564150509770735)
      ·
        refine ⟨56168885720346225764656103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37445923813564150509770735 56168885720346225764656103)
        ·
          refine ⟨84253328580519338646984155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56168885720346225764656103 84253328580519338646984155)
          ·
            refine ⟨126379992870779007970476233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84253328580519338646984155 126379992870779007970476233)
            ·
              refine ⟨94784994653084255977857175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 126379992870779007970476233 94784994653084255977857175)
              ·
                refine ⟨142177491979626383966785763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 94784994653084255977857175 142177491979626383966785763)
                ·
                  refine ⟨213266237969439575950178645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 142177491979626383966785763 213266237969439575950178645)
                  ·
                    refine ⟨624803431551092507666539, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 213266237969439575950178645 624803431551092507666539)
                    ·
                      rfl

theorem cell23_3650401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 1, 1, 10].length) (baseStart_3650401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3650401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3650401 prefixEnd_3650401 := by exact prefixLift 3650401
  have htrace : WordTrace (prefixWord ++ tailWord_3650401) baseStart_3650401 baseEnd_3650401 := by
    simpa [prefixWord, tailWord_3650401, baseEnd_3650401] using wordTrace_append hprefix tailTrace_3650401
  have hstable : (prefixWord ++ tailWord_3650401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3650401).length < 2 ^ (prefixWord ++ tailWord_3650401).sum := by decide
  have hdescent : baseEnd_3650401 < baseStart_3650401 := by decide
  rcases family_descends (prefixWord ++ tailWord_3650401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3650425 : List Nat := [1, 2, 1, 3, 2, 3, 1, 2, 2, 4, 2]
def baseStart_3650425 : Nat := 118140960795 + 3650425 * 2 ^ 59
def prefixEnd_3650425 : Nat := 4983230072969 + 3 ^ 40 * 3650425 * 2
def baseEnd_3650425 : Nat := 1874422618188985429099507

theorem tailTrace_3650425 : CollatzResearch.WordTrace tailWord_3650425 prefixEnd_3650425 1874422618188985429099507 := by
  unfold tailWord_3650425
  simp only [CollatzResearch.WordTrace]
  refine ⟨133141937800141142800280729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88761291866760761866853819 133141937800141142800280729)
  ·
    refine ⟨99856453350105857100210547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133141937800141142800280729 99856453350105857100210547)
    ·
      refine ⟨149784680025158785650315821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99856453350105857100210547 149784680025158785650315821)
      ·
        refine ⟨56169255009434544618868433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 149784680025158785650315821 56169255009434544618868433)
        ·
          refine ⟨42126941257075908464151325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56169255009434544618868433 42126941257075908464151325)
          ·
            refine ⟨15797602971403465674056747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42126941257075908464151325 15797602971403465674056747)
            ·
              refine ⟨23696404457105198511085121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15797602971403465674056747 23696404457105198511085121)
              ·
                refine ⟨17772303342828898883313841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23696404457105198511085121 17772303342828898883313841)
                ·
                  refine ⟨13329227507121674162485381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17772303342828898883313841 13329227507121674162485381)
                  ·
                    refine ⟨2499230157585313905466009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13329227507121674162485381 2499230157585313905466009)
                    ·
                      refine ⟨1874422618188985429099507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2499230157585313905466009 1874422618188985429099507)
                      ·
                        rfl

theorem cell23_3650425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 1, 2, 2, 4, 2].length) (baseStart_3650425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3650425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3650425 prefixEnd_3650425 := by exact prefixLift 3650425
  have htrace : WordTrace (prefixWord ++ tailWord_3650425) baseStart_3650425 baseEnd_3650425 := by
    simpa [prefixWord, tailWord_3650425, baseEnd_3650425] using wordTrace_append hprefix tailTrace_3650425
  have hstable : (prefixWord ++ tailWord_3650425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3650425).length < 2 ^ (prefixWord ++ tailWord_3650425).sum := by decide
  have hdescent : baseEnd_3650425 < baseStart_3650425 := by decide
  rcases family_descends (prefixWord ++ tailWord_3650425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3650435 : List Nat := [1, 1, 1, 3, 4, 1, 4, 1, 3, 4]
def baseStart_3650435 : Nat := 118140960795 + 3650435 * 2 ^ 59
def prefixEnd_3650435 : Nat := 4983230072969 + 3 ^ 40 * 3650435 * 2
def baseEnd_3650435 : Nat := 624809250998510129991487

theorem tailTrace_3650435 : CollatzResearch.WordTrace tailWord_3650435 prefixEnd_3650435 624809250998510129991487 := by
  unfold tailWord_3650435
  simp only [CollatzResearch.WordTrace]
  refine ⟨133142302530104914508144759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88761535020069943005429839 133142302530104914508144759)
  ·
    refine ⟨199713453795157371762217139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133142302530104914508144759 199713453795157371762217139)
    ·
      refine ⟨299570180692736057643325709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 199713453795157371762217139 299570180692736057643325709)
      ·
        refine ⟨112338817759776021616247141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 299570180692736057643325709 112338817759776021616247141)
        ·
          refine ⟨21063528329958004053046339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 112338817759776021616247141 21063528329958004053046339)
          ·
            refine ⟨31595292494937006079569509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21063528329958004053046339 31595292494937006079569509)
            ·
              refine ⟨5924117342800688639919283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31595292494937006079569509 5924117342800688639919283)
              ·
                refine ⟨8886176014201032959878925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5924117342800688639919283 8886176014201032959878925)
                ·
                  refine ⟨3332316005325387359954597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8886176014201032959878925 3332316005325387359954597)
                  ·
                    refine ⟨624809250998510129991487, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3332316005325387359954597 624809250998510129991487)
                    ·
                      rfl

theorem cell23_3650435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 4, 1, 3, 4].length) (baseStart_3650435 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3650435 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3650435 prefixEnd_3650435 := by exact prefixLift 3650435
  have htrace : WordTrace (prefixWord ++ tailWord_3650435) baseStart_3650435 baseEnd_3650435 := by
    simpa [prefixWord, tailWord_3650435, baseEnd_3650435] using wordTrace_append hprefix tailTrace_3650435
  have hstable : (prefixWord ++ tailWord_3650435).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3650435).length < 2 ^ (prefixWord ++ tailWord_3650435).sum := by decide
  have hdescent : baseEnd_3650435 < baseStart_3650435 := by decide
  rcases family_descends (prefixWord ++ tailWord_3650435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3650442 : List Nat := [3, 1, 2, 4, 1, 1, 2, 1, 2, 4, 2]
def baseStart_3650442 : Nat := 118140960795 + 3650442 * 2 ^ 59
def prefixEnd_3650442 : Nat := 4983230072969 + 3 ^ 40 * 3650442 * 2
def baseEnd_3650442 : Nat := 1874431347360111862586929

theorem tailTrace_3650442 : CollatzResearch.WordTrace tailWord_3650442 prefixEnd_3650442 1874431347360111862586929 := by
  unfold tailWord_3650442
  simp only [CollatzResearch.WordTrace]
  refine ⟨33285639460269888675912395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88761705227386369802433053 33285639460269888675912395)
  ·
    refine ⟨49928459190404833013868593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33285639460269888675912395 49928459190404833013868593)
    ·
      refine ⟨37446344392803624760401445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49928459190404833013868593 37446344392803624760401445)
      ·
        refine ⟨7021189573650679642575271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 37446344392803624760401445 7021189573650679642575271)
        ·
          refine ⟨10531784360476019463862907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7021189573650679642575271 10531784360476019463862907)
          ·
            refine ⟨15797676540714029195794361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10531784360476019463862907 15797676540714029195794361)
            ·
              refine ⟨11848257405535521896845771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15797676540714029195794361 11848257405535521896845771)
              ·
                refine ⟨17772386108303282845268657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11848257405535521896845771 17772386108303282845268657)
                ·
                  refine ⟨13329289581227462133951493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17772386108303282845268657 13329289581227462133951493)
                  ·
                    refine ⟨2499241796480149150115905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13329289581227462133951493 2499241796480149150115905)
                    ·
                      refine ⟨1874431347360111862586929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2499241796480149150115905 1874431347360111862586929)
                      ·
                        rfl

theorem cell23_3650442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 2, 1, 2, 4, 2].length) (baseStart_3650442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3650442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3650442 prefixEnd_3650442 := by exact prefixLift 3650442
  have htrace : WordTrace (prefixWord ++ tailWord_3650442) baseStart_3650442 baseEnd_3650442 := by
    simpa [prefixWord, tailWord_3650442, baseEnd_3650442] using wordTrace_append hprefix tailTrace_3650442
  have hstable : (prefixWord ++ tailWord_3650442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3650442).length < 2 ^ (prefixWord ++ tailWord_3650442).sum := by decide
  have hdescent : baseEnd_3650442 < baseStart_3650442 := by decide
  rcases family_descends (prefixWord ++ tailWord_3650442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3650525 : List Nat := [1, 4, 3, 1, 2, 1, 1, 1, 3, 6]
def baseStart_3650525 : Nat := 118140960795 + 3650525 * 2 ^ 59
def prefixEnd_3650525 : Nat := 4983230072969 + 3 ^ 40 * 3650525 * 2
def baseEnd_3650525 : Nat := 624824655418145012616349

theorem tailTrace_3650525 : CollatzResearch.WordTrace tailWord_3650525 prefixEnd_3650525 624824655418145012616349 := by
  unfold tailWord_3650525
  simp only [CollatzResearch.WordTrace]
  refine ⟨133145585099778859878921029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88763723399852573252614019 133145585099778859878921029)
  ·
    refine ⟨24964797206208536227297693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 133145585099778859878921029 24964797206208536227297693)
    ·
      refine ⟨9361798952328201085236635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24964797206208536227297693 9361798952328201085236635)
      ·
        refine ⟨14042698428492301627854953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9361798952328201085236635 14042698428492301627854953)
        ·
          refine ⟨10532023821369226220891215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14042698428492301627854953 10532023821369226220891215)
          ·
            refine ⟨15798035732053839331336823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10532023821369226220891215 15798035732053839331336823)
            ·
              refine ⟨23697053598080758997005235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15798035732053839331336823 23697053598080758997005235)
              ·
                refine ⟨35545580397121138495507853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23697053598080758997005235 35545580397121138495507853)
                ·
                  refine ⟨13329592648920426935815445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35545580397121138495507853 13329592648920426935815445)
                  ·
                    refine ⟨624824655418145012616349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13329592648920426935815445 624824655418145012616349)
                    ·
                      rfl

theorem cell23_3650525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 1, 1, 3, 6].length) (baseStart_3650525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3650525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3650525 prefixEnd_3650525 := by exact prefixLift 3650525
  have htrace : WordTrace (prefixWord ++ tailWord_3650525) baseStart_3650525 baseEnd_3650525 := by
    simpa [prefixWord, tailWord_3650525, baseEnd_3650525] using wordTrace_append hprefix tailTrace_3650525
  have hstable : (prefixWord ++ tailWord_3650525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3650525).length < 2 ^ (prefixWord ++ tailWord_3650525).sum := by decide
  have hdescent : baseEnd_3650525 < baseStart_3650525 := by decide
  rcases family_descends (prefixWord ++ tailWord_3650525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3650532 : List Nat := [2, 3, 1, 1, 1, 1, 2, 1, 7, 2, 2]
def baseStart_3650532 : Nat := 118140960795 + 3650532 * 2 ^ 59
def prefixEnd_3650532 : Nat := 4983230072969 + 3 ^ 40 * 3650532 * 2
def baseEnd_3650532 : Nat := 1874477560619016510461515

theorem tailTrace_3650532 : CollatzResearch.WordTrace tailWord_3650532 prefixEnd_3650532 1874477560619016510461515 := by
  unfold tailWord_3650532
  simp only [CollatzResearch.WordTrace]
  refine ⟨66572920205376750037212925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88763893607169000049617233 66572920205376750037212925)
  ·
    refine ⟨24964845077016281263954847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66572920205376750037212925 24964845077016281263954847)
    ·
      refine ⟨37447267615524421895932271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24964845077016281263954847 37447267615524421895932271)
      ·
        refine ⟨56170901423286632843898407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37447267615524421895932271 56170901423286632843898407)
        ·
          refine ⟨84256352134929949265847611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56170901423286632843898407 84256352134929949265847611)
          ·
            refine ⟨126384528202394923898771417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84256352134929949265847611 126384528202394923898771417)
            ·
              refine ⟨94788396151796192924078563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 126384528202394923898771417 94788396151796192924078563)
              ·
                refine ⟨142182594227694289386117845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 94788396151796192924078563 142182594227694289386117845)
                ·
                  refine ⟨3332404552211584907487137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 142182594227694289386117845 3332404552211584907487137)
                  ·
                    refine ⟨2499303414158688680615353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3332404552211584907487137 2499303414158688680615353)
                    ·
                      refine ⟨1874477560619016510461515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2499303414158688680615353 1874477560619016510461515)
                      ·
                        rfl

theorem cell23_3650532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 1, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 1, 7, 2, 2].length) (baseStart_3650532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3650532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3650532 prefixEnd_3650532 := by exact prefixLift 3650532
  have htrace : WordTrace (prefixWord ++ tailWord_3650532) baseStart_3650532 baseEnd_3650532 := by
    simpa [prefixWord, tailWord_3650532, baseEnd_3650532] using wordTrace_append hprefix tailTrace_3650532
  have hstable : (prefixWord ++ tailWord_3650532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3650532).length < 2 ^ (prefixWord ++ tailWord_3650532).sum := by decide
  have hdescent : baseEnd_3650532 < baseStart_3650532 := by decide
  rcases family_descends (prefixWord ++ tailWord_3650532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3650538 : List Nat := [3, 1, 3, 1, 2, 13]
def baseStart_3650538 : Nat := 118140960795 + 3650538 * 2 ^ 59
def prefixEnd_3650538 : Nat := 4983230072969 + 3 ^ 40 * 3650538 * 2
def baseEnd_3650538 : Nat := 7713912104950384720109

theorem tailTrace_3650538 : CollatzResearch.WordTrace tailWord_3650538 prefixEnd_3650538 7713912104950384720109 := by
  unfold tailWord_3650538
  simp only [CollatzResearch.WordTrace]
  refine ⟨33286514812182940774786067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88764039499154508732762845 33286514812182940774786067)
  ·
    refine ⟨49929772218274411162179101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33286514812182940774786067 49929772218274411162179101)
    ·
      refine ⟨18723664581852904185817163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49929772218274411162179101 18723664581852904185817163)
      ·
        refine ⟨28085496872779356278725745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18723664581852904185817163 28085496872779356278725745)
        ·
          refine ⟨21064122654584517209044309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28085496872779356278725745 21064122654584517209044309)
          ·
            refine ⟨7713912104950384720109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 13 21064122654584517209044309 7713912104950384720109)
            ·
              rfl

theorem cell23_3650538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 13].length) (baseStart_3650538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3650538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3650538 prefixEnd_3650538 := by exact prefixLift 3650538
  have htrace : WordTrace (prefixWord ++ tailWord_3650538) baseStart_3650538 baseEnd_3650538 := by
    simpa [prefixWord, tailWord_3650538, baseEnd_3650538] using wordTrace_append hprefix tailTrace_3650538
  have hstable : (prefixWord ++ tailWord_3650538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3650538).length < 2 ^ (prefixWord ++ tailWord_3650538).sum := by decide
  have hdescent : baseEnd_3650538 < baseStart_3650538 := by decide
  rcases family_descends (prefixWord ++ tailWord_3650538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3650575 : List Nat := [1, 1, 2, 1, 1, 1, 2, 1, 4, 7, 2]
def baseStart_3650575 : Nat := 118140960795 + 3650575 * 2 ^ 59
def prefixEnd_3650575 : Nat := 4983230072969 + 3 ^ 40 * 3650575 * 2
def baseEnd_3650575 : Nat := 1874499640287159842223817

theorem tailTrace_3650575 : CollatzResearch.WordTrace tailWord_3650575 prefixEnd_3650575 1874499640287159842223817 := by
  unfold tailWord_3650575
  simp only [CollatzResearch.WordTrace]
  refine ⟨133147408749597718418241179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88764939166398478945494119 133147408749597718418241179)
  ·
    refine ⟨199721113124396577627361769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133147408749597718418241179 199721113124396577627361769)
    ·
      refine ⟨149790834843297433220521327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 199721113124396577627361769 149790834843297433220521327)
      ·
        refine ⟨224686252264946149830781991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149790834843297433220521327 224686252264946149830781991)
        ·
          refine ⟨337029378397419224746172987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 224686252264946149830781991 337029378397419224746172987)
          ·
            refine ⟨505544067596128837119259481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 337029378397419224746172987 505544067596128837119259481)
            ·
              refine ⟨379158050697096627839444611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 505544067596128837119259481 379158050697096627839444611)
              ·
                refine ⟨568737076045644941759166917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 379158050697096627839444611 568737076045644941759166917)
                ·
                  refine ⟨106638201758558426579843797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 568737076045644941759166917 106638201758558426579843797)
                  ·
                    refine ⟨2499332853716213122965089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 106638201758558426579843797 2499332853716213122965089)
                    ·
                      refine ⟨1874499640287159842223817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2499332853716213122965089 1874499640287159842223817)
                      ·
                        rfl

theorem cell23_3650575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 1, 4, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 1, 4, 7, 2].length) (baseStart_3650575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3650575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3650575 prefixEnd_3650575 := by exact prefixLift 3650575
  have htrace : WordTrace (prefixWord ++ tailWord_3650575) baseStart_3650575 baseEnd_3650575 := by
    simpa [prefixWord, tailWord_3650575, baseEnd_3650575] using wordTrace_append hprefix tailTrace_3650575
  have hstable : (prefixWord ++ tailWord_3650575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3650575).length < 2 ^ (prefixWord ++ tailWord_3650575).sum := by decide
  have hdescent : baseEnd_3650575 < baseStart_3650575 := by decide
  rcases family_descends (prefixWord ++ tailWord_3650575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3650583 : List Nat := [1, 1, 3, 5, 1, 2, 2, 3, 1, 2, 2]
def baseStart_3650583 : Nat := 118140960795 + 3650583 * 2 ^ 59
def prefixEnd_3650583 : Nat := 4983230072969 + 3 ^ 40 * 3650583 * 2
def baseEnd_3650583 : Nat := 1874503748132395810923781

theorem tailTrace_3650583 : CollatzResearch.WordTrace tailWord_3650583 prefixEnd_3650583 1874503748132395810923781 := by
  unfold tailWord_3650583
  simp only [CollatzResearch.WordTrace]
  refine ⟨133147700533568735784532403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88765133689045823856354935 133147700533568735784532403)
  ·
    refine ⟨199721550800353103676798605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133147700533568735784532403 199721550800353103676798605)
    ·
      refine ⟨74895581550132413878799477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 199721550800353103676798605 74895581550132413878799477)
      ·
        refine ⟨7021460770324913801137451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 74895581550132413878799477 7021460770324913801137451)
        ·
          refine ⟨10532191155487370701706177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7021460770324913801137451 10532191155487370701706177)
          ·
            refine ⟨7899143366615528026279633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10532191155487370701706177 7899143366615528026279633)
            ·
              refine ⟨5924357524961646019709725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7899143366615528026279633 5924357524961646019709725)
              ·
                refine ⟨2221634071860617257391147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5924357524961646019709725 2221634071860617257391147)
                ·
                  refine ⟨3332451107790925886086721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2221634071860617257391147 3332451107790925886086721)
                  ·
                    refine ⟨2499338330843194414565041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3332451107790925886086721 2499338330843194414565041)
                    ·
                      refine ⟨1874503748132395810923781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2499338330843194414565041 1874503748132395810923781)
                      ·
                        rfl

theorem cell23_3650583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 2, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 2, 2, 3, 1, 2, 2].length) (baseStart_3650583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3650583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3650583 prefixEnd_3650583 := by exact prefixLift 3650583
  have htrace : WordTrace (prefixWord ++ tailWord_3650583) baseStart_3650583 baseEnd_3650583 := by
    simpa [prefixWord, tailWord_3650583, baseEnd_3650583] using wordTrace_append hprefix tailTrace_3650583
  have hstable : (prefixWord ++ tailWord_3650583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3650583).length < 2 ^ (prefixWord ++ tailWord_3650583).sum := by decide
  have hdescent : baseEnd_3650583 < baseStart_3650583 := by decide
  rcases family_descends (prefixWord ++ tailWord_3650583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3650616 : List Nat := [2, 1, 2, 1, 5, 2, 3, 1, 2, 1, 3]
def baseStart_3650616 : Nat := 118140960795 + 3650616 * 2 ^ 59
def prefixEnd_3650616 : Nat := 4983230072969 + 3 ^ 40 * 3650616 * 2
def baseEnd_3650616 : Nat := 1874520692993994181811129

theorem tailTrace_3650616 : CollatzResearch.WordTrace tailWord_3650616 prefixEnd_3650616 1874520692993994181811129 := by
  unfold tailWord_3650616
  simp only [CollatzResearch.WordTrace]
  refine ⟨66574452071224591210241851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88765936094966121613655801 66574452071224591210241851)
  ·
    refine ⟨99861678106836886815362777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66574452071224591210241851 99861678106836886815362777)
    ·
      refine ⟨74896258580127665111522083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99861678106836886815362777 74896258580127665111522083)
      ·
        refine ⟨112344387870191497667283125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74896258580127665111522083 112344387870191497667283125)
        ·
          refine ⟨10532286362830452906307793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 112344387870191497667283125 10532286362830452906307793)
          ·
            refine ⟨7899214772122839679730845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10532286362830452906307793 7899214772122839679730845)
            ·
              refine ⟨2962205539546064879899067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7899214772122839679730845 2962205539546064879899067)
              ·
                refine ⟨4443308309319097319848601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2962205539546064879899067 4443308309319097319848601)
                ·
                  refine ⟨3332481231989322989886451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4443308309319097319848601 3332481231989322989886451)
                  ·
                    refine ⟨4998721847983984484829677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3332481231989322989886451 4998721847983984484829677)
                    ·
                      refine ⟨1874520692993994181811129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4998721847983984484829677 1874520692993994181811129)
                      ·
                        rfl

theorem cell23_3650616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 2, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 2, 3, 1, 2, 1, 3].length) (baseStart_3650616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3650616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3650616 prefixEnd_3650616 := by exact prefixLift 3650616
  have htrace : WordTrace (prefixWord ++ tailWord_3650616) baseStart_3650616 baseEnd_3650616 := by
    simpa [prefixWord, tailWord_3650616, baseEnd_3650616] using wordTrace_append hprefix tailTrace_3650616
  have hstable : (prefixWord ++ tailWord_3650616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3650616).length < 2 ^ (prefixWord ++ tailWord_3650616).sum := by decide
  have hdescent : baseEnd_3650616 < baseStart_3650616 := by decide
  rcases family_descends (prefixWord ++ tailWord_3650616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3650642 : List Nat := [3, 2, 2, 1, 3, 2, 1, 1, 2, 1, 5]
def baseStart_3650642 : Nat := 118140960795 + 3650642 * 2 ^ 59
def prefixEnd_3650642 : Nat := 4983230072969 + 3 ^ 40 * 3650642 * 2
def baseEnd_3650642 : Nat := 1874534043491011080086009

theorem tailTrace_3650642 : CollatzResearch.WordTrace tailWord_3650642 prefixEnd_3650642 1874534043491011080086009 := by
  unfold tailWord_3650642
  simp only [CollatzResearch.WordTrace]
  refine ⟨33287463110088747215232545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88766568293569992573953453 33287463110088747215232545)
  ·
    refine ⟨24965597332566560411424409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33287463110088747215232545 24965597332566560411424409)
    ·
      refine ⟨18724197999424920308568307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24965597332566560411424409 18724197999424920308568307)
      ·
        refine ⟨28086296999137380462852461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18724197999424920308568307 28086296999137380462852461)
        ·
          refine ⟨10532361374676517673569673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28086296999137380462852461 10532361374676517673569673)
          ·
            refine ⟨7899271031007388255177255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10532361374676517673569673 7899271031007388255177255)
            ·
              refine ⟨11848906546511082382765883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7899271031007388255177255 11848906546511082382765883)
              ·
                refine ⟨17773359819766623574148825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11848906546511082382765883 17773359819766623574148825)
                ·
                  refine ⟨13330019864824967680611619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17773359819766623574148825 13330019864824967680611619)
                  ·
                    refine ⟨19995029797237451520917429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13330019864824967680611619 19995029797237451520917429)
                    ·
                      refine ⟨1874534043491011080086009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19995029797237451520917429 1874534043491011080086009)
                      ·
                        rfl

theorem cell23_3650642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 2, 1, 1, 2, 1, 5].length) (baseStart_3650642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3650642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3650642 prefixEnd_3650642 := by exact prefixLift 3650642
  have htrace : WordTrace (prefixWord ++ tailWord_3650642) baseStart_3650642 baseEnd_3650642 := by
    simpa [prefixWord, tailWord_3650642, baseEnd_3650642] using wordTrace_append hprefix tailTrace_3650642
  have hstable : (prefixWord ++ tailWord_3650642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3650642).length < 2 ^ (prefixWord ++ tailWord_3650642).sum := by decide
  have hdescent : baseEnd_3650642 < baseStart_3650642 := by decide
  rcases family_descends (prefixWord ++ tailWord_3650642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3650685 : List Nat := [1, 4, 1, 1, 3, 1, 1, 2, 1, 1, 7]
def baseStart_3650685 : Nat := 118140960795 + 3650685 * 2 ^ 59
def prefixEnd_3650685 : Nat := 4983230072969 + 3 ^ 40 * 3650685 * 2
def baseEnd_3650685 : Nat := 1874556123159154411848311

theorem tailTrace_3650685 : CollatzResearch.WordTrace tailWord_3650685 prefixEnd_3650685 1874556123159154411848311 := by
  unfold tailWord_3650685
  simp only [CollatzResearch.WordTrace]
  refine ⟨133151420779199207204745509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88767613852799471469830339 133151420779199207204745509)
  ·
    refine ⟨24965891396099851350889783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 133151420779199207204745509 24965891396099851350889783)
    ·
      refine ⟨37448837094149777026334675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24965891396099851350889783 37448837094149777026334675)
      ·
        refine ⟨56173255641224665539502013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37448837094149777026334675 56173255641224665539502013)
        ·
          refine ⟨21064970865459249577313255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56173255641224665539502013 21064970865459249577313255)
          ·
            refine ⟨31597456298188874365969883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21064970865459249577313255 31597456298188874365969883)
            ·
              refine ⟨47396184447283311548954825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31597456298188874365969883 47396184447283311548954825)
              ·
                refine ⟨35547138335462483661716119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47396184447283311548954825 35547138335462483661716119)
                ·
                  refine ⟨53320707503193725492574179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35547138335462483661716119 53320707503193725492574179)
                  ·
                    refine ⟨79981061254790588238861269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 53320707503193725492574179 79981061254790588238861269)
                    ·
                      refine ⟨1874556123159154411848311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 79981061254790588238861269 1874556123159154411848311)
                      ·
                        rfl

theorem cell23_3650685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 1, 2, 1, 1, 7].length) (baseStart_3650685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3650685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3650685 prefixEnd_3650685 := by exact prefixLift 3650685
  have htrace : WordTrace (prefixWord ++ tailWord_3650685) baseStart_3650685 baseEnd_3650685 := by
    simpa [prefixWord, tailWord_3650685, baseEnd_3650685] using wordTrace_append hprefix tailTrace_3650685
  have hstable : (prefixWord ++ tailWord_3650685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3650685).length < 2 ^ (prefixWord ++ tailWord_3650685).sum := by decide
  have hdescent : baseEnd_3650685 < baseStart_3650685 := by decide
  rcases family_descends (prefixWord ++ tailWord_3650685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3650692 : List Nat := [2, 3, 2, 1, 2, 2, 1, 3, 2, 5]
def baseStart_3650692 : Nat := 118140960795 + 3650692 * 2 ^ 59
def prefixEnd_3650692 : Nat := 4983230072969 + 3 ^ 40 * 3650692 * 2
def baseEnd_3650692 : Nat := 624853239174578628153593

theorem tailTrace_3650692 : CollatzResearch.WordTrace tailWord_3650692 prefixEnd_3650692 624853239174578628153593 := by
  unfold tailWord_3650692
  simp only [CollatzResearch.WordTrace]
  refine ⟨66575838045086923700125165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88767784060115898266833553 66575838045086923700125165)
  ·
    refine ⟨24965939266907596387546937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66575838045086923700125165 24965939266907596387546937)
    ·
      refine ⟨18724454450180697290660203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24965939266907596387546937 18724454450180697290660203)
      ·
        refine ⟨28086681675271045935990305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18724454450180697290660203 28086681675271045935990305)
        ·
          refine ⟨21065011256453284451992729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28086681675271045935990305 21065011256453284451992729)
          ·
            refine ⟨15798758442339963338994547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21065011256453284451992729 15798758442339963338994547)
            ·
              refine ⟨23698137663509945008491821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15798758442339963338994547 23698137663509945008491821)
              ·
                refine ⟨8886801623816229378184433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23698137663509945008491821 8886801623816229378184433)
                ·
                  refine ⟨6665101217862172033638325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8886801623816229378184433 6665101217862172033638325)
                  ·
                    refine ⟨624853239174578628153593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6665101217862172033638325 624853239174578628153593)
                    ·
                      rfl

theorem cell23_3650692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 1, 3, 2, 5].length) (baseStart_3650692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3650692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3650692 prefixEnd_3650692 := by exact prefixLift 3650692
  have htrace : WordTrace (prefixWord ++ tailWord_3650692) baseStart_3650692 baseEnd_3650692 := by
    simpa [prefixWord, tailWord_3650692, baseEnd_3650692] using wordTrace_append hprefix tailTrace_3650692
  have hstable : (prefixWord ++ tailWord_3650692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3650692).length < 2 ^ (prefixWord ++ tailWord_3650692).sum := by decide
  have hdescent : baseEnd_3650692 < baseStart_3650692 := by decide
  rcases family_descends (prefixWord ++ tailWord_3650692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3650702 : List Nat := [4, 1, 1, 3, 2, 1, 1, 2, 1, 2, 5]
def baseStart_3650702 : Nat := 118140960795 + 3650702 * 2 ^ 59
def prefixEnd_3650702 : Nat := 4983230072969 + 3 ^ 40 * 3650702 * 2
def baseEnd_3650702 : Nat := 1874564852330280845335733

theorem tailTrace_3650702 : CollatzResearch.WordTrace tailWord_3650702 prefixEnd_3650702 1874564852330280845335733 := by
  unfold tailWord_3650702
  simp only [CollatzResearch.WordTrace]
  refine ⟨16644005102517202388514295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 88768027213425079405409573 16644005102517202388514295)
  ·
    refine ⟨24966007653775803582771443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16644005102517202388514295 24966007653775803582771443)
    ·
      refine ⟨37449011480663705374157165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24966007653775803582771443 37449011480663705374157165)
      ·
        refine ⟨14043379305248889515308937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37449011480663705374157165 14043379305248889515308937)
        ·
          refine ⟨10532534478936667136481703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14043379305248889515308937 10532534478936667136481703)
          ·
            refine ⟨15798801718405000704722555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10532534478936667136481703 15798801718405000704722555)
            ·
              refine ⟨23698202577607501057083833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15798801718405000704722555 23698202577607501057083833)
              ·
                refine ⟨17773651933205625792812875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23698202577607501057083833 17773651933205625792812875)
                ·
                  refine ⟨26660477899808438689219313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17773651933205625792812875 26660477899808438689219313)
                  ·
                    refine ⟨19995358424856329016914485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26660477899808438689219313 19995358424856329016914485)
                    ·
                      refine ⟨1874564852330280845335733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19995358424856329016914485 1874564852330280845335733)
                      ·
                        rfl

theorem cell23_3650702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 1, 2, 1, 2, 5].length) (baseStart_3650702 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3650702 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3650702 prefixEnd_3650702 := by exact prefixLift 3650702
  have htrace : WordTrace (prefixWord ++ tailWord_3650702) baseStart_3650702 baseEnd_3650702 := by
    simpa [prefixWord, tailWord_3650702, baseEnd_3650702] using wordTrace_append hprefix tailTrace_3650702
  have hstable : (prefixWord ++ tailWord_3650702).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3650702).length < 2 ^ (prefixWord ++ tailWord_3650702).sum := by decide
  have hdescent : baseEnd_3650702 < baseStart_3650702 := by decide
  rcases family_descends (prefixWord ++ tailWord_3650702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3650749 : List Nat := [1, 4, 1, 2, 1, 1, 5, 1, 2, 2, 3]
def baseStart_3650749 : Nat := 118140960795 + 3650749 * 2 ^ 59
def prefixEnd_3650749 : Nat := 4983230072969 + 3 ^ 40 * 3650749 * 2
def baseEnd_3650749 : Nat := 1874588985921042161448017

theorem tailTrace_3650749 : CollatzResearch.WordTrace tailWord_3650749 prefixEnd_3650749 1874588985921042161448017 := by
  unfold tailWord_3650749
  simp only [CollatzResearch.WordTrace]
  refine ⟨133153755050967346135075301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88769170033978230756716867 133153755050967346135075301)
  ·
    refine ⟨24966329072056377400326619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 133153755050967346135075301 24966329072056377400326619)
    ·
      refine ⟨37449493608084566100489929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24966329072056377400326619 37449493608084566100489929)
      ·
        refine ⟨28087120206063424575367447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37449493608084566100489929 28087120206063424575367447)
        ·
          refine ⟨42130680309095136863051171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28087120206063424575367447 42130680309095136863051171)
          ·
            refine ⟨63196020463642705294576757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42130680309095136863051171 63196020463642705294576757)
            ·
              refine ⟨5924626918466503621366571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 63196020463642705294576757 5924626918466503621366571)
              ·
                refine ⟨8886940377699755432049857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5924626918466503621366571 8886940377699755432049857)
                ·
                  refine ⟨6665205283274816574037393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8886940377699755432049857 6665205283274816574037393)
                  ·
                    refine ⟨4998903962456112430528045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6665205283274816574037393 4998903962456112430528045)
                    ·
                      refine ⟨1874588985921042161448017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4998903962456112430528045 1874588985921042161448017)
                      ·
                        rfl

theorem cell23_3650749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 5, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 5, 1, 2, 2, 3].length) (baseStart_3650749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3650749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3650749 prefixEnd_3650749 := by exact prefixLift 3650749
  have htrace : WordTrace (prefixWord ++ tailWord_3650749) baseStart_3650749 baseEnd_3650749 := by
    simpa [prefixWord, tailWord_3650749, baseEnd_3650749] using wordTrace_append hprefix tailTrace_3650749
  have hstable : (prefixWord ++ tailWord_3650749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3650749).length < 2 ^ (prefixWord ++ tailWord_3650749).sum := by decide
  have hdescent : baseEnd_3650749 < baseStart_3650749 := by decide
  rcases family_descends (prefixWord ++ tailWord_3650749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3650806 : List Nat := [5, 1, 1, 1, 1, 1, 1, 5, 2, 3, 2]
def baseStart_3650806 : Nat := 118140960795 + 3650806 * 2 ^ 59
def prefixEnd_3650806 : Nat := 4983230072969 + 3 ^ 40 * 3650806 * 2
def baseEnd_3650806 : Nat := 1874618254318348438435255

theorem tailTrace_3650806 : CollatzResearch.WordTrace tailWord_3650806 prefixEnd_3650806 1874618254318348438435255 := by
  unfold tailWord_3650806
  simp only [CollatzResearch.WordTrace]
  refine ⟨8322239625735052804368767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 88770556007840563246600181 8322239625735052804368767)
  ·
    refine ⟨12483359438602579206553151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8322239625735052804368767 12483359438602579206553151)
    ·
      refine ⟨18725039157903868809829727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12483359438602579206553151 18725039157903868809829727)
      ·
        refine ⟨28087558736855803214744591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18725039157903868809829727 28087558736855803214744591)
        ·
          refine ⟨42131338105283704822116887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28087558736855803214744591 42131338105283704822116887)
          ·
            refine ⟨63197007157925557233175331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42131338105283704822116887 63197007157925557233175331)
            ·
              refine ⟨94795510736888335849762997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63197007157925557233175331 94795510736888335849762997)
              ·
                refine ⟨8887079131583281485915281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 94795510736888335849762997 8887079131583281485915281)
                ·
                  refine ⟨6665309348687461114436461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8887079131583281485915281 6665309348687461114436461)
                  ·
                    refine ⟨2499491005757797917913673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6665309348687461114436461 2499491005757797917913673)
                    ·
                      refine ⟨1874618254318348438435255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2499491005757797917913673 1874618254318348438435255)
                      ·
                        rfl

theorem cell23_3650806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 5, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 5, 2, 3, 2].length) (baseStart_3650806 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3650806 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3650806 prefixEnd_3650806 := by exact prefixLift 3650806
  have htrace : WordTrace (prefixWord ++ tailWord_3650806) baseStart_3650806 baseEnd_3650806 := by
    simpa [prefixWord, tailWord_3650806, baseEnd_3650806] using wordTrace_append hprefix tailTrace_3650806
  have hstable : (prefixWord ++ tailWord_3650806).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3650806).length < 2 ^ (prefixWord ++ tailWord_3650806).sum := by decide
  have hdescent : baseEnd_3650806 < baseStart_3650806 := by decide
  rcases family_descends (prefixWord ++ tailWord_3650806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3650819 : List Nat := [1, 1, 1, 3, 2, 4, 2, 3, 1, 1, 4]
def baseStart_3650819 : Nat := 118140960795 + 3650819 * 2 ^ 59
def prefixEnd_3650819 : Nat := 4983230072969 + 3 ^ 40 * 3650819 * 2
def baseEnd_3650819 : Nat := 1874624929566856887572695

theorem tailTrace_3650819 : CollatzResearch.WordTrace tailWord_3650819 prefixEnd_3650819 1874624929566856887572695 := by
  unfold tailWord_3650819
  simp only [CollatzResearch.WordTrace]
  refine ⟨133156308160713748090123511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88770872107142498726749007 133156308160713748090123511)
  ·
    refine ⟨199734462241070622135185267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133156308160713748090123511 199734462241070622135185267)
    ·
      refine ⟨299601693361605933202777901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 199734462241070622135185267 299601693361605933202777901)
      ·
        refine ⟨112350635010602224951041713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 299601693361605933202777901 112350635010602224951041713)
        ·
          refine ⟨84262976257951668713281285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 112350635010602224951041713 84262976257951668713281285)
          ·
            refine ⟨15799308048365937883740241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 84262976257951668713281285 15799308048365937883740241)
            ·
              refine ⟨11849481036274453412805181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15799308048365937883740241 11849481036274453412805181)
              ·
                refine ⟨4443555388602920029801943, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11849481036274453412805181 4443555388602920029801943)
                ·
                  refine ⟨6665333082904380044702915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4443555388602920029801943 6665333082904380044702915)
                  ·
                    refine ⟨9997999624356570067054373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6665333082904380044702915 9997999624356570067054373)
                    ·
                      refine ⟨1874624929566856887572695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9997999624356570067054373 1874624929566856887572695)
                      ·
                        rfl

theorem cell23_3650819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 2, 3, 1, 1, 4].length) (baseStart_3650819 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3650819 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3650819 prefixEnd_3650819 := by exact prefixLift 3650819
  have htrace : WordTrace (prefixWord ++ tailWord_3650819) baseStart_3650819 baseEnd_3650819 := by
    simpa [prefixWord, tailWord_3650819, baseEnd_3650819] using wordTrace_append hprefix tailTrace_3650819
  have hstable : (prefixWord ++ tailWord_3650819).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3650819).length < 2 ^ (prefixWord ++ tailWord_3650819).sum := by decide
  have hdescent : baseEnd_3650819 < baseStart_3650819 := by decide
  rcases family_descends (prefixWord ++ tailWord_3650819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3650830 : List Nat := [4, 1, 1, 2, 1, 4, 3, 2, 1, 1, 3]
def baseStart_3650830 : Nat := 118140960795 + 3650830 * 2 ^ 59
def prefixEnd_3650830 : Nat := 4983230072969 + 3 ^ 40 * 3650830 * 2
def baseEnd_3650830 : Nat := 1874630577854056344535145

theorem tailTrace_3650830 : CollatzResearch.WordTrace tailWord_3650830 prefixEnd_3650830 1874630577854056344535145 := by
  unfold tailWord_3650830
  simp only [CollatzResearch.WordTrace]
  refine ⟨16644588670459237121096743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 88771139575782597979182629 16644588670459237121096743)
  ·
    refine ⟨24966883005688855681645115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16644588670459237121096743 24966883005688855681645115)
    ·
      refine ⟨37450324508533283522467673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24966883005688855681645115 37450324508533283522467673)
      ·
        refine ⟨28087743381399962641850755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37450324508533283522467673 28087743381399962641850755)
        ·
          refine ⟨42131615072099943962776133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28087743381399962641850755 42131615072099943962776133)
          ·
            refine ⟨7899677826018739493020525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 42131615072099943962776133 7899677826018739493020525)
            ·
              refine ⟨2962379184757027309882697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7899677826018739493020525 2962379184757027309882697)
              ·
                refine ⟨2221784388567770482412023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2962379184757027309882697 2221784388567770482412023)
                ·
                  refine ⟨3332676582851655723618035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2221784388567770482412023 3332676582851655723618035)
                  ·
                    refine ⟨4999014874277483585427053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3332676582851655723618035 4999014874277483585427053)
                    ·
                      refine ⟨1874630577854056344535145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4999014874277483585427053 1874630577854056344535145)
                      ·
                        rfl

theorem cell23_3650830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 4, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 4, 3, 2, 1, 1, 3].length) (baseStart_3650830 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3650830 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3650830 prefixEnd_3650830 := by exact prefixLift 3650830
  have htrace : WordTrace (prefixWord ++ tailWord_3650830) baseStart_3650830 baseEnd_3650830 := by
    simpa [prefixWord, tailWord_3650830, baseEnd_3650830] using wordTrace_append hprefix tailTrace_3650830
  have hstable : (prefixWord ++ tailWord_3650830).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3650830).length < 2 ^ (prefixWord ++ tailWord_3650830).sum := by decide
  have hdescent : baseEnd_3650830 < baseStart_3650830 := by decide
  rcases family_descends (prefixWord ++ tailWord_3650830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3650839 : List Nat := [1, 1, 3, 4, 1, 1, 2, 2, 3, 2, 3]
def baseStart_3650839 : Nat := 118140960795 + 3650839 * 2 ^ 59
def prefixEnd_3650839 : Nat := 4983230072969 + 3 ^ 40 * 3650839 * 2
def baseEnd_3650839 : Nat := 1874635199179946809322603

theorem tailTrace_3650839 : CollatzResearch.WordTrace tailWord_3650839 prefixEnd_3650839 1874635199179946809322603 := by
  unfold tailWord_3650839
  simp only [CollatzResearch.WordTrace]
  refine ⟨133157037620641291505851571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88771358413760861003901047 133157037620641291505851571)
  ·
    refine ⟨199735556430961937258777357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133157037620641291505851571 199735556430961937258777357)
    ·
      refine ⟨74900833661610726472041509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 199735556430961937258777357 74900833661610726472041509)
      ·
        refine ⟨14043906311552011213507783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 74900833661610726472041509 14043906311552011213507783)
        ·
          refine ⟨21065859467328016820261675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14043906311552011213507783 21065859467328016820261675)
          ·
            refine ⟨31598789200992025230392513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21065859467328016820261675 31598789200992025230392513)
            ·
              refine ⟨23699091900744018922794385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31598789200992025230392513 23699091900744018922794385)
              ·
                refine ⟨17774318925558014192095789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23699091900744018922794385 17774318925558014192095789)
                ·
                  refine ⟨6665369597084255322035921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17774318925558014192095789 6665369597084255322035921)
                  ·
                    refine ⟨4999027197813191491526941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6665369597084255322035921 4999027197813191491526941)
                    ·
                      refine ⟨1874635199179946809322603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4999027197813191491526941 1874635199179946809322603)
                      ·
                        rfl

theorem cell23_3650839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 2, 2, 3, 2, 3].length) (baseStart_3650839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3650839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3650839 prefixEnd_3650839 := by exact prefixLift 3650839
  have htrace : WordTrace (prefixWord ++ tailWord_3650839) baseStart_3650839 baseEnd_3650839 := by
    simpa [prefixWord, tailWord_3650839, baseEnd_3650839] using wordTrace_append hprefix tailTrace_3650839
  have hstable : (prefixWord ++ tailWord_3650839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3650839).length < 2 ^ (prefixWord ++ tailWord_3650839).sum := by decide
  have hdescent : baseEnd_3650839 < baseStart_3650839 := by decide
  rcases family_descends (prefixWord ++ tailWord_3650839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3650842 : List Nat := [3, 1, 1, 3, 3, 1, 1, 10]
def baseStart_3650842 : Nat := 118140960795 + 3650842 * 2 ^ 59
def prefixEnd_3650842 : Nat := 4983230072969 + 3 ^ 40 * 3650842 * 2
def baseEnd_3650842 : Nat := 69430990356367048058707

theorem tailTrace_3650842 : CollatzResearch.WordTrace tailWord_3650842 prefixEnd_3650842 69430990356367048058707 := by
  unfold tailWord_3650842
  simp only [CollatzResearch.WordTrace]
  refine ⟨33289286759907605754552695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88771431359753615345473853 33289286759907605754552695)
  ·
    refine ⟨49933930139861408631829043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33289286759907605754552695 49933930139861408631829043)
    ·
      refine ⟨74900895209792112947743565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49933930139861408631829043 74900895209792112947743565)
      ·
        refine ⟨28087835703672042355403837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 74900895209792112947743565 28087835703672042355403837)
        ·
          refine ⟨10532938388877015883276439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28087835703672042355403837 10532938388877015883276439)
          ·
            refine ⟨15799407583315523824914659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10532938388877015883276439 15799407583315523824914659)
            ·
              refine ⟨23699111374973285737371989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15799407583315523824914659 23699111374973285737371989)
              ·
                refine ⟨69430990356367048058707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 23699111374973285737371989 69430990356367048058707)
                ·
                  rfl

theorem cell23_3650842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 1, 10].length) (baseStart_3650842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3650842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3650842 prefixEnd_3650842 := by exact prefixLift 3650842
  have htrace : WordTrace (prefixWord ++ tailWord_3650842) baseStart_3650842 baseEnd_3650842 := by
    simpa [prefixWord, tailWord_3650842, baseEnd_3650842] using wordTrace_append hprefix tailTrace_3650842
  have hstable : (prefixWord ++ tailWord_3650842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3650842).length < 2 ^ (prefixWord ++ tailWord_3650842).sum := by decide
  have hdescent : baseEnd_3650842 < baseStart_3650842 := by decide
  rcases family_descends (prefixWord ++ tailWord_3650842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3650856 : List Nat := [2, 1, 5, 1, 2, 2, 1, 1, 3, 2, 3]
def baseStart_3650856 : Nat := 118140960795 + 3650856 * 2 ^ 59
def prefixEnd_3650856 : Nat := 4983230072969 + 3 ^ 40 * 3650856 * 2
def baseEnd_3650856 : Nat := 1874643928351073242810025

theorem tailTrace_3650856 : CollatzResearch.WordTrace tailWord_3650856 prefixEnd_3650856 1874643928351073242810025 := by
  unfold tailWord_3650856
  simp only [CollatzResearch.WordTrace]
  refine ⟨66578828830789851704610211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88771771774386468939480281 66578828830789851704610211)
  ·
    refine ⟨99868243246184777556915317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66578828830789851704610211 99868243246184777556915317)
    ·
      refine ⟨9362647804329822895960811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 99868243246184777556915317 9362647804329822895960811)
      ·
        refine ⟨14043971706494734343941217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9362647804329822895960811 14043971706494734343941217)
        ·
          refine ⟨10532978779871050757955913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14043971706494734343941217 10532978779871050757955913)
          ·
            refine ⟨7899734084903288068466935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10532978779871050757955913 7899734084903288068466935)
            ·
              refine ⟨11849601127354932102700403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7899734084903288068466935 11849601127354932102700403)
              ·
                refine ⟨17774401691032398154050605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11849601127354932102700403 17774401691032398154050605)
                ·
                  refine ⟨6665400634137149307768977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17774401691032398154050605 6665400634137149307768977)
                  ·
                    refine ⟨4999050475602861980826733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6665400634137149307768977 4999050475602861980826733)
                    ·
                      refine ⟨1874643928351073242810025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4999050475602861980826733 1874643928351073242810025)
                      ·
                        rfl

theorem cell23_3650856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 2, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 2, 1, 1, 3, 2, 3].length) (baseStart_3650856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3650856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3650856 prefixEnd_3650856 := by exact prefixLift 3650856
  have htrace : WordTrace (prefixWord ++ tailWord_3650856) baseStart_3650856 baseEnd_3650856 := by
    simpa [prefixWord, tailWord_3650856, baseEnd_3650856] using wordTrace_append hprefix tailTrace_3650856
  have hstable : (prefixWord ++ tailWord_3650856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3650856).length < 2 ^ (prefixWord ++ tailWord_3650856).sum := by decide
  have hdescent : baseEnd_3650856 < baseStart_3650856 := by decide
  rcases family_descends (prefixWord ++ tailWord_3650856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3650869 : List Nat := [1, 3, 3, 1, 2, 2, 1, 1, 3, 3, 3]
def baseStart_3650869 : Nat := 118140960795 + 3650869 * 2 ^ 59
def prefixEnd_3650869 : Nat := 4983230072969 + 3 ^ 40 * 3650869 * 2
def baseEnd_3650869 : Nat := 1874650603599581691947465

theorem tailTrace_3650869 : CollatzResearch.WordTrace tailWord_3650869 prefixEnd_3650869 1874650603599581691947465 := by
  unfold tailWord_3650869
  simp only [CollatzResearch.WordTrace]
  refine ⟨133158131810532606629443661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88772087873688404419629107 133158131810532606629443661)
  ·
    refine ⟨49934299428949727486041373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 133158131810532606629443661 49934299428949727486041373)
    ·
      refine ⟨18725362285856147807265515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49934299428949727486041373 18725362285856147807265515)
      ·
        refine ⟨28088043428784221710898273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18725362285856147807265515 28088043428784221710898273)
        ·
          refine ⟨21066032571588166283173705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28088043428784221710898273 21066032571588166283173705)
          ·
            refine ⟨15799524428691124712380279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21066032571588166283173705 15799524428691124712380279)
            ·
              refine ⟨23699286643036687068570419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15799524428691124712380279 23699286643036687068570419)
              ·
                refine ⟨35548929964555030602855629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23699286643036687068570419 35548929964555030602855629)
                ·
                  refine ⟨13330848736708136476070861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35548929964555030602855629 13330848736708136476070861)
                  ·
                    refine ⟨4999068276265551178526573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13330848736708136476070861 4999068276265551178526573)
                    ·
                      refine ⟨1874650603599581691947465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4999068276265551178526573 1874650603599581691947465)
                      ·
                        rfl

theorem cell23_3650869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 1, 1, 3, 3, 3].length) (baseStart_3650869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3650869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3650869 prefixEnd_3650869 := by exact prefixLift 3650869
  have htrace : WordTrace (prefixWord ++ tailWord_3650869) baseStart_3650869 baseEnd_3650869 := by
    simpa [prefixWord, tailWord_3650869, baseEnd_3650869] using wordTrace_append hprefix tailTrace_3650869
  have hstable : (prefixWord ++ tailWord_3650869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3650869).length < 2 ^ (prefixWord ++ tailWord_3650869).sum := by decide
  have hdescent : baseEnd_3650869 < baseStart_3650869 := by decide
  rcases family_descends (prefixWord ++ tailWord_3650869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3650873 : List Nat := [1, 2, 1, 6, 3, 1, 1, 1, 1, 1, 5]
def baseStart_3650873 : Nat := 118140960795 + 3650873 * 2 ^ 59
def prefixEnd_3650873 : Nat := 4983230072969 + 3 ^ 40 * 3650873 * 2
def baseEnd_3650873 : Nat := 1874652657522199676297447

theorem tailTrace_3650873 : CollatzResearch.WordTrace tailWord_3650873 prefixEnd_3650873 1874652657522199676297447 := by
  unfold tailWord_3650873
  simp only [CollatzResearch.WordTrace]
  refine ⟨133158277702518115312589273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88772185135012076875059515 133158277702518115312589273)
  ·
    refine ⟨99868708276888586484441955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133158277702518115312589273 99868708276888586484441955)
    ·
      refine ⟨149803062415332879726662933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99868708276888586484441955 149803062415332879726662933)
      ·
        refine ⟨7022018550718728737187325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 149803062415332879726662933 7022018550718728737187325)
        ·
          refine ⟨2633256956519523276445247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7022018550718728737187325 2633256956519523276445247)
          ·
            refine ⟨3949885434779284914667871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2633256956519523276445247 3949885434779284914667871)
            ·
              refine ⟨5924828152168927372001807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3949885434779284914667871 5924828152168927372001807)
              ·
                refine ⟨8887242228253391058002711, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5924828152168927372001807 8887242228253391058002711)
                ·
                  refine ⟨13330863342380086587004067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8887242228253391058002711 13330863342380086587004067)
                  ·
                    refine ⟨19996295013570129880506101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13330863342380086587004067 19996295013570129880506101)
                    ·
                      refine ⟨1874652657522199676297447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 19996295013570129880506101 1874652657522199676297447)
                      ·
                        rfl

theorem cell23_3650873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 3, 1, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 3, 1, 1, 1, 1, 1, 5].length) (baseStart_3650873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3650873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3650873 prefixEnd_3650873 := by exact prefixLift 3650873
  have htrace : WordTrace (prefixWord ++ tailWord_3650873) baseStart_3650873 baseEnd_3650873 := by
    simpa [prefixWord, tailWord_3650873, baseEnd_3650873] using wordTrace_append hprefix tailTrace_3650873
  have hstable : (prefixWord ++ tailWord_3650873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3650873).length < 2 ^ (prefixWord ++ tailWord_3650873).sum := by decide
  have hdescent : baseEnd_3650873 < baseStart_3650873 := by decide
  rcases family_descends (prefixWord ++ tailWord_3650873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3650887 : List Nat := [1, 1, 4, 1, 2, 5, 2, 2, 1, 2, 2]
def baseStart_3650887 : Nat := 118140960795 + 3650887 * 2 ^ 59
def prefixEnd_3650887 : Nat := 4983230072969 + 3 ^ 40 * 3650887 * 2
def baseEnd_3650887 : Nat := 1874659846251362621522383

theorem tailTrace_3650887 : CollatzResearch.WordTrace tailWord_3650887 prefixEnd_3650887 1874659846251362621522383 := by
  unfold tailWord_3650887
  simp only [CollatzResearch.WordTrace]
  refine ⟨133158788324467395703598915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88772525549644930469065943 133158788324467395703598915)
  ·
    refine ⟨199738182486701093555398373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133158788324467395703598915 199738182486701093555398373)
    ·
      refine ⟨37450909216256455041637195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 199738182486701093555398373 37450909216256455041637195)
      ·
        refine ⟨56176363824384682562455793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37450909216256455041637195 56176363824384682562455793)
        ·
          refine ⟨42132272868288511921841845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56176363824384682562455793 42132272868288511921841845)
          ·
            refine ⟨3949900581402047992672673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 42132272868288511921841845 3949900581402047992672673)
            ·
              refine ⟨2962425436051535994504505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3949900581402047992672673 2962425436051535994504505)
              ·
                refine ⟨2221819077038651995878379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2962425436051535994504505 2221819077038651995878379)
                ·
                  refine ⟨3332728615557977993817569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2221819077038651995878379 3332728615557977993817569)
                  ·
                    refine ⟨2499546461668483495363177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3332728615557977993817569 2499546461668483495363177)
                    ·
                      refine ⟨1874659846251362621522383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2499546461668483495363177 1874659846251362621522383)
                      ·
                        rfl

theorem cell23_3650887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 5, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 5, 2, 2, 1, 2, 2].length) (baseStart_3650887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3650887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3650887 prefixEnd_3650887 := by exact prefixLift 3650887
  have htrace : WordTrace (prefixWord ++ tailWord_3650887) baseStart_3650887 baseEnd_3650887 := by
    simpa [prefixWord, tailWord_3650887, baseEnd_3650887] using wordTrace_append hprefix tailTrace_3650887
  have hstable : (prefixWord ++ tailWord_3650887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3650887).length < 2 ^ (prefixWord ++ tailWord_3650887).sum := by decide
  have hdescent : baseEnd_3650887 < baseStart_3650887 := by decide
  rcases family_descends (prefixWord ++ tailWord_3650887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3650893 : List Nat := [1, 6, 1, 3, 1, 2, 1, 8]
def baseStart_3650893 : Nat := 118140960795 + 3650893 * 2 ^ 59
def prefixEnd_3650893 : Nat := 4983230072969 + 3 ^ 40 * 3650893 * 2
def baseEnd_3650893 : Nat := 69431960264269985112865

theorem tailTrace_3650893 : CollatzResearch.WordTrace tailWord_3650893 prefixEnd_3650893 69431960264269985112865 := by
  unfold tailWord_3650893
  simp only [CollatzResearch.WordTrace]
  refine ⟨133159007162445658728317333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88772671441630439152211555 133159007162445658728317333)
  ·
    refine ⟨6241828460739640252889875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 133159007162445658728317333 6241828460739640252889875)
    ·
      refine ⟨9362742691109460379334813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6241828460739640252889875 9362742691109460379334813)
      ·
        refine ⟨3511028509166047642250555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9362742691109460379334813 3511028509166047642250555)
        ·
          refine ⟨5266542763749071463375833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3511028509166047642250555 5266542763749071463375833)
          ·
            refine ⟨3949907072811803597531875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5266542763749071463375833 3949907072811803597531875)
            ·
              refine ⟨5924860609217705396297813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3949907072811803597531875 5924860609217705396297813)
              ·
                refine ⟨69431960264269985112865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5924860609217705396297813 69431960264269985112865)
                ·
                  rfl

theorem cell23_3650893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 2, 1, 8].length) (baseStart_3650893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3650893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3650893 prefixEnd_3650893 := by exact prefixLift 3650893
  have htrace : WordTrace (prefixWord ++ tailWord_3650893) baseStart_3650893 baseEnd_3650893 := by
    simpa [prefixWord, tailWord_3650893, baseEnd_3650893] using wordTrace_append hprefix tailTrace_3650893
  have hstable : (prefixWord ++ tailWord_3650893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3650893).length < 2 ^ (prefixWord ++ tailWord_3650893).sum := by decide
  have hdescent : baseEnd_3650893 < baseStart_3650893 := by decide
  rcases family_descends (prefixWord ++ tailWord_3650893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3650979 : List Nat := [1, 1, 1, 4, 1, 3, 2, 3, 2, 5]
def baseStart_3650979 : Nat := 118140960795 + 3650979 * 2 ^ 59
def prefixEnd_3650979 : Nat := 4983230072969 + 3 ^ 40 * 3650979 * 2
def baseEnd_3650979 : Nat := 624902362157192087190653

theorem tailTrace_3650979 : CollatzResearch.WordTrace tailWord_3650979 prefixEnd_3650979 624902362157192087190653 := by
  unfold tailWord_3650979
  simp only [CollatzResearch.WordTrace]
  refine ⟨133162143840134095415947991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88774762560089396943965327 133162143840134095415947991)
  ·
    refine ⟨199743215760201143123921987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133162143840134095415947991 199743215760201143123921987)
    ·
      refine ⟨299614823640301714685882981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 199743215760201143123921987 299614823640301714685882981)
      ·
        refine ⟨56177779432556571503603059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 299614823640301714685882981 56177779432556571503603059)
        ·
          refine ⟨84266669148834857255404589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56177779432556571503603059 84266669148834857255404589)
          ·
            refine ⟨31600000930813071470776721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 84266669148834857255404589 31600000930813071470776721)
            ·
              refine ⟨23700000698109803603082541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31600000930813071470776721 23700000698109803603082541)
              ·
                refine ⟨8887500261791176351155953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23700000698109803603082541 8887500261791176351155953)
                ·
                  refine ⟨6665625196343382263366965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8887500261791176351155953 6665625196343382263366965)
                  ·
                    refine ⟨624902362157192087190653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6665625196343382263366965 624902362157192087190653)
                    ·
                      rfl

theorem cell23_3650979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 2, 3, 2, 5].length) (baseStart_3650979 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3650979 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3650979 prefixEnd_3650979 := by exact prefixLift 3650979
  have htrace : WordTrace (prefixWord ++ tailWord_3650979) baseStart_3650979 baseEnd_3650979 := by
    simpa [prefixWord, tailWord_3650979, baseEnd_3650979] using wordTrace_append hprefix tailTrace_3650979
  have hstable : (prefixWord ++ tailWord_3650979).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3650979).length < 2 ^ (prefixWord ++ tailWord_3650979).sum := by decide
  have hdescent : baseEnd_3650979 < baseStart_3650979 := by decide
  rcases family_descends (prefixWord ++ tailWord_3650979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3651016 : List Nat := [2, 1, 3, 1, 3, 1, 2, 1, 1, 6, 2]
def baseStart_3651016 : Nat := 118140960795 + 3651016 * 2 ^ 59
def prefixEnd_3651016 : Nat := 4983230072969 + 3 ^ 40 * 3651016 * 2
def baseEnd_3651016 : Nat := 1874726085255792616809289

theorem tailTrace_3651016 : CollatzResearch.WordTrace tailWord_3651016 prefixEnd_3651016 1874726085255792616809289 := by
  unfold tailWord_3651016
  simp only [CollatzResearch.WordTrace]
  refine ⟨66581746670500025367522451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88775662227333367156696601 66581746670500025367522451)
  ·
    refine ⟨99872620005750038051283677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66581746670500025367522451 99872620005750038051283677)
    ·
      refine ⟨37452232502156264269231379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 99872620005750038051283677 37452232502156264269231379)
      ·
        refine ⟨56178348753234396403847069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37452232502156264269231379 56178348753234396403847069)
        ·
          refine ⟨21066880782462898651442651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56178348753234396403847069 21066880782462898651442651)
          ·
            refine ⟨31600321173694347977163977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21066880782462898651442651 31600321173694347977163977)
            ·
              refine ⟨23700240880270760982872983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31600321173694347977163977 23700240880270760982872983)
              ·
                refine ⟨35550361320406141474309475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23700240880270760982872983 35550361320406141474309475)
                ·
                  refine ⟨53325541980609212211464213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35550361320406141474309475 53325541980609212211464213)
                  ·
                    refine ⟨2499634780341056822412385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 53325541980609212211464213 2499634780341056822412385)
                    ·
                      refine ⟨1874726085255792616809289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2499634780341056822412385 1874726085255792616809289)
                      ·
                        rfl

theorem cell23_3651016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 2, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 2, 1, 1, 6, 2].length) (baseStart_3651016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3651016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3651016 prefixEnd_3651016 := by exact prefixLift 3651016
  have htrace : WordTrace (prefixWord ++ tailWord_3651016) baseStart_3651016 baseEnd_3651016 := by
    simpa [prefixWord, tailWord_3651016, baseEnd_3651016] using wordTrace_append hprefix tailTrace_3651016
  have hstable : (prefixWord ++ tailWord_3651016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3651016).length < 2 ^ (prefixWord ++ tailWord_3651016).sum := by decide
  have hdescent : baseEnd_3651016 < baseStart_3651016 := by decide
  rcases family_descends (prefixWord ++ tailWord_3651016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3651019 : List Nat := [1, 1, 1, 1, 3, 3, 2, 1, 3, 4, 3]
def baseStart_3651019 : Nat := 118140960795 + 3651019 * 2 ^ 59
def prefixEnd_3651019 : Nat := 4983230072969 + 3 ^ 40 * 3651019 * 2
def baseEnd_3651019 : Nat := 1874727625697756105071775

theorem tailTrace_3651019 : CollatzResearch.WordTrace tailWord_3651019 prefixEnd_3651019 1874727625697756105071775 := by
  unfold tailWord_3651019
  simp only [CollatzResearch.WordTrace]
  refine ⟨133163602759989182247404111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88775735173326121498269407 133163602759989182247404111)
  ·
    refine ⟨199745404139983773371106167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133163602759989182247404111 199745404139983773371106167)
    ·
      refine ⟨299618106209975660056659251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 199745404139983773371106167 299618106209975660056659251)
      ·
        refine ⟨449427159314963490084988877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 299618106209975660056659251 449427159314963490084988877)
        ·
          refine ⟨168535184743111308781870829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 449427159314963490084988877 168535184743111308781870829)
          ·
            refine ⟨63200694278666740793201561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 168535184743111308781870829 63200694278666740793201561)
            ·
              refine ⟨47400520709000055594901171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63200694278666740793201561 47400520709000055594901171)
              ·
                refine ⟨71100781063500083392351757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47400520709000055594901171 71100781063500083392351757)
                ·
                  refine ⟨26662792898812531272131909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 71100781063500083392351757 26662792898812531272131909)
                  ·
                    refine ⟨4999273668527349613524733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26662792898812531272131909 4999273668527349613524733)
                    ·
                      refine ⟨1874727625697756105071775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4999273668527349613524733 1874727625697756105071775)
                      ·
                        rfl

theorem cell23_3651019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 2, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 2, 1, 3, 4, 3].length) (baseStart_3651019 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3651019 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3651019 prefixEnd_3651019 := by exact prefixLift 3651019
  have htrace : WordTrace (prefixWord ++ tailWord_3651019) baseStart_3651019 baseEnd_3651019 := by
    simpa [prefixWord, tailWord_3651019, baseEnd_3651019] using wordTrace_append hprefix tailTrace_3651019
  have hstable : (prefixWord ++ tailWord_3651019).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3651019).length < 2 ^ (prefixWord ++ tailWord_3651019).sum := by decide
  have hdescent : baseEnd_3651019 < baseStart_3651019 := by decide
  rcases family_descends (prefixWord ++ tailWord_3651019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3651049 : List Nat := [1, 2, 1, 1, 1, 2, 1, 2, 4, 5, 3]
def baseStart_3651049 : Nat := 118140960795 + 3651049 * 2 ^ 59
def prefixEnd_3651049 : Nat := 4983230072969 + 3 ^ 40 * 3651049 * 2
def baseEnd_3651049 : Nat := 1874743030117390987696637

theorem tailTrace_3651049 : CollatzResearch.WordTrace tailWord_3651049 prefixEnd_3651049 1874743030117390987696637 := by
  unfold tailWord_3651049
  simp only [CollatzResearch.WordTrace]
  refine ⟨133164696949880497370996201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88776464633253664913997467 133164696949880497370996201)
  ·
    refine ⟨99873522712410373028247151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133164696949880497370996201 99873522712410373028247151)
    ·
      refine ⟨149810284068615559542370727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99873522712410373028247151 149810284068615559542370727)
      ·
        refine ⟨224715426102923339313556091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149810284068615559542370727 224715426102923339313556091)
        ·
          refine ⟨337073139154385008970334137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 224715426102923339313556091 337073139154385008970334137)
          ·
            refine ⟨252804854365788756727750603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 337073139154385008970334137 252804854365788756727750603)
            ·
              refine ⟨379207281548683135091625905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 252804854365788756727750603 379207281548683135091625905)
              ·
                refine ⟨284405461161512351318719429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 379207281548683135091625905 284405461161512351318719429)
                ·
                  refine ⟨53326023967783565872259893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 284405461161512351318719429 53326023967783565872259893)
                  ·
                    refine ⟨4999314746979709300524365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 53326023967783565872259893 4999314746979709300524365)
                    ·
                      refine ⟨1874743030117390987696637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4999314746979709300524365 1874743030117390987696637)
                      ·
                        rfl

theorem cell23_3651049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 2, 4, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 2, 4, 5, 3].length) (baseStart_3651049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3651049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3651049 prefixEnd_3651049 := by exact prefixLift 3651049
  have htrace : WordTrace (prefixWord ++ tailWord_3651049) baseStart_3651049 baseEnd_3651049 := by
    simpa [prefixWord, tailWord_3651049, baseEnd_3651049] using wordTrace_append hprefix tailTrace_3651049
  have hstable : (prefixWord ++ tailWord_3651049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3651049).length < 2 ^ (prefixWord ++ tailWord_3651049).sum := by decide
  have hdescent : baseEnd_3651049 < baseStart_3651049 := by decide
  rcases family_descends (prefixWord ++ tailWord_3651049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3651056 : List Nat := [2, 1, 1, 1, 3, 5, 2, 2, 6]
def baseStart_3651056 : Nat := 118140960795 + 3651056 * 2 ^ 59
def prefixEnd_3651056 : Nat := 4983230072969 + 3 ^ 40 * 3651056 * 2
def baseEnd_3651056 : Nat := 208305180497996940034345

theorem tailTrace_3651056 : CollatzResearch.WordTrace tailWord_3651056 prefixEnd_3651056 208305180497996940034345 := by
  unfold tailWord_3651056
  simp only [CollatzResearch.WordTrace]
  refine ⟨66582476130427568783250511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88776634840570091711000681 66582476130427568783250511)
  ·
    refine ⟨99873714195641353174875767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66582476130427568783250511 99873714195641353174875767)
    ·
      refine ⟨149810571293462029762313651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99873714195641353174875767 149810571293462029762313651)
      ·
        refine ⟨224715856940193044643470477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149810571293462029762313651 224715856940193044643470477)
        ·
          refine ⟨84268446352572391741301429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 224715856940193044643470477 84268446352572391741301429)
          ·
            refine ⟨7900166845553661725747009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 84268446352572391741301429 7900166845553661725747009)
            ·
              refine ⟨5925125134165246294310257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7900166845553661725747009 5925125134165246294310257)
              ·
                refine ⟨4443843850623934720732693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5925125134165246294310257 4443843850623934720732693)
                ·
                  refine ⟨208305180497996940034345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4443843850623934720732693 208305180497996940034345)
                  ·
                    rfl

theorem cell23_3651056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 5, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 5, 2, 2, 6].length) (baseStart_3651056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3651056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3651056 prefixEnd_3651056 := by exact prefixLift 3651056
  have htrace : WordTrace (prefixWord ++ tailWord_3651056) baseStart_3651056 baseEnd_3651056 := by
    simpa [prefixWord, tailWord_3651056, baseEnd_3651056] using wordTrace_append hprefix tailTrace_3651056
  have hstable : (prefixWord ++ tailWord_3651056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3651056).length < 2 ^ (prefixWord ++ tailWord_3651056).sum := by decide
  have hdescent : baseEnd_3651056 < baseStart_3651056 := by decide
  rcases family_descends (prefixWord ++ tailWord_3651056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3651093 : List Nat := [1, 3, 2, 1, 3, 3, 1, 1, 1, 5, 2]
def baseStart_3651093 : Nat := 118140960795 + 3651093 * 2 ^ 59
def prefixEnd_3651093 : Nat := 4983230072969 + 3 ^ 40 * 3651093 * 2
def baseEnd_3651093 : Nat := 1874765623266188815546435

theorem tailTrace_3651093 : CollatzResearch.WordTrace tailWord_3651093 prefixEnd_3651093 1874765623266188815546435 := by
  unfold tailWord_3651093
  simp only [CollatzResearch.WordTrace]
  refine ⟨133166301761721092885597933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88777534507814061923731955 133166301761721092885597933)
  ·
    refine ⟨49937363160645409832099225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 133166301761721092885597933 49937363160645409832099225)
    ·
      refine ⟨37453022370484057374074419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49937363160645409832099225 37453022370484057374074419)
      ·
        refine ⟨56179533555726086061111629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37453022370484057374074419 56179533555726086061111629)
        ·
          refine ⟨21067325083397282272916861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56179533555726086061111629 21067325083397282272916861)
          ·
            refine ⟨7900246906273980852343823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21067325083397282272916861 7900246906273980852343823)
            ·
              refine ⟨11850370359410971278515735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7900246906273980852343823 11850370359410971278515735)
              ·
                refine ⟨17775555539116456917773603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11850370359410971278515735 17775555539116456917773603)
                ·
                  refine ⟨26663333308674685376660405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17775555539116456917773603 26663333308674685376660405)
                  ·
                    refine ⟨2499687497688251754061913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 26663333308674685376660405 2499687497688251754061913)
                    ·
                      refine ⟨1874765623266188815546435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2499687497688251754061913 1874765623266188815546435)
                      ·
                        rfl

theorem cell23_3651093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 3, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 3, 1, 1, 1, 5, 2].length) (baseStart_3651093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3651093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3651093 prefixEnd_3651093 := by exact prefixLift 3651093
  have htrace : WordTrace (prefixWord ++ tailWord_3651093) baseStart_3651093 baseEnd_3651093 := by
    simpa [prefixWord, tailWord_3651093, baseEnd_3651093] using wordTrace_append hprefix tailTrace_3651093
  have hstable : (prefixWord ++ tailWord_3651093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3651093).length < 2 ^ (prefixWord ++ tailWord_3651093).sum := by decide
  have hdescent : baseEnd_3651093 < baseStart_3651093 := by decide
  rcases family_descends (prefixWord ++ tailWord_3651093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3651103 : List Nat := [1, 1, 2, 4, 1, 1, 6, 1, 1, 5]
def baseStart_3651103 : Nat := 118140960795 + 3651103 * 2 ^ 59
def prefixEnd_3651103 : Nat := 4983230072969 + 3 ^ 40 * 3651103 * 2
def baseEnd_3651103 : Nat := 624923586024244592140463

theorem tailTrace_3651103 : CollatzResearch.WordTrace tailWord_3651103 prefixEnd_3651103 624923586024244592140463 := by
  unfold tailWord_3651103
  simp only [CollatzResearch.WordTrace]
  refine ⟨133166666491684864593461963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88777777661123243062307975 133166666491684864593461963)
  ·
    refine ⟨199749999737527296890192945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133166666491684864593461963 199749999737527296890192945)
    ·
      refine ⟨149812499803145472667644709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 199749999737527296890192945 149812499803145472667644709)
      ·
        refine ⟨28089843713089776125183383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 149812499803145472667644709 28089843713089776125183383)
        ·
          refine ⟨42134765569634664187775075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28089843713089776125183383 42134765569634664187775075)
          ·
            refine ⟨63202148354451996281662613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42134765569634664187775075 63202148354451996281662613)
            ·
              refine ⟨2962600704114937325702935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 63202148354451996281662613 2962600704114937325702935)
              ·
                refine ⟨4443901056172405988554403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2962600704114937325702935 4443901056172405988554403)
                ·
                  refine ⟨6665851584258608982831605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4443901056172405988554403 6665851584258608982831605)
                  ·
                    refine ⟨624923586024244592140463, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6665851584258608982831605 624923586024244592140463)
                    ·
                      rfl

theorem cell23_3651103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 6, 1, 1, 5].length) (baseStart_3651103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3651103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3651103 prefixEnd_3651103 := by exact prefixLift 3651103
  have htrace : WordTrace (prefixWord ++ tailWord_3651103) baseStart_3651103 baseEnd_3651103 := by
    simpa [prefixWord, tailWord_3651103, baseEnd_3651103] using wordTrace_append hprefix tailTrace_3651103
  have hstable : (prefixWord ++ tailWord_3651103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3651103).length < 2 ^ (prefixWord ++ tailWord_3651103).sum := by decide
  have hdescent : baseEnd_3651103 < baseStart_3651103 := by decide
  rcases family_descends (prefixWord ++ tailWord_3651103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3651119 : List Nat := [1, 1, 2, 1, 2, 1, 1, 1, 1, 8, 4]
def baseStart_3651119 : Nat := 118140960795 + 3651119 * 2 ^ 59
def prefixEnd_3651119 : Nat := 4983230072969 + 3 ^ 40 * 3651119 * 2
def baseEnd_3651119 : Nat := 1874778973763205713821315

theorem tailTrace_3651119 : CollatzResearch.WordTrace tailWord_3651119 prefixEnd_3651119 1874778973763205713821315 := by
  unfold tailWord_3651119
  simp only [CollatzResearch.WordTrace]
  refine ⟨133167250059626899326044411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88778166706417932884029607 133167250059626899326044411)
  ·
    refine ⟨199750875089440348989066617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133167250059626899326044411 199750875089440348989066617)
    ·
      refine ⟨149813156317080261741799963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 199750875089440348989066617 149813156317080261741799963)
      ·
        refine ⟨224719734475620392612699945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149813156317080261741799963 224719734475620392612699945)
        ·
          refine ⟨168539800856715294459524959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 224719734475620392612699945 168539800856715294459524959)
          ·
            refine ⟨252809701285072941689287439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 168539800856715294459524959 252809701285072941689287439)
            ·
              refine ⟨379214551927609412533931159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 252809701285072941689287439 379214551927609412533931159)
              ·
                refine ⟨568821827891414118800896739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 379214551927609412533931159 568821827891414118800896739)
                ·
                  refine ⟨853232741837121178201345109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 568821827891414118800896739 853232741837121178201345109)
                  ·
                    refine ⟨9998821193403763807047013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 853232741837121178201345109 9998821193403763807047013)
                    ·
                      refine ⟨1874778973763205713821315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9998821193403763807047013 1874778973763205713821315)
                      ·
                        rfl

theorem cell23_3651119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 1, 1, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 1, 1, 8, 4].length) (baseStart_3651119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3651119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3651119 prefixEnd_3651119 := by exact prefixLift 3651119
  have htrace : WordTrace (prefixWord ++ tailWord_3651119) baseStart_3651119 baseEnd_3651119 := by
    simpa [prefixWord, tailWord_3651119, baseEnd_3651119] using wordTrace_append hprefix tailTrace_3651119
  have hstable : (prefixWord ++ tailWord_3651119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3651119).length < 2 ^ (prefixWord ++ tailWord_3651119).sum := by decide
  have hdescent : baseEnd_3651119 < baseStart_3651119 := by decide
  rcases family_descends (prefixWord ++ tailWord_3651119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3651179 : List Nat := [1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 10]
def baseStart_3651179 : Nat := 118140960795 + 3651179 * 2 ^ 59
def prefixEnd_3651179 : Nat := 4983230072969 + 3 ^ 40 * 3651179 * 2
def baseEnd_3651179 : Nat := 1874809782602475479071039

theorem tailTrace_3651179 : CollatzResearch.WordTrace tailWord_3651179 prefixEnd_3651179 1874809782602475479071039 := by
  unfold tailWord_3651179
  simp only [CollatzResearch.WordTrace]
  refine ⟨133169438439409529573228591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88779625626273019715485727 133169438439409529573228591)
  ·
    refine ⟨199754157659114294359842887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133169438439409529573228591 199754157659114294359842887)
    ·
      refine ⟨299631236488671441539764331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 199754157659114294359842887 299631236488671441539764331)
      ·
        refine ⟨449446854733007162309646497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 299631236488671441539764331 449446854733007162309646497)
        ·
          refine ⟨337085141049755371732234873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 449446854733007162309646497 337085141049755371732234873)
          ·
            refine ⟨252813855787316528799176155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 337085141049755371732234873 252813855787316528799176155)
            ·
              refine ⟨379220783680974793198764233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 252813855787316528799176155 379220783680974793198764233)
              ·
                refine ⟨284415587760731094899073175, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 379220783680974793198764233 284415587760731094899073175)
                ·
                  refine ⟨426623381641096642348609763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 284415587760731094899073175 426623381641096642348609763)
                  ·
                    refine ⟨639935072461644963522914645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 426623381641096642348609763 639935072461644963522914645)
                    ·
                      refine ⟨1874809782602475479071039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 10 639935072461644963522914645 1874809782602475479071039)
                      ·
                        rfl

theorem cell23_3651179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 10].length) (baseStart_3651179 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3651179 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3651179 prefixEnd_3651179 := by exact prefixLift 3651179
  have htrace : WordTrace (prefixWord ++ tailWord_3651179) baseStart_3651179 baseEnd_3651179 := by
    simpa [prefixWord, tailWord_3651179, baseEnd_3651179] using wordTrace_append hprefix tailTrace_3651179
  have hstable : (prefixWord ++ tailWord_3651179).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3651179).length < 2 ^ (prefixWord ++ tailWord_3651179).sum := by decide
  have hdescent : baseEnd_3651179 < baseStart_3651179 := by decide
  rcases family_descends (prefixWord ++ tailWord_3651179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3651183 : List Nat := [1, 1, 2, 1, 3, 2, 1, 4, 3, 3, 2]
def baseStart_3651183 : Nat := 118140960795 + 3651183 * 2 ^ 59
def prefixEnd_3651183 : Nat := 4983230072969 + 3 ^ 40 * 3651183 * 2
def baseEnd_3651183 : Nat := 1874811836525093463421021

theorem tailTrace_3651183 : CollatzResearch.WordTrace tailWord_3651183 prefixEnd_3651183 1874811836525093463421021 := by
  unfold tailWord_3651183
  simp only [CollatzResearch.WordTrace]
  refine ⟨133169584331395038256374203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88779722887596692170916135 133169584331395038256374203)
  ·
    refine ⟨199754376497092557384561305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133169584331395038256374203 199754376497092557384561305)
    ·
      refine ⟨149815782372819418038420979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 199754376497092557384561305 149815782372819418038420979)
      ·
        refine ⟨224723673559229127057631469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149815782372819418038420979 224723673559229127057631469)
        ·
          refine ⟨84271377584710922646611801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 224723673559229127057631469 84271377584710922646611801)
          ·
            refine ⟨63203533188533191984958851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84271377584710922646611801 63203533188533191984958851)
            ·
              refine ⟨94805299782799787977438277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63203533188533191984958851 94805299782799787977438277)
              ·
                refine ⟨17775993709274960245769677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 94805299782799787977438277 17775993709274960245769677)
                ·
                  refine ⟨6665997640978110092163629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17775993709274960245769677 6665997640978110092163629)
                  ·
                    refine ⟨2499749115366791284561361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6665997640978110092163629 2499749115366791284561361)
                    ·
                      refine ⟨1874811836525093463421021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2499749115366791284561361 1874811836525093463421021)
                      ·
                        rfl

theorem cell23_3651183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 4, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 4, 3, 3, 2].length) (baseStart_3651183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3651183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3651183 prefixEnd_3651183 := by exact prefixLift 3651183
  have htrace : WordTrace (prefixWord ++ tailWord_3651183) baseStart_3651183 baseEnd_3651183 := by
    simpa [prefixWord, tailWord_3651183, baseEnd_3651183] using wordTrace_append hprefix tailTrace_3651183
  have hstable : (prefixWord ++ tailWord_3651183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3651183).length < 2 ^ (prefixWord ++ tailWord_3651183).sum := by decide
  have hdescent : baseEnd_3651183 < baseStart_3651183 := by decide
  rcases family_descends (prefixWord ++ tailWord_3651183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3651216 : List Nat := [2, 1, 1, 1, 1, 1, 3, 2, 4, 4, 3]
def baseStart_3651216 : Nat := 118140960795 + 3651216 * 2 ^ 59
def prefixEnd_3651216 : Nat := 4983230072969 + 3 ^ 40 * 3651216 * 2
def baseEnd_3651216 : Nat := 1874828781386691834308369

theorem tailTrace_3651216 : CollatzResearch.WordTrace tailWord_3651216 prefixEnd_3651216 1874828781386691834308369 := by
  unfold tailWord_3651216
  simp only [CollatzResearch.WordTrace]
  refine ⟨66585393970137742446162751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88780525293516989928217001 66585393970137742446162751)
  ·
    refine ⟨99878090955206613669244127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66585393970137742446162751 99878090955206613669244127)
    ·
      refine ⟨149817136432809920503866191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99878090955206613669244127 149817136432809920503866191)
      ·
        refine ⟨224725704649214880755799287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149817136432809920503866191 224725704649214880755799287)
        ·
          refine ⟨337088556973822321133698931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 224725704649214880755799287 337088556973822321133698931)
          ·
            refine ⟨505632835460733481700548397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 337088556973822321133698931 505632835460733481700548397)
            ·
              refine ⟨189612313297775055637705649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 505632835460733481700548397 189612313297775055637705649)
              ·
                refine ⟨142209234973331291728279237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 189612313297775055637705649 142209234973331291728279237)
                ·
                  refine ⟨26664231557499617199052357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 142209234973331291728279237 26664231557499617199052357)
                  ·
                    refine ⟨4999543417031178224822317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26664231557499617199052357 4999543417031178224822317)
                    ·
                      refine ⟨1874828781386691834308369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4999543417031178224822317 1874828781386691834308369)
                      ·
                        rfl

theorem cell23_3651216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 2, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 2, 4, 4, 3].length) (baseStart_3651216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3651216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3651216 prefixEnd_3651216 := by exact prefixLift 3651216
  have htrace : WordTrace (prefixWord ++ tailWord_3651216) baseStart_3651216 baseEnd_3651216 := by
    simpa [prefixWord, tailWord_3651216, baseEnd_3651216] using wordTrace_append hprefix tailTrace_3651216
  have hstable : (prefixWord ++ tailWord_3651216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3651216).length < 2 ^ (prefixWord ++ tailWord_3651216).sum := by decide
  have hdescent : baseEnd_3651216 < baseStart_3651216 := by decide
  rcases family_descends (prefixWord ++ tailWord_3651216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3651233 : List Nat := [1, 2, 3, 3, 2, 1, 1, 1, 2, 4, 3]
def baseStart_3651233 : Nat := 118140960795 + 3651233 * 2 ^ 59
def prefixEnd_3651233 : Nat := 4983230072969 + 3 ^ 40 * 3651233 * 2
def baseEnd_3651233 : Nat := 1874837510557818267795791

theorem tailTrace_3651233 : CollatzResearch.WordTrace tailWord_3651233 prefixEnd_3651233 1874837510557818267795791 := by
  unfold tailWord_3651233
  simp only [CollatzResearch.WordTrace]
  refine ⟨133171407981213896795694353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88780938654142597863796235 133171407981213896795694353)
  ·
    refine ⟨99878555985910422596770765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133171407981213896795694353 99878555985910422596770765)
    ·
      refine ⟨37454458494716408473789037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 99878555985910422596770765 37454458494716408473789037)
      ·
        refine ⟨14045421935518653177670889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37454458494716408473789037 14045421935518653177670889)
        ·
          refine ⟨10534066451638989883253167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14045421935518653177670889 10534066451638989883253167)
          ·
            refine ⟨15801099677458484824879751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10534066451638989883253167 15801099677458484824879751)
            ·
              refine ⟨23701649516187727237319627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15801099677458484824879751 23701649516187727237319627)
              ·
                refine ⟨35552474274281590855979441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23701649516187727237319627 35552474274281590855979441)
                ·
                  refine ⟨26664355705711193141984581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35552474274281590855979441 26664355705711193141984581)
                  ·
                    refine ⟨4999566694820848714122109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26664355705711193141984581 4999566694820848714122109)
                    ·
                      refine ⟨1874837510557818267795791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4999566694820848714122109 1874837510557818267795791)
                      ·
                        rfl

theorem cell23_3651233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 1, 1, 2, 4, 3].length) (baseStart_3651233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3651233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3651233 prefixEnd_3651233 := by exact prefixLift 3651233
  have htrace : WordTrace (prefixWord ++ tailWord_3651233) baseStart_3651233 baseEnd_3651233 := by
    simpa [prefixWord, tailWord_3651233, baseEnd_3651233] using wordTrace_append hprefix tailTrace_3651233
  have hstable : (prefixWord ++ tailWord_3651233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3651233).length < 2 ^ (prefixWord ++ tailWord_3651233).sum := by decide
  have hdescent : baseEnd_3651233 < baseStart_3651233 := by decide
  rcases family_descends (prefixWord ++ tailWord_3651233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3651374 : List Nat := [4, 1, 3, 2, 2, 1, 2, 1, 2, 2, 3]
def baseStart_3651374 : Nat := 118140960795 + 3651374 * 2 ^ 59
def prefixEnd_3651374 : Nat := 4983230072969 + 3 ^ 40 * 3651374 * 2
def baseEnd_3651374 : Nat := 1874909911330102216132643

theorem tailTrace_3651374 : CollatzResearch.WordTrace tailWord_3651374 prefixEnd_3651374 1874909911330102216132643 := by
  unfold tailWord_3651374
  simp only [CollatzResearch.WordTrace]
  refine ⟨16647068834212884734572147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 88784367115802051917718117 16647068834212884734572147)
  ·
    refine ⟨24970603251319327101858221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16647068834212884734572147 24970603251319327101858221)
    ·
      refine ⟨9363976219244747663196833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24970603251319327101858221 9363976219244747663196833)
      ·
        refine ⟨7022982164433560747397625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9363976219244747663196833 7022982164433560747397625)
        ·
          refine ⟨5267236623325170560548219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7022982164433560747397625 5267236623325170560548219)
          ·
            refine ⟨7900854934987755840822329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5267236623325170560548219 7900854934987755840822329)
            ·
              refine ⟨5925641201240816880616747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7900854934987755840822329 5925641201240816880616747)
              ·
                refine ⟨8888461801861225320925121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5925641201240816880616747 8888461801861225320925121)
                ·
                  refine ⟨6666346351395918990693841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8888461801861225320925121 6666346351395918990693841)
                  ·
                    refine ⟨4999759763546939243020381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6666346351395918990693841 4999759763546939243020381)
                    ·
                      refine ⟨1874909911330102216132643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4999759763546939243020381 1874909911330102216132643)
                      ·
                        rfl

theorem cell23_3651374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 1, 2, 1, 2, 2, 3].length) (baseStart_3651374 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3651374 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3651374 prefixEnd_3651374 := by exact prefixLift 3651374
  have htrace : WordTrace (prefixWord ++ tailWord_3651374) baseStart_3651374 baseEnd_3651374 := by
    simpa [prefixWord, tailWord_3651374, baseEnd_3651374] using wordTrace_append hprefix tailTrace_3651374
  have hstable : (prefixWord ++ tailWord_3651374).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3651374).length < 2 ^ (prefixWord ++ tailWord_3651374).sum := by decide
  have hdescent : baseEnd_3651374 < baseStart_3651374 := by decide
  rcases family_descends (prefixWord ++ tailWord_3651374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3651398 : List Nat := [6, 1, 1, 2, 1, 1, 4, 2, 1, 4]
def baseStart_3651398 : Nat := 118140960795 + 3651398 * 2 ^ 59
def prefixEnd_3651398 : Nat := 4983230072969 + 3 ^ 40 * 3651398 * 2
def baseEnd_3651398 : Nat := 624974078288603374077511

theorem tailTrace_3651398 : CollatzResearch.WordTrace tailWord_3651398 prefixEnd_3651398 624974078288603374077511 := by
  unfold tailWord_3651398
  simp only [CollatzResearch.WordTrace]
  refine ⟨4161794563300504061732839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 88784950683744086650300565 4161794563300504061732839)
  ·
    refine ⟨6242691844950756092599259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4161794563300504061732839 6242691844950756092599259)
    ·
      refine ⟨9364037767426134138898889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6242691844950756092599259 9364037767426134138898889)
      ·
        refine ⟨7023028325569600604174167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9364037767426134138898889 7023028325569600604174167)
        ·
          refine ⟨10534542488354400906261251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7023028325569600604174167 10534542488354400906261251)
          ·
            refine ⟨15801813732531601359391877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10534542488354400906261251 15801813732531601359391877)
            ·
              refine ⟨2962840074849675254885977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15801813732531601359391877 2962840074849675254885977)
              ·
                refine ⟨2222130056137256441164483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2962840074849675254885977 2222130056137256441164483)
                ·
                  refine ⟨3333195084205884661746725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2222130056137256441164483 3333195084205884661746725)
                  ·
                    refine ⟨624974078288603374077511, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3333195084205884661746725 624974078288603374077511)
                    ·
                      rfl

theorem cell23_3651398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 4, 2, 1, 4].length) (baseStart_3651398 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3651398 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3651398 prefixEnd_3651398 := by exact prefixLift 3651398
  have htrace : WordTrace (prefixWord ++ tailWord_3651398) baseStart_3651398 baseEnd_3651398 := by
    simpa [prefixWord, tailWord_3651398, baseEnd_3651398] using wordTrace_append hprefix tailTrace_3651398
  have hstable : (prefixWord ++ tailWord_3651398).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3651398).length < 2 ^ (prefixWord ++ tailWord_3651398).sum := by decide
  have hdescent : baseEnd_3651398 < baseStart_3651398 := by decide
  rcases family_descends (prefixWord ++ tailWord_3651398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3651410 : List Nat := [3, 2, 2, 1, 1, 3, 1, 2, 3, 1, 4]
def baseStart_3651410 : Nat := 118140960795 + 3651410 * 2 ^ 59
def prefixEnd_3651410 : Nat := 4983230072969 + 3 ^ 40 * 3651410 * 2
def baseEnd_3651410 : Nat := 1874928396633664075282477

theorem tailTrace_3651410 : CollatzResearch.WordTrace tailWord_3651410 prefixEnd_3651410 1874928396633664075282477 := by
  unfold tailWord_3651410
  simp only [CollatzResearch.WordTrace]
  refine ⟨33294465925393164006221921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88785242467715104016591789 33294465925393164006221921)
  ·
    refine ⟨24970849444044873004666441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33294465925393164006221921 24970849444044873004666441)
    ·
      refine ⟨18728137083033654753499831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24970849444044873004666441 18728137083033654753499831)
      ·
        refine ⟨28092205624550482130249747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18728137083033654753499831 28092205624550482130249747)
        ·
          refine ⟨42138308436825723195374621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28092205624550482130249747 42138308436825723195374621)
          ·
            refine ⟨15801865663809646198265483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42138308436825723195374621 15801865663809646198265483)
            ·
              refine ⟨23702798495714469297398225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15801865663809646198265483 23702798495714469297398225)
              ·
                refine ⟨17777098871785851973048669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23702798495714469297398225 17777098871785851973048669)
                ·
                  refine ⟨6666412076919694489893251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17777098871785851973048669 6666412076919694489893251)
                  ·
                    refine ⟨9999618115379541734839877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6666412076919694489893251 9999618115379541734839877)
                    ·
                      refine ⟨1874928396633664075282477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9999618115379541734839877 1874928396633664075282477)
                      ·
                        rfl

theorem cell23_3651410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 1, 2, 3, 1, 4].length) (baseStart_3651410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3651410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3651410 prefixEnd_3651410 := by exact prefixLift 3651410
  have htrace : WordTrace (prefixWord ++ tailWord_3651410) baseStart_3651410 baseEnd_3651410 := by
    simpa [prefixWord, tailWord_3651410, baseEnd_3651410] using wordTrace_append hprefix tailTrace_3651410
  have hstable : (prefixWord ++ tailWord_3651410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3651410).length < 2 ^ (prefixWord ++ tailWord_3651410).sum := by decide
  have hdescent : baseEnd_3651410 < baseStart_3651410 := by decide
  rcases family_descends (prefixWord ++ tailWord_3651410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3651453 : List Nat := [1, 4, 1, 1, 2, 1, 1, 2, 2, 2, 6]
def baseStart_3651453 : Nat := 118140960795 + 3651453 * 2 ^ 59
def prefixEnd_3651453 : Nat := 4983230072969 + 3 ^ 40 * 3651453 * 2
def baseEnd_3651453 : Nat := 1874950476301807407044779

theorem tailTrace_3651453 : CollatzResearch.WordTrace tailWord_3651453 prefixEnd_3651453 1874950476301807407044779 := by
  unfold tailWord_3651453
  simp only [CollatzResearch.WordTrace]
  refine ⟨133179432040416874368703013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88786288026944582912468675 133179432040416874368703013)
  ·
    refine ⟨24971143507578163944131815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 133179432040416874368703013 24971143507578163944131815)
    ·
      refine ⟨37456715261367245916197723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24971143507578163944131815 37456715261367245916197723)
      ·
        refine ⟨56185072892050868874296585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37456715261367245916197723 56185072892050868874296585)
        ·
          refine ⟨42138804669038151655722439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56185072892050868874296585 42138804669038151655722439)
          ·
            refine ⟨63208207003557227483583659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42138804669038151655722439 63208207003557227483583659)
            ·
              refine ⟨94812310505335841225375489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63208207003557227483583659 94812310505335841225375489)
              ·
                refine ⟨71109232879001880919031617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 94812310505335841225375489 71109232879001880919031617)
                ·
                  refine ⟨53331924659251410689273713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 71109232879001880919031617 53331924659251410689273713)
                  ·
                    refine ⟨39998943494438558016955285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 53331924659251410689273713 39998943494438558016955285)
                    ·
                      refine ⟨1874950476301807407044779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 39998943494438558016955285 1874950476301807407044779)
                      ·
                        rfl

theorem cell23_3651453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 2, 2, 2, 6].length) (baseStart_3651453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3651453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3651453 prefixEnd_3651453 := by exact prefixLift 3651453
  have htrace : WordTrace (prefixWord ++ tailWord_3651453) baseStart_3651453 baseEnd_3651453 := by
    simpa [prefixWord, tailWord_3651453, baseEnd_3651453] using wordTrace_append hprefix tailTrace_3651453
  have hstable : (prefixWord ++ tailWord_3651453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3651453).length < 2 ^ (prefixWord ++ tailWord_3651453).sum := by decide
  have hdescent : baseEnd_3651453 < baseStart_3651453 := by decide
  rcases family_descends (prefixWord ++ tailWord_3651453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3651454 : List Nat := [4, 2, 3, 1, 1, 2, 1, 1, 4, 4]
def baseStart_3651454 : Nat := 118140960795 + 3651454 * 2 ^ 59
def prefixEnd_3651454 : Nat := 4983230072969 + 3 ^ 40 * 3651454 * 2
def baseEnd_3651454 : Nat := 624983663260820634377425

theorem tailTrace_3651454 : CollatzResearch.WordTrace tailWord_3651454 prefixEnd_3651454 624983663260820634377425 := by
  unfold tailWord_3651454
  simp only [CollatzResearch.WordTrace]
  refine ⟨16647433564176656442436177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 88786312342275501026326277 16647433564176656442436177)
  ·
    refine ⟨12485575173132492331827133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16647433564176656442436177 12485575173132492331827133)
    ·
      refine ⟨4682090689924684624435175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12485575173132492331827133 4682090689924684624435175)
      ·
        refine ⟨7023136034887026936652763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4682090689924684624435175 7023136034887026936652763)
        ·
          refine ⟨10534704052330540404979145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7023136034887026936652763 10534704052330540404979145)
          ·
            refine ⟨7901028039247905303734359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10534704052330540404979145 7901028039247905303734359)
            ·
              refine ⟨11851542058871857955601539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7901028039247905303734359 11851542058871857955601539)
              ·
                refine ⟨17777313088307786933402309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11851542058871857955601539 17777313088307786933402309)
                ·
                  refine ⟨3333246204057710050012933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17777313088307786933402309 3333246204057710050012933)
                  ·
                    refine ⟨624983663260820634377425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3333246204057710050012933 624983663260820634377425)
                    ·
                      rfl

theorem cell23_3651454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 2, 1, 1, 4, 4].length) (baseStart_3651454 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3651454 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3651454 prefixEnd_3651454 := by exact prefixLift 3651454
  have htrace : WordTrace (prefixWord ++ tailWord_3651454) baseStart_3651454 baseEnd_3651454 := by
    simpa [prefixWord, tailWord_3651454, baseEnd_3651454] using wordTrace_append hprefix tailTrace_3651454
  have hstable : (prefixWord ++ tailWord_3651454).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3651454).length < 2 ^ (prefixWord ++ tailWord_3651454).sum := by decide
  have hdescent : baseEnd_3651454 < baseStart_3651454 := by decide
  rcases family_descends (prefixWord ++ tailWord_3651454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3651460 : List Nat := [2, 3, 2, 1, 1, 1, 2, 2, 3, 3, 3]
def baseStart_3651460 : Nat := 118140960795 + 3651460 * 2 ^ 59
def prefixEnd_3651460 : Nat := 4983230072969 + 3 ^ 40 * 3651460 * 2
def baseEnd_3651460 : Nat := 1874954070666388879657247

theorem tailTrace_3651460 : CollatzResearch.WordTrace tailWord_3651460 prefixEnd_3651460 1874954070666388879657247 := by
  unfold tailWord_3651460
  simp only [CollatzResearch.WordTrace]
  refine ⟨66589843675695757282103917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88786458234261009709471889 66589843675695757282103917)
  ·
    refine ⟨24971191378385908980788969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66589843675695757282103917 24971191378385908980788969)
    ·
      refine ⟨18728393533789431735591727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24971191378385908980788969 18728393533789431735591727)
      ·
        refine ⟨28092590300684147603387591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18728393533789431735591727 28092590300684147603387591)
        ·
          refine ⟨42138885451026221405081387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28092590300684147603387591 42138885451026221405081387)
          ·
            refine ⟨63208328176539332107622081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42138885451026221405081387 63208328176539332107622081)
            ·
              refine ⟨47406246132404499080716561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63208328176539332107622081 47406246132404499080716561)
              ·
                refine ⟨35554684599303374310537421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47406246132404499080716561 35554684599303374310537421)
                ·
                  refine ⟨13333006724738765366451533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35554684599303374310537421 13333006724738765366451533)
                  ·
                    refine ⟨4999877521777037012419325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13333006724738765366451533 4999877521777037012419325)
                    ·
                      refine ⟨1874954070666388879657247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4999877521777037012419325 1874954070666388879657247)
                      ·
                        rfl

theorem cell23_3651460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 2, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 2, 2, 3, 3, 3].length) (baseStart_3651460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3651460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3651460 prefixEnd_3651460 := by exact prefixLift 3651460
  have htrace : WordTrace (prefixWord ++ tailWord_3651460) baseStart_3651460 baseEnd_3651460 := by
    simpa [prefixWord, tailWord_3651460, baseEnd_3651460] using wordTrace_append hprefix tailTrace_3651460
  have hstable : (prefixWord ++ tailWord_3651460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3651460).length < 2 ^ (prefixWord ++ tailWord_3651460).sum := by decide
  have hdescent : baseEnd_3651460 < baseStart_3651460 := by decide
  rcases family_descends (prefixWord ++ tailWord_3651460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3651474 : List Nat := [3, 2, 3, 2, 1, 3, 1, 1, 1, 2, 4]
def baseStart_3651474 : Nat := 118140960795 + 3651474 * 2 ^ 59
def prefixEnd_3651474 : Nat := 4983230072969 + 3 ^ 40 * 3651474 * 2
def baseEnd_3651474 : Nat := 1874961259395551824882183

theorem tailTrace_3651474 : CollatzResearch.WordTrace tailWord_3651474 prefixEnd_3651474 1874961259395551824882183 := by
  unfold tailWord_3651474
  simp only [CollatzResearch.WordTrace]
  refine ⟨33295049493335198738804369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88786798648893863303478317 33295049493335198738804369)
  ·
    refine ⟨24971287120001399054103277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33295049493335198738804369 24971287120001399054103277)
    ·
      refine ⟨9364232670000524645288729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24971287120001399054103277 9364232670000524645288729)
      ·
        refine ⟨7023174502500393483966547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9364232670000524645288729 7023174502500393483966547)
        ·
          refine ⟨10534761753750590225949821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7023174502500393483966547 10534761753750590225949821)
          ·
            refine ⟨3950535657656471334731183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10534761753750590225949821 3950535657656471334731183)
            ·
              refine ⟨5925803486484707002096775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3950535657656471334731183 5925803486484707002096775)
              ·
                refine ⟨8888705229727060503145163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5925803486484707002096775 8888705229727060503145163)
                ·
                  refine ⟨13333057844590590754717745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8888705229727060503145163 13333057844590590754717745)
                  ·
                    refine ⟨9999793383442943066038309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13333057844590590754717745 9999793383442943066038309)
                    ·
                      refine ⟨1874961259395551824882183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9999793383442943066038309 1874961259395551824882183)
                      ·
                        rfl

theorem cell23_3651474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 3, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 3, 1, 1, 1, 2, 4].length) (baseStart_3651474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3651474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3651474 prefixEnd_3651474 := by exact prefixLift 3651474
  have htrace : WordTrace (prefixWord ++ tailWord_3651474) baseStart_3651474 baseEnd_3651474 := by
    simpa [prefixWord, tailWord_3651474, baseEnd_3651474] using wordTrace_append hprefix tailTrace_3651474
  have hstable : (prefixWord ++ tailWord_3651474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3651474).length < 2 ^ (prefixWord ++ tailWord_3651474).sum := by decide
  have hdescent : baseEnd_3651474 < baseStart_3651474 := by decide
  rcases family_descends (prefixWord ++ tailWord_3651474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3651478 : List Nat := [5, 3, 1, 1, 2, 1, 2, 2, 1, 1, 4]
def baseStart_3651478 : Nat := 118140960795 + 3651478 * 2 ^ 59
def prefixEnd_3651478 : Nat := 4983230072969 + 3 ^ 40 * 3651478 * 2
def baseEnd_3651478 : Nat := 1874963313318169809232165

theorem tailTrace_3651478 : CollatzResearch.WordTrace tailWord_3651478 prefixEnd_3651478 1874963313318169809232165 := by
  unfold tailWord_3651478
  simp only [CollatzResearch.WordTrace]
  refine ⟨8323771491582893977397693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 88786895910217535758908725 8323771491582893977397693)
  ·
    refine ⟨3121414309343585241524135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8323771491582893977397693 3121414309343585241524135)
    ·
      refine ⟨4682121464015377862286203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3121414309343585241524135 4682121464015377862286203)
      ·
        refine ⟨7023182196023066793429305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4682121464015377862286203 7023182196023066793429305)
        ·
          refine ⟨5267386647017300095071979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7023182196023066793429305 5267386647017300095071979)
          ·
            refine ⟨7901079970525950142607969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5267386647017300095071979 7901079970525950142607969)
            ·
              refine ⟨5925809977894462606955977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7901079970525950142607969 5925809977894462606955977)
              ·
                refine ⟨4444357483420846955216983, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5925809977894462606955977 4444357483420846955216983)
                ·
                  refine ⟨6666536225131270432825475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4444357483420846955216983 6666536225131270432825475)
                  ·
                    refine ⟨9999804337696905649238213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6666536225131270432825475 9999804337696905649238213)
                    ·
                      refine ⟨1874963313318169809232165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9999804337696905649238213 1874963313318169809232165)
                      ·
                        rfl

theorem cell23_3651478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 1, 2, 2, 1, 1, 4].length) (baseStart_3651478 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3651478 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3651478 prefixEnd_3651478 := by exact prefixLift 3651478
  have htrace : WordTrace (prefixWord ++ tailWord_3651478) baseStart_3651478 baseEnd_3651478 := by
    simpa [prefixWord, tailWord_3651478, baseEnd_3651478] using wordTrace_append hprefix tailTrace_3651478
  have hstable : (prefixWord ++ tailWord_3651478).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3651478).length < 2 ^ (prefixWord ++ tailWord_3651478).sum := by decide
  have hdescent : baseEnd_3651478 < baseStart_3651478 := by decide
  rcases family_descends (prefixWord ++ tailWord_3651478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3651493 : List Nat := [1, 3, 1, 2, 1, 1, 1, 4, 1, 8]
def baseStart_3651493 : Nat := 118140960795 + 3651493 * 2 ^ 59
def prefixEnd_3651493 : Nat := 4983230072969 + 3 ^ 40 * 3651493 * 2
def baseEnd_3651493 : Nat := 624990338509329083514865

theorem tailTrace_3651493 : CollatzResearch.WordTrace tailWord_3651493 prefixEnd_3651493 624990338509329083514865 := by
  unfold tailWord_3651493
  simp only [CollatzResearch.WordTrace]
  refine ⟨133180890960271961200159133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88787260640181307466772755 133180890960271961200159133)
  ·
    refine ⟨49942834110101985450059675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 133180890960271961200159133 49942834110101985450059675)
    ·
      refine ⟨74914251165152978175089513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49942834110101985450059675 74914251165152978175089513)
      ·
        refine ⟨56185688373864733631317135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74914251165152978175089513 56185688373864733631317135)
        ·
          refine ⟨84278532560797100446975703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56185688373864733631317135 84278532560797100446975703)
          ·
            refine ⟨126417798841195650670463555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84278532560797100446975703 126417798841195650670463555)
            ·
              refine ⟨189626698261793476005695333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 126417798841195650670463555 189626698261793476005695333)
              ·
                refine ⟨35555005924086276751067875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 189626698261793476005695333 35555005924086276751067875)
                ·
                  refine ⟨53332508886129415126601813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35555005924086276751067875 53332508886129415126601813)
                  ·
                    refine ⟨624990338509329083514865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 53332508886129415126601813 624990338509329083514865)
                    ·
                      rfl

theorem cell23_3651493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 4, 1, 8].length) (baseStart_3651493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3651493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3651493 prefixEnd_3651493 := by exact prefixLift 3651493
  have htrace : WordTrace (prefixWord ++ tailWord_3651493) baseStart_3651493 baseEnd_3651493 := by
    simpa [prefixWord, tailWord_3651493, baseEnd_3651493] using wordTrace_append hprefix tailTrace_3651493
  have hstable : (prefixWord ++ tailWord_3651493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3651493).length < 2 ^ (prefixWord ++ tailWord_3651493).sum := by decide
  have hdescent : baseEnd_3651493 < baseStart_3651493 := by decide
  rcases family_descends (prefixWord ++ tailWord_3651493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3651520 : List Nat := [2, 1, 1, 2, 3, 2, 2, 1, 2, 4, 3]
def baseStart_3651520 : Nat := 118140960795 + 3651520 * 2 ^ 59
def prefixEnd_3651520 : Nat := 4983230072969 + 3 ^ 40 * 3651520 * 2
def baseEnd_3651520 : Nat := 1874984879505658644906971

theorem tailTrace_3651520 : CollatzResearch.WordTrace tailWord_3651520 prefixEnd_3651520 1874984879505658644906971 := by
  unfold tailWord_3651520
  simp only [CollatzResearch.WordTrace]
  refine ⟨66590937865587072405696007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88787917154116096540928009 66590937865587072405696007)
  ·
    refine ⟨99886406798380608608544011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66590937865587072405696007 99886406798380608608544011)
    ·
      refine ⟨149829610197570912912816017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99886406798380608608544011 149829610197570912912816017)
      ·
        refine ⟨112372207648178184684612013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 149829610197570912912816017 112372207648178184684612013)
        ·
          refine ⟨42139577868066819256729505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 112372207648178184684612013 42139577868066819256729505)
          ·
            refine ⟨31604683401050114442547129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42139577868066819256729505 31604683401050114442547129)
            ·
              refine ⟨23703512550787585831910347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31604683401050114442547129 23703512550787585831910347)
              ·
                refine ⟨35555268826181378747865521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23703512550787585831910347 35555268826181378747865521)
                ·
                  refine ⟨26666451619636034060899141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35555268826181378747865521 26666451619636034060899141)
                  ·
                    refine ⟨4999959678681756386418589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26666451619636034060899141 4999959678681756386418589)
                    ·
                      refine ⟨1874984879505658644906971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4999959678681756386418589 1874984879505658644906971)
                      ·
                        rfl

theorem cell23_3651520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 2, 1, 2, 4, 3].length) (baseStart_3651520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3651520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3651520 prefixEnd_3651520 := by exact prefixLift 3651520
  have htrace : WordTrace (prefixWord ++ tailWord_3651520) baseStart_3651520 baseEnd_3651520 := by
    simpa [prefixWord, tailWord_3651520, baseEnd_3651520] using wordTrace_append hprefix tailTrace_3651520
  have hstable : (prefixWord ++ tailWord_3651520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3651520).length < 2 ^ (prefixWord ++ tailWord_3651520).sum := by decide
  have hdescent : baseEnd_3651520 < baseStart_3651520 := by decide
  rcases family_descends (prefixWord ++ tailWord_3651520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3651530 : List Nat := [3, 1, 2, 1, 2, 1, 2, 3, 2, 2, 4]
def baseStart_3651530 : Nat := 118140960795 + 3651530 * 2 ^ 59
def prefixEnd_3651530 : Nat := 4983230072969 + 3 ^ 40 * 3651530 * 2
def baseEnd_3651530 : Nat := 1874990014312203605781925

theorem tailTrace_3651530 : CollatzResearch.WordTrace tailWord_3651530 prefixEnd_3651530 1874990014312203605781925 := by
  unfold tailWord_3651530
  simp only [CollatzResearch.WordTrace]
  refine ⟨33295560115284479129814011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88788160307425277679504029 33295560115284479129814011)
  ·
    refine ⟨49943340172926718694721017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33295560115284479129814011 49943340172926718694721017)
    ·
      refine ⟨37457505129695039021040763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49943340172926718694721017 37457505129695039021040763)
      ·
        refine ⟨56186257694542558531561145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37457505129695039021040763 56186257694542558531561145)
        ·
          refine ⟨42139693270906918898670859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56186257694542558531561145 42139693270906918898670859)
          ·
            refine ⟨63209539906360378348006289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42139693270906918898670859 63209539906360378348006289)
            ·
              refine ⟨47407154929770283761004717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63209539906360378348006289 47407154929770283761004717)
              ·
                refine ⟨17777683098663856410376769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47407154929770283761004717 17777683098663856410376769)
                ·
                  refine ⟨13333262323997892307782577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17777683098663856410376769 13333262323997892307782577)
                  ·
                    refine ⟨9999946742998419230836933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13333262323997892307782577 9999946742998419230836933)
                    ·
                      refine ⟨1874990014312203605781925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9999946742998419230836933 1874990014312203605781925)
                      ·
                        rfl

theorem cell23_3651530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 2, 3, 2, 2, 4].length) (baseStart_3651530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3651530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3651530 prefixEnd_3651530 := by exact prefixLift 3651530
  have htrace : WordTrace (prefixWord ++ tailWord_3651530) baseStart_3651530 baseEnd_3651530 := by
    simpa [prefixWord, tailWord_3651530, baseEnd_3651530] using wordTrace_append hprefix tailTrace_3651530
  have hstable : (prefixWord ++ tailWord_3651530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3651530).length < 2 ^ (prefixWord ++ tailWord_3651530).sum := by decide
  have hdescent : baseEnd_3651530 < baseStart_3651530 := by decide
  rcases family_descends (prefixWord ++ tailWord_3651530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3651538 : List Nat := [3, 2, 2, 3, 2, 2, 1, 2, 1, 3, 2]
def baseStart_3651538 : Nat := 118140960795 + 3651538 * 2 ^ 59
def prefixEnd_3651538 : Nat := 4983230072969 + 3 ^ 40 * 3651538 * 2
def baseEnd_3651538 : Nat := 1874994122157439574481889

theorem tailTrace_3651538 : CollatzResearch.WordTrace tailWord_3651538 prefixEnd_3651538 1874994122157439574481889 := by
  unfold tailWord_3651538
  simp only [CollatzResearch.WordTrace]
  refine ⟨33295633061277233471386817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88788354830072622590364845 33295633061277233471386817)
  ·
    refine ⟨24971724795957925103540113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33295633061277233471386817 24971724795957925103540113)
    ·
      refine ⟨18728793596968443827655085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24971724795957925103540113 18728793596968443827655085)
      ·
        refine ⟨7023297598863166435370657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18728793596968443827655085 7023297598863166435370657)
        ·
          refine ⟨5267473199147374826527993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7023297598863166435370657 5267473199147374826527993)
          ·
            refine ⟨3950604899360531119895995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5267473199147374826527993 3950604899360531119895995)
            ·
              refine ⟨5925907349040796679843993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3950604899360531119895995 5925907349040796679843993)
              ·
                refine ⟨4444430511780597509882995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5925907349040796679843993 4444430511780597509882995)
                ·
                  refine ⟨6666645767670896264824493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4444430511780597509882995 6666645767670896264824493)
                  ·
                    refine ⟨2499992162876586099309185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6666645767670896264824493 2499992162876586099309185)
                    ·
                      refine ⟨1874994122157439574481889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2499992162876586099309185 1874994122157439574481889)
                      ·
                        rfl

theorem cell23_3651538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 2, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 2, 1, 2, 1, 3, 2].length) (baseStart_3651538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3651538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3651538 prefixEnd_3651538 := by exact prefixLift 3651538
  have htrace : WordTrace (prefixWord ++ tailWord_3651538) baseStart_3651538 baseEnd_3651538 := by
    simpa [prefixWord, tailWord_3651538, baseEnd_3651538] using wordTrace_append hprefix tailTrace_3651538
  have hstable : (prefixWord ++ tailWord_3651538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3651538).length < 2 ^ (prefixWord ++ tailWord_3651538).sum := by decide
  have hdescent : baseEnd_3651538 < baseStart_3651538 := by decide
  rcases family_descends (prefixWord ++ tailWord_3651538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3651540 : List Nat := [2, 4, 1, 2, 1, 1, 2, 1, 9]
def baseStart_3651540 : Nat := 118140960795 + 3651540 * 2 ^ 59
def prefixEnd_3651540 : Nat := 4983230072969 + 3 ^ 40 * 3651540 * 2
def baseEnd_3651540 : Nat := 208332794346527618517431

theorem tailTrace_3651540 : CollatzResearch.WordTrace tailWord_3651540 prefixEnd_3651540 208332794346527618517431 := by
  unfold tailWord_3651540
  simp only [CollatzResearch.WordTrace]
  refine ⟨66591302595550844113560037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88788403460734458818080049 66591302595550844113560037)
  ·
    refine ⟨12485869236665783271292507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 66591302595550844113560037 12485869236665783271292507)
    ·
      refine ⟨18728803854998674906938761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12485869236665783271292507 18728803854998674906938761)
      ·
        refine ⟨14046602891249006180204071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18728803854998674906938761 14046602891249006180204071)
        ·
          refine ⟨21069904336873509270306107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14046602891249006180204071 21069904336873509270306107)
          ·
            refine ⟨31604856505310263905459161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21069904336873509270306107 31604856505310263905459161)
            ·
              refine ⟨23703642378982697929094371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31604856505310263905459161 23703642378982697929094371)
              ·
                refine ⟨35555463568474046893641557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23703642378982697929094371 35555463568474046893641557)
                ·
                  refine ⟨208332794346527618517431, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 35555463568474046893641557 208332794346527618517431)
                  ·
                    rfl

theorem cell23_3651540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 2, 1, 9].length) (baseStart_3651540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3651540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3651540 prefixEnd_3651540 := by exact prefixLift 3651540
  have htrace : WordTrace (prefixWord ++ tailWord_3651540) baseStart_3651540 baseEnd_3651540 := by
    simpa [prefixWord, tailWord_3651540, baseEnd_3651540] using wordTrace_append hprefix tailTrace_3651540
  have hstable : (prefixWord ++ tailWord_3651540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3651540).length < 2 ^ (prefixWord ++ tailWord_3651540).sum := by decide
  have hdescent : baseEnd_3651540 < baseStart_3651540 := by decide
  rcases family_descends (prefixWord ++ tailWord_3651540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3651577 : List Nat := [1, 2, 1, 3, 1, 4, 1, 1, 2, 5, 2]
def baseStart_3651577 : Nat := 118140960795 + 3651577 * 2 ^ 59
def prefixEnd_3651577 : Nat := 4983230072969 + 3 ^ 40 * 3651577 * 2
def baseEnd_3651577 : Nat := 1875014147902964921894209

theorem tailTrace_3651577 : CollatzResearch.WordTrace tailWord_3651577 prefixEnd_3651577 1875014147902964921894209 := by
  unfold tailWord_3651577
  simp only [CollatzResearch.WordTrace]
  refine ⟨133183954691967643546216985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88789303127978429030811323 133183954691967643546216985)
  ·
    refine ⟨99887966018975732659662739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133183954691967643546216985 99887966018975732659662739)
    ·
      refine ⟨149831949028463598989494109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99887966018975732659662739 149831949028463598989494109)
      ·
        refine ⟨56186980885673849621060291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 149831949028463598989494109 56186980885673849621060291)
        ·
          refine ⟨84280471328510774431590437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56186980885673849621060291 84280471328510774431590437)
          ·
            refine ⟨15802588374095770205923207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 84280471328510774431590437 15802588374095770205923207)
            ·
              refine ⟨23703882561143655308884811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15802588374095770205923207 23703882561143655308884811)
              ·
                refine ⟨35555823841715482963327217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23703882561143655308884811 35555823841715482963327217)
                ·
                  refine ⟨26666867881286612222495413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35555823841715482963327217 26666867881286612222495413)
                  ·
                    refine ⟨2500018863870619895858945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 26666867881286612222495413 2500018863870619895858945)
                    ·
                      refine ⟨1875014147902964921894209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2500018863870619895858945 1875014147902964921894209)
                      ·
                        rfl

theorem cell23_3651577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 1, 1, 2, 5, 2].length) (baseStart_3651577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3651577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3651577 prefixEnd_3651577 := by exact prefixLift 3651577
  have htrace : WordTrace (prefixWord ++ tailWord_3651577) baseStart_3651577 baseEnd_3651577 := by
    simpa [prefixWord, tailWord_3651577, baseEnd_3651577] using wordTrace_append hprefix tailTrace_3651577
  have hstable : (prefixWord ++ tailWord_3651577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3651577).length < 2 ^ (prefixWord ++ tailWord_3651577).sum := by decide
  have hdescent : baseEnd_3651577 < baseStart_3651577 := by decide
  rcases family_descends (prefixWord ++ tailWord_3651577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3651580 : List Nat := [2, 2, 2, 1, 2, 2, 1, 3, 1, 2, 5]
def baseStart_3651580 : Nat := 118140960795 + 3651580 * 2 ^ 59
def prefixEnd_3651580 : Nat := 4983230072969 + 3 ^ 40 * 3651580 * 2
def baseEnd_3651580 : Nat := 1875015688344928410156695

theorem tailTrace_3651580 : CollatzResearch.WordTrace tailWord_3651580 prefixEnd_3651580 1875015688344928410156695 := by
  unfold tailWord_3651580
  simp only [CollatzResearch.WordTrace]
  refine ⟨66592032055478387529288097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88789376073971183372384129 66592032055478387529288097)
  ·
    refine ⟨49944024041608790646966073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66592032055478387529288097 49944024041608790646966073)
    ·
      refine ⟨37458018031206592985224555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49944024041608790646966073 37458018031206592985224555)
      ·
        refine ⟨56187027046809889477836833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37458018031206592985224555 56187027046809889477836833)
        ·
          refine ⟨42140270285107417108377625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56187027046809889477836833 42140270285107417108377625)
          ·
            refine ⟨31605202713830562831283219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42140270285107417108377625 31605202713830562831283219)
            ·
              refine ⟨47407804070745844246924829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31605202713830562831283219 47407804070745844246924829)
              ·
                refine ⟨17777926526529691592596811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47407804070745844246924829 17777926526529691592596811)
                ·
                  refine ⟨26666889789794537388895217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17777926526529691592596811 26666889789794537388895217)
                  ·
                    refine ⟨20000167342345903041671413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26666889789794537388895217 20000167342345903041671413)
                    ·
                      refine ⟨1875015688344928410156695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20000167342345903041671413 1875015688344928410156695)
                      ·
                        rfl

theorem cell23_3651580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 1, 3, 1, 2, 5].length) (baseStart_3651580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3651580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3651580 prefixEnd_3651580 := by exact prefixLift 3651580
  have htrace : WordTrace (prefixWord ++ tailWord_3651580) baseStart_3651580 baseEnd_3651580 := by
    simpa [prefixWord, tailWord_3651580, baseEnd_3651580] using wordTrace_append hprefix tailTrace_3651580
  have hstable : (prefixWord ++ tailWord_3651580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3651580).length < 2 ^ (prefixWord ++ tailWord_3651580).sum := by decide
  have hdescent : baseEnd_3651580 < baseStart_3651580 := by decide
  rcases family_descends (prefixWord ++ tailWord_3651580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3651634 : List Nat := [3, 2, 1, 1, 2, 4, 2, 1, 3, 4]
def baseStart_3651634 : Nat := 118140960795 + 3651634 * 2 ^ 59
def prefixEnd_3651634 : Nat := 4983230072969 + 3 ^ 40 * 3651634 * 2
def baseEnd_3651634 : Nat := 625014472100090399627149

theorem tailTrace_3651634 : CollatzResearch.WordTrace tailWord_3651634 prefixEnd_3651634 625014472100090399627149 := by
  unfold tailWord_3651634
  simp only [CollatzResearch.WordTrace]
  refine ⟨33296508413190285570260489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88790689101840761520694637 33296508413190285570260489)
  ·
    refine ⟨24972381309892714177695367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33296508413190285570260489 24972381309892714177695367)
    ·
      refine ⟨37458571964839071266543051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24972381309892714177695367 37458571964839071266543051)
      ·
        refine ⟨56187857947258606899814577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37458571964839071266543051 56187857947258606899814577)
        ·
          refine ⟨42140893460443955174860933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56187857947258606899814577 42140893460443955174860933)
          ·
            refine ⟨7901417523833241595286425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 42140893460443955174860933 7901417523833241595286425)
            ·
              refine ⟨5926063142874931196464819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7901417523833241595286425 5926063142874931196464819)
              ·
                refine ⟨8889094714312396794697229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5926063142874931196464819 8889094714312396794697229)
                ·
                  refine ⟨3333410517867148798011461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8889094714312396794697229 3333410517867148798011461)
                  ·
                    refine ⟨625014472100090399627149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3333410517867148798011461 625014472100090399627149)
                    ·
                      rfl

theorem cell23_3651634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 4, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 4, 2, 1, 3, 4].length) (baseStart_3651634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3651634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3651634 prefixEnd_3651634 := by exact prefixLift 3651634
  have htrace : WordTrace (prefixWord ++ tailWord_3651634) baseStart_3651634 baseEnd_3651634 := by
    simpa [prefixWord, tailWord_3651634, baseEnd_3651634] using wordTrace_append hprefix tailTrace_3651634
  have hstable : (prefixWord ++ tailWord_3651634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3651634).length < 2 ^ (prefixWord ++ tailWord_3651634).sum := by decide
  have hdescent : baseEnd_3651634 < baseStart_3651634 := by decide
  rcases family_descends (prefixWord ++ tailWord_3651634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3651654 : List Nat := [6, 1, 1, 1, 1, 1, 1, 1, 2, 4, 4]
def baseStart_3651654 : Nat := 118140960795 + 3651654 * 2 ^ 59
def prefixEnd_3651654 : Nat := 4983230072969 + 3 ^ 40 * 3651654 * 2
def baseEnd_3651654 : Nat := 1875053685913361120631355

theorem tailTrace_3651654 : CollatzResearch.WordTrace tailWord_3651654 prefixEnd_3651654 1875053685913361120631355 := by
  unfold tailWord_3651654
  simp only [CollatzResearch.WordTrace]
  refine ⟨4162086347271521428024063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 88791175408459123797846677 4162086347271521428024063)
  ·
    refine ⟨6243129520907282142036095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4162086347271521428024063 6243129520907282142036095)
    ·
      refine ⟨9364694281360923213054143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6243129520907282142036095 9364694281360923213054143)
      ·
        refine ⟨14047041422041384819581215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9364694281360923213054143 14047041422041384819581215)
        ·
          refine ⟨21070562133062077229371823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14047041422041384819581215 21070562133062077229371823)
          ·
            refine ⟨31605843199593115844057735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21070562133062077229371823 31605843199593115844057735)
            ·
              refine ⟨47408764799389673766086603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31605843199593115844057735 47408764799389673766086603)
              ·
                refine ⟨71113147199084510649129905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47408764799389673766086603 71113147199084510649129905)
                ·
                  refine ⟨53334860399313382986847429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 71113147199084510649129905 53334860399313382986847429)
                  ·
                    refine ⟨10000286324871259310033893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 53334860399313382986847429 10000286324871259310033893)
                    ·
                      refine ⟨1875053685913361120631355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10000286324871259310033893 1875053685913361120631355)
                      ·
                        rfl

theorem cell23_3651654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 1, 1, 2, 4, 4].length) (baseStart_3651654 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3651654 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3651654 prefixEnd_3651654 := by exact prefixLift 3651654
  have htrace : WordTrace (prefixWord ++ tailWord_3651654) baseStart_3651654 baseEnd_3651654 := by
    simpa [prefixWord, tailWord_3651654, baseEnd_3651654] using wordTrace_append hprefix tailTrace_3651654
  have hstable : (prefixWord ++ tailWord_3651654).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3651654).length < 2 ^ (prefixWord ++ tailWord_3651654).sum := by decide
  have hdescent : baseEnd_3651654 < baseStart_3651654 := by decide
  rcases family_descends (prefixWord ++ tailWord_3651654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3651667 : List Nat := [1, 1, 1, 2, 1, 1, 2, 2, 5, 5, 2]
def baseStart_3651667 : Nat := 118140960795 + 3651667 * 2 ^ 59
def prefixEnd_3651667 : Nat := 4983230072969 + 3 ^ 40 * 3651667 * 2
def baseEnd_3651667 : Nat := 1875060361161869569768795

theorem tailTrace_3651667 : CollatzResearch.WordTrace tailWord_3651667 prefixEnd_3651667 1875060361161869569768795 := by
  unfold tailWord_3651667
  simp only [CollatzResearch.WordTrace]
  refine ⟨133187237261641588916993255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88791491507761059277995503 133187237261641588916993255)
  ·
    refine ⟨199780855892462383375489883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133187237261641588916993255 199780855892462383375489883)
    ·
      refine ⟨299671283838693575063234825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 199780855892462383375489883 299671283838693575063234825)
      ·
        refine ⟨224753462879020181297426119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 299671283838693575063234825 224753462879020181297426119)
        ·
          refine ⟨337130194318530271946139179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 224753462879020181297426119 337130194318530271946139179)
          ·
            refine ⟨505695291477795407919208769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 337130194318530271946139179 505695291477795407919208769)
            ·
              refine ⟨379271468608346555939406577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 505695291477795407919208769 379271468608346555939406577)
              ·
                refine ⟨284453601456259916954554933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 379271468608346555939406577 284453601456259916954554933)
                ·
                  refine ⟨26667525136524367214489525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 284453601456259916954554933 26667525136524367214489525)
                  ·
                    refine ⟨2500080481549159426358393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 26667525136524367214489525 2500080481549159426358393)
                    ·
                      refine ⟨1875060361161869569768795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2500080481549159426358393 1875060361161869569768795)
                      ·
                        rfl

theorem cell23_3651667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 2, 5, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 2, 5, 5, 2].length) (baseStart_3651667 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3651667 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3651667 prefixEnd_3651667 := by exact prefixLift 3651667
  have htrace : WordTrace (prefixWord ++ tailWord_3651667) baseStart_3651667 baseEnd_3651667 := by
    simpa [prefixWord, tailWord_3651667, baseEnd_3651667] using wordTrace_append hprefix tailTrace_3651667
  have hstable : (prefixWord ++ tailWord_3651667).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3651667).length < 2 ^ (prefixWord ++ tailWord_3651667).sum := by decide
  have hdescent : baseEnd_3651667 < baseStart_3651667 := by decide
  rcases family_descends (prefixWord ++ tailWord_3651667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3651684 : List Nat := [2, 3, 1, 1, 2, 1, 3, 1, 4, 3, 2]
def baseStart_3651684 : Nat := 118140960795 + 3651684 * 2 ^ 59
def prefixEnd_3651684 : Nat := 4983230072969 + 3 ^ 40 * 3651684 * 2
def baseEnd_3651684 : Nat := 1875069090332996003256217

theorem tailTrace_3651684 : CollatzResearch.WordTrace tailWord_3651684 prefixEnd_3651684 1875069090332996003256217 := by
  unfold tailWord_3651684
  simp only [CollatzResearch.WordTrace]
  refine ⟨66593928651290000410181053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88791904868386667213574737 66593928651290000410181053)
  ·
    refine ⟨24972723244233750153817895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66593928651290000410181053 24972723244233750153817895)
    ·
      refine ⟨37459084866350625230726843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24972723244233750153817895 37459084866350625230726843)
      ·
        refine ⟨56188627299525937846090265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37459084866350625230726843 56188627299525937846090265)
        ·
          refine ⟨42141470474644453384567699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56188627299525937846090265 42141470474644453384567699)
          ·
            refine ⟨63212205711966680076851549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42141470474644453384567699 63212205711966680076851549)
            ·
              refine ⟨23704577141987505028819331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 63212205711966680076851549 23704577141987505028819331)
              ·
                refine ⟨35556865712981257543228997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23704577141987505028819331 35556865712981257543228997)
                ·
                  refine ⟨6666912321183985789355437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35556865712981257543228997 6666912321183985789355437)
                  ·
                    refine ⟨2500092120443994671008289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6666912321183985789355437 2500092120443994671008289)
                    ·
                      refine ⟨1875069090332996003256217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2500092120443994671008289 1875069090332996003256217)
                      ·
                        rfl

theorem cell23_3651684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 3, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 3, 1, 4, 3, 2].length) (baseStart_3651684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3651684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3651684 prefixEnd_3651684 := by exact prefixLift 3651684
  have htrace : WordTrace (prefixWord ++ tailWord_3651684) baseStart_3651684 baseEnd_3651684 := by
    simpa [prefixWord, tailWord_3651684, baseEnd_3651684] using wordTrace_append hprefix tailTrace_3651684
  have hstable : (prefixWord ++ tailWord_3651684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3651684).length < 2 ^ (prefixWord ++ tailWord_3651684).sum := by decide
  have hdescent : baseEnd_3651684 < baseStart_3651684 := by decide
  rcases family_descends (prefixWord ++ tailWord_3651684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3651697 : List Nat := [1, 2, 2, 2, 1, 1, 4, 2, 3, 1, 4]
def baseStart_3651697 : Nat := 118140960795 + 3651697 * 2 ^ 59
def prefixEnd_3651697 : Nat := 4983230072969 + 3 ^ 40 * 3651697 * 2
def baseEnd_3651697 : Nat := 1875075765581504452393657

theorem tailTrace_3651697 : CollatzResearch.WordTrace tailWord_3651697 prefixEnd_3651697 1875075765581504452393657 := by
  unfold tailWord_3651697
  simp only [CollatzResearch.WordTrace]
  refine ⟨133188331451532904040585345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88792220967688602693723563 133188331451532904040585345)
  ·
    refine ⟨99891248588649678030439009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133188331451532904040585345 99891248588649678030439009)
    ·
      refine ⟨74918436441487258522829257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99891248588649678030439009 74918436441487258522829257)
      ·
        refine ⟨56188827331115443892121943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74918436441487258522829257 56188827331115443892121943)
        ·
          refine ⟨84283240996673165838182915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56188827331115443892121943 84283240996673165838182915)
          ·
            refine ⟨126424861495009748757274373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84283240996673165838182915 126424861495009748757274373)
            ·
              refine ⟨23704661530314327891988945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 126424861495009748757274373 23704661530314327891988945)
              ·
                refine ⟨17778496147735745918991709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23704661530314327891988945 17778496147735745918991709)
                ·
                  refine ⟨6666936055400904719621891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17778496147735745918991709 6666936055400904719621891)
                  ·
                    refine ⟨10000404083101357079432837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6666936055400904719621891 10000404083101357079432837)
                    ·
                      refine ⟨1875075765581504452393657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10000404083101357079432837 1875075765581504452393657)
                      ·
                        rfl

theorem cell23_3651697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 4, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 4, 2, 3, 1, 4].length) (baseStart_3651697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3651697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3651697 prefixEnd_3651697 := by exact prefixLift 3651697
  have htrace : WordTrace (prefixWord ++ tailWord_3651697) baseStart_3651697 baseEnd_3651697 := by
    simpa [prefixWord, tailWord_3651697, baseEnd_3651697] using wordTrace_append hprefix tailTrace_3651697
  have hstable : (prefixWord ++ tailWord_3651697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3651697).length < 2 ^ (prefixWord ++ tailWord_3651697).sum := by decide
  have hdescent : baseEnd_3651697 < baseStart_3651697 := by decide
  rcases family_descends (prefixWord ++ tailWord_3651697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3651741 : List Nat := [1, 4, 2, 1, 1, 4, 2, 2, 2, 4]
def baseStart_3651741 : Nat := 118140960795 + 3651741 * 2 ^ 59
def prefixEnd_3651741 : Nat := 4983230072969 + 3 ^ 40 * 3651741 * 2
def baseEnd_3651741 : Nat := 625032786243434093414485

theorem tailTrace_3651741 : CollatzResearch.WordTrace tailWord_3651741 prefixEnd_3651741 625032786243434093414485 := by
  unfold tailWord_3651741
  simp only [CollatzResearch.WordTrace]
  refine ⟨133189936263373499555187077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88793290842248999703458051 133189936263373499555187077)
  ·
    refine ⟨24973113049382531166597577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 133189936263373499555187077 24973113049382531166597577)
    ·
      refine ⟨18729834787036898374948183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24973113049382531166597577 18729834787036898374948183)
      ·
        refine ⟨28094752180555347562422275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18729834787036898374948183 28094752180555347562422275)
        ·
          refine ⟨42142128270833021343633413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28094752180555347562422275 42142128270833021343633413)
          ·
            refine ⟨7901649050781191501931265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 42142128270833021343633413 7901649050781191501931265)
            ·
              refine ⟨5926236788085893626448449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7901649050781191501931265 5926236788085893626448449)
              ·
                refine ⟨4444677591064420219836337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5926236788085893626448449 4444677591064420219836337)
                ·
                  refine ⟨3333508193298315164877253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4444677591064420219836337 3333508193298315164877253)
                  ·
                    refine ⟨625032786243434093414485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3333508193298315164877253 625032786243434093414485)
                    ·
                      rfl

theorem cell23_3651741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 4, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 4, 2, 2, 2, 4].length) (baseStart_3651741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3651741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3651741 prefixEnd_3651741 := by exact prefixLift 3651741
  have htrace : WordTrace (prefixWord ++ tailWord_3651741) baseStart_3651741 baseEnd_3651741 := by
    simpa [prefixWord, tailWord_3651741, baseEnd_3651741] using wordTrace_append hprefix tailTrace_3651741
  have hstable : (prefixWord ++ tailWord_3651741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3651741).length < 2 ^ (prefixWord ++ tailWord_3651741).sum := by decide
  have hdescent : baseEnd_3651741 < baseStart_3651741 := by decide
  rcases family_descends (prefixWord ++ tailWord_3651741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3651758 : List Nat := [4, 1, 4, 2, 1, 1, 2, 1, 1, 6]
def baseStart_3651758 : Nat := 118140960795 + 3651758 * 2 ^ 59
def prefixEnd_3651758 : Nat := 4983230072969 + 3 ^ 40 * 3651758 * 2
def baseEnd_3651758 : Nat := 625035695967142904576959

theorem tailTrace_3651758 : CollatzResearch.WordTrace tailWord_3651758 prefixEnd_3651758 625035695967142904576959 := by
  unfold tailWord_3651758
  simp only [CollatzResearch.WordTrace]
  refine ⟨16648819538038988932319491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 88793704202874607639037285 16648819538038988932319491)
  ·
    refine ⟨24973229307058483398479237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16648819538038988932319491 24973229307058483398479237)
    ·
      refine ⟨4682480495073465637214857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24973229307058483398479237 4682480495073465637214857)
      ·
        refine ⟨3511860371305099227911143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4682480495073465637214857 3511860371305099227911143)
        ·
          refine ⟨5267790556957648841866715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3511860371305099227911143 5267790556957648841866715)
          ·
            refine ⟨7901685835436473262800073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5267790556957648841866715 7901685835436473262800073)
            ·
              refine ⟨5926264376577354947100055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7901685835436473262800073 5926264376577354947100055)
              ·
                refine ⟨8889396564866032420650083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5926264376577354947100055 8889396564866032420650083)
                ·
                  refine ⟨13334094847299048630975125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8889396564866032420650083 13334094847299048630975125)
                  ·
                    refine ⟨625035695967142904576959, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13334094847299048630975125 625035695967142904576959)
                    ·
                      rfl

theorem cell23_3651758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 1, 2, 1, 1, 6].length) (baseStart_3651758 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3651758 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3651758 prefixEnd_3651758 := by exact prefixLift 3651758
  have htrace : WordTrace (prefixWord ++ tailWord_3651758) baseStart_3651758 baseEnd_3651758 := by
    simpa [prefixWord, tailWord_3651758, baseEnd_3651758] using wordTrace_append hprefix tailTrace_3651758
  have hstable : (prefixWord ++ tailWord_3651758).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3651758).length < 2 ^ (prefixWord ++ tailWord_3651758).sum := by decide
  have hdescent : baseEnd_3651758 < baseStart_3651758 := by decide
  rcases family_descends (prefixWord ++ tailWord_3651758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3651761 : List Nat := [1, 2, 2, 5, 2, 1, 2, 1, 1, 2, 4]
def baseStart_3651761 : Nat := 118140960795 + 3651761 * 2 ^ 59
def prefixEnd_3651761 : Nat := 4983230072969 + 3 ^ 40 * 3651761 * 2
def baseEnd_3651761 : Nat := 1875108628343392201993363

theorem tailTrace_3651761 : CollatzResearch.WordTrace tailWord_3651761 prefixEnd_3651761 1875108628343392201993363 := by
  unfold tailWord_3651761
  simp only [CollatzResearch.WordTrace]
  refine ⟨133190665723301042970915137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88793777148867361980610091 133190665723301042970915137)
  ·
    refine ⟨99892999292475782228186353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133190665723301042970915137 99892999292475782228186353)
    ·
      refine ⟨74919749469356836671139765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99892999292475782228186353 74919749469356836671139765)
      ·
        refine ⟨7023726512752203437919353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 74919749469356836671139765 7023726512752203437919353)
        ·
          refine ⟨5267794884564152578439515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7023726512752203437919353 5267794884564152578439515)
          ·
            refine ⟨7901692326846228867659273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5267794884564152578439515 7901692326846228867659273)
            ·
              refine ⟨5926269245134671650744455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7901692326846228867659273 5926269245134671650744455)
              ·
                refine ⟨8889403867702007476116683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5926269245134671650744455 8889403867702007476116683)
                ·
                  refine ⟨13334105801553011214175025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8889403867702007476116683 13334105801553011214175025)
                  ·
                    refine ⟨10000579351164758410631269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13334105801553011214175025 10000579351164758410631269)
                    ·
                      refine ⟨1875108628343392201993363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10000579351164758410631269 1875108628343392201993363)
                      ·
                        rfl

theorem cell23_3651761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 1, 2, 1, 1, 2, 4].length) (baseStart_3651761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3651761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3651761 prefixEnd_3651761 := by exact prefixLift 3651761
  have htrace : WordTrace (prefixWord ++ tailWord_3651761) baseStart_3651761 baseEnd_3651761 := by
    simpa [prefixWord, tailWord_3651761, baseEnd_3651761] using wordTrace_append hprefix tailTrace_3651761
  have hstable : (prefixWord ++ tailWord_3651761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3651761).length < 2 ^ (prefixWord ++ tailWord_3651761).sum := by decide
  have hdescent : baseEnd_3651761 < baseStart_3651761 := by decide
  rcases family_descends (prefixWord ++ tailWord_3651761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3651765 : List Nat := [1, 3, 3, 4, 1, 1, 1, 2, 3, 2, 2]
def baseStart_3651765 : Nat := 118140960795 + 3651765 * 2 ^ 59
def prefixEnd_3651765 : Nat := 4983230072969 + 3 ^ 40 * 3651765 * 2
def baseEnd_3651765 : Nat := 1875110682266010186343345

theorem tailTrace_3651765 : CollatzResearch.WordTrace tailWord_3651765 prefixEnd_3651765 1875110682266010186343345 := by
  unfold tailWord_3651765
  simp only [CollatzResearch.WordTrace]
  refine ⟨133190811615286551654060749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88793874410191034436040499 133190811615286551654060749)
  ·
    refine ⟨49946554355732456870272781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 133190811615286551654060749 49946554355732456870272781)
    ·
      refine ⟨18729957883399671326352293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49946554355732456870272781 18729957883399671326352293)
      ·
        refine ⟨3511867103137438373691055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18729957883399671326352293 3511867103137438373691055)
        ·
          refine ⟨5267800654706157560536583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3511867103137438373691055 5267800654706157560536583)
          ·
            refine ⟨7901700982059236340804875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5267800654706157560536583 7901700982059236340804875)
            ·
              refine ⟨11852551473088854511207313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7901700982059236340804875 11852551473088854511207313)
              ·
                refine ⟨8889413604816640883405485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11852551473088854511207313 8889413604816640883405485)
                ·
                  refine ⟨3333530101806240331277057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8889413604816640883405485 3333530101806240331277057)
                  ·
                    refine ⟨2500147576354680248457793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3333530101806240331277057 2500147576354680248457793)
                    ·
                      refine ⟨1875110682266010186343345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2500147576354680248457793 1875110682266010186343345)
                      ·
                        rfl

theorem cell23_3651765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 1, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 1, 1, 2, 3, 2, 2].length) (baseStart_3651765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3651765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3651765 prefixEnd_3651765 := by exact prefixLift 3651765
  have htrace : WordTrace (prefixWord ++ tailWord_3651765) baseStart_3651765 baseEnd_3651765 := by
    simpa [prefixWord, tailWord_3651765, baseEnd_3651765] using wordTrace_append hprefix tailTrace_3651765
  have hstable : (prefixWord ++ tailWord_3651765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3651765).length < 2 ^ (prefixWord ++ tailWord_3651765).sum := by decide
  have hdescent : baseEnd_3651765 < baseStart_3651765 := by decide
  rcases family_descends (prefixWord ++ tailWord_3651765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3651778 : List Nat := [3, 5, 1, 1, 1, 1, 2, 2, 1, 2, 4]
def baseStart_3651778 : Nat := 118140960795 + 3651778 * 2 ^ 59
def prefixEnd_3651778 : Nat := 4983230072969 + 3 ^ 40 * 3651778 * 2
def baseEnd_3651778 : Nat := 1875117357514518635480785

theorem tailTrace_3651778 : CollatzResearch.WordTrace tailWord_3651778 prefixEnd_3651778 1875117357514518635480785 := by
  unfold tailWord_3651778
  simp only [CollatzResearch.WordTrace]
  refine ⟨33297821441059863718570997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88794190509492969916189325 33297821441059863718570997)
  ·
    refine ⟨3121670760099362223616031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 33297821441059863718570997 3121670760099362223616031)
    ·
      refine ⟨4682506140149043335424047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3121670760099362223616031 4682506140149043335424047)
      ·
        refine ⟨7023759210223565003136071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4682506140149043335424047 7023759210223565003136071)
        ·
          refine ⟨10535638815335347504704107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7023759210223565003136071 10535638815335347504704107)
          ·
            refine ⟨15803458223003021257056161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10535638815335347504704107 15803458223003021257056161)
            ·
              refine ⟨11852593667252265942792121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15803458223003021257056161 11852593667252265942792121)
              ·
                refine ⟨8889445250439199457094091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11852593667252265942792121 8889445250439199457094091)
                ·
                  refine ⟨13334167875658799185641137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8889445250439199457094091 13334167875658799185641137)
                  ·
                    refine ⟨10000625906744099389230853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13334167875658799185641137 10000625906744099389230853)
                    ·
                      refine ⟨1875117357514518635480785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10000625906744099389230853 1875117357514518635480785)
                      ·
                        rfl

theorem cell23_3651778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 2, 2, 1, 2, 4].length) (baseStart_3651778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3651778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3651778 prefixEnd_3651778 := by exact prefixLift 3651778
  have htrace : WordTrace (prefixWord ++ tailWord_3651778) baseStart_3651778 baseEnd_3651778 := by
    simpa [prefixWord, tailWord_3651778, baseEnd_3651778] using wordTrace_append hprefix tailTrace_3651778
  have hstable : (prefixWord ++ tailWord_3651778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3651778).length < 2 ^ (prefixWord ++ tailWord_3651778).sum := by decide
  have hdescent : baseEnd_3651778 < baseStart_3651778 := by decide
  rcases family_descends (prefixWord ++ tailWord_3651778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3651791 : List Nat := [1, 1, 2, 1, 1, 3, 5, 3, 1, 3, 2]
def baseStart_3651791 : Nat := 118140960795 + 3651791 * 2 ^ 59
def prefixEnd_3651791 : Nat := 4983230072969 + 3 ^ 40 * 3651791 * 2
def baseEnd_3651791 : Nat := 1875124032763027084618225

theorem tailTrace_3651791 : CollatzResearch.WordTrace tailWord_3651791 prefixEnd_3651791 1875124032763027084618225 := by
  unfold tailWord_3651791
  simp only [CollatzResearch.WordTrace]
  refine ⟨133191759913192358094507227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88794506608794905396338151 133191759913192358094507227)
  ·
    refine ⟨199787639869788537141760841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133191759913192358094507227 199787639869788537141760841)
    ·
      refine ⟨149840729902341402856320631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 199787639869788537141760841 149840729902341402856320631)
      ·
        refine ⟨224761094853512104284480947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149840729902341402856320631 224761094853512104284480947)
        ·
          refine ⟨337141642280268156426721421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 224761094853512104284480947 337141642280268156426721421)
          ·
            refine ⟨126428115855100558660020533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 337141642280268156426721421 126428115855100558660020533)
            ·
              refine ⟨11852635861415677374376925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 126428115855100558660020533 11852635861415677374376925)
              ·
                refine ⟨4444738448030879015391347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11852635861415677374376925 4444738448030879015391347)
                ·
                  refine ⟨6667107672046318523087021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4444738448030879015391347 6667107672046318523087021)
                  ·
                    refine ⟨2500165377017369446157633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6667107672046318523087021 2500165377017369446157633)
                    ·
                      refine ⟨1875124032763027084618225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2500165377017369446157633 1875124032763027084618225)
                      ·
                        rfl

theorem cell23_3651791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 5, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 5, 3, 1, 3, 2].length) (baseStart_3651791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3651791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3651791 prefixEnd_3651791 := by exact prefixLift 3651791
  have htrace : WordTrace (prefixWord ++ tailWord_3651791) baseStart_3651791 baseEnd_3651791 := by
    simpa [prefixWord, tailWord_3651791, baseEnd_3651791] using wordTrace_append hprefix tailTrace_3651791
  have hstable : (prefixWord ++ tailWord_3651791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3651791).length < 2 ^ (prefixWord ++ tailWord_3651791).sum := by decide
  have hdescent : baseEnd_3651791 < baseStart_3651791 := by decide
  rcases family_descends (prefixWord ++ tailWord_3651791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3651807 : List Nat := [1, 1, 2, 3, 2, 1, 1, 2, 4, 1, 5]
def baseStart_3651807 : Nat := 118140960795 + 3651807 * 2 ^ 59
def prefixEnd_3651807 : Nat := 4983230072969 + 3 ^ 40 * 3651807 * 2
def baseEnd_3651807 : Nat := 1875132248453499022018151

theorem tailTrace_3651807 : CollatzResearch.WordTrace tailWord_3651807 prefixEnd_3651807 1875132248453499022018151 := by
  unfold tailWord_3651807
  simp only [CollatzResearch.WordTrace]
  refine ⟨133192343481134392827089675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88794895654089595218059783 133192343481134392827089675)
  ·
    refine ⟨199788515221701589240634513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133192343481134392827089675 199788515221701589240634513)
    ·
      refine ⟨149841386416276191930475885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 199788515221701589240634513 149841386416276191930475885)
      ·
        refine ⟨56190519906103571973928457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 149841386416276191930475885 56190519906103571973928457)
        ·
          refine ⟨42142889929577678980446343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56190519906103571973928457 42142889929577678980446343)
          ·
            refine ⟨63214334894366518470669515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42142889929577678980446343 63214334894366518470669515)
            ·
              refine ⟨94821502341549777706004273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63214334894366518470669515 94821502341549777706004273)
              ·
                refine ⟨71116126756162333279503205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 94821502341549777706004273 71116126756162333279503205)
                ·
                  refine ⟨13334273766780437489906851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 71116126756162333279503205 13334273766780437489906851)
                  ·
                    refine ⟨20001410650170656234860277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13334273766780437489906851 20001410650170656234860277)
                    ·
                      refine ⟨1875132248453499022018151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20001410650170656234860277 1875132248453499022018151)
                      ·
                        rfl

theorem cell23_3651807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 2, 4, 1, 5].length) (baseStart_3651807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3651807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3651807 prefixEnd_3651807 := by exact prefixLift 3651807
  have htrace : WordTrace (prefixWord ++ tailWord_3651807) baseStart_3651807 baseEnd_3651807 := by
    simpa [prefixWord, tailWord_3651807, baseEnd_3651807] using wordTrace_append hprefix tailTrace_3651807
  have hstable : (prefixWord ++ tailWord_3651807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3651807).length < 2 ^ (prefixWord ++ tailWord_3651807).sum := by decide
  have hdescent : baseEnd_3651807 < baseStart_3651807 := by decide
  rcases family_descends (prefixWord ++ tailWord_3651807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3651815 : List Nat := [1, 1, 5, 3, 1, 2, 3, 1, 2, 1, 3]
def baseStart_3651815 : Nat := 118140960795 + 3651815 * 2 ^ 59
def prefixEnd_3651815 : Nat := 4983230072969 + 3 ^ 40 * 3651815 * 2
def baseEnd_3651815 : Nat := 1875136356298734990718115

theorem tailTrace_3651815 : CollatzResearch.WordTrace tailWord_3651815 prefixEnd_3651815 1875136356298734990718115 := by
  unfold tailWord_3651815
  simp only [CollatzResearch.WordTrace]
  refine ⟨133192635265105410193380899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88795090176736940128920599 133192635265105410193380899)
  ·
    refine ⟨199788952897658115290071349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133192635265105410193380899 199788952897658115290071349)
    ·
      refine ⟨18730214334155448308444189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 199788952897658115290071349 18730214334155448308444189)
      ·
        refine ⟨7023830375308293115666571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18730214334155448308444189 7023830375308293115666571)
        ·
          refine ⟨10535745562962439673499857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7023830375308293115666571 10535745562962439673499857)
          ·
            refine ⟨7901809172221829755124893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10535745562962439673499857 7901809172221829755124893)
            ·
              refine ⟨2963178439583186158171835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7901809172221829755124893 2963178439583186158171835)
              ·
                refine ⟨4444767659374779237257753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2963178439583186158171835 4444767659374779237257753)
                ·
                  refine ⟨3333575744531084427943315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4444767659374779237257753 3333575744531084427943315)
                  ·
                    refine ⟨5000363616796626641914973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3333575744531084427943315 5000363616796626641914973)
                    ·
                      refine ⟨1875136356298734990718115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5000363616796626641914973 1875136356298734990718115)
                      ·
                        rfl

theorem cell23_3651815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 2, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 2, 3, 1, 2, 1, 3].length) (baseStart_3651815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3651815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3651815 prefixEnd_3651815 := by exact prefixLift 3651815
  have htrace : WordTrace (prefixWord ++ tailWord_3651815) baseStart_3651815 baseEnd_3651815 := by
    simpa [prefixWord, tailWord_3651815, baseEnd_3651815] using wordTrace_append hprefix tailTrace_3651815
  have hstable : (prefixWord ++ tailWord_3651815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3651815).length < 2 ^ (prefixWord ++ tailWord_3651815).sum := by decide
  have hdescent : baseEnd_3651815 < baseStart_3651815 := by decide
  rcases family_descends (prefixWord ++ tailWord_3651815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3651827 : List Nat := [1, 1, 1, 2, 2, 4, 1, 4, 7]
def baseStart_3651827 : Nat := 118140960795 + 3651827 * 2 ^ 59
def prefixEnd_3651827 : Nat := 4983230072969 + 3 ^ 40 * 3651827 * 2
def baseEnd_3651827 : Nat := 208349168674065438196451

theorem tailTrace_3651827 : CollatzResearch.WordTrace tailWord_3651827 prefixEnd_3651827 208349168674065438196451 := by
  unfold tailWord_3651827
  simp only [CollatzResearch.WordTrace]
  refine ⟨133193072941061936242817735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88795381960707957495211823 133193072941061936242817735)
  ·
    refine ⟨199789609411592904364226603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133193072941061936242817735 199789609411592904364226603)
    ·
      refine ⟨299684414117389356546339905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 199789609411592904364226603 299684414117389356546339905)
      ·
        refine ⟨224763310588042017409754929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 299684414117389356546339905 224763310588042017409754929)
        ·
          refine ⟨168572482941031513057316197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 224763310588042017409754929 168572482941031513057316197)
          ·
            refine ⟨31607340551443408698246787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 168572482941031513057316197 31607340551443408698246787)
            ·
              refine ⟨47411010827165113047370181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31607340551443408698246787 47411010827165113047370181)
              ·
                refine ⟨8889564530093458696381909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 47411010827165113047370181 8889564530093458696381909)
                ·
                  refine ⟨208349168674065438196451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8889564530093458696381909 208349168674065438196451)
                  ·
                    rfl

theorem cell23_3651827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 1, 4, 7].length) (baseStart_3651827 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3651827 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3651827 prefixEnd_3651827 := by exact prefixLift 3651827
  have htrace : WordTrace (prefixWord ++ tailWord_3651827) baseStart_3651827 baseEnd_3651827 := by
    simpa [prefixWord, tailWord_3651827, baseEnd_3651827] using wordTrace_append hprefix tailTrace_3651827
  have hstable : (prefixWord ++ tailWord_3651827).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3651827).length < 2 ^ (prefixWord ++ tailWord_3651827).sum := by decide
  have hdescent : baseEnd_3651827 < baseStart_3651827 := by decide
  rcases family_descends (prefixWord ++ tailWord_3651827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3651838 : List Nat := [4, 2, 2, 1, 1, 1, 1, 1, 6, 2, 2]
def baseStart_3651838 : Nat := 118140960795 + 3651838 * 2 ^ 59
def prefixEnd_3651838 : Nat := 4983230072969 + 3 ^ 40 * 3651838 * 2
def baseEnd_3651838 : Nat := 1875148166353788400730509

theorem tailTrace_3651838 : CollatzResearch.WordTrace tailWord_3651838 prefixEnd_3651838 1875148166353788400730509 := by
  unfold tailWord_3651838
  simp only [CollatzResearch.WordTrace]
  refine ⟨16649184268002760640183521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 88795649429348056747645445 16649184268002760640183521)
  ·
    refine ⟨12486888201002070480137641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16649184268002760640183521 12486888201002070480137641)
    ·
      refine ⟨9365166150751552860103231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12486888201002070480137641 9365166150751552860103231)
      ·
        refine ⟨14047749226127329290154847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9365166150751552860103231 14047749226127329290154847)
        ·
          refine ⟨21071623839190993935232271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14047749226127329290154847 21071623839190993935232271)
          ·
            refine ⟨31607435758786490902848407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21071623839190993935232271 31607435758786490902848407)
            ·
              refine ⟨47411153638179736354272611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31607435758786490902848407 47411153638179736354272611)
              ·
                refine ⟨71116730457269604531408917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47411153638179736354272611 71116730457269604531408917)
                ·
                  refine ⟨3333596740184512712409793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 71116730457269604531408917 3333596740184512712409793)
                  ·
                    refine ⟨2500197555138384534307345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3333596740184512712409793 2500197555138384534307345)
                    ·
                      refine ⟨1875148166353788400730509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2500197555138384534307345 1875148166353788400730509)
                      ·
                        rfl

theorem cell23_3651838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 1, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 1, 1, 6, 2, 2].length) (baseStart_3651838 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3651838 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3651838 prefixEnd_3651838 := by exact prefixLift 3651838
  have htrace : WordTrace (prefixWord ++ tailWord_3651838) baseStart_3651838 baseEnd_3651838 := by
    simpa [prefixWord, tailWord_3651838, baseEnd_3651838] using wordTrace_append hprefix tailTrace_3651838
  have hstable : (prefixWord ++ tailWord_3651838).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3651838).length < 2 ^ (prefixWord ++ tailWord_3651838).sum := by decide
  have hdescent : baseEnd_3651838 < baseStart_3651838 := by decide
  rcases family_descends (prefixWord ++ tailWord_3651838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3651867 : List Nat := [1, 1, 1, 1, 1, 1, 7, 1, 1, 1, 7]
def baseStart_3651867 : Nat := 118140960795 + 3651867 * 2 ^ 59
def prefixEnd_3651867 : Nat := 4983230072969 + 3 ^ 40 * 3651867 * 2
def baseEnd_3651867 : Nat := 1875163057292768787267875

theorem tailTrace_3651867 : CollatzResearch.WordTrace tailWord_3651867 prefixEnd_3651867 1875163057292768787267875 := by
  unfold tailWord_3651867
  simp only [CollatzResearch.WordTrace]
  refine ⟨133194531860917023074273855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88796354573944682049515903 133194531860917023074273855)
  ·
    refine ⟨199791797791375534611410783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133194531860917023074273855 199791797791375534611410783)
    ·
      refine ⟨299687696687063301917116175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 199791797791375534611410783 299687696687063301917116175)
      ·
        refine ⟨449531545030594952875674263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 299687696687063301917116175 449531545030594952875674263)
        ·
          refine ⟨674297317545892429313511395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 449531545030594952875674263 674297317545892429313511395)
          ·
            refine ⟨1011445976318838643970267093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 674297317545892429313511395 1011445976318838643970267093)
            ·
              refine ⟨23705765069972780718053135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1011445976318838643970267093 23705765069972780718053135)
              ·
                refine ⟨35558647604959171077079703, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23705765069972780718053135 35558647604959171077079703)
                ·
                  refine ⟨53337971407438756615619555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35558647604959171077079703 53337971407438756615619555)
                  ·
                    refine ⟨80006957111158134923429333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 53337971407438756615619555 80006957111158134923429333)
                    ·
                      refine ⟨1875163057292768787267875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 80006957111158134923429333 1875163057292768787267875)
                      ·
                        rfl

theorem cell23_3651867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 7, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 7, 1, 1, 1, 7].length) (baseStart_3651867 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3651867 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3651867 prefixEnd_3651867 := by exact prefixLift 3651867
  have htrace : WordTrace (prefixWord ++ tailWord_3651867) baseStart_3651867 baseEnd_3651867 := by
    simpa [prefixWord, tailWord_3651867, baseEnd_3651867] using wordTrace_append hprefix tailTrace_3651867
  have hstable : (prefixWord ++ tailWord_3651867).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3651867).length < 2 ^ (prefixWord ++ tailWord_3651867).sum := by decide
  have hdescent : baseEnd_3651867 < baseStart_3651867 := by decide
  rcases family_descends (prefixWord ++ tailWord_3651867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3651872 : List Nat := [2, 1, 1, 5, 2, 3, 2, 1, 2, 2, 2]
def baseStart_3651872 : Nat := 118140960795 + 3651872 * 2 ^ 59
def prefixEnd_3651872 : Nat := 4983230072969 + 3 ^ 40 * 3651872 * 2
def baseEnd_3651872 : Nat := 1875165624696041267705353

theorem tailTrace_3651872 : CollatzResearch.WordTrace tailWord_3651872 prefixEnd_3651872 1875165624696041267705353 := by
  unfold tailWord_3651872
  simp only [CollatzResearch.WordTrace]
  refine ⟨66597357112949454464102935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88796476150599272618803913 66597357112949454464102935)
  ·
    refine ⟨99896035669424181696154403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66597357112949454464102935 99896035669424181696154403)
    ·
      refine ⟨149844053504136272544231605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99896035669424181696154403 149844053504136272544231605)
      ·
        refine ⟨14047880016012775551021713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 149844053504136272544231605 14047880016012775551021713)
        ·
          refine ⟨10535910012009581663266285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14047880016012775551021713 10535910012009581663266285)
          ·
            refine ⟨3950966254503593123724857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10535910012009581663266285 3950966254503593123724857)
            ·
              refine ⟨2963224690877694842793643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3950966254503593123724857 2963224690877694842793643)
              ·
                refine ⟨4444837036316542264190465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2963224690877694842793643 4444837036316542264190465)
                ·
                  refine ⟨3333627777237406698142849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4444837036316542264190465 3333627777237406698142849)
                  ·
                    refine ⟨2500220832928055023607137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3333627777237406698142849 2500220832928055023607137)
                    ·
                      refine ⟨1875165624696041267705353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2500220832928055023607137 1875165624696041267705353)
                      ·
                        rfl

theorem cell23_3651872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 3, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 3, 2, 1, 2, 2, 2].length) (baseStart_3651872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3651872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3651872 prefixEnd_3651872 := by exact prefixLift 3651872
  have htrace : WordTrace (prefixWord ++ tailWord_3651872) baseStart_3651872 baseEnd_3651872 := by
    simpa [prefixWord, tailWord_3651872, baseEnd_3651872] using wordTrace_append hprefix tailTrace_3651872
  have hstable : (prefixWord ++ tailWord_3651872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3651872).length < 2 ^ (prefixWord ++ tailWord_3651872).sum := by decide
  have hdescent : baseEnd_3651872 < baseStart_3651872 := by decide
  rcases family_descends (prefixWord ++ tailWord_3651872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3651887 : List Nat := [1, 1, 2, 1, 2, 1, 4, 1, 2, 8]
def baseStart_3651887 : Nat := 118140960795 + 3651887 * 2 ^ 59
def prefixEnd_3651887 : Nat := 4983230072969 + 3 ^ 40 * 3651887 * 2
def baseEnd_3651887 : Nat := 625057775635286236339261

theorem tailTrace_3651887 : CollatzResearch.WordTrace tailWord_3651887 prefixEnd_3651887 625057775635286236339261 := by
  unfold tailWord_3651887
  simp only [CollatzResearch.WordTrace]
  refine ⟨133195261320844566490001915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88796840880563044326667943 133195261320844566490001915)
  ·
    refine ⟨199792891981266849735002873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133195261320844566490001915 199792891981266849735002873)
    ·
      refine ⟨149844668985950137301252155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 199792891981266849735002873 149844668985950137301252155)
      ·
        refine ⟨224767003478925205951878233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149844668985950137301252155 224767003478925205951878233)
        ·
          refine ⟨168575252609193904463908675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 224767003478925205951878233 168575252609193904463908675)
          ·
            refine ⟨252862878913790856695863013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 168575252609193904463908675 252862878913790856695863013)
            ·
              refine ⟨47411789796335785630474315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 252862878913790856695863013 47411789796335785630474315)
              ·
                refine ⟨71117684694503678445711473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47411789796335785630474315 71117684694503678445711473)
                ·
                  refine ⟨53338263520877758834283605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 71117684694503678445711473 53338263520877758834283605)
                  ·
                    refine ⟨625057775635286236339261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 53338263520877758834283605 625057775635286236339261)
                    ·
                      rfl

theorem cell23_3651887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 4, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 4, 1, 2, 8].length) (baseStart_3651887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3651887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3651887 prefixEnd_3651887 := by exact prefixLift 3651887
  have htrace : WordTrace (prefixWord ++ tailWord_3651887) baseStart_3651887 baseEnd_3651887 := by
    simpa [prefixWord, tailWord_3651887, baseEnd_3651887] using wordTrace_append hprefix tailTrace_3651887
  have hstable : (prefixWord ++ tailWord_3651887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3651887).length < 2 ^ (prefixWord ++ tailWord_3651887).sum := by decide
  have hdescent : baseEnd_3651887 < baseStart_3651887 := by decide
  rcases family_descends (prefixWord ++ tailWord_3651887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3651904 : List Nat := [2, 1, 1, 2, 2, 1, 2, 1, 7, 4]
def baseStart_3651904 : Nat := 118140960795 + 3651904 * 2 ^ 59
def prefixEnd_3651904 : Nat := 4983230072969 + 3 ^ 40 * 3651904 * 2
def baseEnd_3651904 : Nat := 625060685358995047501735

theorem tailTrace_3651904 : CollatzResearch.WordTrace tailWord_3651904 prefixEnd_3651904 625060685358995047501735 := by
  unfold tailWord_3651904
  simp only [CollatzResearch.WordTrace]
  refine ⟨66597940680891489196685383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88797254241188652262247177 66597940680891489196685383)
  ·
    refine ⟨99896911021337233795028075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66597940680891489196685383 99896911021337233795028075)
    ·
      refine ⟨149845366532005850692542113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99896911021337233795028075 149845366532005850692542113)
      ·
        refine ⟨112384024899004388019406585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 149845366532005850692542113 112384024899004388019406585)
        ·
          refine ⟨84288018674253291014554939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 112384024899004388019406585 84288018674253291014554939)
          ·
            refine ⟨126432028011379936521832409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84288018674253291014554939 126432028011379936521832409)
            ·
              refine ⟨94824021008534952391374307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 126432028011379936521832409 94824021008534952391374307)
              ·
                refine ⟨142236031512802428587061461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 94824021008534952391374307 142236031512802428587061461)
                ·
                  refine ⟨3333656988581306920009253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 142236031512802428587061461 3333656988581306920009253)
                  ·
                    refine ⟨625060685358995047501735, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3333656988581306920009253 625060685358995047501735)
                    ·
                      rfl

theorem cell23_3651904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 1, 7, 4].length) (baseStart_3651904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3651904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3651904 prefixEnd_3651904 := by exact prefixLift 3651904
  have htrace : WordTrace (prefixWord ++ tailWord_3651904) baseStart_3651904 baseEnd_3651904 := by
    simpa [prefixWord, tailWord_3651904, baseEnd_3651904] using wordTrace_append hprefix tailTrace_3651904
  have hstable : (prefixWord ++ tailWord_3651904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3651904).length < 2 ^ (prefixWord ++ tailWord_3651904).sum := by decide
  have hdescent : baseEnd_3651904 < baseStart_3651904 := by decide
  rcases family_descends (prefixWord ++ tailWord_3651904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3651911 : List Nat := [1, 1, 4, 1, 2, 2, 2, 2, 2, 4, 2]
def baseStart_3651911 : Nat := 118140960795 + 3651911 * 2 ^ 59
def prefixEnd_3651911 : Nat := 4983230072969 + 3 ^ 40 * 3651911 * 2
def baseEnd_3651911 : Nat := 1875185650441566615117673

theorem tailTrace_3651911 : CollatzResearch.WordTrace tailWord_3651911 prefixEnd_3651911 1875185650441566615117673 := by
  unfold tailWord_3651911
  simp only [CollatzResearch.WordTrace]
  refine ⟨133196136672757618588875587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88797424448505079059250391 133196136672757618588875587)
  ·
    refine ⟨199794205009136427883313381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133196136672757618588875587 199794205009136427883313381)
    ·
      refine ⟨37461413439213080228121259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 199794205009136427883313381 37461413439213080228121259)
      ·
        refine ⟨56192120158819620342181889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37461413439213080228121259 56192120158819620342181889)
        ·
          refine ⟨42144090119114715256636417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56192120158819620342181889 42144090119114715256636417)
          ·
            refine ⟨31608067589336036442477313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42144090119114715256636417 31608067589336036442477313)
            ·
              refine ⟨23706050692002027331857985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31608067589336036442477313 23706050692002027331857985)
              ·
                refine ⟨17779538019001520498893489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23706050692002027331857985 17779538019001520498893489)
                ·
                  refine ⟨13334653514251140374170117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17779538019001520498893489 13334653514251140374170117)
                  ·
                    refine ⟨2500247533922088820156897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13334653514251140374170117 2500247533922088820156897)
                    ·
                      refine ⟨1875185650441566615117673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2500247533922088820156897 1875185650441566615117673)
                      ·
                        rfl

theorem cell23_3651911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 2, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 2, 2, 2, 4, 2].length) (baseStart_3651911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3651911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3651911 prefixEnd_3651911 := by exact prefixLift 3651911
  have htrace : WordTrace (prefixWord ++ tailWord_3651911) baseStart_3651911 baseEnd_3651911 := by
    simpa [prefixWord, tailWord_3651911, baseEnd_3651911] using wordTrace_append hprefix tailTrace_3651911
  have hstable : (prefixWord ++ tailWord_3651911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3651911).length < 2 ^ (prefixWord ++ tailWord_3651911).sum := by decide
  have hdescent : baseEnd_3651911 < baseStart_3651911 := by decide
  rcases family_descends (prefixWord ++ tailWord_3651911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3651914 : List Nat := [3, 1, 2, 1, 1, 1, 1, 1, 5, 4, 3]
def baseStart_3651914 : Nat := 118140960795 + 3651914 * 2 ^ 59
def prefixEnd_3651914 : Nat := 4983230072969 + 3 ^ 40 * 3651914 * 2
def baseEnd_3651914 : Nat := 1875187190883530103380159

theorem tailTrace_3651914 : CollatzResearch.WordTrace tailWord_3651914 prefixEnd_3651914 1875187190883530103380159 := by
  unfold tailWord_3651914
  simp only [CollatzResearch.WordTrace]
  refine ⟨33299061522936687525308699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88797497394497833400823197 33299061522936687525308699)
  ·
    refine ⟨49948592284405031287963049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33299061522936687525308699 49948592284405031287963049)
    ·
      refine ⟨37461444213303773465972287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49948592284405031287963049 37461444213303773465972287)
      ·
        refine ⟨56192166319955660198958431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37461444213303773465972287 56192166319955660198958431)
        ·
          refine ⟨84288249479933490298437647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56192166319955660198958431 84288249479933490298437647)
          ·
            refine ⟨126432374219900235447656471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84288249479933490298437647 126432374219900235447656471)
            ·
              refine ⟨189648561329850353171484707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 126432374219900235447656471 189648561329850353171484707)
              ·
                refine ⟨284472841994775529757227061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 189648561329850353171484707 284472841994775529757227061)
                ·
                  refine ⟨26669328937010205914740037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 284472841994775529757227061 26669328937010205914740037)
                  ·
                    refine ⟨5000499175689413609013757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26669328937010205914740037 5000499175689413609013757)
                    ·
                      refine ⟨1875187190883530103380159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5000499175689413609013757 1875187190883530103380159)
                      ·
                        rfl

theorem cell23_3651914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 5, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 5, 4, 3].length) (baseStart_3651914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3651914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3651914 prefixEnd_3651914 := by exact prefixLift 3651914
  have htrace : WordTrace (prefixWord ++ tailWord_3651914) baseStart_3651914 baseEnd_3651914 := by
    simpa [prefixWord, tailWord_3651914, baseEnd_3651914] using wordTrace_append hprefix tailTrace_3651914
  have hstable : (prefixWord ++ tailWord_3651914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3651914).length < 2 ^ (prefixWord ++ tailWord_3651914).sum := by decide
  have hdescent : baseEnd_3651914 < baseStart_3651914 := by decide
  rcases family_descends (prefixWord ++ tailWord_3651914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3651938 : List Nat := [3, 3, 2, 1, 1, 3, 1, 2, 3, 4]
def baseStart_3651938 : Nat := 118140960795 + 3651938 * 2 ^ 59
def prefixEnd_3651938 : Nat := 4983230072969 + 3 ^ 40 * 3651938 * 2
def baseEnd_3651938 : Nat := 625066504806412669826683

theorem tailTrace_3651938 : CollatzResearch.WordTrace tailWord_3651938 prefixEnd_3651938 625066504806412669826683 := by
  unfold tailWord_3651938
  simp only [CollatzResearch.WordTrace]
  refine ⟨33299280360914950550027117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88798080962439868133405645 33299280360914950550027117)
  ·
    refine ⟨12487230135343106456260169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33299280360914950550027117 12487230135343106456260169)
    ·
      refine ⟨9365422601507329842195127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12487230135343106456260169 9365422601507329842195127)
      ·
        refine ⟨14048133902260994763292691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9365422601507329842195127 14048133902260994763292691)
        ·
          refine ⟨21072200853391492144939037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14048133902260994763292691 21072200853391492144939037)
          ·
            refine ⟨7902075320021809554352139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21072200853391492144939037 7902075320021809554352139)
            ·
              refine ⟨11853112980032714331528209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7902075320021809554352139 11853112980032714331528209)
              ·
                refine ⟨8889834735024535748646157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11853112980032714331528209 8889834735024535748646157)
                ·
                  refine ⟨3333688025634200905742309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8889834735024535748646157 3333688025634200905742309)
                  ·
                    refine ⟨625066504806412669826683, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3333688025634200905742309 625066504806412669826683)
                    ·
                      rfl

theorem cell23_3651938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 3, 1, 2, 3, 4].length) (baseStart_3651938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3651938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3651938 prefixEnd_3651938 := by exact prefixLift 3651938
  have htrace : WordTrace (prefixWord ++ tailWord_3651938) baseStart_3651938 baseEnd_3651938 := by
    simpa [prefixWord, tailWord_3651938, baseEnd_3651938] using wordTrace_append hprefix tailTrace_3651938
  have hstable : (prefixWord ++ tailWord_3651938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3651938).length < 2 ^ (prefixWord ++ tailWord_3651938).sum := by decide
  have hdescent : baseEnd_3651938 < baseStart_3651938 := by decide
  rcases family_descends (prefixWord ++ tailWord_3651938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3651961 : List Nat := [1, 2, 1, 3, 2, 1, 1, 1, 7, 1, 3]
def baseStart_3651961 : Nat := 118140960795 + 3651961 * 2 ^ 59
def prefixEnd_3651961 : Nat := 4983230072969 + 3 ^ 40 * 3651961 * 2
def baseEnd_3651961 : Nat := 1875211324474291419492443

theorem tailTrace_3651961 : CollatzResearch.WordTrace tailWord_3651961 prefixEnd_3651961 1875211324474291419492443 := by
  unfold tailWord_3651961
  simp only [CollatzResearch.WordTrace]
  refine ⟨133197960322576477128195737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88798640215050984752130491 133197960322576477128195737)
  ·
    refine ⟨99898470241932357846146803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133197960322576477128195737 99898470241932357846146803)
    ·
      refine ⟨149847705362898536769220205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99898470241932357846146803 149847705362898536769220205)
      ·
        refine ⟨56192889511086951288457577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 149847705362898536769220205 56192889511086951288457577)
        ·
          refine ⟨42144667133315213466343183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56192889511086951288457577 42144667133315213466343183)
          ·
            refine ⟨63217000699972820199514775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42144667133315213466343183 63217000699972820199514775)
            ·
              refine ⟨94825501049959230299272163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63217000699972820199514775 94825501049959230299272163)
              ·
                refine ⟨142238251574938845448908245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 94825501049959230299272163 142238251574938845448908245)
                ·
                  refine ⟨3333709021287629190208787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 142238251574938845448908245 3333709021287629190208787)
                  ·
                    refine ⟨5000563531931443785313181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3333709021287629190208787 5000563531931443785313181)
                    ·
                      refine ⟨1875211324474291419492443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5000563531931443785313181 1875211324474291419492443)
                      ·
                        rfl

theorem cell23_3651961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 1, 7, 1, 3].length) (baseStart_3651961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3651961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3651961 prefixEnd_3651961 := by exact prefixLift 3651961
  have htrace : WordTrace (prefixWord ++ tailWord_3651961) baseStart_3651961 baseEnd_3651961 := by
    simpa [prefixWord, tailWord_3651961, baseEnd_3651961] using wordTrace_append hprefix tailTrace_3651961
  have hstable : (prefixWord ++ tailWord_3651961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3651961).length < 2 ^ (prefixWord ++ tailWord_3651961).sum := by decide
  have hdescent : baseEnd_3651961 < baseStart_3651961 := by decide
  rcases family_descends (prefixWord ++ tailWord_3651961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3651964 : List Nat := [2, 2, 2, 1, 1, 1, 2, 2, 5, 5]
def baseStart_3651964 : Nat := 118140960795 + 3651964 * 2 ^ 59
def prefixEnd_3651964 : Nat := 4983230072969 + 3 ^ 40 * 3651964 * 2
def baseEnd_3651964 : Nat := 625070954972084969251643

theorem tailTrace_3651964 : CollatzResearch.WordTrace tailWord_3651964 prefixEnd_3651964 625070954972084969251643 := by
  unfold tailWord_3651964
  simp only [CollatzResearch.WordTrace]
  refine ⟨66599034870782804320277473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88798713161043739093703297 66599034870782804320277473)
  ·
    refine ⟨49949276153087103240208105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66599034870782804320277473 49949276153087103240208105)
    ·
      refine ⟨37461957114815327430156079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49949276153087103240208105 37461957114815327430156079)
      ·
        refine ⟨56192935672222991145234119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37461957114815327430156079 56192935672222991145234119)
        ·
          refine ⟨84289403508334486717851179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56192935672222991145234119 84289403508334486717851179)
          ·
            refine ⟨126434105262501730076776769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84289403508334486717851179 126434105262501730076776769)
            ·
              refine ⟨94825578946876297557582577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 126434105262501730076776769 94825578946876297557582577)
              ·
                refine ⟨71119184210157223168186933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 94825578946876297557582577 71119184210157223168186933)
                ·
                  refine ⟨6667423519702239672017525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 71119184210157223168186933 6667423519702239672017525)
                  ·
                    refine ⟨625070954972084969251643, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6667423519702239672017525 625070954972084969251643)
                    ·
                      rfl

theorem cell23_3651964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 2, 5, 5].length) (baseStart_3651964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3651964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3651964 prefixEnd_3651964 := by exact prefixLift 3651964
  have htrace : WordTrace (prefixWord ++ tailWord_3651964) baseStart_3651964 baseEnd_3651964 := by
    simpa [prefixWord, tailWord_3651964, baseEnd_3651964] using wordTrace_append hprefix tailTrace_3651964
  have hstable : (prefixWord ++ tailWord_3651964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3651964).length < 2 ^ (prefixWord ++ tailWord_3651964).sum := by decide
  have hdescent : baseEnd_3651964 < baseStart_3651964 := by decide
  rcases family_descends (prefixWord ++ tailWord_3651964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3652028 : List Nat := [2, 2, 2, 4, 1, 1, 2, 1, 4, 4]
def baseStart_3652028 : Nat := 118140960795 + 3652028 * 2 ^ 59
def prefixEnd_3652028 : Nat := 4983230072969 + 3 ^ 40 * 3652028 * 2
def baseEnd_3652028 : Nat := 625081909226047552451545

theorem tailTrace_3652028 : CollatzResearch.WordTrace tailWord_3652028 prefixEnd_3652028 625081909226047552451545 := by
  unfold tailWord_3652028
  simp only [CollatzResearch.WordTrace]
  refine ⟨66600202006666873785442369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88800269342222498380589825 66600202006666873785442369)
  ·
    refine ⟨49950151505000155339081777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66600202006666873785442369 49950151505000155339081777)
    ·
      refine ⟨37462613628750116504311333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49950151505000155339081777 37462613628750116504311333)
      ·
        refine ⟨7024240055390646844558375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 37462613628750116504311333 7024240055390646844558375)
        ·
          refine ⟨10536360083085970266837563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7024240055390646844558375 10536360083085970266837563)
          ·
            refine ⟨15804540124628955400256345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10536360083085970266837563 15804540124628955400256345)
            ·
              refine ⟨11853405093471716550192259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15804540124628955400256345 11853405093471716550192259)
              ·
                refine ⟨17780107640207574825288389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11853405093471716550192259 17780107640207574825288389)
                ·
                  refine ⟨3333770182538920279741573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17780107640207574825288389 3333770182538920279741573)
                  ·
                    refine ⟨625081909226047552451545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3333770182538920279741573 625081909226047552451545)
                    ·
                      rfl

theorem cell23_3652028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 2, 1, 4, 4].length) (baseStart_3652028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3652028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3652028 prefixEnd_3652028 := by exact prefixLift 3652028
  have htrace : WordTrace (prefixWord ++ tailWord_3652028) baseStart_3652028 baseEnd_3652028 := by
    simpa [prefixWord, tailWord_3652028, baseEnd_3652028] using wordTrace_append hprefix tailTrace_3652028
  have hstable : (prefixWord ++ tailWord_3652028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3652028).length < 2 ^ (prefixWord ++ tailWord_3652028).sum := by decide
  have hdescent : baseEnd_3652028 < baseStart_3652028 := by decide
  rcases family_descends (prefixWord ++ tailWord_3652028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3652125 : List Nat := [1, 4, 2, 2, 1, 2, 2, 2, 1, 4, 2]
def baseStart_3652125 : Nat := 118140960795 + 3652125 * 2 ^ 59
def prefixEnd_3652125 : Nat := 4983230072969 + 3 ^ 40 * 3652125 * 2
def baseEnd_3652125 : Nat := 1875295535301628777841689

theorem tailTrace_3652125 : CollatzResearch.WordTrace tailWord_3652125 prefixEnd_3652125 1875295535301628777841689 := by
  unfold tailWord_3652125
  simp only [CollatzResearch.WordTrace]
  refine ⟨133203941893982333137165829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88802627929321555424777219 133203941893982333137165829)
  ·
    refine ⟨24975739105121687463218593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 133203941893982333137165829 24975739105121687463218593)
    ·
      refine ⟨18731804328841265597413945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24975739105121687463218593 18731804328841265597413945)
      ·
        refine ⟨14048853246630949198060459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18731804328841265597413945 14048853246630949198060459)
        ·
          refine ⟨21073279869946423797090689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14048853246630949198060459 21073279869946423797090689)
          ·
            refine ⟨15804959902459817847818017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21073279869946423797090689 15804959902459817847818017)
            ·
              refine ⟨11853719926844863385863513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15804959902459817847818017 11853719926844863385863513)
              ·
                refine ⟨8890289945133647539397635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11853719926844863385863513 8890289945133647539397635)
                ·
                  refine ⟨13335434917700471309096453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8890289945133647539397635 13335434917700471309096453)
                  ·
                    refine ⟨2500394047068838370455585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13335434917700471309096453 2500394047068838370455585)
                    ·
                      refine ⟨1875295535301628777841689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2500394047068838370455585 1875295535301628777841689)
                      ·
                        rfl

theorem cell23_3652125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 2, 2, 1, 4, 2].length) (baseStart_3652125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3652125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3652125 prefixEnd_3652125 := by exact prefixLift 3652125
  have htrace : WordTrace (prefixWord ++ tailWord_3652125) baseStart_3652125 baseEnd_3652125 := by
    simpa [prefixWord, tailWord_3652125, baseEnd_3652125] using wordTrace_append hprefix tailTrace_3652125
  have hstable : (prefixWord ++ tailWord_3652125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3652125).length < 2 ^ (prefixWord ++ tailWord_3652125).sum := by decide
  have hdescent : baseEnd_3652125 < baseStart_3652125 := by decide
  rcases family_descends (prefixWord ++ tailWord_3652125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3652138 : List Nat := [3, 1, 4, 1, 1, 2, 1, 2, 2, 2, 4]
def baseStart_3652138 : Nat := 118140960795 + 3652138 * 2 ^ 59
def prefixEnd_3652138 : Nat := 4983230072969 + 3 ^ 40 * 3652138 * 2
def baseEnd_3652138 : Nat := 1875302210550137226979129

theorem tailTrace_3652138 : CollatzResearch.WordTrace tailWord_3652138 prefixEnd_3652138 1875302210550137226979129 := by
  unfold tailWord_3652138
  simp only [CollatzResearch.WordTrace]
  refine ⟨33301104010733809089347267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88802944028623490904926045 33301104010733809089347267)
  ·
    refine ⟨49951656016100713634020901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33301104010733809089347267 49951656016100713634020901)
    ·
      refine ⟨9365935503018883806378919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 49951656016100713634020901 9365935503018883806378919)
      ·
        refine ⟨14048903254528325709568379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9365935503018883806378919 14048903254528325709568379)
        ·
          refine ⟨21073354881792488564352569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14048903254528325709568379 21073354881792488564352569)
          ·
            refine ⟨15805016161344366423264427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21073354881792488564352569 15805016161344366423264427)
            ·
              refine ⟨23707524242016549634896641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15805016161344366423264427 23707524242016549634896641)
              ·
                refine ⟨17780643181512412226172481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23707524242016549634896641 17780643181512412226172481)
                ·
                  refine ⟨13335482386134309169629361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17780643181512412226172481 13335482386134309169629361)
                  ·
                    refine ⟨10001611789600731877222021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13335482386134309169629361 10001611789600731877222021)
                    ·
                      refine ⟨1875302210550137226979129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10001611789600731877222021 1875302210550137226979129)
                      ·
                        rfl

theorem cell23_3652138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 1, 2, 2, 2, 4].length) (baseStart_3652138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3652138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3652138 prefixEnd_3652138 := by exact prefixLift 3652138
  have htrace : WordTrace (prefixWord ++ tailWord_3652138) baseStart_3652138 baseEnd_3652138 := by
    simpa [prefixWord, tailWord_3652138, baseEnd_3652138] using wordTrace_append hprefix tailTrace_3652138
  have hstable : (prefixWord ++ tailWord_3652138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3652138).length < 2 ^ (prefixWord ++ tailWord_3652138).sum := by decide
  have hdescent : baseEnd_3652138 < baseStart_3652138 := by decide
  rcases family_descends (prefixWord ++ tailWord_3652138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3652168 : List Nat := [2, 1, 3, 1, 1, 1, 1, 4, 2, 5, 2]
def baseStart_3652168 : Nat := 118140960795 + 3652168 * 2 ^ 59
def prefixEnd_3652168 : Nat := 4983230072969 + 3 ^ 40 * 3652168 * 2
def baseEnd_3652168 : Nat := 1875317614969772109603991

theorem tailTrace_3652168 : CollatzResearch.WordTrace tailWord_3652168 prefixEnd_3652168 1875317614969772109603991 := by
  unfold tailWord_3652168
  simp only [CollatzResearch.WordTrace]
  refine ⟨66602755116413275740490579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88803673488551034320654105 66602755116413275740490579)
  ·
    refine ⟨99904132674619913610735869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66602755116413275740490579 99904132674619913610735869)
    ·
      refine ⟨37464049752982467604025951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 99904132674619913610735869 37464049752982467604025951)
      ·
        refine ⟨56196074629473701406038927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37464049752982467604025951 56196074629473701406038927)
        ·
          refine ⟨84294111944210552109058391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56196074629473701406038927 84294111944210552109058391)
          ·
            refine ⟨126441167916315828163587587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84294111944210552109058391 126441167916315828163587587)
            ·
              refine ⟨189661751874473742245381381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 126441167916315828163587587 189661751874473742245381381)
              ·
                refine ⟨35561578476463826671009009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 189661751874473742245381381 35561578476463826671009009)
                ·
                  refine ⟨26671183857347870003256757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35561578476463826671009009 26671183857347870003256757)
                  ·
                    refine ⟨2500423486626362812805321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 26671183857347870003256757 2500423486626362812805321)
                    ·
                      refine ⟨1875317614969772109603991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2500423486626362812805321 1875317614969772109603991)
                      ·
                        rfl

theorem cell23_3652168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 4, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 4, 2, 5, 2].length) (baseStart_3652168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3652168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3652168 prefixEnd_3652168 := by exact prefixLift 3652168
  have htrace : WordTrace (prefixWord ++ tailWord_3652168) baseStart_3652168 baseEnd_3652168 := by
    simpa [prefixWord, tailWord_3652168, baseEnd_3652168] using wordTrace_append hprefix tailTrace_3652168
  have hstable : (prefixWord ++ tailWord_3652168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3652168).length < 2 ^ (prefixWord ++ tailWord_3652168).sum := by decide
  have hdescent : baseEnd_3652168 < baseStart_3652168 := by decide
  rcases family_descends (prefixWord ++ tailWord_3652168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3652178 : List Nat := [3, 2, 2, 1, 2, 1, 2, 3, 2, 5]
def baseStart_3652178 : Nat := 118140960795 + 3652178 * 2 ^ 59
def prefixEnd_3652178 : Nat := 4983230072969 + 3 ^ 40 * 3652178 * 2
def baseEnd_3652178 : Nat := 625107583258772356826315

theorem tailTrace_3652178 : CollatzResearch.WordTrace tailWord_3652178 prefixEnd_3652178 625107583258772356826315 := by
  unfold tailWord_3652178
  simp only [CollatzResearch.WordTrace]
  refine ⟨33301468740697580797211297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88803916641860215459230125 33301468740697580797211297)
  ·
    refine ⟨24976101555523185597908473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33301468740697580797211297 24976101555523185597908473)
    ·
      refine ⟨18732076166642389198431355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24976101555523185597908473 18732076166642389198431355)
      ·
        refine ⟨28098114249963583797647033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18732076166642389198431355 28098114249963583797647033)
        ·
          refine ⟨21073585687472687848235275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28098114249963583797647033 21073585687472687848235275)
          ·
            refine ⟨31610378531209031772352913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21073585687472687848235275 31610378531209031772352913)
            ·
              refine ⟨23707783898406773829264685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31610378531209031772352913 23707783898406773829264685)
              ·
                refine ⟨8890418961902540185974257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23707783898406773829264685 8890418961902540185974257)
                ·
                  refine ⟨6667814221426905139480693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8890418961902540185974257 6667814221426905139480693)
                  ·
                    refine ⟨625107583258772356826315, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6667814221426905139480693 625107583258772356826315)
                    ·
                      rfl

theorem cell23_3652178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 2, 3, 2, 5].length) (baseStart_3652178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3652178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3652178 prefixEnd_3652178 := by exact prefixLift 3652178
  have htrace : WordTrace (prefixWord ++ tailWord_3652178) baseStart_3652178 baseEnd_3652178 := by
    simpa [prefixWord, tailWord_3652178, baseEnd_3652178] using wordTrace_append hprefix tailTrace_3652178
  have hstable : (prefixWord ++ tailWord_3652178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3652178).length < 2 ^ (prefixWord ++ tailWord_3652178).sum := by decide
  have hdescent : baseEnd_3652178 < baseStart_3652178 := by decide
  rcases family_descends (prefixWord ++ tailWord_3652178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3652211 : List Nat := [1, 1, 1, 2, 2, 1, 1, 4, 2, 4, 4]
def baseStart_3652211 : Nat := 118140960795 + 3652211 * 2 ^ 59
def prefixEnd_3652211 : Nat := 4983230072969 + 3 ^ 40 * 3652211 * 2
def baseEnd_3652211 : Nat := 1875339694637915441366293

theorem tailTrace_3652211 : CollatzResearch.WordTrace tailWord_3652211 prefixEnd_3652211 1875339694637915441366293 := by
  unfold tailWord_3652211
  simp only [CollatzResearch.WordTrace]
  refine ⟨133207078571670769824796487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88804719047780513216530991 133207078571670769824796487)
  ·
    refine ⟨199810617857506154737194731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133207078571670769824796487 199810617857506154737194731)
    ·
      refine ⟨299715926786259232105792097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 199810617857506154737194731 299715926786259232105792097)
      ·
        refine ⟨224786945089694424079344073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 299715926786259232105792097 224786945089694424079344073)
        ·
          refine ⟨168590208817270818059508055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 224786945089694424079344073 168590208817270818059508055)
          ·
            refine ⟨252885313225906227089262083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 168590208817270818059508055 252885313225906227089262083)
            ·
              refine ⟨379327969838859340633893125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 252885313225906227089262083 379327969838859340633893125)
              ·
                refine ⟨71123994344786126368854961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 379327969838859340633893125 71123994344786126368854961)
                ·
                  refine ⟨53342995758589594776641221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 71123994344786126368854961 53342995758589594776641221)
                  ·
                    refine ⟨10001811704735549020620229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 53342995758589594776641221 10001811704735549020620229)
                    ·
                      refine ⟨1875339694637915441366293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10001811704735549020620229 1875339694637915441366293)
                      ·
                        rfl

theorem cell23_3652211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 4, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 4, 2, 4, 4].length) (baseStart_3652211 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3652211 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3652211 prefixEnd_3652211 := by exact prefixLift 3652211
  have htrace : WordTrace (prefixWord ++ tailWord_3652211) baseStart_3652211 baseEnd_3652211 := by
    simpa [prefixWord, tailWord_3652211, baseEnd_3652211] using wordTrace_append hprefix tailTrace_3652211
  have hstable : (prefixWord ++ tailWord_3652211).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3652211).length < 2 ^ (prefixWord ++ tailWord_3652211).sum := by decide
  have hdescent : baseEnd_3652211 < baseStart_3652211 := by decide
  rcases family_descends (prefixWord ++ tailWord_3652211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3652292 : List Nat := [2, 3, 3, 1, 1, 3, 1, 1, 1, 5, 2]
def baseStart_3652292 : Nat := 118140960795 + 3652292 * 2 ^ 59
def prefixEnd_3652292 : Nat := 4983230072969 + 3 ^ 40 * 3652292 * 2
def baseEnd_3652292 : Nat := 1875381286570929624453421

theorem tailTrace_3652292 : CollatzResearch.WordTrace tailWord_3652292 prefixEnd_3652292 1875381286570929624453421 := by
  unfold tailWord_3652292
  simp only [CollatzResearch.WordTrace]
  refine ⟨66605016442188660329247565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88806688589584880438996753 66605016442188660329247565)
  ·
    refine ⟨24976881165820747623467837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66605016442188660329247565 24976881165820747623467837)
    ·
      refine ⟨9366330437182780358800439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24976881165820747623467837 9366330437182780358800439)
      ·
        refine ⟨14049495655774170538200659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9366330437182780358800439 14049495655774170538200659)
        ·
          refine ⟨21074243483661255807300989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14049495655774170538200659 21074243483661255807300989)
          ·
            refine ⟨7902841306372970927737871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21074243483661255807300989 7902841306372970927737871)
            ·
              refine ⟨11854261959559456391606807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7902841306372970927737871 11854261959559456391606807)
              ·
                refine ⟨17781392939339184587410211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11854261959559456391606807 17781392939339184587410211)
                ·
                  refine ⟨26672089409008776881115317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17781392939339184587410211 26672089409008776881115317)
                  ·
                    refine ⟨2500508382094572832604561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 26672089409008776881115317 2500508382094572832604561)
                    ·
                      refine ⟨1875381286570929624453421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2500508382094572832604561 1875381286570929624453421)
                      ·
                        rfl

theorem cell23_3652292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 3, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 3, 1, 1, 1, 5, 2].length) (baseStart_3652292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3652292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3652292 prefixEnd_3652292 := by exact prefixLift 3652292
  have htrace : WordTrace (prefixWord ++ tailWord_3652292) baseStart_3652292 baseEnd_3652292 := by
    simpa [prefixWord, tailWord_3652292, baseEnd_3652292] using wordTrace_append hprefix tailTrace_3652292
  have hstable : (prefixWord ++ tailWord_3652292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3652292).length < 2 ^ (prefixWord ++ tailWord_3652292).sum := by decide
  have hdescent : baseEnd_3652292 < baseStart_3652292 := by decide
  rcases family_descends (prefixWord ++ tailWord_3652292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3652302 : List Nat := [4, 1, 1, 1, 3, 2, 4, 1, 1, 5]
def baseStart_3652302 : Nat := 118140960795 + 3652302 * 2 ^ 59
def prefixEnd_3652302 : Nat := 4983230072969 + 3 ^ 40 * 3652302 * 2
def baseEnd_3652302 : Nat := 625128807125824861776125

theorem tailTrace_3652302 : CollatzResearch.WordTrace tailWord_3652302 prefixEnd_3652302 625128807125824861776125 := by
  unfold tailWord_3652302
  simp only [CollatzResearch.WordTrace]
  refine ⟨16651299701792636545794895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 88806931742894061577572773 16651299701792636545794895)
  ·
    refine ⟨24976949552688954818692343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16651299701792636545794895 24976949552688954818692343)
    ·
      refine ⟨37465424329033432228038515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24976949552688954818692343 37465424329033432228038515)
      ·
        refine ⟨56198136493550148342057773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37465424329033432228038515 56198136493550148342057773)
        ·
          refine ⟨21074301185081305628271665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56198136493550148342057773 21074301185081305628271665)
          ·
            refine ⟨15805725888810979221203749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21074301185081305628271665 15805725888810979221203749)
            ·
              refine ⟨2963573604152058603975703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15805725888810979221203749 2963573604152058603975703)
              ·
                refine ⟨4445360406228087905963555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2963573604152058603975703 4445360406228087905963555)
                ·
                  refine ⟨6668040609342131858945333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4445360406228087905963555 6668040609342131858945333)
                  ·
                    refine ⟨625128807125824861776125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6668040609342131858945333 625128807125824861776125)
                    ·
                      rfl

theorem cell23_3652302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 4, 1, 1, 5].length) (baseStart_3652302 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3652302 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3652302 prefixEnd_3652302 := by exact prefixLift 3652302
  have htrace : WordTrace (prefixWord ++ tailWord_3652302) baseStart_3652302 baseEnd_3652302 := by
    simpa [prefixWord, tailWord_3652302, baseEnd_3652302] using wordTrace_append hprefix tailTrace_3652302
  have hstable : (prefixWord ++ tailWord_3652302).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3652302).length < 2 ^ (prefixWord ++ tailWord_3652302).sum := by decide
  have hdescent : baseEnd_3652302 < baseStart_3652302 := by decide
  rcases family_descends (prefixWord ++ tailWord_3652302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3652305 : List Nat := [1, 2, 2, 1, 2, 3, 3, 3, 1, 1, 4]
def baseStart_3652305 : Nat := 118140960795 + 3652305 * 2 ^ 59
def prefixEnd_3652305 : Nat := 4983230072969 + 3 ^ 40 * 3652305 * 2
def baseEnd_3652305 : Nat := 1875387961819438073590861

theorem tailTrace_3652305 : CollatzResearch.WordTrace tailWord_3652305 prefixEnd_3652305 1875387961819438073590861 := by
  unfold tailWord_3652305
  simp only [CollatzResearch.WordTrace]
  refine ⟨133210507033330223878718369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88807004688886815919145579 133210507033330223878718369)
  ·
    refine ⟨99907880274997667909038777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133210507033330223878718369 99907880274997667909038777)
    ·
      refine ⟨74930910206248250931779083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99907880274997667909038777 74930910206248250931779083)
      ·
        refine ⟨112396365309372376397668625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74930910206248250931779083 112396365309372376397668625)
        ·
          refine ⟨84297273982029282298251469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 112396365309372376397668625 84297273982029282298251469)
          ·
            refine ⟨31611477743260980861844301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 84297273982029282298251469 31611477743260980861844301)
            ·
              refine ⟨11854304153722867823191613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31611477743260980861844301 11854304153722867823191613)
              ·
                refine ⟨4445364057646075433696855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11854304153722867823191613 4445364057646075433696855)
                ·
                  refine ⟨6668046086469113150545283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4445364057646075433696855 6668046086469113150545283)
                  ·
                    refine ⟨10002069129703669725817925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6668046086469113150545283 10002069129703669725817925)
                    ·
                      refine ⟨1875387961819438073590861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10002069129703669725817925 1875387961819438073590861)
                      ·
                        rfl

theorem cell23_3652305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 3, 3, 1, 1, 4].length) (baseStart_3652305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3652305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3652305 prefixEnd_3652305 := by exact prefixLift 3652305
  have htrace : WordTrace (prefixWord ++ tailWord_3652305) baseStart_3652305 baseEnd_3652305 := by
    simpa [prefixWord, tailWord_3652305, baseEnd_3652305] using wordTrace_append hprefix tailTrace_3652305
  have hstable : (prefixWord ++ tailWord_3652305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3652305).length < 2 ^ (prefixWord ++ tailWord_3652305).sum := by decide
  have hdescent : baseEnd_3652305 < baseStart_3652305 := by decide
  rcases family_descends (prefixWord ++ tailWord_3652305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3652316 : List Nat := [2, 2, 5, 1, 1, 1, 2, 4, 1, 1, 3]
def baseStart_3652316 : Nat := 118140960795 + 3652316 * 2 ^ 59
def prefixEnd_3652316 : Nat := 4983230072969 + 3 ^ 40 * 3652316 * 2
def baseEnd_3652316 : Nat := 1875393610106637530553311

theorem tailTrace_3652316 : CollatzResearch.WordTrace tailWord_3652316 prefixEnd_3652316 1875393610106637530553311 := by
  unfold tailWord_3652316
  simp only [CollatzResearch.WordTrace]
  refine ⟨66605454118145186378684401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88807272157526915171579201 66605454118145186378684401)
  ·
    refine ⟨49954090588608889784013301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66605454118145186378684401 49954090588608889784013301)
    ·
      refine ⟨4683195992682083417251247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 49954090588608889784013301 4683195992682083417251247)
      ·
        refine ⟨7024793989023125125876871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4683195992682083417251247 7024793989023125125876871)
        ·
          refine ⟨10537190983534687688815307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7024793989023125125876871 10537190983534687688815307)
          ·
            refine ⟨15805786475302031533222961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10537190983534687688815307 15805786475302031533222961)
            ·
              refine ⟨11854339856476523649917221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15805786475302031533222961 11854339856476523649917221)
              ·
                refine ⟨2222688723089348184359479, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11854339856476523649917221 2222688723089348184359479)
                ·
                  refine ⟨3334033084634022276539219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2222688723089348184359479 3334033084634022276539219)
                  ·
                    refine ⟨5001049626951033414808829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3334033084634022276539219 5001049626951033414808829)
                    ·
                      refine ⟨1875393610106637530553311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5001049626951033414808829 1875393610106637530553311)
                      ·
                        rfl

theorem cell23_3652316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 2, 4, 1, 1, 3].length) (baseStart_3652316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3652316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3652316 prefixEnd_3652316 := by exact prefixLift 3652316
  have htrace : WordTrace (prefixWord ++ tailWord_3652316) baseStart_3652316 baseEnd_3652316 := by
    simpa [prefixWord, tailWord_3652316, baseEnd_3652316] using wordTrace_append hprefix tailTrace_3652316
  have hstable : (prefixWord ++ tailWord_3652316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3652316).length < 2 ^ (prefixWord ++ tailWord_3652316).sum := by decide
  have hdescent : baseEnd_3652316 < baseStart_3652316 := by decide
  rcases family_descends (prefixWord ++ tailWord_3652316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3652325 : List Nat := [1, 3, 1, 4, 1, 3, 1, 2, 1, 1, 5]
def baseStart_3652325 : Nat := 118140960795 + 3652325 * 2 ^ 59
def prefixEnd_3652325 : Nat := 4983230072969 + 3 ^ 40 * 3652325 * 2
def baseEnd_3652325 : Nat := 1875398231432527995340769

theorem tailTrace_3652325 : CollatzResearch.WordTrace tailWord_3652325 prefixEnd_3652325 1875398231432527995340769 := by
  unfold tailWord_3652325
  simp only [CollatzResearch.WordTrace]
  refine ⟨133211236493257767294446429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88807490995505178196297619 133211236493257767294446429)
  ·
    refine ⟨49954213684971662735417411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 133211236493257767294446429 49954213684971662735417411)
    ·
      refine ⟨74931320527457494103126117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49954213684971662735417411 74931320527457494103126117)
      ·
        refine ⟨14049622598898280144336147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 74931320527457494103126117 14049622598898280144336147)
        ·
          refine ⟨21074433898347420216504221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14049622598898280144336147 21074433898347420216504221)
          ·
            refine ⟨7902912711880282581189083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21074433898347420216504221 7902912711880282581189083)
            ·
              refine ⟨11854369067820423871783625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7902912711880282581189083 11854369067820423871783625)
              ·
                refine ⟨8890776800865317903837719, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11854369067820423871783625 8890776800865317903837719)
                ·
                  refine ⟨13336165201297976855756579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8890776800865317903837719 13336165201297976855756579)
                  ·
                    refine ⟨20004247801946965283634869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13336165201297976855756579 20004247801946965283634869)
                    ·
                      refine ⟨1875398231432527995340769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20004247801946965283634869 1875398231432527995340769)
                      ·
                        rfl

theorem cell23_3652325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 3, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 3, 1, 2, 1, 1, 5].length) (baseStart_3652325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3652325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3652325 prefixEnd_3652325 := by exact prefixLift 3652325
  have htrace : WordTrace (prefixWord ++ tailWord_3652325) baseStart_3652325 baseEnd_3652325 := by
    simpa [prefixWord, tailWord_3652325, baseEnd_3652325] using wordTrace_append hprefix tailTrace_3652325
  have hstable : (prefixWord ++ tailWord_3652325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3652325).length < 2 ^ (prefixWord ++ tailWord_3652325).sum := by decide
  have hdescent : baseEnd_3652325 < baseStart_3652325 := by decide
  rcases family_descends (prefixWord ++ tailWord_3652325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3652335 : List Nat := [1, 1, 2, 1, 5, 2, 3, 1, 1, 2, 4]
def baseStart_3652335 : Nat := 118140960795 + 3652335 * 2 ^ 59
def prefixEnd_3652335 : Nat := 4983230072969 + 3 ^ 40 * 3652335 * 2
def baseEnd_3652335 : Nat := 1875403366239072956215723

theorem tailTrace_3652335 : CollatzResearch.WordTrace tailWord_3652335 prefixEnd_3652335 1875403366239072956215723 := by
  unfold tailWord_3652335
  simp only [CollatzResearch.WordTrace]
  refine ⟨133211601223221539002310459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88807734148814359334873639 133211601223221539002310459)
  ·
    refine ⟨199817401834832308503465689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133211601223221539002310459 199817401834832308503465689)
    ·
      refine ⟨149863051376124231377599267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 199817401834832308503465689 149863051376124231377599267)
      ·
        refine ⟨224794577064186347066398901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149863051376124231377599267 224794577064186347066398901)
        ·
          refine ⟨21074491599767470037474897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 224794577064186347066398901 21074491599767470037474897)
          ·
            refine ⟨15805868699825602528106173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21074491599767470037474897 15805868699825602528106173)
            ·
              refine ⟨5927200762434600948039815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15805868699825602528106173 5927200762434600948039815)
              ·
                refine ⟨8890801143651901422059723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5927200762434600948039815 8890801143651901422059723)
                ·
                  refine ⟨13336201715477852133089585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8890801143651901422059723 13336201715477852133089585)
                  ·
                    refine ⟨10002151286608389099817189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13336201715477852133089585 10002151286608389099817189)
                    ·
                      refine ⟨1875403366239072956215723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10002151286608389099817189 1875403366239072956215723)
                      ·
                        rfl

theorem cell23_3652335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 3, 1, 1, 2, 4].length) (baseStart_3652335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3652335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3652335 prefixEnd_3652335 := by exact prefixLift 3652335
  have htrace : WordTrace (prefixWord ++ tailWord_3652335) baseStart_3652335 baseEnd_3652335 := by
    simpa [prefixWord, tailWord_3652335, baseEnd_3652335] using wordTrace_append hprefix tailTrace_3652335
  have hstable : (prefixWord ++ tailWord_3652335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3652335).length < 2 ^ (prefixWord ++ tailWord_3652335).sum := by decide
  have hdescent : baseEnd_3652335 < baseStart_3652335 := by decide
  rcases family_descends (prefixWord ++ tailWord_3652335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3652415 : List Nat := [1, 1, 2, 2, 5, 1, 2, 1, 2, 1, 5]
def baseStart_3652415 : Nat := 118140960795 + 3652415 * 2 ^ 59
def prefixEnd_3652415 : Nat := 4983230072969 + 3 ^ 40 * 3652415 * 2
def baseEnd_3652415 : Nat := 1875444444691432643215355

theorem tailTrace_3652415 : CollatzResearch.WordTrace tailWord_3652415 prefixEnd_3652415 1875444444691432643215355 := by
  unfold tailWord_3652415
  simp only [CollatzResearch.WordTrace]
  refine ⟨133214519062931712665222699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88809679375287808443481799 133214519062931712665222699)
  ·
    refine ⟨199821778594397568997834049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133214519062931712665222699 199821778594397568997834049)
    ·
      refine ⟨149866333945798176748375537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 199821778594397568997834049 149866333945798176748375537)
      ·
        refine ⟨112399750459348632561281653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 149866333945798176748375537 112399750459348632561281653)
        ·
          refine ⟨10537476605563934302620155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 112399750459348632561281653 10537476605563934302620155)
          ·
            refine ⟨15806214908345901453930233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10537476605563934302620155 15806214908345901453930233)
            ·
              refine ⟨11854661181259426090447675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15806214908345901453930233 11854661181259426090447675)
              ·
                refine ⟨17781991771889139135671513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11854661181259426090447675 17781991771889139135671513)
                ·
                  refine ⟨13336493828916854351753635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17781991771889139135671513 13336493828916854351753635)
                  ·
                    refine ⟨20004740743375281527630453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13336493828916854351753635 20004740743375281527630453)
                    ·
                      refine ⟨1875444444691432643215355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20004740743375281527630453 1875444444691432643215355)
                      ·
                        rfl

theorem cell23_3652415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 2, 1, 2, 1, 5].length) (baseStart_3652415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3652415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3652415 prefixEnd_3652415 := by exact prefixLift 3652415
  have htrace : WordTrace (prefixWord ++ tailWord_3652415) baseStart_3652415 baseEnd_3652415 := by
    simpa [prefixWord, tailWord_3652415, baseEnd_3652415] using wordTrace_append hprefix tailTrace_3652415
  have hstable : (prefixWord ++ tailWord_3652415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3652415).length < 2 ^ (prefixWord ++ tailWord_3652415).sum := by decide
  have hdescent : baseEnd_3652415 < baseStart_3652415 := by decide
  rcases family_descends (prefixWord ++ tailWord_3652415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3652465 : List Nat := [1, 2, 2, 2, 1, 5, 1, 1, 1, 7]
def baseStart_3652465 : Nat := 118140960795 + 3652465 * 2 ^ 59
def prefixEnd_3652465 : Nat := 4983230072969 + 3 ^ 40 * 3652465 * 2
def baseEnd_3652465 : Nat := 625156706241385815863375

theorem tailTrace_3652465 : CollatzResearch.WordTrace tailWord_3652465 prefixEnd_3652465 625156706241385815863375 := by
  unfold tailWord_3652465
  simp only [CollatzResearch.WordTrace]
  refine ⟨133216342712750571204542849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88810895141833714136361899 133216342712750571204542849)
  ·
    refine ⟨99912257034562928403407137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133216342712750571204542849 99912257034562928403407137)
    ·
      refine ⟨74934192775922196302555353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99912257034562928403407137 74934192775922196302555353)
      ·
        refine ⟨56200644581941647226916515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74934192775922196302555353 56200644581941647226916515)
        ·
          refine ⟨84300966872912470840374773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56200644581941647226916515 84300966872912470840374773)
          ·
            refine ⟨7903215644335544141285135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 84300966872912470840374773 7903215644335544141285135)
            ·
              refine ⟨11854823466503316211927703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7903215644335544141285135 11854823466503316211927703)
              ·
                refine ⟨17782235199754974317891555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11854823466503316211927703 17782235199754974317891555)
                ·
                  refine ⟨26673352799632461476837333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17782235199754974317891555 26673352799632461476837333)
                  ·
                    refine ⟨625156706241385815863375, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 26673352799632461476837333 625156706241385815863375)
                    ·
                      rfl

theorem cell23_3652465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 5, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 5, 1, 1, 1, 7].length) (baseStart_3652465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3652465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3652465 prefixEnd_3652465 := by exact prefixLift 3652465
  have htrace : WordTrace (prefixWord ++ tailWord_3652465) baseStart_3652465 baseEnd_3652465 := by
    simpa [prefixWord, tailWord_3652465, baseEnd_3652465] using wordTrace_append hprefix tailTrace_3652465
  have hstable : (prefixWord ++ tailWord_3652465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3652465).length < 2 ^ (prefixWord ++ tailWord_3652465).sum := by decide
  have hdescent : baseEnd_3652465 < baseStart_3652465 := by decide
  rcases family_descends (prefixWord ++ tailWord_3652465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3652469 : List Nat := [1, 3, 4, 1, 1, 3, 2, 3, 5]
def baseStart_3652469 : Nat := 118140960795 + 3652469 * 2 ^ 59
def prefixEnd_3652469 : Nat := 4983230072969 + 3 ^ 40 * 3652469 * 2
def baseEnd_3652469 : Nat := 208385796960752825771123

theorem tailTrace_3652469 : CollatzResearch.WordTrace tailWord_3652469 prefixEnd_3652469 208385796960752825771123 := by
  unfold tailWord_3652469
  simp only [CollatzResearch.WordTrace]
  refine ⟨133216488604736079887688461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88810992403157386591792307 133216488604736079887688461)
  ·
    refine ⟨49956183226776029957883173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 133216488604736079887688461 49956183226776029957883173)
    ·
      refine ⟨9366784355020505617103095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 49956183226776029957883173 9366784355020505617103095)
      ·
        refine ⟨14050176532530758425654643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9366784355020505617103095 14050176532530758425654643)
        ·
          refine ⟨21075264798796137638481965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14050176532530758425654643 21075264798796137638481965)
          ·
            refine ⟨7903224299548551614430737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21075264798796137638481965 7903224299548551614430737)
            ·
              refine ⟨5927418224661413710823053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7903224299548551614430737 5927418224661413710823053)
              ·
                refine ⟨2222781834248030141558645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5927418224661413710823053 2222781834248030141558645)
                ·
                  refine ⟨208385796960752825771123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2222781834248030141558645 208385796960752825771123)
                  ·
                    rfl

theorem cell23_3652469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 3, 2, 3, 5].length) (baseStart_3652469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3652469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3652469 prefixEnd_3652469 := by exact prefixLift 3652469
  have htrace : WordTrace (prefixWord ++ tailWord_3652469) baseStart_3652469 baseEnd_3652469 := by
    simpa [prefixWord, tailWord_3652469, baseEnd_3652469] using wordTrace_append hprefix tailTrace_3652469
  have hstable : (prefixWord ++ tailWord_3652469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3652469).length < 2 ^ (prefixWord ++ tailWord_3652469).sum := by decide
  have hdescent : baseEnd_3652469 < baseStart_3652469 := by decide
  rcases family_descends (prefixWord ++ tailWord_3652469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3652512 : List Nat := [2, 1, 1, 4, 1, 1, 4, 2, 3, 4]
def baseStart_3652512 : Nat := 118140960795 + 3652512 * 2 ^ 59
def prefixEnd_3652512 : Nat := 4983230072969 + 3 ^ 40 * 3652512 * 2
def baseEnd_3652512 : Nat := 625164750771639587900803

theorem tailTrace_3652512 : CollatzResearch.WordTrace tailWord_3652512 prefixEnd_3652512 625164750771639587900803 := by
  unfold tailWord_3652512
  simp only [CollatzResearch.WordTrace]
  refine ⟨66609028471790149115751895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88812037962386865487669193 66609028471790149115751895)
  ·
    refine ⟨99913542707685223673627843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66609028471790149115751895 99913542707685223673627843)
    ·
      refine ⟨149870314061527835510441765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99913542707685223673627843 149870314061527835510441765)
      ·
        refine ⟨28100683886536469158207831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 149870314061527835510441765 28100683886536469158207831)
        ·
          refine ⟨42151025829804703737311747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28100683886536469158207831 42151025829804703737311747)
          ·
            refine ⟨63226538744707055605967621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42151025829804703737311747 63226538744707055605967621)
            ·
              refine ⟨11854976014632572926118929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 63226538744707055605967621 11854976014632572926118929)
              ·
                refine ⟨8891232010974429694589197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11854976014632572926118929 8891232010974429694589197)
                ·
                  refine ⟨3334212004115411135470949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8891232010974429694589197 3334212004115411135470949)
                  ·
                    refine ⟨625164750771639587900803, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3334212004115411135470949 625164750771639587900803)
                    ·
                      rfl

theorem cell23_3652512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 4, 2, 3, 4].length) (baseStart_3652512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3652512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3652512 prefixEnd_3652512 := by exact prefixLift 3652512
  have htrace : WordTrace (prefixWord ++ tailWord_3652512) baseStart_3652512 baseEnd_3652512 := by
    simpa [prefixWord, tailWord_3652512, baseEnd_3652512] using wordTrace_append hprefix tailTrace_3652512
  have hstable : (prefixWord ++ tailWord_3652512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3652512).length < 2 ^ (prefixWord ++ tailWord_3652512).sum := by decide
  have hdescent : baseEnd_3652512 < baseStart_3652512 := by decide
  rcases family_descends (prefixWord ++ tailWord_3652512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3652542 : List Nat := [4, 2, 1, 1, 1, 2, 2, 4, 6]
def baseStart_3652542 : Nat := 118140960795 + 3652542 * 2 ^ 59
def prefixEnd_3652542 : Nat := 4983230072969 + 3 ^ 40 * 3652542 * 2
def baseEnd_3652542 : Nat := 208389961859394849591919

theorem tailTrace_3652542 : CollatzResearch.WordTrace tailWord_3652542 prefixEnd_3652542 208389961859394849591919 := by
  unfold tailWord_3652542
  simp only [CollatzResearch.WordTrace]
  refine ⟨16652393891683951669386985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 88812767422314408903397253 16652393891683951669386985)
  ·
    refine ⟨12489295418762963752040239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16652393891683951669386985 12489295418762963752040239)
    ·
      refine ⟨18733943128144445628060359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12489295418762963752040239 18733943128144445628060359)
      ·
        refine ⟨28100914692216668442090539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18733943128144445628060359 28100914692216668442090539)
        ·
          refine ⟨42151372038325002663135809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28100914692216668442090539 42151372038325002663135809)
          ·
            refine ⟨31613529028743751997351857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42151372038325002663135809 31613529028743751997351857)
            ·
              refine ⟨23710146771557813998013893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31613529028743751997351857 23710146771557813998013893)
              ·
                refine ⟨4445652519667090124627605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23710146771557813998013893 4445652519667090124627605)
                ·
                  refine ⟨208389961859394849591919, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4445652519667090124627605 208389961859394849591919)
                  ·
                    rfl

theorem cell23_3652542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 2, 4, 6].length) (baseStart_3652542 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3652542 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3652542 prefixEnd_3652542 := by exact prefixLift 3652542
  have htrace : WordTrace (prefixWord ++ tailWord_3652542) baseStart_3652542 baseEnd_3652542 := by
    simpa [prefixWord, tailWord_3652542, baseEnd_3652542] using wordTrace_append hprefix tailTrace_3652542
  have hstable : (prefixWord ++ tailWord_3652542).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3652542).length < 2 ^ (prefixWord ++ tailWord_3652542).sum := by decide
  have hdescent : baseEnd_3652542 < baseStart_3652542 := by decide
  rcases family_descends (prefixWord ++ tailWord_3652542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3652559 : List Nat := [1, 1, 2, 1, 1, 8, 2, 1, 6]
def baseStart_3652559 : Nat := 118140960795 + 3652559 * 2 ^ 59
def prefixEnd_3652559 : Nat := 4983230072969 + 3 ^ 40 * 3652559 * 2
def baseEnd_3652559 : Nat := 208390931767297786646077

theorem tailTrace_3652559 : CollatzResearch.WordTrace tailWord_3652559 prefixEnd_3652559 208390931767297786646077 := by
  unfold tailWord_3652559
  simp only [CollatzResearch.WordTrace]
  refine ⟨133219771174410025258464731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88813180782940016838976487 133219771174410025258464731)
  ·
    refine ⟨199829656761615037887697097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133219771174410025258464731 199829656761615037887697097)
    ·
      refine ⟨149872242571211278415772823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 199829656761615037887697097 149872242571211278415772823)
      ·
        refine ⟨224808363856816917623659235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149872242571211278415772823 224808363856816917623659235)
        ·
          refine ⟨337212545785225376435488853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 224808363856816917623659235 337212545785225376435488853)
          ·
            refine ⟨3951709520920609880103385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 337212545785225376435488853 3951709520920609880103385)
            ·
              refine ⟨2963782140690457410077539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3951709520920609880103385 2963782140690457410077539)
              ·
                refine ⟨4445673211035686115116309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2963782140690457410077539 4445673211035686115116309)
                ·
                  refine ⟨208390931767297786646077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4445673211035686115116309 208390931767297786646077)
                  ·
                    rfl

theorem cell23_3652559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 8, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 8, 2, 1, 6].length) (baseStart_3652559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3652559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3652559 prefixEnd_3652559 := by exact prefixLift 3652559
  have htrace : WordTrace (prefixWord ++ tailWord_3652559) baseStart_3652559 baseEnd_3652559 := by
    simpa [prefixWord, tailWord_3652559, baseEnd_3652559] using wordTrace_append hprefix tailTrace_3652559
  have hstable : (prefixWord ++ tailWord_3652559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3652559).length < 2 ^ (prefixWord ++ tailWord_3652559).sum := by decide
  have hdescent : baseEnd_3652559 < baseStart_3652559 := by decide
  rcases family_descends (prefixWord ++ tailWord_3652559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3652597 : List Nat := [1, 3, 5, 2, 1, 2, 2, 2, 1, 4]
def baseStart_3652597 : Nat := 118140960795 + 3652597 * 2 ^ 59
def prefixEnd_3652597 : Nat := 4983230072969 + 3 ^ 40 * 3652597 * 2
def baseEnd_3652597 : Nat := 625179299390183643713173

theorem tailTrace_3652597 : CollatzResearch.WordTrace tailWord_3652597 prefixEnd_3652597 625179299390183643713173 := by
  unfold tailWord_3652597
  simp only [CollatzResearch.WordTrace]
  refine ⟨133221157148272357748348045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88814104765514905165565363 133221157148272357748348045)
  ·
    refine ⟨49957933930602134155630517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 133221157148272357748348045 49957933930602134155630517)
    ·
      refine ⟨4683556305993950077090361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 49957933930602134155630517 4683556305993950077090361)
      ·
        refine ⟨3512667229495462557817771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4683556305993950077090361 3512667229495462557817771)
        ·
          refine ⟨5269000844243193836726657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3512667229495462557817771 5269000844243193836726657)
          ·
            refine ⟨3951750633182395377544993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5269000844243193836726657 3951750633182395377544993)
            ·
              refine ⟨2963812974886796533158745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3951750633182395377544993 2963812974886796533158745)
              ·
                refine ⟨2222859731165097399869059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2963812974886796533158745 2222859731165097399869059)
                ·
                  refine ⟨3334289596747646099803589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2222859731165097399869059 3334289596747646099803589)
                  ·
                    refine ⟨625179299390183643713173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3334289596747646099803589 625179299390183643713173)
                    ·
                      rfl

theorem cell23_3652597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 2, 2, 2, 1, 4].length) (baseStart_3652597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3652597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3652597 prefixEnd_3652597 := by exact prefixLift 3652597
  have htrace : WordTrace (prefixWord ++ tailWord_3652597) baseStart_3652597 baseEnd_3652597 := by
    simpa [prefixWord, tailWord_3652597, baseEnd_3652597] using wordTrace_append hprefix tailTrace_3652597
  have hstable : (prefixWord ++ tailWord_3652597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3652597).length < 2 ^ (prefixWord ++ tailWord_3652597).sum := by decide
  have hdescent : baseEnd_3652597 < baseStart_3652597 := by decide
  rcases family_descends (prefixWord ++ tailWord_3652597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3652602 : List Nat := [3, 1, 1, 1, 1, 2, 1, 5, 4, 4]
def baseStart_3652602 : Nat := 118140960795 + 3652602 * 2 ^ 59
def prefixEnd_3652602 : Nat := 4983230072969 + 3 ^ 40 * 3652602 * 2
def baseEnd_3652602 : Nat := 625180155191274470525665

theorem tailTrace_3652602 : CollatzResearch.WordTrace tailWord_3652602 prefixEnd_3652602 625180155191274470525665 := by
  unfold tailWord_3652602
  simp only [CollatzResearch.WordTrace]
  refine ⟨33305334878313560900570015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88814226342169495734853373 33305334878313560900570015)
  ·
    refine ⟨49958002317470341350855023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33305334878313560900570015 49958002317470341350855023)
    ·
      refine ⟨74937003476205512026282535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49958002317470341350855023 74937003476205512026282535)
      ·
        refine ⟨112405505214308268039423803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74937003476205512026282535 112405505214308268039423803)
        ·
          refine ⟨168608257821462402059135705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112405505214308268039423803 168608257821462402059135705)
          ·
            refine ⟨126456193366096801544351779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 168608257821462402059135705 126456193366096801544351779)
            ·
              refine ⟨189684290049145202316527669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 126456193366096801544351779 189684290049145202316527669)
              ·
                refine ⟨17782902192107362717174469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 189684290049145202316527669 17782902192107362717174469)
                ·
                  refine ⟨3334294161020130509470213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17782902192107362717174469 3334294161020130509470213)
                  ·
                    refine ⟨625180155191274470525665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3334294161020130509470213 625180155191274470525665)
                    ·
                      rfl

theorem cell23_3652602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 5, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 5, 4, 4].length) (baseStart_3652602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3652602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3652602 prefixEnd_3652602 := by exact prefixLift 3652602
  have htrace : WordTrace (prefixWord ++ tailWord_3652602) baseStart_3652602 baseEnd_3652602 := by
    simpa [prefixWord, tailWord_3652602, baseEnd_3652602] using wordTrace_append hprefix tailTrace_3652602
  have hstable : (prefixWord ++ tailWord_3652602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3652602).length < 2 ^ (prefixWord ++ tailWord_3652602).sum := by decide
  have hdescent : baseEnd_3652602 < baseStart_3652602 := by decide
  rcases family_descends (prefixWord ++ tailWord_3652602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3652619 : List Nat := [1, 1, 1, 1, 6, 2, 2, 3, 2, 4]
def baseStart_3652619 : Nat := 118140960795 + 3652619 * 2 ^ 59
def prefixEnd_3652619 : Nat := 4983230072969 + 3 ^ 40 * 3652619 * 2
def baseEnd_3652619 : Nat := 625183064914983281688139

theorem tailTrace_3652619 : CollatzResearch.WordTrace tailWord_3652619 prefixEnd_3652619 625183064914983281688139 := by
  unfold tailWord_3652619
  simp only [CollatzResearch.WordTrace]
  refine ⟨133221959554192655505648911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88814639702795103670432607 133221959554192655505648911)
  ·
    refine ⟨199832939331288983258473367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133221959554192655505648911 199832939331288983258473367)
    ·
      refine ⟨299749408996933474887710051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 199832939331288983258473367 299749408996933474887710051)
      ·
        refine ⟨449624113495400212331565077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 299749408996933474887710051 449624113495400212331565077)
        ·
          refine ⟨21076130320096884953042113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 449624113495400212331565077 21076130320096884953042113)
          ·
            refine ⟨15807097740072663714781585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21076130320096884953042113 15807097740072663714781585)
            ·
              refine ⟨11855323305054497786086189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15807097740072663714781585 11855323305054497786086189)
              ·
                refine ⟨4445746239395436669782321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11855323305054497786086189 4445746239395436669782321)
                ·
                  refine ⟨3334309679546577502336741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4445746239395436669782321 3334309679546577502336741)
                  ·
                    refine ⟨625183064914983281688139, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3334309679546577502336741 625183064914983281688139)
                    ·
                      rfl

theorem cell23_3652619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 2, 3, 2, 4].length) (baseStart_3652619 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3652619 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3652619 prefixEnd_3652619 := by exact prefixLift 3652619
  have htrace : WordTrace (prefixWord ++ tailWord_3652619) baseStart_3652619 baseEnd_3652619 := by
    simpa [prefixWord, tailWord_3652619, baseEnd_3652619] using wordTrace_append hprefix tailTrace_3652619
  have hstable : (prefixWord ++ tailWord_3652619).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3652619).length < 2 ^ (prefixWord ++ tailWord_3652619).sum := by decide
  have hdescent : baseEnd_3652619 < baseStart_3652619 := by decide
  rcases family_descends (prefixWord ++ tailWord_3652619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3652625 : List Nat := [1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 7]
def baseStart_3652625 : Nat := 118140960795 + 3652625 * 2 ^ 59
def prefixEnd_3652625 : Nat := 4983230072969 + 3 ^ 40 * 3652625 * 2
def baseEnd_3652625 : Nat := 1875552275628876821589389

theorem tailTrace_3652625 : CollatzResearch.WordTrace tailWord_3652625 prefixEnd_3652625 1875552275628876821589389 := by
  unfold tailWord_3652625
  simp only [CollatzResearch.WordTrace]
  refine ⟨133222178392170918530367329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88814785594780612353578219 133222178392170918530367329)
  ·
    refine ⟨99916633794128188897775497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133222178392170918530367329 99916633794128188897775497)
    ·
      refine ⟨74937475345596141673331623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99916633794128188897775497 74937475345596141673331623)
      ·
        refine ⟨112406213018394212509997435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74937475345596141673331623 112406213018394212509997435)
        ·
          refine ⟨168609319527591318764996153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112406213018394212509997435 168609319527591318764996153)
          ·
            refine ⟨126456989645693489073747115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 168609319527591318764996153 126456989645693489073747115)
            ·
              refine ⟨189685484468540233610620673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 126456989645693489073747115 189685484468540233610620673)
              ·
                refine ⟨142264113351405175207965505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 189685484468540233610620673 142264113351405175207965505)
                ·
                  refine ⟨106698085013553881405974129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 142264113351405175207965505 106698085013553881405974129)
                  ·
                    refine ⟨80023563760165411054480597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 106698085013553881405974129 80023563760165411054480597)
                    ·
                      refine ⟨1875552275628876821589389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 80023563760165411054480597 1875552275628876821589389)
                      ·
                        rfl

theorem cell23_3652625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 7].length) (baseStart_3652625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3652625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3652625 prefixEnd_3652625 := by exact prefixLift 3652625
  have htrace : WordTrace (prefixWord ++ tailWord_3652625) baseStart_3652625 baseEnd_3652625 := by
    simpa [prefixWord, tailWord_3652625, baseEnd_3652625] using wordTrace_append hprefix tailTrace_3652625
  have hstable : (prefixWord ++ tailWord_3652625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3652625).length < 2 ^ (prefixWord ++ tailWord_3652625).sum := by decide
  have hdescent : baseEnd_3652625 < baseStart_3652625 := by decide
  rcases family_descends (prefixWord ++ tailWord_3652625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3652629 : List Nat := [1, 3, 2, 1, 4, 1, 2, 1, 3, 2, 3]
def baseStart_3652629 : Nat := 118140960795 + 3652629 * 2 ^ 59
def prefixEnd_3652629 : Nat := 4983230072969 + 3 ^ 40 * 3652629 * 2
def baseEnd_3652629 : Nat := 1875554329551494805939371

theorem tailTrace_3652629 : CollatzResearch.WordTrace tailWord_3652629 prefixEnd_3652629 1875554329551494805939371 := by
  unfold tailWord_3652629
  simp only [CollatzResearch.WordTrace]
  refine ⟨133222324284156427213512941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88814882856104284809008627 133222324284156427213512941)
  ·
    refine ⟨49958371606558660205067353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 133222324284156427213512941 49958371606558660205067353)
    ·
      refine ⟨37468778704918995153800515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49958371606558660205067353 37468778704918995153800515)
      ·
        refine ⟨56203168057378492730700773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37468778704918995153800515 56203168057378492730700773)
        ·
          refine ⟨10538094010758467387006395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 56203168057378492730700773 10538094010758467387006395)
          ·
            refine ⟨15807141016137701080509593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10538094010758467387006395 15807141016137701080509593)
            ·
              refine ⟨11855355762103275810382195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15807141016137701080509593 11855355762103275810382195)
              ·
                refine ⟨17783033643154913715573293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11855355762103275810382195 17783033643154913715573293)
                ·
                  refine ⟨6668637616183092643339985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17783033643154913715573293 6668637616183092643339985)
                  ·
                    refine ⟨5001478212137319482504989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6668637616183092643339985 5001478212137319482504989)
                    ·
                      refine ⟨1875554329551494805939371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5001478212137319482504989 1875554329551494805939371)
                      ·
                        rfl

theorem cell23_3652629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 2, 1, 3, 2, 3].length) (baseStart_3652629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3652629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3652629 prefixEnd_3652629 := by exact prefixLift 3652629
  have htrace : WordTrace (prefixWord ++ tailWord_3652629) baseStart_3652629 baseEnd_3652629 := by
    simpa [prefixWord, tailWord_3652629, baseEnd_3652629] using wordTrace_append hprefix tailTrace_3652629
  have hstable : (prefixWord ++ tailWord_3652629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3652629).length < 2 ^ (prefixWord ++ tailWord_3652629).sum := by decide
  have hdescent : baseEnd_3652629 < baseStart_3652629 := by decide
  rcases family_descends (prefixWord ++ tailWord_3652629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3652635 : List Nat := [1, 1, 1, 1, 1, 1, 3, 2, 4, 2, 6]
def baseStart_3652635 : Nat := 118140960795 + 3652635 * 2 ^ 59
def prefixEnd_3652635 : Nat := 4983230072969 + 3 ^ 40 * 3652635 * 2
def baseEnd_3652635 : Nat := 1875557410435421782464343

theorem tailTrace_3652635 : CollatzResearch.WordTrace tailWord_3652635 prefixEnd_3652635 1875557410435421782464343 := by
  unfold tailWord_3652635
  simp only [CollatzResearch.WordTrace]
  refine ⟨133222543122134690238231359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88815028748089793492154239 133222543122134690238231359)
  ·
    refine ⟨199833814683202035357347039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133222543122134690238231359 199833814683202035357347039)
    ·
      refine ⟨299750722024803053036020559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 199833814683202035357347039 299750722024803053036020559)
      ·
        refine ⟨449626083037204579554030839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 299750722024803053036020559 449626083037204579554030839)
        ·
          refine ⟨674439124555806869331046259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 449626083037204579554030839 674439124555806869331046259)
          ·
            refine ⟨1011658686833710303996569389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 674439124555806869331046259 1011658686833710303996569389)
            ·
              refine ⟨379372007562641363998713521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1011658686833710303996569389 379372007562641363998713521)
              ·
                refine ⟨284529005671981022999035141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 379372007562641363998713521 284529005671981022999035141)
                ·
                  refine ⟨53349188563496441812319089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 284529005671981022999035141 53349188563496441812319089)
                  ·
                    refine ⟨40011891422622331359239317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 53349188563496441812319089 40011891422622331359239317)
                    ·
                      refine ⟨1875557410435421782464343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 40011891422622331359239317 1875557410435421782464343)
                      ·
                        rfl

theorem cell23_3652635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 2, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 2, 4, 2, 6].length) (baseStart_3652635 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3652635 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3652635 prefixEnd_3652635 := by exact prefixLift 3652635
  have htrace : WordTrace (prefixWord ++ tailWord_3652635) baseStart_3652635 baseEnd_3652635 := by
    simpa [prefixWord, tailWord_3652635, baseEnd_3652635] using wordTrace_append hprefix tailTrace_3652635
  have hstable : (prefixWord ++ tailWord_3652635).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3652635).length < 2 ^ (prefixWord ++ tailWord_3652635).sum := by decide
  have hdescent : baseEnd_3652635 < baseStart_3652635 := by decide
  rcases family_descends (prefixWord ++ tailWord_3652635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3652640 : List Nat := [2, 1, 1, 7, 2, 1, 2, 1, 1, 5]
def baseStart_3652640 : Nat := 118140960795 + 3652640 * 2 ^ 59
def prefixEnd_3652640 : Nat := 4983230072969 + 3 ^ 40 * 3652640 * 2
def baseEnd_3652640 : Nat := 625186659279564754300607

theorem tailTrace_3652640 : CollatzResearch.WordTrace tailWord_3652640 prefixEnd_3652640 625186659279564754300607 := by
  unfold tailWord_3652640
  simp only [CollatzResearch.WordTrace]
  refine ⟨66611362743558288046081687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88815150324744384061442249 66611362743558288046081687)
  ·
    refine ⟨99917044115337432069122531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66611362743558288046081687 99917044115337432069122531)
    ·
      refine ⟨149875566173006148103683797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99917044115337432069122531 149875566173006148103683797)
      ·
        refine ⟨3512708582179831596180089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 149875566173006148103683797 3512708582179831596180089)
        ·
          refine ⟨2634531436634873697135067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3512708582179831596180089 2634531436634873697135067)
          ·
            refine ⟨3951797154952310545702601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2634531436634873697135067 3951797154952310545702601)
            ·
              refine ⟨2963847866214232909276951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3951797154952310545702601 2963847866214232909276951)
              ·
                refine ⟨4445771799321349363915427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2963847866214232909276951 4445771799321349363915427)
                ·
                  refine ⟨6668657698982024045873141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4445771799321349363915427 6668657698982024045873141)
                  ·
                    refine ⟨625186659279564754300607, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6668657698982024045873141 625186659279564754300607)
                    ·
                      rfl

theorem cell23_3652640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 2, 1, 2, 1, 1, 5].length) (baseStart_3652640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3652640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3652640 prefixEnd_3652640 := by exact prefixLift 3652640
  have htrace : WordTrace (prefixWord ++ tailWord_3652640) baseStart_3652640 baseEnd_3652640 := by
    simpa [prefixWord, tailWord_3652640, baseEnd_3652640] using wordTrace_append hprefix tailTrace_3652640
  have hstable : (prefixWord ++ tailWord_3652640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3652640).length < 2 ^ (prefixWord ++ tailWord_3652640).sum := by decide
  have hdescent : baseEnd_3652640 < baseStart_3652640 := by decide
  rcases family_descends (prefixWord ++ tailWord_3652640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3652643 : List Nat := [1, 1, 1, 4, 3, 2, 1, 5, 1, 2, 2]
def baseStart_3652643 : Nat := 118140960795 + 3652643 * 2 ^ 59
def prefixEnd_3652643 : Nat := 4983230072969 + 3 ^ 40 * 3652643 * 2
def baseEnd_3652643 : Nat := 1875561518280657751164307

theorem tailTrace_3652643 : CollatzResearch.WordTrace tailWord_3652643 prefixEnd_3652643 1875561518280657751164307 := by
  unfold tailWord_3652643
  simp only [CollatzResearch.WordTrace]
  refine ⟨133222834906105707604522583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88815223270737138403015055 133222834906105707604522583)
  ·
    refine ⟨199834252359158561406783875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133222834906105707604522583 199834252359158561406783875)
    ·
      refine ⟨299751378538737842110175813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 199834252359158561406783875 299751378538737842110175813)
      ·
        refine ⟨56203383476013345395657965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 299751378538737842110175813 56203383476013345395657965)
        ·
          refine ⟨21076268803505004523371737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56203383476013345395657965 21076268803505004523371737)
          ·
            refine ⟨15807201602628753392528803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21076268803505004523371737 15807201602628753392528803)
            ·
              refine ⟨23710802403943130088793205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15807201602628753392528803 23710802403943130088793205)
              ·
                refine ⟨2222887725369668445824363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 23710802403943130088793205 2222887725369668445824363)
                ·
                  refine ⟨3334331588054502668736545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2222887725369668445824363 3334331588054502668736545)
                  ·
                    refine ⟨2500748691040877001552409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3334331588054502668736545 2500748691040877001552409)
                    ·
                      refine ⟨1875561518280657751164307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2500748691040877001552409 1875561518280657751164307)
                      ·
                        rfl

theorem cell23_3652643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 1, 5, 1, 2, 2].length) (baseStart_3652643 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3652643 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3652643 prefixEnd_3652643 := by exact prefixLift 3652643
  have htrace : WordTrace (prefixWord ++ tailWord_3652643) baseStart_3652643 baseEnd_3652643 := by
    simpa [prefixWord, tailWord_3652643, baseEnd_3652643] using wordTrace_append hprefix tailTrace_3652643
  have hstable : (prefixWord ++ tailWord_3652643).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3652643).length < 2 ^ (prefixWord ++ tailWord_3652643).sum := by decide
  have hdescent : baseEnd_3652643 < baseStart_3652643 := by decide
  rcases family_descends (prefixWord ++ tailWord_3652643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3652660 : List Nat := [2, 5, 1, 2, 1, 2, 2, 1, 3, 2, 2]
def baseStart_3652660 : Nat := 118140960795 + 3652660 * 2 ^ 59
def prefixEnd_3652660 : Nat := 4983230072969 + 3 ^ 40 * 3652660 * 2
def baseEnd_3652660 : Nat := 1875570247451784184651729

theorem tailTrace_3652660 : CollatzResearch.WordTrace tailWord_3652660 prefixEnd_3652660 1875570247451784184651729 := by
  unfold tailWord_3652660
  simp only [CollatzResearch.WordTrace]
  refine ⟨66611727473522059753945717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88815636631362746338594289 66611727473522059753945717)
  ·
    refine ⟨6244849450642693101932411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 66611727473522059753945717 6244849450642693101932411)
    ·
      refine ⟨9367274175964039652898617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6244849450642693101932411 9367274175964039652898617)
      ·
        refine ⟨7025455631973029739673963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9367274175964039652898617 7025455631973029739673963)
        ·
          refine ⟨10538183447959544609510945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7025455631973029739673963 10538183447959544609510945)
          ·
            refine ⟨7903637585969658457133209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10538183447959544609510945 7903637585969658457133209)
            ·
              refine ⟨5927728189477243842849907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7903637585969658457133209 5927728189477243842849907)
              ·
                refine ⟨8891592284215865764274861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5927728189477243842849907 8891592284215865764274861)
                ·
                  refine ⟨3334347106580949661603073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8891592284215865764274861 3334347106580949661603073)
                  ·
                    refine ⟨2500760329935712246202305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3334347106580949661603073 2500760329935712246202305)
                    ·
                      refine ⟨1875570247451784184651729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2500760329935712246202305 1875570247451784184651729)
                      ·
                        rfl

theorem cell23_3652660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 2, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 2, 2, 1, 3, 2, 2].length) (baseStart_3652660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3652660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3652660 prefixEnd_3652660 := by exact prefixLift 3652660
  have htrace : WordTrace (prefixWord ++ tailWord_3652660) baseStart_3652660 baseEnd_3652660 := by
    simpa [prefixWord, tailWord_3652660, baseEnd_3652660] using wordTrace_append hprefix tailTrace_3652660
  have hstable : (prefixWord ++ tailWord_3652660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3652660).length < 2 ^ (prefixWord ++ tailWord_3652660).sum := by decide
  have hdescent : baseEnd_3652660 < baseStart_3652660 := by decide
  rcases family_descends (prefixWord ++ tailWord_3652660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3652673 : List Nat := [1, 2, 5, 1, 4, 1, 1, 1, 1, 2, 4]
def baseStart_3652673 : Nat := 118140960795 + 3652673 * 2 ^ 59
def prefixEnd_3652673 : Nat := 4983230072969 + 3 ^ 40 * 3652673 * 2
def baseEnd_3652673 : Nat := 1875576922700292633789169

theorem tailTrace_3652673 : CollatzResearch.WordTrace tailWord_3652673 prefixEnd_3652673 1875576922700292633789169 := by
  unfold tailWord_3652673
  simp only [CollatzResearch.WordTrace]
  refine ⟨133223929095997022728114673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88815952730664681818743115 133223929095997022728114673)
  ·
    refine ⟨99917946821997767046086005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133223929095997022728114673 99917946821997767046086005)
    ·
      refine ⟨9367307514562290660570563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 99917946821997767046086005 9367307514562290660570563)
      ·
        refine ⟨14050961271843435990855845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9367307514562290660570563 14050961271843435990855845)
        ·
          refine ⟨2634555238470644248285471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14050961271843435990855845 2634555238470644248285471)
          ·
            refine ⟨3951832857705966372428207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2634555238470644248285471 3951832857705966372428207)
            ·
              refine ⟨5927749286558949558642311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3951832857705966372428207 5927749286558949558642311)
              ·
                refine ⟨8891623929838424337963467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5927749286558949558642311 8891623929838424337963467)
                ·
                  refine ⟨13337435894757636506945201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8891623929838424337963467 13337435894757636506945201)
                  ·
                    refine ⟨10003076921068227380208901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13337435894757636506945201 10003076921068227380208901)
                    ·
                      refine ⟨1875576922700292633789169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10003076921068227380208901 1875576922700292633789169)
                      ·
                        rfl

theorem cell23_3652673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 4, 1, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 4, 1, 1, 1, 1, 2, 4].length) (baseStart_3652673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3652673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3652673 prefixEnd_3652673 := by exact prefixLift 3652673
  have htrace : WordTrace (prefixWord ++ tailWord_3652673) baseStart_3652673 baseEnd_3652673 := by
    simpa [prefixWord, tailWord_3652673, baseEnd_3652673] using wordTrace_append hprefix tailTrace_3652673
  have hstable : (prefixWord ++ tailWord_3652673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3652673).length < 2 ^ (prefixWord ++ tailWord_3652673).sum := by decide
  have hdescent : baseEnd_3652673 < baseStart_3652673 := by decide
  rcases family_descends (prefixWord ++ tailWord_3652673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3652682 : List Nat := [3, 1, 2, 1, 1, 2, 2, 2, 2, 3, 4]
def baseStart_3652682 : Nat := 118140960795 + 3652682 * 2 ^ 59
def prefixEnd_3652682 : Nat := 4983230072969 + 3 ^ 40 * 3652682 * 2
def baseEnd_3652682 : Nat := 1875581544026183098576627

theorem tailTrace_3652682 : CollatzResearch.WordTrace tailWord_3652682 prefixEnd_3652682 1875581544026183098576627 := by
  unfold tailWord_3652682
  simp only [CollatzResearch.WordTrace]
  refine ⟨33306064338241104316298075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88816171568642944843461533 33306064338241104316298075)
  ·
    refine ⟨49959096507361656474447113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33306064338241104316298075 49959096507361656474447113)
    ·
      refine ⟨37469322380521242355835335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49959096507361656474447113 37469322380521242355835335)
      ·
        refine ⟨56203983570781863533753003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37469322380521242355835335 56203983570781863533753003)
        ·
          refine ⟨84305975356172795300629505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56203983570781863533753003 84305975356172795300629505)
          ·
            refine ⟨63229481517129596475472129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84305975356172795300629505 63229481517129596475472129)
            ·
              refine ⟨47422111137847197356604097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63229481517129596475472129 47422111137847197356604097)
              ·
                refine ⟨35566583353385398017453073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47422111137847197356604097 35566583353385398017453073)
                ·
                  refine ⟨26674937515039048513089805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35566583353385398017453073 26674937515039048513089805)
                  ·
                    refine ⟨10003101568139643192408677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26674937515039048513089805 10003101568139643192408677)
                    ·
                      refine ⟨1875581544026183098576627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10003101568139643192408677 1875581544026183098576627)
                      ·
                        rfl

theorem cell23_3652682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 2, 2, 2, 3, 4].length) (baseStart_3652682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3652682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3652682 prefixEnd_3652682 := by exact prefixLift 3652682
  have htrace : WordTrace (prefixWord ++ tailWord_3652682) baseStart_3652682 baseEnd_3652682 := by
    simpa [prefixWord, tailWord_3652682, baseEnd_3652682] using wordTrace_append hprefix tailTrace_3652682
  have hstable : (prefixWord ++ tailWord_3652682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3652682).length < 2 ^ (prefixWord ++ tailWord_3652682).sum := by decide
  have hdescent : baseEnd_3652682 < baseStart_3652682 := by decide
  rcases family_descends (prefixWord ++ tailWord_3652682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3652692 : List Nat := [2, 4, 1, 1, 1, 1, 2, 2, 1, 8]
def baseStart_3652692 : Nat := 118140960795 + 3652692 * 2 ^ 59
def prefixEnd_3652692 : Nat := 4983230072969 + 3 ^ 40 * 3652692 * 2
def baseEnd_3652692 : Nat := 625195559610909353150527

theorem tailTrace_3652692 : CollatzResearch.WordTrace tailWord_3652692 prefixEnd_3652692 625195559610909353150527 := by
  unfold tailWord_3652692
  simp only [CollatzResearch.WordTrace]
  refine ⟨66612311041464094486528165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88816414721952125982037553 66612311041464094486528165)
  ·
    refine ⟨12489808320274517716224031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 66612311041464094486528165 12489808320274517716224031)
    ·
      refine ⟨18734712480411776574336047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12489808320274517716224031 18734712480411776574336047)
      ·
        refine ⟨28102068720617664861504071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18734712480411776574336047 28102068720617664861504071)
        ·
          refine ⟨42153103080926497292256107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28102068720617664861504071 42153103080926497292256107)
          ·
            refine ⟨63229654621389745938384161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42153103080926497292256107 63229654621389745938384161)
            ·
              refine ⟨47422240966042309453788121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63229654621389745938384161 47422240966042309453788121)
              ·
                refine ⟨35566680724531732090341091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47422240966042309453788121 35566680724531732090341091)
                ·
                  refine ⟨53350021086797598135511637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35566680724531732090341091 53350021086797598135511637)
                  ·
                    refine ⟨625195559610909353150527, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 53350021086797598135511637 625195559610909353150527)
                    ·
                      rfl

theorem cell23_3652692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 2, 2, 1, 8].length) (baseStart_3652692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3652692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3652692 prefixEnd_3652692 := by exact prefixLift 3652692
  have htrace : WordTrace (prefixWord ++ tailWord_3652692) baseStart_3652692 baseEnd_3652692 := by
    simpa [prefixWord, tailWord_3652692, baseEnd_3652692] using wordTrace_append hprefix tailTrace_3652692
  have hstable : (prefixWord ++ tailWord_3652692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3652692).length < 2 ^ (prefixWord ++ tailWord_3652692).sum := by decide
  have hdescent : baseEnd_3652692 < baseStart_3652692 := by decide
  rcases family_descends (prefixWord ++ tailWord_3652692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3652716 : List Nat := [2, 2, 1, 1, 3, 2, 1, 3, 4, 2, 2]
def baseStart_3652716 : Nat := 118140960795 + 3652716 * 2 ^ 59
def prefixEnd_3652716 : Nat := 4983230072969 + 3 ^ 40 * 3652716 * 2
def baseEnd_3652716 : Nat := 1875599002368435965551471

theorem tailTrace_3652716 : CollatzResearch.WordTrace tailWord_3652716 prefixEnd_3652716 1875599002368435965551471 := by
  unfold tailWord_3652716
  simp only [CollatzResearch.WordTrace]
  refine ⟨66612748717420620535965001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88816998289894160714620001 66612748717420620535965001)
  ·
    refine ⟨49959561538065465401973751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66612748717420620535965001 49959561538065465401973751)
    ·
      refine ⟨74939342307098198102960627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49959561538065465401973751 74939342307098198102960627)
      ·
        refine ⟨112409013460647297154440941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74939342307098198102960627 112409013460647297154440941)
        ·
          refine ⟨42153380047742736432915353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 112409013460647297154440941 42153380047742736432915353)
          ·
            refine ⟨31615035035807052324686515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42153380047742736432915353 31615035035807052324686515)
            ·
              refine ⟨47422552553710578487029773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31615035035807052324686515 47422552553710578487029773)
              ·
                refine ⟨17783457207641466932636165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47422552553710578487029773 17783457207641466932636165)
                ·
                  refine ⟨3334398226432775049869281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17783457207641466932636165 3334398226432775049869281)
                  ·
                    refine ⟨2500798669824581287401961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3334398226432775049869281 2500798669824581287401961)
                    ·
                      refine ⟨1875599002368435965551471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2500798669824581287401961 1875599002368435965551471)
                      ·
                        rfl

theorem cell23_3652716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 4, 2, 2].length) (baseStart_3652716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3652716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3652716 prefixEnd_3652716 := by exact prefixLift 3652716
  have htrace : WordTrace (prefixWord ++ tailWord_3652716) baseStart_3652716 baseEnd_3652716 := by
    simpa [prefixWord, tailWord_3652716, baseEnd_3652716] using wordTrace_append hprefix tailTrace_3652716
  have hstable : (prefixWord ++ tailWord_3652716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3652716).length < 2 ^ (prefixWord ++ tailWord_3652716).sum := by decide
  have hdescent : baseEnd_3652716 < baseStart_3652716 := by decide
  rcases family_descends (prefixWord ++ tailWord_3652716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3652733 : List Nat := [1, 4, 1, 1, 3, 1, 3, 3, 2, 2, 2]
def baseStart_3652733 : Nat := 118140960795 + 3652733 * 2 ^ 59
def prefixEnd_3652733 : Nat := 4983230072969 + 3 ^ 40 * 3652733 * 2
def baseEnd_3652733 : Nat := 1875607731539562399038893

theorem tailTrace_3652733 : CollatzResearch.WordTrace tailWord_3652733 prefixEnd_3652733 1875607731539562399038893 := by
  unfold tailWord_3652733
  simp only [CollatzResearch.WordTrace]
  refine ⟨133226117475779652975298853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88817411650519768650199235 133226117475779652975298853)
  ·
    refine ⟨24979897026708684932868535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 133226117475779652975298853 24979897026708684932868535)
    ·
      refine ⟨37469845540063027399302803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24979897026708684932868535 37469845540063027399302803)
      ·
        refine ⟨56204768310094541098954205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37469845540063027399302803 56204768310094541098954205)
        ·
          refine ⟨21076788116285452912107827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56204768310094541098954205 21076788116285452912107827)
          ·
            refine ⟨31615182174428179368161741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21076788116285452912107827 31615182174428179368161741)
            ·
              refine ⟨11855693315410567263060653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31615182174428179368161741 11855693315410567263060653)
              ·
                refine ⟨4445884993278962723647745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11855693315410567263060653 4445884993278962723647745)
                ·
                  refine ⟨3334413744959222042735809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4445884993278962723647745 3334413744959222042735809)
                  ·
                    refine ⟨2500810308719416532051857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3334413744959222042735809 2500810308719416532051857)
                    ·
                      refine ⟨1875607731539562399038893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2500810308719416532051857 1875607731539562399038893)
                      ·
                        rfl

theorem cell23_3652733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 3, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 3, 3, 2, 2, 2].length) (baseStart_3652733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3652733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3652733 prefixEnd_3652733 := by exact prefixLift 3652733
  have htrace : WordTrace (prefixWord ++ tailWord_3652733) baseStart_3652733 baseEnd_3652733 := by
    simpa [prefixWord, tailWord_3652733, baseEnd_3652733] using wordTrace_append hprefix tailTrace_3652733
  have hstable : (prefixWord ++ tailWord_3652733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3652733).length < 2 ^ (prefixWord ++ tailWord_3652733).sum := by decide
  have hdescent : baseEnd_3652733 < baseStart_3652733 := by decide
  rcases family_descends (prefixWord ++ tailWord_3652733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3652769 : List Nat := [1, 2, 3, 3, 1, 1, 1, 4, 2, 5]
def baseStart_3652769 : Nat := 118140960795 + 3652769 * 2 ^ 59
def prefixEnd_3652769 : Nat := 4983230072969 + 3 ^ 40 * 3652769 * 2
def baseEnd_3652769 : Nat := 625208738947708086062909

theorem tailTrace_3652769 : CollatzResearch.WordTrace tailWord_3652769 prefixEnd_3652769 625208738947708086062909 := by
  unfold tailWord_3652769
  simp only [CollatzResearch.WordTrace]
  refine ⟨133227430503649231123609361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88818287002432820749072907 133227430503649231123609361)
  ·
    refine ⟨99920572877736923342707021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133227430503649231123609361 99920572877736923342707021)
    ·
      refine ⟨37470214829151346253515133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 99920572877736923342707021 37470214829151346253515133)
      ·
        refine ⟨14051330560931754845068175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37470214829151346253515133 14051330560931754845068175)
        ·
          refine ⟨21076995841397632267602263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14051330560931754845068175 21076995841397632267602263)
          ·
            refine ⟨31615493762096448401403395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21076995841397632267602263 31615493762096448401403395)
            ·
              refine ⟨47423240643144672602105093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31615493762096448401403395 47423240643144672602105093)
              ·
                refine ⟨8891857620589626112894705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 47423240643144672602105093 8891857620589626112894705)
                ·
                  refine ⟨6668893215442219584671029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8891857620589626112894705 6668893215442219584671029)
                  ·
                    refine ⟨625208738947708086062909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6668893215442219584671029 625208738947708086062909)
                    ·
                      rfl

theorem cell23_3652769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 1, 4, 2, 5].length) (baseStart_3652769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3652769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3652769 prefixEnd_3652769 := by exact prefixLift 3652769
  have htrace : WordTrace (prefixWord ++ tailWord_3652769) baseStart_3652769 baseEnd_3652769 := by
    simpa [prefixWord, tailWord_3652769, baseEnd_3652769] using wordTrace_append hprefix tailTrace_3652769
  have hstable : (prefixWord ++ tailWord_3652769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3652769).length < 2 ^ (prefixWord ++ tailWord_3652769).sum := by decide
  have hdescent : baseEnd_3652769 < baseStart_3652769 := by decide
  rcases family_descends (prefixWord ++ tailWord_3652769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3652773 : List Nat := [1, 3, 1, 2, 1, 6, 2, 2, 5]
def baseStart_3652773 : Nat := 118140960795 + 3652773 * 2 ^ 59
def prefixEnd_3652773 : Nat := 4983230072969 + 3 ^ 40 * 3652773 * 2
def baseEnd_3652773 : Nat := 208403141196193582504301

theorem tailTrace_3652773 : CollatzResearch.WordTrace tailWord_3652773 prefixEnd_3652773 208403141196193582504301 := by
  unfold tailWord_3652773
  simp only [CollatzResearch.WordTrace]
  refine ⟨133227576395634739806754973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88818384263756493204503315 133227576395634739806754973)
  ·
    refine ⟨49960341148363027427533115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 133227576395634739806754973 49960341148363027427533115)
    ·
      refine ⟨74940511722544541141299673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49960341148363027427533115 74940511722544541141299673)
      ·
        refine ⟨56205383791908405855974755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74940511722544541141299673 56205383791908405855974755)
        ·
          refine ⟨84308075687862608783962133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56205383791908405855974755 84308075687862608783962133)
          ·
            refine ⟨3951941047868559786748225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 84308075687862608783962133 3951941047868559786748225)
            ·
              refine ⟨2963955785901419840061169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3951941047868559786748225 2963955785901419840061169)
              ·
                refine ⟨2222966839426064880045877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2963955785901419840061169 2222966839426064880045877)
                ·
                  refine ⟨208403141196193582504301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2222966839426064880045877 208403141196193582504301)
                  ·
                    rfl

theorem cell23_3652773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 6, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 6, 2, 2, 5].length) (baseStart_3652773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3652773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3652773 prefixEnd_3652773 := by exact prefixLift 3652773
  have htrace : WordTrace (prefixWord ++ tailWord_3652773) baseStart_3652773 baseEnd_3652773 := by
    simpa [prefixWord, tailWord_3652773, baseEnd_3652773] using wordTrace_append hprefix tailTrace_3652773
  have hstable : (prefixWord ++ tailWord_3652773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3652773).length < 2 ^ (prefixWord ++ tailWord_3652773).sum := by decide
  have hdescent : baseEnd_3652773 < baseStart_3652773 := by decide
  rcases family_descends (prefixWord ++ tailWord_3652773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3652799 : List Nat := [1, 1, 2, 2, 2, 2, 3, 1, 5, 4]
def baseStart_3652799 : Nat := 118140960795 + 3652799 * 2 ^ 59
def prefixEnd_3652799 : Nat := 4983230072969 + 3 ^ 40 * 3652799 * 2
def baseEnd_3652799 : Nat := 625213873754253046937863

theorem tailTrace_3652799 : CollatzResearch.WordTrace tailWord_3652799 prefixEnd_3652799 625213873754253046937863 := by
  unfold tailWord_3652799
  simp only [CollatzResearch.WordTrace]
  refine ⟨133228524693540546247201451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88819016462360364164800967 133228524693540546247201451)
  ·
    refine ⟨199842787040310819370802177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133228524693540546247201451 199842787040310819370802177)
    ·
      refine ⟨149882090280233114528101633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 199842787040310819370802177 149882090280233114528101633)
      ·
        refine ⟨112411567710174835896076225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 149882090280233114528101633 112411567710174835896076225)
        ·
          refine ⟨84308675782631126922057169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 112411567710174835896076225 84308675782631126922057169)
          ·
            refine ⟨63231506836973345191542877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84308675782631126922057169 63231506836973345191542877)
            ·
              refine ⟨23711815063865004446828579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 63231506836973345191542877 23711815063865004446828579)
              ·
                refine ⟨35567722595797506670242869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23711815063865004446828579 35567722595797506670242869)
                ·
                  refine ⟨3334473993356016250335269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 35567722595797506670242869 3334473993356016250335269)
                  ·
                    refine ⟨625213873754253046937863, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3334473993356016250335269 625213873754253046937863)
                    ·
                      rfl

theorem cell23_3652799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 3, 1, 5, 4].length) (baseStart_3652799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3652799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3652799 prefixEnd_3652799 := by exact prefixLift 3652799
  have htrace : WordTrace (prefixWord ++ tailWord_3652799) baseStart_3652799 baseEnd_3652799 := by
    simpa [prefixWord, tailWord_3652799, baseEnd_3652799] using wordTrace_append hprefix tailTrace_3652799
  have hstable : (prefixWord ++ tailWord_3652799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3652799).length < 2 ^ (prefixWord ++ tailWord_3652799).sum := by decide
  have hdescent : baseEnd_3652799 < baseStart_3652799 := by decide
  rcases family_descends (prefixWord ++ tailWord_3652799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3652833 : List Nat := [1, 2, 3, 1, 3, 2, 2, 4, 1, 4]
def baseStart_3652833 : Nat := 118140960795 + 3652833 * 2 ^ 59
def prefixEnd_3652833 : Nat := 4983230072969 + 3 ^ 40 * 3652833 * 2
def baseEnd_3652833 : Nat := 625219693201670669262811

theorem tailTrace_3652833 : CollatzResearch.WordTrace tailWord_3652833 prefixEnd_3652833 625219693201670669262811 := by
  unfold tailWord_3652833
  simp only [CollatzResearch.WordTrace]
  refine ⟨133229764775417370053939153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88819843183611580035959435 133229764775417370053939153)
  ·
    refine ⟨99922323581563027540454365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133229764775417370053939153 99922323581563027540454365)
    ·
      refine ⟨37470871343086135327670387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 99922323581563027540454365 37470871343086135327670387)
      ·
        refine ⟨56206307014629202991505581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37470871343086135327670387 56206307014629202991505581)
        ·
          refine ⟨21077365130485951121814593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56206307014629202991505581 21077365130485951121814593)
          ·
            refine ⟨15808023847864463341360945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21077365130485951121814593 15808023847864463341360945)
            ·
              refine ⟨11856017885898347506020709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15808023847864463341360945 11856017885898347506020709)
              ·
                refine ⟨2223003353605940157378883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11856017885898347506020709 2223003353605940157378883)
                ·
                  refine ⟨3334505030408910236068325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2223003353605940157378883 3334505030408910236068325)
                  ·
                    refine ⟨625219693201670669262811, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3334505030408910236068325 625219693201670669262811)
                    ·
                      rfl

theorem cell23_3652833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 2, 4, 1, 4].length) (baseStart_3652833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3652833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3652833 prefixEnd_3652833 := by exact prefixLift 3652833
  have htrace : WordTrace (prefixWord ++ tailWord_3652833) baseStart_3652833 baseEnd_3652833 := by
    simpa [prefixWord, tailWord_3652833, baseEnd_3652833] using wordTrace_append hprefix tailTrace_3652833
  have hstable : (prefixWord ++ tailWord_3652833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3652833).length < 2 ^ (prefixWord ++ tailWord_3652833).sum := by decide
  have hdescent : baseEnd_3652833 < baseStart_3652833 := by decide
  rcases family_descends (prefixWord ++ tailWord_3652833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3652876 : List Nat := [2, 2, 1, 2, 2, 3, 2, 3, 1, 5]
def baseStart_3652876 : Nat := 118140960795 + 3652876 * 2 ^ 59
def prefixEnd_3652876 : Nat := 4983230072969 + 3 ^ 40 * 3652876 * 2
def baseEnd_3652876 : Nat := 625227053091051779850245

theorem tailTrace_3652876 : CollatzResearch.WordTrace tailWord_3652876 prefixEnd_3652876 625227053091051779850245 := by
  unfold tailWord_3652876
  simp only [CollatzResearch.WordTrace]
  refine ⟨66615666557130794198877241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88820888742841058931836321 66615666557130794198877241)
  ·
    refine ⟨49961749917848095649157931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66615666557130794198877241 49961749917848095649157931)
    ·
      refine ⟨74942624876772143473736897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49961749917848095649157931 74942624876772143473736897)
      ·
        refine ⟨56206968657579107605302673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74942624876772143473736897 56206968657579107605302673)
        ·
          refine ⟨42155226493184330703977005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56206968657579107605302673 42155226493184330703977005)
          ·
            refine ⟨15808209934944124013991377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42155226493184330703977005 15808209934944124013991377)
            ·
              refine ⟨11856157451208093010493533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15808209934944124013991377 11856157451208093010493533)
              ·
                refine ⟨4446059044203034878935075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11856157451208093010493533 4446059044203034878935075)
                ·
                  refine ⟨6669088566304552318402613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4446059044203034878935075 6669088566304552318402613)
                  ·
                    refine ⟨625227053091051779850245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6669088566304552318402613 625227053091051779850245)
                    ·
                      rfl

theorem cell23_3652876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 2, 3, 1, 5].length) (baseStart_3652876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3652876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3652876 prefixEnd_3652876 := by exact prefixLift 3652876
  have htrace : WordTrace (prefixWord ++ tailWord_3652876) baseStart_3652876 baseEnd_3652876 := by
    simpa [prefixWord, tailWord_3652876, baseEnd_3652876] using wordTrace_append hprefix tailTrace_3652876
  have hstable : (prefixWord ++ tailWord_3652876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3652876).length < 2 ^ (prefixWord ++ tailWord_3652876).sum := by decide
  have hdescent : baseEnd_3652876 < baseStart_3652876 := by decide
  rcases family_descends (prefixWord ++ tailWord_3652876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3652879 : List Nat := [1, 1, 2, 1, 1, 1, 3, 1, 7, 1, 4]
def baseStart_3652879 : Nat := 118140960795 + 3652879 * 2 ^ 59
def prefixEnd_3652879 : Nat := 4983230072969 + 3 ^ 40 * 3652879 * 2
def baseEnd_3652879 : Nat := 1875682699715118827813221

theorem tailTrace_3652879 : CollatzResearch.WordTrace tailWord_3652879 prefixEnd_3652879 1875682699715118827813221 := by
  unfold tailWord_3652879
  simp only [CollatzResearch.WordTrace]
  refine ⟨133231442533250719910113691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88820961688833813273409127 133231442533250719910113691)
  ·
    refine ⟨199847163799876079865170537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133231442533250719910113691 199847163799876079865170537)
    ·
      refine ⟨149885372849907059898877903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 199847163799876079865170537 149885372849907059898877903)
      ·
        refine ⟨224828059274860589848316855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149885372849907059898877903 224828059274860589848316855)
        ·
          refine ⟨337242088912290884772475283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 224828059274860589848316855 337242088912290884772475283)
          ·
            refine ⟨505863133368436327158712925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 337242088912290884772475283 505863133368436327158712925)
            ·
              refine ⟨189698675013163622684517347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 505863133368436327158712925 189698675013163622684517347)
              ·
                refine ⟨284548012519745434026776021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 189698675013163622684517347 284548012519745434026776021)
                ·
                  refine ⟨6669094043431533610002563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 284548012519745434026776021 6669094043431533610002563)
                  ·
                    refine ⟨10003641065147300415003845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6669094043431533610002563 10003641065147300415003845)
                    ·
                      refine ⟨1875682699715118827813221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10003641065147300415003845 1875682699715118827813221)
                      ·
                        rfl

theorem cell23_3652879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 1, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 1, 7, 1, 4].length) (baseStart_3652879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3652879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3652879 prefixEnd_3652879 := by exact prefixLift 3652879
  have htrace : WordTrace (prefixWord ++ tailWord_3652879) baseStart_3652879 baseEnd_3652879 := by
    simpa [prefixWord, tailWord_3652879, baseEnd_3652879] using wordTrace_append hprefix tailTrace_3652879
  have hstable : (prefixWord ++ tailWord_3652879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3652879).length < 2 ^ (prefixWord ++ tailWord_3652879).sum := by decide
  have hdescent : baseEnd_3652879 < baseStart_3652879 := by decide
  rcases family_descends (prefixWord ++ tailWord_3652879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3652890 : List Nat := [3, 1, 1, 3, 3, 3, 1, 1, 3, 1, 3]
def baseStart_3652890 : Nat := 118140960795 + 3652890 * 2 ^ 59
def prefixEnd_3652890 : Nat := 4983230072969 + 3 ^ 40 * 3652890 * 2
def baseEnd_3652890 : Nat := 1875688348002318284775671

theorem tailTrace_3652890 : CollatzResearch.WordTrace tailWord_3652890 prefixEnd_3652890 1875688348002318284775671 := by
  unfold tailWord_3652890
  simp only [CollatzResearch.WordTrace]
  refine ⟨33307960934052717197191031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88821229157473912525842749 33307960934052717197191031)
  ·
    refine ⟨49961941401079075795786547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33307960934052717197191031 49961941401079075795786547)
    ·
      refine ⟨74942912101618613693679821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49961941401079075795786547 74942912101618613693679821)
      ·
        refine ⟨28103592038106980135129933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 74942912101618613693679821 28103592038106980135129933)
        ·
          refine ⟨10538847014290117550673725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28103592038106980135129933 10538847014290117550673725)
          ·
            refine ⟨3952067630358794081502647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10538847014290117550673725 3952067630358794081502647)
            ·
              refine ⟨5928101445538191122253971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3952067630358794081502647 5928101445538191122253971)
              ·
                refine ⟨8892152168307286683380957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5928101445538191122253971 8892152168307286683380957)
                ·
                  refine ⟨3334557063115232506267859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8892152168307286683380957 3334557063115232506267859)
                  ·
                    refine ⟨5001835594672848759401789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3334557063115232506267859 5001835594672848759401789)
                    ·
                      refine ⟨1875688348002318284775671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5001835594672848759401789 1875688348002318284775671)
                      ·
                        rfl

theorem cell23_3652890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 3, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 3, 1, 1, 3, 1, 3].length) (baseStart_3652890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3652890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3652890 prefixEnd_3652890 := by exact prefixLift 3652890
  have htrace : WordTrace (prefixWord ++ tailWord_3652890) baseStart_3652890 baseEnd_3652890 := by
    simpa [prefixWord, tailWord_3652890, baseEnd_3652890] using wordTrace_append hprefix tailTrace_3652890
  have hstable : (prefixWord ++ tailWord_3652890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3652890).length < 2 ^ (prefixWord ++ tailWord_3652890).sum := by decide
  have hdescent : baseEnd_3652890 < baseStart_3652890 := by decide
  rcases family_descends (prefixWord ++ tailWord_3652890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3652913 : List Nat := [1, 2, 2, 3, 3, 1, 3, 2, 1, 1, 4]
def baseStart_3652913 : Nat := 118140960795 + 3652913 * 2 ^ 59
def prefixEnd_3652913 : Nat := 4983230072969 + 3 ^ 40 * 3652913 * 2
def baseEnd_3652913 : Nat := 1875700158057371694788065

theorem tailTrace_3652913 : CollatzResearch.WordTrace tailWord_3652913 prefixEnd_3652913 1875700158057371694788065 := by
  unfold tailWord_3652913
  simp only [CollatzResearch.WordTrace]
  refine ⟨133232682615127543716851393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88821788410085029144567595 133232682615127543716851393)
  ·
    refine ⟨99924511961345657787638545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133232682615127543716851393 99924511961345657787638545)
    ·
      refine ⟨74943383971009243340728909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99924511961345657787638545 74943383971009243340728909)
      ·
        refine ⟨28103768989128466252773341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 74943383971009243340728909 28103768989128466252773341)
        ·
          refine ⟨10538913370923174844790003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28103768989128466252773341 10538913370923174844790003)
          ·
            refine ⟨15808370056384762267185005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10538913370923174844790003 15808370056384762267185005)
            ·
              refine ⟨5928138771144285850194377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15808370056384762267185005 5928138771144285850194377)
              ·
                refine ⟨4446104078358214387645783, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5928138771144285850194377 4446104078358214387645783)
                ·
                  refine ⟨6669156117537321581468675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4446104078358214387645783 6669156117537321581468675)
                  ·
                    refine ⟨10003734176305982372203013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6669156117537321581468675 10003734176305982372203013)
                    ·
                      refine ⟨1875700158057371694788065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10003734176305982372203013 1875700158057371694788065)
                      ·
                        rfl

theorem cell23_3652913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 3, 2, 1, 1, 4].length) (baseStart_3652913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3652913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3652913 prefixEnd_3652913 := by exact prefixLift 3652913
  have htrace : WordTrace (prefixWord ++ tailWord_3652913) baseStart_3652913 baseEnd_3652913 := by
    simpa [prefixWord, tailWord_3652913, baseEnd_3652913] using wordTrace_append hprefix tailTrace_3652913
  have hstable : (prefixWord ++ tailWord_3652913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3652913).length < 2 ^ (prefixWord ++ tailWord_3652913).sum := by decide
  have hdescent : baseEnd_3652913 < baseStart_3652913 := by decide
  rcases family_descends (prefixWord ++ tailWord_3652913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3652946 : List Nat := [3, 2, 2, 1, 1, 1, 1, 1, 5, 3, 3]
def baseStart_3652946 : Nat := 118140960795 + 3652946 * 2 ^ 59
def prefixEnd_3652946 : Nat := 4983230072969 + 3 ^ 40 * 3652946 * 2
def baseEnd_3652946 : Nat := 1875717102918970065675413

theorem tailTrace_3652946 : CollatzResearch.WordTrace tailWord_3652946 prefixEnd_3652946 1875717102918970065675413 := by
  unfold tailWord_3652946
  simp only [CollatzResearch.WordTrace]
  refine ⟨33308471556001997588200673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88822590816005326901868461 33308471556001997588200673)
  ·
    refine ⟨24981353667001498191150505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33308471556001997588200673 24981353667001498191150505)
    ·
      refine ⟨18736015250251123643362879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24981353667001498191150505 18736015250251123643362879)
      ·
        refine ⟨28104022875376685465044319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18736015250251123643362879 28104022875376685465044319)
        ·
          refine ⟨42156034313065028197566479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28104022875376685465044319 42156034313065028197566479)
          ·
            refine ⟨63234051469597542296349719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42156034313065028197566479 63234051469597542296349719)
            ·
              refine ⟨94851077204396313444524579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63234051469597542296349719 94851077204396313444524579)
              ·
                refine ⟨142276615806594470166786869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 94851077204396313444524579 142276615806594470166786869)
                ·
                  refine ⟨13338432731868231578136269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 142276615806594470166786869 13338432731868231578136269)
                  ·
                    refine ⟨5001912274450586841801101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13338432731868231578136269 5001912274450586841801101)
                    ·
                      refine ⟨1875717102918970065675413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5001912274450586841801101 1875717102918970065675413)
                      ·
                        rfl

theorem cell23_3652946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 1, 5, 3, 3].length) (baseStart_3652946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3652946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3652946 prefixEnd_3652946 := by exact prefixLift 3652946
  have htrace : WordTrace (prefixWord ++ tailWord_3652946) baseStart_3652946 baseEnd_3652946 := by
    simpa [prefixWord, tailWord_3652946, baseEnd_3652946] using wordTrace_append hprefix tailTrace_3652946
  have hstable : (prefixWord ++ tailWord_3652946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3652946).length < 2 ^ (prefixWord ++ tailWord_3652946).sum := by decide
  have hdescent : baseEnd_3652946 < baseStart_3652946 := by decide
  rcases family_descends (prefixWord ++ tailWord_3652946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3652957 : List Nat := [1, 4, 5, 1, 1, 1, 2, 1, 1, 6]
def baseStart_3652957 : Nat := 118140960795 + 3652957 * 2 ^ 59
def prefixEnd_3652957 : Nat := 4983230072969 + 3 ^ 40 * 3652957 * 2
def baseEnd_3652957 : Nat := 625240917068723174212621

theorem tailTrace_3652957 : CollatzResearch.WordTrace tailWord_3652957 prefixEnd_3652957 625240917068723174212621 := by
  unfold tailWord_3652957
  simp only [CollatzResearch.WordTrace]
  refine ⟨133234287426968139231453125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88822858284645426154302083 133234287426968139231453125)
  ·
    refine ⟨24981428892556526105897461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 133234287426968139231453125 24981428892556526105897461)
    ·
      refine ⟨2342008958677174322427887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 24981428892556526105897461 2342008958677174322427887)
      ·
        refine ⟨3513013438015761483641831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2342008958677174322427887 3513013438015761483641831)
        ·
          refine ⟨5269520157023642225462747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3513013438015761483641831 5269520157023642225462747)
          ·
            refine ⟨7904280235535463338194121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5269520157023642225462747 7904280235535463338194121)
            ·
              refine ⟨5928210176651597503645591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7904280235535463338194121 5928210176651597503645591)
              ·
                refine ⟨8892315264977396255468387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5928210176651597503645591 8892315264977396255468387)
                ·
                  refine ⟨13338472897466094383202581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8892315264977396255468387 13338472897466094383202581)
                  ·
                    refine ⟨625240917068723174212621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13338472897466094383202581 625240917068723174212621)
                    ·
                      rfl

theorem cell23_3652957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 1, 2, 1, 1, 6].length) (baseStart_3652957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3652957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3652957 prefixEnd_3652957 := by exact prefixLift 3652957
  have htrace : WordTrace (prefixWord ++ tailWord_3652957) baseStart_3652957 baseEnd_3652957 := by
    simpa [prefixWord, tailWord_3652957, baseEnd_3652957] using wordTrace_append hprefix tailTrace_3652957
  have hstable : (prefixWord ++ tailWord_3652957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3652957).length < 2 ^ (prefixWord ++ tailWord_3652957).sum := by decide
  have hdescent : baseEnd_3652957 < baseStart_3652957 := by decide
  rcases family_descends (prefixWord ++ tailWord_3652957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3652959 : List Nat := [1, 1, 2, 3, 1, 2, 1, 2, 1, 4, 5]
def baseStart_3652959 : Nat := 118140960795 + 3652959 * 2 ^ 59
def prefixEnd_3652959 : Nat := 4983230072969 + 3 ^ 40 * 3652959 * 2
def baseEnd_3652959 : Nat := 1875723778167478514812853

theorem tailTrace_3652959 : CollatzResearch.WordTrace tailWord_3652959 prefixEnd_3652959 1875723778167478514812853 := by
  unfold tailWord_3652959
  simp only [CollatzResearch.WordTrace]
  refine ⟨133234360372960893573025931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88822906915307262382017287 133234360372960893573025931)
  ·
    refine ⟨199851540559441340359538897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133234360372960893573025931 199851540559441340359538897)
    ·
      refine ⟨149888655419581005269654173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 199851540559441340359538897 149888655419581005269654173)
      ·
        refine ⟨56208245782342876976120315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 149888655419581005269654173 56208245782342876976120315)
        ·
          refine ⟨84312368673514315464180473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56208245782342876976120315 84312368673514315464180473)
          ·
            refine ⟨63234276505135736598135355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84312368673514315464180473 63234276505135736598135355)
            ·
              refine ⟨94851414757703604897203033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63234276505135736598135355 94851414757703604897203033)
              ·
                refine ⟨71138561068277703672902275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 94851414757703604897203033 71138561068277703672902275)
                ·
                  refine ⟨106707841602416555509353413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 71138561068277703672902275 106707841602416555509353413)
                  ·
                    refine ⟨20007720300453104158003765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 106707841602416555509353413 20007720300453104158003765)
                    ·
                      refine ⟨1875723778167478514812853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20007720300453104158003765 1875723778167478514812853)
                      ·
                        rfl

theorem cell23_3652959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 2, 1, 4, 5].length) (baseStart_3652959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3652959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3652959 prefixEnd_3652959 := by exact prefixLift 3652959
  have htrace : WordTrace (prefixWord ++ tailWord_3652959) baseStart_3652959 baseEnd_3652959 := by
    simpa [prefixWord, tailWord_3652959, baseEnd_3652959] using wordTrace_append hprefix tailTrace_3652959
  have hstable : (prefixWord ++ tailWord_3652959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3652959).length < 2 ^ (prefixWord ++ tailWord_3652959).sum := by decide
  have hdescent : baseEnd_3652959 < baseStart_3652959 := by decide
  rcases family_descends (prefixWord ++ tailWord_3652959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3652963 : List Nat := [1, 1, 1, 5, 2, 3, 2, 1, 1, 3, 3]
def baseStart_3652963 : Nat := 118140960795 + 3652963 * 2 ^ 59
def prefixEnd_3652963 : Nat := 4983230072969 + 3 ^ 40 * 3652963 * 2
def baseEnd_3652963 : Nat := 1875725832090096499162835

theorem tailTrace_3652963 : CollatzResearch.WordTrace tailWord_3652963 prefixEnd_3652963 1875725832090096499162835 := by
  unfold tailWord_3652963
  simp only [CollatzResearch.WordTrace]
  refine ⟨133234506264946402256171543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88823004176630934837447695 133234506264946402256171543)
  ·
    refine ⟨199851759397419603384257315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133234506264946402256171543 199851759397419603384257315)
    ·
      refine ⟨299777639096129405076385973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 199851759397419603384257315 299777639096129405076385973)
      ·
        refine ⟨28104153665262131725911185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 299777639096129405076385973 28104153665262131725911185)
        ·
          refine ⟨21078115248946598794433389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28104153665262131725911185 21078115248946598794433389)
          ·
            refine ⟨7904293218354974547912521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21078115248946598794433389 7904293218354974547912521)
            ·
              refine ⟨5928219913766230910934391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7904293218354974547912521 5928219913766230910934391)
              ·
                refine ⟨8892329870649346366401587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5928219913766230910934391 8892329870649346366401587)
                ·
                  refine ⟨13338494805974019549602381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8892329870649346366401587 13338494805974019549602381)
                  ·
                    refine ⟨5001935552240257331100893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13338494805974019549602381 5001935552240257331100893)
                    ·
                      refine ⟨1875725832090096499162835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5001935552240257331100893 1875725832090096499162835)
                      ·
                        rfl

theorem cell23_3652963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 3, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 3, 2, 1, 1, 3, 3].length) (baseStart_3652963 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3652963 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3652963 prefixEnd_3652963 := by exact prefixLift 3652963
  have htrace : WordTrace (prefixWord ++ tailWord_3652963) baseStart_3652963 baseEnd_3652963 := by
    simpa [prefixWord, tailWord_3652963, baseEnd_3652963] using wordTrace_append hprefix tailTrace_3652963
  have hstable : (prefixWord ++ tailWord_3652963).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3652963).length < 2 ^ (prefixWord ++ tailWord_3652963).sum := by decide
  have hdescent : baseEnd_3652963 < baseStart_3652963 := by decide
  rcases family_descends (prefixWord ++ tailWord_3652963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3652979 : List Nat := [1, 1, 1, 2, 2, 1, 2, 1, 6, 6]
def baseStart_3652979 : Nat := 118140960795 + 3652979 * 2 ^ 59
def prefixEnd_3652979 : Nat := 4983230072969 + 3 ^ 40 * 3652979 * 2
def baseEnd_3652979 : Nat := 625244682593522812187587

theorem tailTrace_3652979 : CollatzResearch.WordTrace tailWord_3652979 prefixEnd_3652979 625244682593522812187587 := by
  unfold tailWord_3652979
  simp only [CollatzResearch.WordTrace]
  refine ⟨133235089832888436988753991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88823393221925624659169327 133235089832888436988753991)
  ·
    refine ⟨199852634749332655483130987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133235089832888436988753991 199852634749332655483130987)
    ·
      refine ⟨299778952123998983224696481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 199852634749332655483130987 299778952123998983224696481)
      ·
        refine ⟨224834214092999237418522361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 299778952123998983224696481 224834214092999237418522361)
        ·
          refine ⟨168625660569749428063891771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 224834214092999237418522361 168625660569749428063891771)
          ·
            refine ⟨252938490854624142095837657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 168625660569749428063891771 252938490854624142095837657)
            ·
              refine ⟨189703868140968106571878243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 252938490854624142095837657 189703868140968106571878243)
              ·
                refine ⟨284555802211452159857817365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 189703868140968106571878243 284555802211452159857817365)
                ·
                  refine ⟨13338553228661819993335189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 284555802211452159857817365 13338553228661819993335189)
                  ·
                    refine ⟨625244682593522812187587, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13338553228661819993335189 625244682593522812187587)
                    ·
                      rfl

theorem cell23_3652979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 1, 6, 6].length) (baseStart_3652979 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3652979 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3652979 prefixEnd_3652979 := by exact prefixLift 3652979
  have htrace : WordTrace (prefixWord ++ tailWord_3652979) baseStart_3652979 baseEnd_3652979 := by
    simpa [prefixWord, tailWord_3652979, baseEnd_3652979] using wordTrace_append hprefix tailTrace_3652979
  have hstable : (prefixWord ++ tailWord_3652979).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3652979).length < 2 ^ (prefixWord ++ tailWord_3652979).sum := by decide
  have hdescent : baseEnd_3652979 < baseStart_3652979 := by decide
  rcases family_descends (prefixWord ++ tailWord_3652979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3652996 : List Nat := [2, 3, 2, 1, 1, 3, 1, 2, 2, 6]
def baseStart_3652996 : Nat := 118140960795 + 3652996 * 2 ^ 59
def prefixEnd_3652996 : Nat := 4983230072969 + 3 ^ 40 * 3652996 * 2
def baseEnd_3652996 : Nat := 625247592317231623350061

theorem tailTrace_3652996 : CollatzResearch.WordTrace tailWord_3652996 prefixEnd_3652996 625247592317231623350061 := by
  unfold tailWord_3652996
  simp only [CollatzResearch.WordTrace]
  refine ⟨66617854936913424446061421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88823806582551232594748561 66617854936913424446061421)
  ·
    refine ⟨24981695601342534167273033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66617854936913424446061421 24981695601342534167273033)
    ·
      refine ⟨18736271701006900625454775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24981695601342534167273033 18736271701006900625454775)
      ·
        refine ⟨28104407551510350938182163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18736271701006900625454775 28104407551510350938182163)
        ·
          refine ⟨42156611327265526407273245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28104407551510350938182163 42156611327265526407273245)
          ·
            refine ⟨15808729247724572402727467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42156611327265526407273245 15808729247724572402727467)
            ·
              refine ⟨23713093871586858604091201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15808729247724572402727467 23713093871586858604091201)
              ·
                refine ⟨17784820403690143953068401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23713093871586858604091201 17784820403690143953068401)
                ·
                  refine ⟨13338615302767607964801301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17784820403690143953068401 13338615302767607964801301)
                  ·
                    refine ⟨625247592317231623350061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13338615302767607964801301 625247592317231623350061)
                    ·
                      rfl

theorem cell23_3652996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 1, 2, 2, 6].length) (baseStart_3652996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3652996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3652996 prefixEnd_3652996 := by exact prefixLift 3652996
  have htrace : WordTrace (prefixWord ++ tailWord_3652996) baseStart_3652996 baseEnd_3652996 := by
    simpa [prefixWord, tailWord_3652996, baseEnd_3652996] using wordTrace_append hprefix tailTrace_3652996
  have hstable : (prefixWord ++ tailWord_3652996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3652996).length < 2 ^ (prefixWord ++ tailWord_3652996).sum := by decide
  have hdescent : baseEnd_3652996 < baseStart_3652996 := by decide
  rcases family_descends (prefixWord ++ tailWord_3652996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3653009 : List Nat := [1, 2, 2, 1, 1, 1, 2, 2, 11]
def baseStart_3653009 : Nat := 118140960795 + 3653009 * 2 ^ 59
def prefixEnd_3653009 : Nat := 4983230072969 + 3 ^ 40 * 3653009 * 2
def baseEnd_3653009 : Nat := 208416605800022591020847

theorem tailTrace_3653009 : CollatzResearch.WordTrace tailWord_3653009 prefixEnd_3653009 208416605800022591020847 := by
  unfold tailWord_3653009
  simp only [CollatzResearch.WordTrace]
  refine ⟨133236184022779752112346081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88824122681853168074897387 133236184022779752112346081)
  ·
    refine ⟨99927138017084814084259561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133236184022779752112346081 99927138017084814084259561)
    ·
      refine ⟨74945353512813610563194671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99927138017084814084259561 74945353512813610563194671)
      ·
        refine ⟨112418030269220415844792007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74945353512813610563194671 112418030269220415844792007)
        ·
          refine ⟨168627045403830623767188011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112418030269220415844792007 168627045403830623767188011)
          ·
            refine ⟨252940568105745935650782017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 168627045403830623767188011 252940568105745935650782017)
            ·
              refine ⟨189705426079309451738086513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 252940568105745935650782017 189705426079309451738086513)
              ·
                refine ⟨142279069559482088803564885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 189705426079309451738086513 142279069559482088803564885)
                ·
                  refine ⟨208416605800022591020847, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 142279069559482088803564885 208416605800022591020847)
                  ·
                    rfl

theorem cell23_3653009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 2, 11].length) (baseStart_3653009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3653009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3653009 prefixEnd_3653009 := by exact prefixLift 3653009
  have htrace : WordTrace (prefixWord ++ tailWord_3653009) baseStart_3653009 baseEnd_3653009 := by
    simpa [prefixWord, tailWord_3653009, baseEnd_3653009] using wordTrace_append hprefix tailTrace_3653009
  have hstable : (prefixWord ++ tailWord_3653009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3653009).length < 2 ^ (prefixWord ++ tailWord_3653009).sum := by decide
  have hdescent : baseEnd_3653009 < baseStart_3653009 := by decide
  rcases family_descends (prefixWord ++ tailWord_3653009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3653019 : List Nat := [1, 1, 1, 1, 1, 1, 2, 1, 5, 2, 7]
def baseStart_3653019 : Nat := 118140960795 + 3653019 * 2 ^ 59
def prefixEnd_3653019 : Nat := 4983230072969 + 3 ^ 40 * 3653019 * 2
def baseEnd_3653019 : Nat := 1875754587006748280062577

theorem tailTrace_3653019 : CollatzResearch.WordTrace tailWord_3653019 prefixEnd_3653019 1875754587006748280062577 := by
  unfold tailWord_3653019
  simp only [CollatzResearch.WordTrace]
  refine ⟨133236548752743523820210111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88824365835162349213473407 133236548752743523820210111)
  ·
    refine ⟨199854823129115285730315167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133236548752743523820210111 199854823129115285730315167)
    ·
      refine ⟨299782234693672928595472751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 199854823129115285730315167 299782234693672928595472751)
      ·
        refine ⟨449673352040509392893209127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 299782234693672928595472751 449673352040509392893209127)
        ·
          refine ⟨674510028060764089339813691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 449673352040509392893209127 674510028060764089339813691)
          ·
            refine ⟨1011765042091146134009720537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 674510028060764089339813691 1011765042091146134009720537)
            ·
              refine ⟨758823781568359600507290403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1011765042091146134009720537 758823781568359600507290403)
              ·
                refine ⟨1138235672352539400760935605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 758823781568359600507290403 1138235672352539400760935605)
                ·
                  refine ⟨106709594283050568821337713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1138235672352539400760935605 106709594283050568821337713)
                  ·
                    refine ⟨80032195712287926616003285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 106709594283050568821337713 80032195712287926616003285)
                    ·
                      refine ⟨1875754587006748280062577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 80032195712287926616003285 1875754587006748280062577)
                      ·
                        rfl

theorem cell23_3653019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 5, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 5, 2, 7].length) (baseStart_3653019 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3653019 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3653019 prefixEnd_3653019 := by exact prefixLift 3653019
  have htrace : WordTrace (prefixWord ++ tailWord_3653019) baseStart_3653019 baseEnd_3653019 := by
    simpa [prefixWord, tailWord_3653019, baseEnd_3653019] using wordTrace_append hprefix tailTrace_3653019
  have hstable : (prefixWord ++ tailWord_3653019).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3653019).length < 2 ^ (prefixWord ++ tailWord_3653019).sum := by decide
  have hdescent : baseEnd_3653019 < baseStart_3653019 := by decide
  rcases family_descends (prefixWord ++ tailWord_3653019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3653036 : List Nat := [2, 2, 1, 1, 1, 1, 4, 2, 1, 5, 3]
def baseStart_3653036 : Nat := 118140960795 + 3653036 * 2 ^ 59
def prefixEnd_3653036 : Nat := 4983230072969 + 3 ^ 40 * 3653036 * 2
def baseEnd_3653036 : Nat := 1875763316177874713549999

theorem tailTrace_3653036 : CollatzResearch.WordTrace tailWord_3653036 prefixEnd_3653036 1875763316177874713549999 := by
  unfold tailWord_3653036
  simp only [CollatzResearch.WordTrace]
  refine ⟨66618584396840967861789481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88824779195787957149052641 66618584396840967861789481)
  ·
    refine ⟨49963938297630725896342111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66618584396840967861789481 49963938297630725896342111)
    ·
      refine ⟨74945907446446088844513167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49963938297630725896342111 74945907446446088844513167)
      ·
        refine ⟨112418861169669133266769751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74945907446446088844513167 112418861169669133266769751)
        ·
          refine ⟨168628291754503699900154627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112418861169669133266769751 168628291754503699900154627)
          ·
            refine ⟨252942437631755549850231941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 168628291754503699900154627 252942437631755549850231941)
            ·
              refine ⟨47426707055954165596918489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 252942437631755549850231941 47426707055954165596918489)
              ·
                refine ⟨35570030291965624197688867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47426707055954165596918489 35570030291965624197688867)
                ·
                  refine ⟨53355045437948436296533301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35570030291965624197688867 53355045437948436296533301)
                  ·
                    refine ⟨5002035509807665902799997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 53355045437948436296533301 5002035509807665902799997)
                    ·
                      refine ⟨1875763316177874713549999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5002035509807665902799997 1875763316177874713549999)
                      ·
                        rfl

theorem cell23_3653036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 5, 3].length) (baseStart_3653036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3653036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3653036 prefixEnd_3653036 := by exact prefixLift 3653036
  have htrace : WordTrace (prefixWord ++ tailWord_3653036) baseStart_3653036 baseEnd_3653036 := by
    simpa [prefixWord, tailWord_3653036, baseEnd_3653036] using wordTrace_append hprefix tailTrace_3653036
  have hstable : (prefixWord ++ tailWord_3653036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3653036).length < 2 ^ (prefixWord ++ tailWord_3653036).sum := by decide
  have hdescent : baseEnd_3653036 < baseStart_3653036 := by decide
  rcases family_descends (prefixWord ++ tailWord_3653036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3653037 : List Nat := [1, 5, 2, 2, 1, 1, 1, 2, 4, 2, 2]
def baseStart_3653037 : Nat := 118140960795 + 3653037 * 2 ^ 59
def prefixEnd_3653037 : Nat := 4983230072969 + 3 ^ 40 * 3653037 * 2
def baseEnd_3653037 : Nat := 1875763829658529209637495

theorem tailTrace_3653037 : CollatzResearch.WordTrace tailWord_3653037 prefixEnd_3653037 1875763829658529209637495 := by
  unfold tailWord_3653037
  simp only [CollatzResearch.WordTrace]
  refine ⟨133237205266678312894365365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88824803511118875262910243 133237205266678312894365365)
  ·
    refine ⟨12490987993751091833846753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 133237205266678312894365365 12490987993751091833846753)
    ·
      refine ⟨9368240995313318875385065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12490987993751091833846753 9368240995313318875385065)
      ·
        refine ⟨7026180746484989156538799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9368240995313318875385065 7026180746484989156538799)
        ·
          refine ⟨10539271119727483734808199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7026180746484989156538799 10539271119727483734808199)
          ·
            refine ⟨15808906679591225602212299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10539271119727483734808199 15808906679591225602212299)
            ·
              refine ⟨23713360019386838403318449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15808906679591225602212299 23713360019386838403318449)
              ·
                refine ⟨17785020014540128802488837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23713360019386838403318449 17785020014540128802488837)
                ·
                  refine ⟨3334691252726274150466657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17785020014540128802488837 3334691252726274150466657)
                  ·
                    refine ⟨2501018439544705612849993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3334691252726274150466657 2501018439544705612849993)
                    ·
                      refine ⟨1875763829658529209637495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2501018439544705612849993 1875763829658529209637495)
                      ·
                        rfl

theorem cell23_3653037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 1, 2, 4, 2, 2].length) (baseStart_3653037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3653037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3653037 prefixEnd_3653037 := by exact prefixLift 3653037
  have htrace : WordTrace (prefixWord ++ tailWord_3653037) baseStart_3653037 baseEnd_3653037 := by
    simpa [prefixWord, tailWord_3653037, baseEnd_3653037] using wordTrace_append hprefix tailTrace_3653037
  have hstable : (prefixWord ++ tailWord_3653037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3653037).length < 2 ^ (prefixWord ++ tailWord_3653037).sum := by decide
  have hdescent : baseEnd_3653037 < baseStart_3653037 := by decide
  rcases family_descends (prefixWord ++ tailWord_3653037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3653056 : List Nat := [2, 1, 1, 2, 3, 1, 3, 1, 4, 5]
def baseStart_3653056 : Nat := 118140960795 + 3653056 * 2 ^ 59
def prefixEnd_3653056 : Nat := 4983230072969 + 3 ^ 40 * 3653056 * 2
def baseEnd_3653056 : Nat := 625257861930321545099969

theorem tailTrace_3653056 : CollatzResearch.WordTrace tailWord_3653056 prefixEnd_3653056 625257861930321545099969 := by
  unfold tailWord_3653056
  simp only [CollatzResearch.WordTrace]
  refine ⟨66618949126804739569653511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88825265502406319426204681 66618949126804739569653511)
  ·
    refine ⟨99928423690207109354480267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66618949126804739569653511 99928423690207109354480267)
    ·
      refine ⟨149892635535310664031720401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99928423690207109354480267 149892635535310664031720401)
      ·
        refine ⟨112419476651482998023790301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 149892635535310664031720401 112419476651482998023790301)
        ·
          refine ⟨42157303744306124258921363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 112419476651482998023790301 42157303744306124258921363)
          ·
            refine ⟨63235955616459186388382045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42157303744306124258921363 63235955616459186388382045)
            ·
              refine ⟨23713483356172194895643267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 63235955616459186388382045 23713483356172194895643267)
              ·
                refine ⟨35570225034258292343464901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23713483356172194895643267 35570225034258292343464901)
                ·
                  refine ⟨6669417193923429814399669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35570225034258292343464901 6669417193923429814399669)
                  ·
                    refine ⟨625257861930321545099969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6669417193923429814399669 625257861930321545099969)
                    ·
                      rfl

theorem cell23_3653056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 3, 1, 4, 5].length) (baseStart_3653056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3653056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3653056 prefixEnd_3653056 := by exact prefixLift 3653056
  have htrace : WordTrace (prefixWord ++ tailWord_3653056) baseStart_3653056 baseEnd_3653056 := by
    simpa [prefixWord, tailWord_3653056, baseEnd_3653056] using wordTrace_append hprefix tailTrace_3653056
  have hstable : (prefixWord ++ tailWord_3653056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3653056).length < 2 ^ (prefixWord ++ tailWord_3653056).sum := by decide
  have hdescent : baseEnd_3653056 < baseStart_3653056 := by decide
  rcases family_descends (prefixWord ++ tailWord_3653056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3653060 : List Nat := [2, 3, 3, 2, 1, 3, 1, 1, 7]
def baseStart_3653060 : Nat := 118140960795 + 3653060 * 2 ^ 59
def prefixEnd_3653060 : Nat := 4983230072969 + 3 ^ 40 * 3653060 * 2
def baseEnd_3653060 : Nat := 208419515523731402183321

theorem tailTrace_3653060 : CollatzResearch.WordTrace tailWord_3653060 prefixEnd_3653060 208419515523731402183321 := by
  unfold tailWord_3653060
  simp only [CollatzResearch.WordTrace]
  refine ⟨66619022072797493911226317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88825362763729991881635089 66619022072797493911226317)
  ·
    refine ⟨24982133277299060216709869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66619022072797493911226317 24982133277299060216709869)
    ·
      refine ⟨9368299978987147581266201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24982133277299060216709869 9368299978987147581266201)
      ·
        refine ⟨7026224984240360685949651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9368299978987147581266201 7026224984240360685949651)
        ·
          refine ⟨10539337476360541028924477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7026224984240360685949651 10539337476360541028924477)
          ·
            refine ⟨3952251553635202885846679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10539337476360541028924477 3952251553635202885846679)
            ·
              refine ⟨5928377330452804328770019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3952251553635202885846679 5928377330452804328770019)
              ·
                refine ⟨8892565995679206493155029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5928377330452804328770019 8892565995679206493155029)
                ·
                  refine ⟨208419515523731402183321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8892565995679206493155029 208419515523731402183321)
                  ·
                    rfl

theorem cell23_3653060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 3, 1, 1, 7].length) (baseStart_3653060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3653060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3653060 prefixEnd_3653060 := by exact prefixLift 3653060
  have htrace : WordTrace (prefixWord ++ tailWord_3653060) baseStart_3653060 baseEnd_3653060 := by
    simpa [prefixWord, tailWord_3653060, baseEnd_3653060] using wordTrace_append hprefix tailTrace_3653060
  have hstable : (prefixWord ++ tailWord_3653060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3653060).length < 2 ^ (prefixWord ++ tailWord_3653060).sum := by decide
  have hdescent : baseEnd_3653060 < baseStart_3653060 := by decide
  rcases family_descends (prefixWord ++ tailWord_3653060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3653063 : List Nat := [1, 1, 4, 1, 1, 3, 2, 1, 2, 5, 2]
def baseStart_3653063 : Nat := 118140960795 + 3653063 * 2 ^ 59
def prefixEnd_3653063 : Nat := 4983230072969 + 3 ^ 40 * 3653063 * 2
def baseEnd_3653063 : Nat := 1875777180155546107912375

theorem tailTrace_3653063 : CollatzResearch.WordTrace tailWord_3653063 prefixEnd_3653063 1875777180155546107912375 := by
  unfold tailWord_3653063
  simp only [CollatzResearch.WordTrace]
  refine ⟨133238153564584119334811843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88825435709722746223207895 133238153564584119334811843)
  ·
    refine ⟨199857230346876179002217765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133238153564584119334811843 199857230346876179002217765)
    ·
      refine ⟨37473230690039283562915831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 199857230346876179002217765 37473230690039283562915831)
      ·
        refine ⟨56209846035058925344373747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37473230690039283562915831 56209846035058925344373747)
        ·
          refine ⟨84314769052588388016560621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56209846035058925344373747 84314769052588388016560621)
          ·
            refine ⟨31618038394720645506210233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 84314769052588388016560621 31618038394720645506210233)
            ·
              refine ⟨23713528796040484129657675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31618038394720645506210233 23713528796040484129657675)
              ·
                refine ⟨35570293194060726194486513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23713528796040484129657675 35570293194060726194486513)
                ·
                  refine ⟨26677719895545544645864885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35570293194060726194486513 26677719895545544645864885)
                  ·
                    refine ⟨2501036240207394810549833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 26677719895545544645864885 2501036240207394810549833)
                    ·
                      refine ⟨1875777180155546107912375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2501036240207394810549833 1875777180155546107912375)
                      ·
                        rfl

theorem cell23_3653063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 2, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 2, 1, 2, 5, 2].length) (baseStart_3653063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3653063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3653063 prefixEnd_3653063 := by exact prefixLift 3653063
  have htrace : WordTrace (prefixWord ++ tailWord_3653063) baseStart_3653063 baseEnd_3653063 := by
    simpa [prefixWord, tailWord_3653063, baseEnd_3653063] using wordTrace_append hprefix tailTrace_3653063
  have hstable : (prefixWord ++ tailWord_3653063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3653063).length < 2 ^ (prefixWord ++ tailWord_3653063).sum := by decide
  have hdescent : baseEnd_3653063 < baseStart_3653063 := by decide
  rcases family_descends (prefixWord ++ tailWord_3653063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3653066 : List Nat := [3, 1, 2, 1, 2, 3, 1, 1, 1, 1, 7]
def baseStart_3653066 : Nat := 118140960795 + 3653066 * 2 ^ 59
def prefixEnd_3653066 : Nat := 4983230072969 + 3 ^ 40 * 3653066 * 2
def baseEnd_3653066 : Nat := 1875778720597509596174861

theorem tailTrace_3653066 : CollatzResearch.WordTrace tailWord_3653066 prefixEnd_3653066 1875778720597509596174861 := by
  unfold tailWord_3653066
  simp only [CollatzResearch.WordTrace]
  refine ⟨33309565745893312711792763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88825508655715500564780701 33309565745893312711792763)
  ·
    refine ⟨49964348618839969067689145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33309565745893312711792763 49964348618839969067689145)
    ·
      refine ⟨37473261464129976800766859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49964348618839969067689145 37473261464129976800766859)
      ·
        refine ⟨56209892196194965201150289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37473261464129976800766859 56209892196194965201150289)
        ·
          refine ⟨42157419147146223900862717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56209892196194965201150289 42157419147146223900862717)
          ·
            refine ⟨15809032180179833962823519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42157419147146223900862717 15809032180179833962823519)
            ·
              refine ⟨23713548270269750944235279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15809032180179833962823519 23713548270269750944235279)
              ·
                refine ⟨35570322405404626416352919, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23713548270269750944235279 35570322405404626416352919)
                ·
                  refine ⟨53355483608106939624529379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35570322405404626416352919 53355483608106939624529379)
                  ·
                    refine ⟨80033225412160409436794069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 53355483608106939624529379 80033225412160409436794069)
                    ·
                      refine ⟨1875778720597509596174861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 80033225412160409436794069 1875778720597509596174861)
                      ·
                        rfl

theorem cell23_3653066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 1, 1, 1, 1, 7].length) (baseStart_3653066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3653066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3653066 prefixEnd_3653066 := by exact prefixLift 3653066
  have htrace : WordTrace (prefixWord ++ tailWord_3653066) baseStart_3653066 baseEnd_3653066 := by
    simpa [prefixWord, tailWord_3653066, baseEnd_3653066] using wordTrace_append hprefix tailTrace_3653066
  have hstable : (prefixWord ++ tailWord_3653066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3653066).length < 2 ^ (prefixWord ++ tailWord_3653066).sum := by decide
  have hdescent : baseEnd_3653066 < baseStart_3653066 := by decide
  rcases family_descends (prefixWord ++ tailWord_3653066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3653110 : List Nat := [5, 1, 1, 1, 2, 2, 2, 2, 2, 1, 4]
def baseStart_3653110 : Nat := 118140960795 + 3653110 * 2 ^ 59
def prefixEnd_3653110 : Nat := 4983230072969 + 3 ^ 40 * 3653110 * 2
def baseEnd_3653110 : Nat := 1875801313746307424024659

theorem tailTrace_3653110 : CollatzResearch.WordTrace tailWord_3653110 prefixEnd_3653110 1875801313746307424024659 := by
  unfold tailWord_3653110
  simp only [CollatzResearch.WordTrace]
  refine ⟨8327491737213365397610799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 88826578530275897574515189 8327491737213365397610799)
  ·
    refine ⟨12491237605820048096416199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8327491737213365397610799 12491237605820048096416199)
    ·
      refine ⟨18736856408730072144624299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12491237605820048096416199 18736856408730072144624299)
      ·
        refine ⟨28105284613095108216936449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18736856408730072144624299 28105284613095108216936449)
        ·
          refine ⟨21078963459821331162702337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28105284613095108216936449 21078963459821331162702337)
          ·
            refine ⟨15809222594865998372026753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21078963459821331162702337 15809222594865998372026753)
            ·
              refine ⟨11856916946149498779020065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15809222594865998372026753 11856916946149498779020065)
              ·
                refine ⟨8892687709612124084265049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11856916946149498779020065 8892687709612124084265049)
                ·
                  refine ⟨6669515782209093063198787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8892687709612124084265049 6669515782209093063198787)
                  ·
                    refine ⟨10004273673313639594798181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6669515782209093063198787 10004273673313639594798181)
                    ·
                      refine ⟨1875801313746307424024659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10004273673313639594798181 1875801313746307424024659)
                      ·
                        rfl

theorem cell23_3653110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 2, 2, 2, 1, 4].length) (baseStart_3653110 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3653110 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3653110 prefixEnd_3653110 := by exact prefixLift 3653110
  have htrace : WordTrace (prefixWord ++ tailWord_3653110) baseStart_3653110 baseEnd_3653110 := by
    simpa [prefixWord, tailWord_3653110, baseEnd_3653110] using wordTrace_append hprefix tailTrace_3653110
  have hstable : (prefixWord ++ tailWord_3653110).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3653110).length < 2 ^ (prefixWord ++ tailWord_3653110).sum := by decide
  have hdescent : baseEnd_3653110 < baseStart_3653110 := by decide
  rcases family_descends (prefixWord ++ tailWord_3653110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3653116 : List Nat := [2, 2, 2, 1, 2, 1, 2, 3, 8]
def baseStart_3653116 : Nat := 118140960795 + 3653116 * 2 ^ 59
def prefixEnd_3653116 : Nat := 4983230072969 + 3 ^ 40 * 3653116 * 2
def baseEnd_3653116 : Nat := 208422710514470488949959

theorem tailTrace_3653116 : CollatzResearch.WordTrace tailWord_3653116 prefixEnd_3653116 208422710514470488949959 := by
  unfold tailWord_3653116
  simp only [CollatzResearch.WordTrace]
  refine ⟨66620043316696054693245601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88826724422261406257660801 66620043316696054693245601)
  ·
    refine ⟨49965032487522041019934201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66620043316696054693245601 49965032487522041019934201)
    ·
      refine ⟨37473774365641530764950651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49965032487522041019934201 37473774365641530764950651)
      ·
        refine ⟨56210661548462296147425977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37473774365641530764950651 56210661548462296147425977)
        ·
          refine ⟨42157996161346722110569483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56210661548462296147425977 42157996161346722110569483)
          ·
            refine ⟨63236994242020083165854225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42157996161346722110569483 63236994242020083165854225)
            ·
              refine ⟨47427745681515062374390669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63236994242020083165854225 47427745681515062374390669)
              ·
                refine ⟨17785404630568148390396501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47427745681515062374390669 17785404630568148390396501)
                ·
                  refine ⟨208422710514470488949959, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 17785404630568148390396501 208422710514470488949959)
                  ·
                    rfl

theorem cell23_3653116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 2, 3, 8].length) (baseStart_3653116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3653116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3653116 prefixEnd_3653116 := by exact prefixLift 3653116
  have htrace : WordTrace (prefixWord ++ tailWord_3653116) baseStart_3653116 baseEnd_3653116 := by
    simpa [prefixWord, tailWord_3653116, baseEnd_3653116] using wordTrace_append hprefix tailTrace_3653116
  have hstable : (prefixWord ++ tailWord_3653116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3653116).length < 2 ^ (prefixWord ++ tailWord_3653116).sum := by decide
  have hdescent : baseEnd_3653116 < baseStart_3653116 := by decide
  rcases family_descends (prefixWord ++ tailWord_3653116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3653170 : List Nat := [3, 2, 1, 1, 2, 1, 1, 3, 4, 3, 2]
def baseStart_3653170 : Nat := 118140960795 + 3653170 * 2 ^ 59
def prefixEnd_3653170 : Nat := 4983230072969 + 3 ^ 40 * 3653170 * 2
def baseEnd_3653170 : Nat := 1875832122585577189274383

theorem tailTrace_3653170 : CollatzResearch.WordTrace tailWord_3653170 prefixEnd_3653170 1875832122585577189274383 := by
  unfold tailWord_3653170
  simp only [CollatzResearch.WordTrace]
  refine ⟨33310514043799119152239241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88828037450130984405971309 33310514043799119152239241)
  ·
    refine ⟨24982885532849339364179431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33310514043799119152239241 24982885532849339364179431)
    ·
      refine ⟨37474328299274009046269147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24982885532849339364179431 37474328299274009046269147)
      ·
        refine ⟨56211492448911013569403721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37474328299274009046269147 56211492448911013569403721)
        ·
          refine ⟨42158619336683260177052791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56211492448911013569403721 42158619336683260177052791)
          ·
            refine ⟨63237929005024890265579187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42158619336683260177052791 63237929005024890265579187)
            ·
              refine ⟨94856893507537335398368781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63237929005024890265579187 94856893507537335398368781)
              ·
                refine ⟨35571335065326500774388293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 94856893507537335398368781 35571335065326500774388293)
                ·
                  refine ⟨6669625324748718895197805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35571335065326500774388293 6669625324748718895197805)
                  ·
                    refine ⟨2501109496780769585699177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6669625324748718895197805 2501109496780769585699177)
                    ·
                      refine ⟨1875832122585577189274383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2501109496780769585699177 1875832122585577189274383)
                      ·
                        rfl

theorem cell23_3653170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 3, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 3, 4, 3, 2].length) (baseStart_3653170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3653170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3653170 prefixEnd_3653170 := by exact prefixLift 3653170
  have htrace : WordTrace (prefixWord ++ tailWord_3653170) baseStart_3653170 baseEnd_3653170 := by
    simpa [prefixWord, tailWord_3653170, baseEnd_3653170] using wordTrace_append hprefix tailTrace_3653170
  have hstable : (prefixWord ++ tailWord_3653170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3653170).length < 2 ^ (prefixWord ++ tailWord_3653170).sum := by decide
  have hdescent : baseEnd_3653170 < baseStart_3653170 := by decide
  rcases family_descends (prefixWord ++ tailWord_3653170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3653177 : List Nat := [1, 2, 1, 5, 1, 3, 2, 1, 3, 1, 3]
def baseStart_3653177 : Nat := 118140960795 + 3653177 * 2 ^ 59
def prefixEnd_3653177 : Nat := 4983230072969 + 3 ^ 40 * 3653177 * 2
def baseEnd_3653177 : Nat := 1875835716950158661886851

theorem tailTrace_3653177 : CollatzResearch.WordTrace tailWord_3653177 prefixEnd_3653177 1875835716950158661886851 := by
  unfold tailWord_3653177
  simp only [CollatzResearch.WordTrace]
  refine ⟨133242311486171116804461785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88828207657447411202974523 133242311486171116804461785)
  ·
    refine ⟨99931733614628337603346339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133242311486171116804461785 99931733614628337603346339)
    ·
      refine ⟨149897600421942506405019509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99931733614628337603346339 149897600421942506405019509)
      ·
        refine ⟨14052900039557109975470579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 149897600421942506405019509 14052900039557109975470579)
        ·
          refine ⟨21079350059335664963205869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14052900039557109975470579 21079350059335664963205869)
          ·
            refine ⟨7904756272250874361202201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21079350059335664963205869 7904756272250874361202201)
            ·
              refine ⟨5928567204188155770901651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7904756272250874361202201 5928567204188155770901651)
              ·
                refine ⟨8892850806282233656352477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5928567204188155770901651 8892850806282233656352477)
                ·
                  refine ⟨3334819052355837621132179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8892850806282233656352477 3334819052355837621132179)
                  ·
                    refine ⟨5002228578533756431698269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3334819052355837621132179 5002228578533756431698269)
                    ·
                      refine ⟨1875835716950158661886851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5002228578533756431698269 1875835716950158661886851)
                      ·
                        rfl

theorem cell23_3653177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 3, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 3, 2, 1, 3, 1, 3].length) (baseStart_3653177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3653177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3653177 prefixEnd_3653177 := by exact prefixLift 3653177
  have htrace : WordTrace (prefixWord ++ tailWord_3653177) baseStart_3653177 baseEnd_3653177 := by
    simpa [prefixWord, tailWord_3653177, baseEnd_3653177] using wordTrace_append hprefix tailTrace_3653177
  have hstable : (prefixWord ++ tailWord_3653177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3653177).length < 2 ^ (prefixWord ++ tailWord_3653177).sum := by decide
  have hdescent : baseEnd_3653177 < baseStart_3653177 := by decide
  rcases family_descends (prefixWord ++ tailWord_3653177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3653200 : List Nat := [2, 1, 1, 1, 1, 3, 6, 2, 1, 1, 4]
def baseStart_3653200 : Nat := 118140960795 + 3653200 * 2 ^ 59
def prefixEnd_3653200 : Nat := 4983230072969 + 3 ^ 40 * 3653200 * 2
def baseEnd_3653200 : Nat := 1875847527005212071899245

theorem tailTrace_3653200 : CollatzResearch.WordTrace tailWord_3653200 prefixEnd_3653200 1875847527005212071899245 := by
  unfold tailWord_3653200
  simp only [CollatzResearch.WordTrace]
  refine ⟨66621575182543895866274527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88828766910058527821699369 66621575182543895866274527)
  ·
    refine ⟨99932362773815843799411791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66621575182543895866274527 99932362773815843799411791)
    ·
      refine ⟨149898544160723765699117687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99932362773815843799411791 149898544160723765699117687)
      ·
        refine ⟨224847816241085648548676531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149898544160723765699117687 224847816241085648548676531)
        ·
          refine ⟨337271724361628472823014797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 224847816241085648548676531 337271724361628472823014797)
          ·
            refine ⟨126476896635610677308630549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 337271724361628472823014797 126476896635610677308630549)
            ·
              refine ⟨5928604529794250498842057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 126476896635610677308630549 5928604529794250498842057)
              ·
                refine ⟨4446453397345687874131543, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5928604529794250498842057 4446453397345687874131543)
                ·
                  refine ⟨6669680096018531811197315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4446453397345687874131543 6669680096018531811197315)
                  ·
                    refine ⟨10004520144027797716795973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6669680096018531811197315 10004520144027797716795973)
                    ·
                      refine ⟨1875847527005212071899245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10004520144027797716795973 1875847527005212071899245)
                      ·
                        rfl

theorem cell23_3653200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 6, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 6, 2, 1, 1, 4].length) (baseStart_3653200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3653200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3653200 prefixEnd_3653200 := by exact prefixLift 3653200
  have htrace : WordTrace (prefixWord ++ tailWord_3653200) baseStart_3653200 baseEnd_3653200 := by
    simpa [prefixWord, tailWord_3653200, baseEnd_3653200] using wordTrace_append hprefix tailTrace_3653200
  have hstable : (prefixWord ++ tailWord_3653200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3653200).length < 2 ^ (prefixWord ++ tailWord_3653200).sum := by decide
  have hdescent : baseEnd_3653200 < baseStart_3653200 := by decide
  rcases family_descends (prefixWord ++ tailWord_3653200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3653220 : List Nat := [2, 3, 1, 1, 2, 4, 2, 1, 1, 1, 5]
def baseStart_3653220 : Nat := 118140960795 + 3653220 * 2 ^ 59
def prefixEnd_3653220 : Nat := 4983230072969 + 3 ^ 40 * 3653220 * 2
def baseEnd_3653220 : Nat := 1875857796618301993649153

theorem tailTrace_3653220 : CollatzResearch.WordTrace tailWord_3653220 prefixEnd_3653220 1875857796618301993649153 := by
  unfold tailWord_3653220
  simp only [CollatzResearch.WordTrace]
  refine ⟨66621939912507667574138557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88829253216676890098851409 66621939912507667574138557)
  ·
    refine ⟨24983227467190375340301959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66621939912507667574138557 24983227467190375340301959)
    ·
      refine ⟨37474841200785563010452939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24983227467190375340301959 37474841200785563010452939)
      ·
        refine ⟨56212261801178344515679409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37474841200785563010452939 56212261801178344515679409)
        ·
          refine ⟨42159196350883758386759557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56212261801178344515679409 42159196350883758386759557)
          ·
            refine ⟨7904849315790704697517417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 42159196350883758386759557 7904849315790704697517417)
            ·
              refine ⟨5928636986843028523138063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7904849315790704697517417 5928636986843028523138063)
              ·
                refine ⟨8892955480264542784707095, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5928636986843028523138063 8892955480264542784707095)
                ·
                  refine ⟨13339433220396814177060643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8892955480264542784707095 13339433220396814177060643)
                  ·
                    refine ⟨20009149830595221265590965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13339433220396814177060643 20009149830595221265590965)
                    ·
                      refine ⟨1875857796618301993649153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20009149830595221265590965 1875857796618301993649153)
                      ·
                        rfl

theorem cell23_3653220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 4, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 4, 2, 1, 1, 1, 5].length) (baseStart_3653220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3653220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3653220 prefixEnd_3653220 := by exact prefixLift 3653220
  have htrace : WordTrace (prefixWord ++ tailWord_3653220) baseStart_3653220 baseEnd_3653220 := by
    simpa [prefixWord, tailWord_3653220, baseEnd_3653220] using wordTrace_append hprefix tailTrace_3653220
  have hstable : (prefixWord ++ tailWord_3653220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3653220).length < 2 ^ (prefixWord ++ tailWord_3653220).sum := by decide
  have hdescent : baseEnd_3653220 < baseStart_3653220 := by decide
  rcases family_descends (prefixWord ++ tailWord_3653220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3653234 : List Nat := [3, 2, 1, 2, 3, 1, 3, 1, 3, 2, 2]
def baseStart_3653234 : Nat := 118140960795 + 3653234 * 2 ^ 59
def prefixEnd_3653234 : Nat := 4983230072969 + 3 ^ 40 * 3653234 * 2
def baseEnd_3653234 : Nat := 1875864985347464938874089

theorem tailTrace_3653234 : CollatzResearch.WordTrace tailWord_3653234 prefixEnd_3653234 1875864985347464938874089 := by
  unfold tailWord_3653234
  simp only [CollatzResearch.WordTrace]
  refine ⟨33311097611741153884821689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88829593631309743692857837 33311097611741153884821689)
  ·
    refine ⟨24983323208805865413616267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33311097611741153884821689 24983323208805865413616267)
    ·
      refine ⟨37474984813208798120424401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24983323208805865413616267 37474984813208798120424401)
      ·
        refine ⟨28106238609906598590318301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37474984813208798120424401 28106238609906598590318301)
        ·
          refine ⟨10539839478714974471369363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28106238609906598590318301 10539839478714974471369363)
          ·
            refine ⟨15809759218072461707054045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10539839478714974471369363 15809759218072461707054045)
            ·
              refine ⟨5928659706777173140145267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15809759218072461707054045 5928659706777173140145267)
              ·
                refine ⟨8892989560165759710217901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5928659706777173140145267 8892989560165759710217901)
                ·
                  refine ⟨3334871085062159891331713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8892989560165759710217901 3334871085062159891331713)
                  ·
                    refine ⟨2501153313796619918498785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3334871085062159891331713 2501153313796619918498785)
                    ·
                      refine ⟨1875864985347464938874089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2501153313796619918498785 1875864985347464938874089)
                      ·
                        rfl

theorem cell23_3653234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 3, 1, 3, 2, 2].length) (baseStart_3653234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3653234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3653234 prefixEnd_3653234 := by exact prefixLift 3653234
  have htrace : WordTrace (prefixWord ++ tailWord_3653234) baseStart_3653234 baseEnd_3653234 := by
    simpa [prefixWord, tailWord_3653234, baseEnd_3653234] using wordTrace_append hprefix tailTrace_3653234
  have hstable : (prefixWord ++ tailWord_3653234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3653234).length < 2 ^ (prefixWord ++ tailWord_3653234).sum := by decide
  have hdescent : baseEnd_3653234 < baseStart_3653234 := by decide
  rcases family_descends (prefixWord ++ tailWord_3653234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3653283 : List Nat := [1, 1, 1, 4, 1, 1, 4, 2, 2, 6]
def baseStart_3653283 : Nat := 118140960795 + 3653283 * 2 ^ 59
def prefixEnd_3653283 : Nat := 4983230072969 + 3 ^ 40 * 3653283 * 2
def baseEnd_3653283 : Nat := 625296715299845082387121

theorem tailTrace_3653283 : CollatzResearch.WordTrace tailWord_3653283 prefixEnd_3653283 625296715299845082387121 := by
  unfold tailWord_3653283
  simp only [CollatzResearch.WordTrace]
  refine ⟨133246177623787096907820503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88830785082524731271880335 133246177623787096907820503)
  ·
    refine ⟨199869266435680645361730755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133246177623787096907820503 199869266435680645361730755)
    ·
      refine ⟨299803899653520968042596133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 199869266435680645361730755 299803899653520968042596133)
      ·
        refine ⟨56213231185035181507986775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 299803899653520968042596133 56213231185035181507986775)
        ·
          refine ⟨84319846777552772261980163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56213231185035181507986775 84319846777552772261980163)
          ·
            refine ⟨126479770166329158392970245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84319846777552772261980163 126479770166329158392970245)
            ·
              refine ⟨23714956906186717198681921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 126479770166329158392970245 23714956906186717198681921)
              ·
                refine ⟨17786217679640037899011441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23714956906186717198681921 17786217679640037899011441)
                ·
                  refine ⟨13339663259730028424258581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17786217679640037899011441 13339663259730028424258581)
                  ·
                    refine ⟨625296715299845082387121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 13339663259730028424258581 625296715299845082387121)
                    ·
                      rfl

theorem cell23_3653283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 4, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 4, 2, 2, 6].length) (baseStart_3653283 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3653283 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3653283 prefixEnd_3653283 := by exact prefixLift 3653283
  have htrace : WordTrace (prefixWord ++ tailWord_3653283) baseStart_3653283 baseEnd_3653283 := by
    simpa [prefixWord, tailWord_3653283, baseEnd_3653283] using wordTrace_append hprefix tailTrace_3653283
  have hstable : (prefixWord ++ tailWord_3653283).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3653283).length < 2 ^ (prefixWord ++ tailWord_3653283).sum := by decide
  have hdescent : baseEnd_3653283 < baseStart_3653283 := by decide
  rcases family_descends (prefixWord ++ tailWord_3653283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3653284 : List Nat := [2, 3, 1, 2, 2, 3, 2, 2, 2, 1, 3]
def baseStart_3653284 : Nat := 118140960795 + 3653284 * 2 ^ 59
def prefixEnd_3653284 : Nat := 4983230072969 + 3 ^ 40 * 3653284 * 2
def baseEnd_3653284 : Nat := 1875890659380189743248859

theorem tailTrace_3653284 : CollatzResearch.WordTrace tailWord_3653284 prefixEnd_3653284 1875890659380189743248859 := by
  unfold tailWord_3653284
  simp only [CollatzResearch.WordTrace]
  refine ⟨66623107048391737039303453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88830809397855649385737937 66623107048391737039303453)
  ·
    refine ⟨24983665143146901389738795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66623107048391737039303453 24983665143146901389738795)
    ·
      refine ⟨37475497714720352084608193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24983665143146901389738795 37475497714720352084608193)
      ·
        refine ⟨28106623286040264063456145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37475497714720352084608193 28106623286040264063456145)
        ·
          refine ⟨21079967464530198047592109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28106623286040264063456145 21079967464530198047592109)
          ·
            refine ⟨7904987799198824267847041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21079967464530198047592109 7904987799198824267847041)
            ·
              refine ⟨5928740849399118200885281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7904987799198824267847041 5928740849399118200885281)
              ·
                refine ⟨4446555637049338650663961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5928740849399118200885281 4446555637049338650663961)
                ·
                  refine ⟨3334916727787003987997971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4446555637049338650663961 3334916727787003987997971)
                  ·
                    refine ⟨5002375091680505981996957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3334916727787003987997971 5002375091680505981996957)
                    ·
                      refine ⟨1875890659380189743248859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5002375091680505981996957 1875890659380189743248859)
                      ·
                        rfl

theorem cell23_3653284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 3, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 3, 2, 2, 2, 1, 3].length) (baseStart_3653284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3653284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3653284 prefixEnd_3653284 := by exact prefixLift 3653284
  have htrace : WordTrace (prefixWord ++ tailWord_3653284) baseStart_3653284 baseEnd_3653284 := by
    simpa [prefixWord, tailWord_3653284, baseEnd_3653284] using wordTrace_append hprefix tailTrace_3653284
  have hstable : (prefixWord ++ tailWord_3653284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3653284).length < 2 ^ (prefixWord ++ tailWord_3653284).sum := by decide
  have hdescent : baseEnd_3653284 < baseStart_3653284 := by decide
  rcases family_descends (prefixWord ++ tailWord_3653284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3653347 : List Nat := [1, 1, 1, 7, 2, 1, 2, 1, 7]
def baseStart_3653347 : Nat := 118140960795 + 3653347 * 2 ^ 59
def prefixEnd_3653347 : Nat := 4983230072969 + 3 ^ 40 * 3653347 * 2
def baseEnd_3653347 : Nat := 208435889851269221862341

theorem tailTrace_3653347 : CollatzResearch.WordTrace tailWord_3653347 prefixEnd_3653347 208435889851269221862341 := by
  unfold tailWord_3653347
  simp only [CollatzResearch.WordTrace]
  refine ⟨133248511895555235838150295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88832341263703490558766863 133248511895555235838150295)
  ·
    refine ⟨199872767843332853757225443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133248511895555235838150295 199872767843332853757225443)
    ·
      refine ⟨299809151764999280635838165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 199872767843332853757225443 299809151764999280635838165)
      ·
        refine ⟨7026776994492170639902457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 299809151764999280635838165 7026776994492170639902457)
        ·
          refine ⟨5270082745869127979926843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7026776994492170639902457 5270082745869127979926843)
          ·
            refine ⟨7905124118803691969890265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5270082745869127979926843 7905124118803691969890265)
            ·
              refine ⟨5928843089102768977417699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7905124118803691969890265 5928843089102768977417699)
              ·
                refine ⟨8893264633654153466126549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5928843089102768977417699 8893264633654153466126549)
                ·
                  refine ⟨208435889851269221862341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8893264633654153466126549 208435889851269221862341)
                  ·
                    rfl

theorem cell23_3653347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 1, 2, 1, 7].length) (baseStart_3653347 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3653347 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3653347 prefixEnd_3653347 := by exact prefixLift 3653347
  have htrace : WordTrace (prefixWord ++ tailWord_3653347) baseStart_3653347 baseEnd_3653347 := by
    simpa [prefixWord, tailWord_3653347, baseEnd_3653347] using wordTrace_append hprefix tailTrace_3653347
  have hstable : (prefixWord ++ tailWord_3653347).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3653347).length < 2 ^ (prefixWord ++ tailWord_3653347).sum := by decide
  have hdescent : baseEnd_3653347 < baseStart_3653347 := by decide
  rcases family_descends (prefixWord ++ tailWord_3653347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3653353 : List Nat := [1, 2, 1, 1, 1, 2, 3, 3, 1, 1, 7]
def baseStart_3653353 : Nat := 118140960795 + 3653353 * 2 ^ 59
def prefixEnd_3653353 : Nat := 4983230072969 + 3 ^ 40 * 3653353 * 2
def baseEnd_3653353 : Nat := 1875926089545349973286041

theorem tailTrace_3653353 : CollatzResearch.WordTrace tailWord_3653353 prefixEnd_3653353 1875926089545349973286041 := by
  unfold tailWord_3653353
  simp only [CollatzResearch.WordTrace]
  refine ⟨133248730733533498862868713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88832487155688999241912475 133248730733533498862868713)
  ·
    refine ⟨99936548050150124147151535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133248730733533498862868713 99936548050150124147151535)
    ·
      refine ⟨149904822075225186220727303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99936548050150124147151535 149904822075225186220727303)
      ·
        refine ⟨224857233112837779331090955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149904822075225186220727303 224857233112837779331090955)
        ·
          refine ⟨337285849669256668996636433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 224857233112837779331090955 337285849669256668996636433)
          ·
            refine ⟨252964387251942501747477325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 337285849669256668996636433 252964387251942501747477325)
            ·
              refine ⟨94861645219478438155303997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 252964387251942501747477325 94861645219478438155303997)
              ·
                refine ⟨35573116957304414308238999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 94861645219478438155303997 35573116957304414308238999)
                ·
                  refine ⟨53359675435956621462358499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35573116957304414308238999 53359675435956621462358499)
                  ·
                    refine ⟨80039513153934932193537749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 53359675435956621462358499 80039513153934932193537749)
                    ·
                      refine ⟨1875926089545349973286041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 80039513153934932193537749 1875926089545349973286041)
                      ·
                        rfl

theorem cell23_3653353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 3, 1, 1, 7].length) (baseStart_3653353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3653353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3653353 prefixEnd_3653353 := by exact prefixLift 3653353
  have htrace : WordTrace (prefixWord ++ tailWord_3653353) baseStart_3653353 baseEnd_3653353 := by
    simpa [prefixWord, tailWord_3653353, baseEnd_3653353] using wordTrace_append hprefix tailTrace_3653353
  have hstable : (prefixWord ++ tailWord_3653353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3653353).length < 2 ^ (prefixWord ++ tailWord_3653353).sum := by decide
  have hdescent : baseEnd_3653353 < baseStart_3653353 := by decide
  rcases family_descends (prefixWord ++ tailWord_3653353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3653357 : List Nat := [1, 5, 1, 2, 1, 2, 2, 1, 2, 3, 3]
def baseStart_3653357 : Nat := 118140960795 + 3653357 * 2 ^ 59
def prefixEnd_3653357 : Nat := 4983230072969 + 3 ^ 40 * 3653357 * 2
def baseEnd_3653357 : Nat := 1875928143467967957636023

theorem tailTrace_3653357 : CollatzResearch.WordTrace tailWord_3653357 prefixEnd_3653357 1875928143467967957636023 := by
  unfold tailWord_3653357
  simp only [CollatzResearch.WordTrace]
  refine ⟨133248876625519007546014325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88832584417012671697342883 133248876625519007546014325)
  ·
    refine ⟨12492082183642406957438843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 133248876625519007546014325 12492082183642406957438843)
    ·
      refine ⟨18738123275463610436158265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12492082183642406957438843 18738123275463610436158265)
      ·
        refine ⟨14053592456597707827118699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18738123275463610436158265 14053592456597707827118699)
        ·
          refine ⟨21080388684896561740678049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14053592456597707827118699 21080388684896561740678049)
          ·
            refine ⟨15810291513672421305508537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21080388684896561740678049 15810291513672421305508537)
            ·
              refine ⟨11857718635254315979131403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15810291513672421305508537 11857718635254315979131403)
              ·
                refine ⟨17786577952881473968697105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11857718635254315979131403 17786577952881473968697105)
                ·
                  refine ⟨13339933464661105476522829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17786577952881473968697105 13339933464661105476522829)
                  ·
                    refine ⟨5002475049247914553696061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13339933464661105476522829 5002475049247914553696061)
                    ·
                      refine ⟨1875928143467967957636023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5002475049247914553696061 1875928143467967957636023)
                      ·
                        rfl

theorem cell23_3653357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 2, 1, 2, 3, 3].length) (baseStart_3653357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3653357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3653357 prefixEnd_3653357 := by exact prefixLift 3653357
  have htrace : WordTrace (prefixWord ++ tailWord_3653357) baseStart_3653357 baseEnd_3653357 := by
    simpa [prefixWord, tailWord_3653357, baseEnd_3653357] using wordTrace_append hprefix tailTrace_3653357
  have hstable : (prefixWord ++ tailWord_3653357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3653357).length < 2 ^ (prefixWord ++ tailWord_3653357).sum := by decide
  have hdescent : baseEnd_3653357 < baseStart_3653357 := by decide
  rcases family_descends (prefixWord ++ tailWord_3653357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3653364 : List Nat := [2, 6, 1, 1, 1, 1, 2, 2, 7]
def baseStart_3653364 : Nat := 118140960795 + 3653364 * 2 ^ 59
def prefixEnd_3653364 : Nat := 4983230072969 + 3 ^ 40 * 3653364 * 2
def baseEnd_3653364 : Nat := 208436859759172158916499

theorem tailTrace_3653364 : CollatzResearch.WordTrace tailWord_3653364 prefixEnd_3653364 208436859759172158916499 := by
  unfold tailWord_3653364
  simp only [CollatzResearch.WordTrace]
  refine ⟨66624565968246823870759573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88832754624329098494346097 66624565968246823870759573)
  ·
    refine ⟨3123026529761569868941855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 66624565968246823870759573 3123026529761569868941855)
    ·
      refine ⟨4684539794642354803412783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3123026529761569868941855 4684539794642354803412783)
      ·
        refine ⟨7026809691963532205119175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4684539794642354803412783 7026809691963532205119175)
        ·
          refine ⟨10540214537945298307678763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7026809691963532205119175 10540214537945298307678763)
          ·
            refine ⟨15810321806917947461518145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10540214537945298307678763 15810321806917947461518145)
            ·
              refine ⟨11857741355188460596138609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15810321806917947461518145 11857741355188460596138609)
              ·
                refine ⟨8893306016391345447103957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11857741355188460596138609 8893306016391345447103957)
                ·
                  refine ⟨208436859759172158916499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8893306016391345447103957 208436859759172158916499)
                  ·
                    rfl

theorem cell23_3653364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 2, 2, 7].length) (baseStart_3653364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3653364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3653364 prefixEnd_3653364 := by exact prefixLift 3653364
  have htrace : WordTrace (prefixWord ++ tailWord_3653364) baseStart_3653364 baseEnd_3653364 := by
    simpa [prefixWord, tailWord_3653364, baseEnd_3653364] using wordTrace_append hprefix tailTrace_3653364
  have hstable : (prefixWord ++ tailWord_3653364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3653364).length < 2 ^ (prefixWord ++ tailWord_3653364).sum := by decide
  have hdescent : baseEnd_3653364 < baseStart_3653364 := by decide
  rcases family_descends (prefixWord ++ tailWord_3653364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3653394 : List Nat := [3, 2, 4, 1, 1, 2, 1, 2, 2, 5]
def baseStart_3653394 : Nat := 118140960795 + 3653394 * 2 ^ 59
def prefixEnd_3653394 : Nat := 4983230072969 + 3 ^ 40 * 3653394 * 2
def baseEnd_3653394 : Nat := 625315714084061437624451

theorem tailTrace_3653394 : CollatzResearch.WordTrace tailWord_3653394 prefixEnd_3653394 625315714084061437624451 := by
  unfold tailWord_3653394
  simp only [CollatzResearch.WordTrace]
  refine ⟨33312556531596240716277809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88833484084256641910074157 33312556531596240716277809)
  ·
    refine ⟨24984417398697180537208357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33312556531596240716277809 24984417398697180537208357)
    ·
      refine ⟨4684578262255721350726567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24984417398697180537208357 4684578262255721350726567)
      ·
        refine ⟨7026867393383582026089851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4684578262255721350726567 7026867393383582026089851)
        ·
          refine ⟨10540301090075373039134777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7026867393383582026089851 10540301090075373039134777)
          ·
            refine ⟨7905225817556529779351083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10540301090075373039134777 7905225817556529779351083)
            ·
              refine ⟨11857838726334794669026625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7905225817556529779351083 11857838726334794669026625)
              ·
                refine ⟨8893379044751096001769969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11857838726334794669026625 8893379044751096001769969)
                ·
                  refine ⟨6670034283563322001327477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8893379044751096001769969 6670034283563322001327477)
                  ·
                    refine ⟨625315714084061437624451, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6670034283563322001327477 625315714084061437624451)
                    ·
                      rfl

theorem cell23_3653394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 2, 1, 2, 2, 5].length) (baseStart_3653394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3653394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3653394 prefixEnd_3653394 := by exact prefixLift 3653394
  have htrace : WordTrace (prefixWord ++ tailWord_3653394) baseStart_3653394 baseEnd_3653394 := by
    simpa [prefixWord, tailWord_3653394, baseEnd_3653394] using wordTrace_append hprefix tailTrace_3653394
  have hstable : (prefixWord ++ tailWord_3653394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3653394).length < 2 ^ (prefixWord ++ tailWord_3653394).sum := by decide
  have hdescent : baseEnd_3653394 < baseStart_3653394 := by decide
  rcases family_descends (prefixWord ++ tailWord_3653394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3653397 : List Nat := [1, 3, 2, 1, 2, 4, 1, 2, 2, 1, 4]
def baseStart_3653397 : Nat := 118140960795 + 3653397 * 2 ^ 59
def prefixEnd_3653397 : Nat := 4983230072969 + 3 ^ 40 * 3653397 * 2
def baseEnd_3653397 : Nat := 1875948682694147801135839

theorem tailTrace_3653397 : CollatzResearch.WordTrace tailWord_3653397 prefixEnd_3653397 1875948682694147801135839 := by
  unfold tailWord_3653397
  simp only [CollatzResearch.WordTrace]
  refine ⟨133250335545374094377470445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88833557030249396251646963 133250335545374094377470445)
  ·
    refine ⟨49968875829515285391551417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 133250335545374094377470445 49968875829515285391551417)
    ·
      refine ⟨37476656872136464043663563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49968875829515285391551417 37476656872136464043663563)
      ·
        refine ⟨56214985308204696065495345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37476656872136464043663563 56214985308204696065495345)
        ·
          refine ⟨42161238981153522049121509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56214985308204696065495345 42161238981153522049121509)
          ·
            refine ⟨7905232308966285384210283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 42161238981153522049121509 7905232308966285384210283)
            ·
              refine ⟨11857848463449428076315425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7905232308966285384210283 11857848463449428076315425)
              ·
                refine ⟨8893386347587071057236569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11857848463449428076315425 8893386347587071057236569)
                ·
                  refine ⟨6670039760690303292927427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8893386347587071057236569 6670039760690303292927427)
                  ·
                    refine ⟨10005059641035454939391141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6670039760690303292927427 10005059641035454939391141)
                    ·
                      refine ⟨1875948682694147801135839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10005059641035454939391141 1875948682694147801135839)
                      ·
                        rfl

theorem cell23_3653397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 4, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 4, 1, 2, 2, 1, 4].length) (baseStart_3653397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3653397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3653397 prefixEnd_3653397 := by exact prefixLift 3653397
  have htrace : WordTrace (prefixWord ++ tailWord_3653397) baseStart_3653397 baseEnd_3653397 := by
    simpa [prefixWord, tailWord_3653397, baseEnd_3653397] using wordTrace_append hprefix tailTrace_3653397
  have hstable : (prefixWord ++ tailWord_3653397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3653397).length < 2 ^ (prefixWord ++ tailWord_3653397).sum := by decide
  have hdescent : baseEnd_3653397 < baseStart_3653397 := by decide
  rcases family_descends (prefixWord ++ tailWord_3653397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3653434 : List Nat := [3, 1, 1, 1, 5, 2, 2, 1, 2, 2, 3]
def baseStart_3653434 : Nat := 118140960795 + 3653434 * 2 ^ 59
def prefixEnd_3653434 : Nat := 4983230072969 + 3 ^ 40 * 3653434 * 2
def baseEnd_3653434 : Nat := 1875967681478364156373169

theorem tailTrace_3653434 : CollatzResearch.WordTrace tailWord_3653434 prefixEnd_3653434 1875967681478364156373169 := by
  unfold tailWord_3653434
  simp only [CollatzResearch.WordTrace]
  refine ⟨33312921261560012424141839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88834456697493366464378237 33312921261560012424141839)
  ·
    refine ⟨49969381892340018636212759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33312921261560012424141839 49969381892340018636212759)
    ·
      refine ⟨74954072838510027954319139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49969381892340018636212759 74954072838510027954319139)
      ·
        refine ⟨112431109257765041931478709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74954072838510027954319139 112431109257765041931478709)
        ·
          refine ⟨10540416492915472681076129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 112431109257765041931478709 10540416492915472681076129)
          ·
            refine ⟨7905312369686604510807097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10540416492915472681076129 7905312369686604510807097)
            ·
              refine ⟨5928984277264953383105323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7905312369686604510807097 5928984277264953383105323)
              ·
                refine ⟨8893476415897430074657985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5928984277264953383105323 8893476415897430074657985)
                ·
                  refine ⟨6670107311923072555993489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8893476415897430074657985 6670107311923072555993489)
                  ·
                    refine ⟨5002580483942304416995117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6670107311923072555993489 5002580483942304416995117)
                    ·
                      refine ⟨1875967681478364156373169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5002580483942304416995117 1875967681478364156373169)
                      ·
                        rfl

theorem cell23_3653434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 2, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 2, 2, 1, 2, 2, 3].length) (baseStart_3653434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3653434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3653434 prefixEnd_3653434 := by exact prefixLift 3653434
  have htrace : WordTrace (prefixWord ++ tailWord_3653434) baseStart_3653434 baseEnd_3653434 := by
    simpa [prefixWord, tailWord_3653434, baseEnd_3653434] using wordTrace_append hprefix tailTrace_3653434
  have hstable : (prefixWord ++ tailWord_3653434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3653434).length < 2 ^ (prefixWord ++ tailWord_3653434).sum := by decide
  have hdescent : baseEnd_3653434 < baseStart_3653434 := by decide
  rcases family_descends (prefixWord ++ tailWord_3653434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3653458 : List Nat := [3, 2, 2, 1, 1, 5, 2, 2, 1, 4]
def baseStart_3653458 : Nat := 118140960795 + 3653458 * 2 ^ 59
def prefixEnd_3653458 : Nat := 4983230072969 + 3 ^ 40 * 3653458 * 2
def baseEnd_3653458 : Nat := 625326668338024020824353

theorem tailTrace_3653458 : CollatzResearch.WordTrace tailWord_3653458 prefixEnd_3653458 625326668338024020824353 := by
  unfold tailWord_3653458
  simp only [CollatzResearch.WordTrace]
  refine ⟨33313140099538275448860257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88835040265435401196960685 33313140099538275448860257)
  ·
    refine ⟨24984855074653706586645193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33313140099538275448860257 24984855074653706586645193)
    ·
      refine ⟨18738641305990279939983895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24984855074653706586645193 18738641305990279939983895)
      ·
        refine ⟨28107961958985419909975843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18738641305990279939983895 28107961958985419909975843)
        ·
          refine ⟨42161942938478129864963765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28107961958985419909975843 42161942938478129864963765)
          ·
            refine ⟨3952682150482324674840353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 42161942938478129864963765 3952682150482324674840353)
            ·
              refine ⟨2964511612861743506130265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3952682150482324674840353 2964511612861743506130265)
              ·
                refine ⟨2223383709646307629597699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2964511612861743506130265 2223383709646307629597699)
                ·
                  refine ⟨3335075564469461444396549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2223383709646307629597699 3335075564469461444396549)
                  ·
                    refine ⟨625326668338024020824353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3335075564469461444396549 625326668338024020824353)
                    ·
                      rfl

theorem cell23_3653458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 5, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 5, 2, 2, 1, 4].length) (baseStart_3653458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3653458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3653458 prefixEnd_3653458 := by exact prefixLift 3653458
  have htrace : WordTrace (prefixWord ++ tailWord_3653458) baseStart_3653458 baseEnd_3653458 := by
    simpa [prefixWord, tailWord_3653458, baseEnd_3653458] using wordTrace_append hprefix tailTrace_3653458
  have hstable : (prefixWord ++ tailWord_3653458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3653458).length < 2 ^ (prefixWord ++ tailWord_3653458).sum := by decide
  have hdescent : baseEnd_3653458 < baseStart_3653458 := by decide
  rcases family_descends (prefixWord ++ tailWord_3653458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3653497 : List Nat := [1, 2, 1, 3, 2, 2, 2, 2, 4, 4]
def baseStart_3653497 : Nat := 118140960795 + 3653497 * 2 ^ 59
def prefixEnd_3653497 : Nat := 4983230072969 + 3 ^ 40 * 3653497 * 2
def baseEnd_3653497 : Nat := 625333343586532469961793

theorem tailTrace_3653497 : CollatzResearch.WordTrace tailWord_3653497 prefixEnd_3653497 625333343586532469961793 := by
  unfold tailWord_3653497
  simp only [CollatzResearch.WordTrace]
  refine ⟨133253982845011811456110745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88835988563341207637407163 133253982845011811456110745)
  ·
    refine ⟨99940487133758858592083059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133253982845011811456110745 99940487133758858592083059)
    ·
      refine ⟨149910730700638287888124589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99940487133758858592083059 149910730700638287888124589)
      ·
        refine ⟨56216524012739357958046721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 149910730700638287888124589 56216524012739357958046721)
        ·
          refine ⟨42162393009554518468535041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56216524012739357958046721 42162393009554518468535041)
          ·
            refine ⟨31621794757165888851401281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42162393009554518468535041 31621794757165888851401281)
            ·
              refine ⟨23716346067874416638550961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31621794757165888851401281 23716346067874416638550961)
              ·
                refine ⟨17787259550905812478913221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23716346067874416638550961 17787259550905812478913221)
                ·
                  refine ⟨3335111165794839839796229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17787259550905812478913221 3335111165794839839796229)
                  ·
                    refine ⟨625333343586532469961793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3335111165794839839796229 625333343586532469961793)
                    ·
                      rfl

theorem cell23_3653497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 2, 2, 4, 4].length) (baseStart_3653497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3653497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3653497 prefixEnd_3653497 := by exact prefixLift 3653497
  have htrace : WordTrace (prefixWord ++ tailWord_3653497) baseStart_3653497 baseEnd_3653497 := by
    simpa [prefixWord, tailWord_3653497, baseEnd_3653497] using wordTrace_append hprefix tailTrace_3653497
  have hstable : (prefixWord ++ tailWord_3653497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3653497).length < 2 ^ (prefixWord ++ tailWord_3653497).sum := by decide
  have hdescent : baseEnd_3653497 < baseStart_3653497 := by decide
  rcases family_descends (prefixWord ++ tailWord_3653497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3653500 : List Nat := [2, 2, 2, 1, 1, 1, 1, 1, 5, 1, 6]
def baseStart_3653500 : Nat := 118140960795 + 3653500 * 2 ^ 59
def prefixEnd_3653500 : Nat := 4983230072969 + 3 ^ 40 * 3653500 * 2
def baseEnd_3653500 : Nat := 1876001571201560898147865

theorem tailTrace_3653500 : CollatzResearch.WordTrace tailWord_3653500 prefixEnd_3653500 1876001571201560898147865 := by
  unfold tailWord_3653500
  simp only [CollatzResearch.WordTrace]
  refine ⟨66627046132000471484234977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88836061509333961978979969 66627046132000471484234977)
  ·
    refine ⟨49970284599000353613176233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66627046132000471484234977 49970284599000353613176233)
    ·
      refine ⟨37477713449250265209882175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49970284599000353613176233 37477713449250265209882175)
      ·
        refine ⟨56216570173875397814823263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37477713449250265209882175 56216570173875397814823263)
        ·
          refine ⟨84324855260813096722234895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56216570173875397814823263 84324855260813096722234895)
          ·
            refine ⟨126487282891219645083352343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84324855260813096722234895 126487282891219645083352343)
            ·
              refine ⟨189730924336829467625028515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 126487282891219645083352343 189730924336829467625028515)
              ·
                refine ⟨284596386505244201437542773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 189730924336829467625028515 284596386505244201437542773)
                ·
                  refine ⟨26680911234866643884769635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 284596386505244201437542773 26680911234866643884769635)
                  ·
                    refine ⟨40021366852299965827154453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26680911234866643884769635 40021366852299965827154453)
                    ·
                      refine ⟨1876001571201560898147865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 40021366852299965827154453 1876001571201560898147865)
                      ·
                        rfl

theorem cell23_3653500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 1, 5, 1, 6].length) (baseStart_3653500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3653500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3653500 prefixEnd_3653500 := by exact prefixLift 3653500
  have htrace : WordTrace (prefixWord ++ tailWord_3653500) baseStart_3653500 baseEnd_3653500 := by
    simpa [prefixWord, tailWord_3653500, baseEnd_3653500] using wordTrace_append hprefix tailTrace_3653500
  have hstable : (prefixWord ++ tailWord_3653500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3653500).length < 2 ^ (prefixWord ++ tailWord_3653500).sum := by decide
  have hdescent : baseEnd_3653500 < baseStart_3653500 := by decide
  rcases family_descends (prefixWord ++ tailWord_3653500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3653504 : List Nat := [2, 1, 1, 2, 1, 2, 3, 2, 5, 2, 2]
def baseStart_3653504 : Nat := 118140960795 + 3653504 * 2 ^ 59
def prefixEnd_3653504 : Nat := 4983230072969 + 3 ^ 40 * 3653504 * 2
def baseEnd_3653504 : Nat := 1876003625124178882497847

theorem tailTrace_3653504 : CollatzResearch.WordTrace tailWord_3653504 prefixEnd_3653504 1876003625124178882497847 := by
  unfold tailWord_3653504
  simp only [CollatzResearch.WordTrace]
  refine ⟨66627119077993225825807783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88836158770657634434410377 66627119077993225825807783)
  ·
    refine ⟨99940678616989838738711675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66627119077993225825807783 99940678616989838738711675)
    ·
      refine ⟨149911017925484758108067513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99940678616989838738711675 149911017925484758108067513)
      ·
        refine ⟨112433263444113568581050635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 149911017925484758108067513 112433263444113568581050635)
        ·
          refine ⟨168649895166170352871575953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112433263444113568581050635 168649895166170352871575953)
          ·
            refine ⟨126487421374627764653681965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 168649895166170352871575953 126487421374627764653681965)
            ·
              refine ⟨47432783015485411745130737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 126487421374627764653681965 47432783015485411745130737)
              ·
                refine ⟨35574587261614058808848053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47432783015485411745130737 35574587261614058808848053)
                ·
                  refine ⟨3335117555776318013329505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 35574587261614058808848053 3335117555776318013329505)
                  ·
                    refine ⟨2501338166832238509997129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3335117555776318013329505 2501338166832238509997129)
                    ·
                      refine ⟨1876003625124178882497847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2501338166832238509997129 1876003625124178882497847)
                      ·
                        rfl

theorem cell23_3653504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 3, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 3, 2, 5, 2, 2].length) (baseStart_3653504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3653504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3653504 prefixEnd_3653504 := by exact prefixLift 3653504
  have htrace : WordTrace (prefixWord ++ tailWord_3653504) baseStart_3653504 baseEnd_3653504 := by
    simpa [prefixWord, tailWord_3653504, baseEnd_3653504] using wordTrace_append hprefix tailTrace_3653504
  have hstable : (prefixWord ++ tailWord_3653504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3653504).length < 2 ^ (prefixWord ++ tailWord_3653504).sum := by decide
  have hdescent : baseEnd_3653504 < baseStart_3653504 := by decide
  rcases family_descends (prefixWord ++ tailWord_3653504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3653524 : List Nat := [2, 4, 2, 1, 1, 3, 1, 2, 1, 1, 5]
def baseStart_3653524 : Nat := 118140960795 + 3653524 * 2 ^ 59
def prefixEnd_3653524 : Nat := 4983230072969 + 3 ^ 40 * 3653524 * 2
def baseEnd_3653524 : Nat := 1876013894737268804247755

theorem tailTrace_3653524 : CollatzResearch.WordTrace tailWord_3653524 prefixEnd_3653524 1876013894737268804247755 := by
  unfold tailWord_3653524
  simp only [CollatzResearch.WordTrace]
  refine ⟨66627483807956997533671813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88836645077275996711562417 66627483807956997533671813)
  ·
    refine ⟨12492653213991937037563465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 66627483807956997533671813 12492653213991937037563465)
    ·
      refine ⟨9369489910493952778172599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12492653213991937037563465 9369489910493952778172599)
      ·
        refine ⟨14054234865740929167258899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9369489910493952778172599 14054234865740929167258899)
        ·
          refine ⟨21081352298611393750888349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14054234865740929167258899 21081352298611393750888349)
          ·
            refine ⟨7905507111979272656583131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21081352298611393750888349 7905507111979272656583131)
            ·
              refine ⟨11858260667968908984874697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7905507111979272656583131 11858260667968908984874697)
              ·
                refine ⟨8893695500976681738656023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11858260667968908984874697 8893695500976681738656023)
                ·
                  refine ⟨13340543251465022607984035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8893695500976681738656023 13340543251465022607984035)
                  ·
                    refine ⟨20010814877197533911976053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13340543251465022607984035 20010814877197533911976053)
                    ·
                      refine ⟨1876013894737268804247755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20010814877197533911976053 1876013894737268804247755)
                      ·
                        rfl

theorem cell23_3653524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 3, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 3, 1, 2, 1, 1, 5].length) (baseStart_3653524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3653524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3653524 prefixEnd_3653524 := by exact prefixLift 3653524
  have htrace : WordTrace (prefixWord ++ tailWord_3653524) baseStart_3653524 baseEnd_3653524 := by
    simpa [prefixWord, tailWord_3653524, baseEnd_3653524] using wordTrace_append hprefix tailTrace_3653524
  have hstable : (prefixWord ++ tailWord_3653524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3653524).length < 2 ^ (prefixWord ++ tailWord_3653524).sum := by decide
  have hdescent : baseEnd_3653524 < baseStart_3653524 := by decide
  rcases family_descends (prefixWord ++ tailWord_3653524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3653614 : List Nat := [4, 1, 2, 1, 3, 1, 2, 1, 2, 1, 5]
def baseStart_3653614 : Nat := 118140960795 + 3653614 * 2 ^ 59
def prefixEnd_3653614 : Nat := 4983230072969 + 3 ^ 40 * 3653614 * 2
def baseEnd_3653614 : Nat := 1876060107996173452122341

theorem tailTrace_3653614 : CollatzResearch.WordTrace tailWord_3653614 prefixEnd_3653614 1876060107996173452122341 := by
  unfold tailWord_3653614
  simp only [CollatzResearch.WordTrace]
  refine ⟨16657281273198492554764987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 88838833457058626958746597 16657281273198492554764987)
  ·
    refine ⟨24985921909797738832147481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16657281273198492554764987 24985921909797738832147481)
    ·
      refine ⟨18739441432348304124110611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24985921909797738832147481 18739441432348304124110611)
      ·
        refine ⟨28109162148522456186165917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18739441432348304124110611 28109162148522456186165917)
        ·
          refine ⟨10540935805695921069812219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28109162148522456186165917 10540935805695921069812219)
          ·
            refine ⟨15811403708543881604718329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10540935805695921069812219 15811403708543881604718329)
            ·
              refine ⟨11858552781407911203538747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15811403708543881604718329 11858552781407911203538747)
              ·
                refine ⟨17787829172111866805308121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11858552781407911203538747 17787829172111866805308121)
                ·
                  refine ⟨13340871879083900103981091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17787829172111866805308121 13340871879083900103981091)
                  ·
                    refine ⟨20011307818625850155971637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13340871879083900103981091 20011307818625850155971637)
                    ·
                      refine ⟨1876060107996173452122341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20011307818625850155971637 1876060107996173452122341)
                      ·
                        rfl

theorem cell23_3653614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 2, 1, 2, 1, 5].length) (baseStart_3653614 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3653614 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3653614 prefixEnd_3653614 := by exact prefixLift 3653614
  have htrace : WordTrace (prefixWord ++ tailWord_3653614) baseStart_3653614 baseEnd_3653614 := by
    simpa [prefixWord, tailWord_3653614, baseEnd_3653614] using wordTrace_append hprefix tailTrace_3653614
  have hstable : (prefixWord ++ tailWord_3653614).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3653614).length < 2 ^ (prefixWord ++ tailWord_3653614).sum := by decide
  have hdescent : baseEnd_3653614 < baseStart_3653614 := by decide
  rcases family_descends (prefixWord ++ tailWord_3653614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3653628 : List Nat := [2, 2, 2, 1, 2, 2, 4, 2, 2, 2, 2]
def baseStart_3653628 : Nat := 118140960795 + 3653628 * 2 ^ 59
def prefixEnd_3653628 : Nat := 4983230072969 + 3 ^ 40 * 3653628 * 2
def baseEnd_3653628 : Nat := 1876067296725336397347277

theorem tailTrace_3653628 : CollatzResearch.WordTrace tailWord_3653628 prefixEnd_3653628 1876067296725336397347277 := by
  unfold tailWord_3653628
  simp only [CollatzResearch.WordTrace]
  refine ⟨66629380403768610414564769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88839173871691480552753025 66629380403768610414564769)
  ·
    refine ⟨49972035302826457810923577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66629380403768610414564769 49972035302826457810923577)
    ·
      refine ⟨37479026477119843358192683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49972035302826457810923577 37479026477119843358192683)
      ·
        refine ⟨56218539715679765037289025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37479026477119843358192683 56218539715679765037289025)
        ·
          refine ⟨42163904786759823777966769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56218539715679765037289025 42163904786759823777966769)
          ·
            refine ⟨31622928590069867833475077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42163904786759823777966769 31622928590069867833475077)
            ·
              refine ⟨5929299110638100218776577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31622928590069867833475077 5929299110638100218776577)
              ·
                refine ⟨4446974332978575164082433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5929299110638100218776577 4446974332978575164082433)
                ·
                  refine ⟨3335230749733931373061825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4446974332978575164082433 3335230749733931373061825)
                  ·
                    refine ⟨2501423062300448529796369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3335230749733931373061825 2501423062300448529796369)
                    ·
                      refine ⟨1876067296725336397347277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2501423062300448529796369 1876067296725336397347277)
                      ·
                        rfl

theorem cell23_3653628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 4, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 4, 2, 2, 2, 2].length) (baseStart_3653628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3653628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3653628 prefixEnd_3653628 := by exact prefixLift 3653628
  have htrace : WordTrace (prefixWord ++ tailWord_3653628) baseStart_3653628 baseEnd_3653628 := by
    simpa [prefixWord, tailWord_3653628, baseEnd_3653628] using wordTrace_append hprefix tailTrace_3653628
  have hstable : (prefixWord ++ tailWord_3653628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3653628).length < 2 ^ (prefixWord ++ tailWord_3653628).sum := by decide
  have hdescent : baseEnd_3653628 < baseStart_3653628 := by decide
  rcases family_descends (prefixWord ++ tailWord_3653628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3653644 : List Nat := [2, 2, 1, 2, 3, 1, 3, 1, 2, 3, 3]
def baseStart_3653644 : Nat := 118140960795 + 3653644 * 2 ^ 59
def prefixEnd_3653644 : Nat := 4983230072969 + 3 ^ 40 * 3653644 * 2
def baseEnd_3653644 : Nat := 1876075512415808334747203

theorem tailTrace_3653644 : CollatzResearch.WordTrace tailWord_3653644 prefixEnd_3653644 1876075512415808334747203 := by
  unfold tailWord_3653644
  simp only [CollatzResearch.WordTrace]
  refine ⟨66629672187739627780855993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88839562916986170374474657 66629672187739627780855993)
  ·
    refine ⟨49972254140804720835641995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66629672187739627780855993 49972254140804720835641995)
    ·
      refine ⟨74958381211207081253462993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49972254140804720835641995 74958381211207081253462993)
      ·
        refine ⟨56218785908405310940097245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74958381211207081253462993 56218785908405310940097245)
        ·
          refine ⟨21082044715651991602536467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56218785908405310940097245 21082044715651991602536467)
          ·
            refine ⟨31623067073477987403804701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21082044715651991602536467 31623067073477987403804701)
            ·
              refine ⟨11858650152554245276426763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31623067073477987403804701 11858650152554245276426763)
              ·
                refine ⟨17787975228831367914640145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11858650152554245276426763 17787975228831367914640145)
                ·
                  refine ⟨13340981421623525935980109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17787975228831367914640145 13340981421623525935980109)
                  ·
                    refine ⟨5002868033108822225992541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13340981421623525935980109 5002868033108822225992541)
                    ·
                      refine ⟨1876075512415808334747203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5002868033108822225992541 1876075512415808334747203)
                      ·
                        rfl

theorem cell23_3653644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 3, 1, 2, 3, 3].length) (baseStart_3653644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3653644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3653644 prefixEnd_3653644 := by exact prefixLift 3653644
  have htrace : WordTrace (prefixWord ++ tailWord_3653644) baseStart_3653644 baseEnd_3653644 := by
    simpa [prefixWord, tailWord_3653644, baseEnd_3653644] using wordTrace_append hprefix tailTrace_3653644
  have hstable : (prefixWord ++ tailWord_3653644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3653644).length < 2 ^ (prefixWord ++ tailWord_3653644).sum := by decide
  have hdescent : baseEnd_3653644 < baseStart_3653644 := by decide
  rcases family_descends (prefixWord ++ tailWord_3653644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3653668 : List Nat := [2, 3, 1, 4, 2, 1, 2, 3, 5]
def baseStart_3653668 : Nat := 118140960795 + 3653668 * 2 ^ 59
def prefixEnd_3653668 : Nat := 4983230072969 + 3 ^ 40 * 3653668 * 2
def baseEnd_3653668 : Nat := 208454203994612915649677

theorem tailTrace_3653668 : CollatzResearch.WordTrace tailWord_3653668 prefixEnd_3653668 208454203994612915649677 := by
  unfold tailWord_3653668
  simp only [CollatzResearch.WordTrace]
  refine ⟨66630109863696153830292829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88840146484928205107057105 66630109863696153830292829)
  ·
    refine ⟨24986291198886057686359811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66630109863696153830292829 24986291198886057686359811)
    ·
      refine ⟨37479436798329086529539717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24986291198886057686359811 37479436798329086529539717)
      ·
        refine ⟨7027394399686703724288697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 37479436798329086529539717 7027394399686703724288697)
        ·
          refine ⟨5270545799765027793216523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7027394399686703724288697 5270545799765027793216523)
          ·
            refine ⟨7905818699647541689824785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5270545799765027793216523 7905818699647541689824785)
            ·
              refine ⟨5929364024735656267368589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7905818699647541689824785 5929364024735656267368589)
              ·
                refine ⟨2223511509275871100263221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5929364024735656267368589 2223511509275871100263221)
                ·
                  refine ⟨208454203994612915649677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2223511509275871100263221 208454203994612915649677)
                  ·
                    rfl

theorem cell23_3653668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 1, 2, 3, 5].length) (baseStart_3653668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3653668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3653668 prefixEnd_3653668 := by exact prefixLift 3653668
  have htrace : WordTrace (prefixWord ++ tailWord_3653668) baseStart_3653668 baseEnd_3653668 := by
    simpa [prefixWord, tailWord_3653668, baseEnd_3653668] using wordTrace_append hprefix tailTrace_3653668
  have hstable : (prefixWord ++ tailWord_3653668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3653668).length < 2 ^ (prefixWord ++ tailWord_3653668).sum := by decide
  have hdescent : baseEnd_3653668 < baseStart_3653668 := by decide
  rcases family_descends (prefixWord ++ tailWord_3653668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3653687 : List Nat := [1, 1, 3, 1, 2, 2, 2, 1, 2, 3, 5]
def baseStart_3653687 : Nat := 118140960795 + 3653687 * 2 ^ 59
def prefixEnd_3653687 : Nat := 4983230072969 + 3 ^ 40 * 3653687 * 2
def baseEnd_3653687 : Nat := 1876097592083951666509505

theorem tailTrace_3653687 : CollatzResearch.WordTrace tailWord_3653687 prefixEnd_3653687 1876097592083951666509505 := by
  unfold tailWord_3653687
  simp only [CollatzResearch.WordTrace]
  refine ⟨133260912714323473905527315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88840608476215649270351543 133260912714323473905527315)
  ·
    refine ⟨199891369071485210858290973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133260912714323473905527315 199891369071485210858290973)
    ·
      refine ⟨74959263401806954071859115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 199891369071485210858290973 74959263401806954071859115)
      ·
        refine ⟨112438895102710431107788673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74959263401806954071859115 112438895102710431107788673)
        ·
          refine ⟨84329171327032823330841505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 112438895102710431107788673 84329171327032823330841505)
          ·
            refine ⟨63246878495274617498131129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84329171327032823330841505 63246878495274617498131129)
            ·
              refine ⟨47435158871455963123598347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63246878495274617498131129 47435158871455963123598347)
              ·
                refine ⟨71152738307183944685397521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47435158871455963123598347 71152738307183944685397521)
                ·
                  refine ⟨53364553730387958514048141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 71152738307183944685397521 53364553730387958514048141)
                  ·
                    refine ⟨20011707648895484442768053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 53364553730387958514048141 20011707648895484442768053)
                    ·
                      refine ⟨1876097592083951666509505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20011707648895484442768053 1876097592083951666509505)
                      ·
                        rfl

theorem cell23_3653687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 2, 1, 2, 3, 5].length) (baseStart_3653687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3653687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3653687 prefixEnd_3653687 := by exact prefixLift 3653687
  have htrace : WordTrace (prefixWord ++ tailWord_3653687) baseStart_3653687 baseEnd_3653687 := by
    simpa [prefixWord, tailWord_3653687, baseEnd_3653687] using wordTrace_append hprefix tailTrace_3653687
  have hstable : (prefixWord ++ tailWord_3653687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3653687).length < 2 ^ (prefixWord ++ tailWord_3653687).sum := by decide
  have hdescent : baseEnd_3653687 < baseStart_3653687 := by decide
  rcases family_descends (prefixWord ++ tailWord_3653687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3653704 : List Nat := [2, 1, 3, 1, 1, 1, 2, 1, 6, 2, 3]
def baseStart_3653704 : Nat := 118140960795 + 3653704 * 2 ^ 59
def prefixEnd_3653704 : Nat := 4983230072969 + 3 ^ 40 * 3653704 * 2
def baseEnd_3653704 : Nat := 1876106321255078099996927

theorem tailTrace_3653704 : CollatzResearch.WordTrace tailWord_3653704 prefixEnd_3653704 1876106321255078099996927 := by
  unfold tailWord_3653704
  simp only [CollatzResearch.WordTrace]
  refine ⟨66630766377630942904448083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88841021836841257205930777 66630766377630942904448083)
  ·
    refine ⟨99946149566446414356672125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66630766377630942904448083 99946149566446414356672125)
    ·
      refine ⟨37479806087417405383752047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 99946149566446414356672125 37479806087417405383752047)
      ·
        refine ⟨56219709131126108075628071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37479806087417405383752047 56219709131126108075628071)
        ·
          refine ⟨84329563696689162113442107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56219709131126108075628071 84329563696689162113442107)
          ·
            refine ⟨126494345545033743170163161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84329563696689162113442107 126494345545033743170163161)
            ·
              refine ⟨94870759158775307377622371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 126494345545033743170163161 94870759158775307377622371)
              ·
                refine ⟨142306138738162961066433557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 94870759158775307377622371 142306138738162961066433557)
                ·
                  refine ⟨6670600253351388799989073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 142306138738162961066433557 6670600253351388799989073)
                  ·
                    refine ⟨5002950190013541599991805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6670600253351388799989073 5002950190013541599991805)
                    ·
                      refine ⟨1876106321255078099996927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5002950190013541599991805 1876106321255078099996927)
                      ·
                        rfl

theorem cell23_3653704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 1, 6, 2, 3].length) (baseStart_3653704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3653704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3653704 prefixEnd_3653704 := by exact prefixLift 3653704
  have htrace : WordTrace (prefixWord ++ tailWord_3653704) baseStart_3653704 baseEnd_3653704 := by
    simpa [prefixWord, tailWord_3653704, baseEnd_3653704] using wordTrace_append hprefix tailTrace_3653704
  have hstable : (prefixWord ++ tailWord_3653704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3653704).length < 2 ^ (prefixWord ++ tailWord_3653704).sum := by decide
  have hdescent : baseEnd_3653704 < baseStart_3653704 := by decide
  rcases family_descends (prefixWord ++ tailWord_3653704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3653718 : List Nat := [5, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4]
def baseStart_3653718 : Nat := 118140960795 + 3653718 * 2 ^ 59
def prefixEnd_3653718 : Nat := 4983230072969 + 3 ^ 40 * 3653718 * 2
def baseEnd_3653718 : Nat := 1876113509984241045221863

theorem tailTrace_3653718 : CollatzResearch.WordTrace tailWord_3653718 prefixEnd_3653718 1876113509984241045221863 := by
  unfold tailWord_3653718
  simp only [CollatzResearch.WordTrace]
  refine ⟨8328877711075697887494113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 88841362251474110799937205 8328877711075697887494113)
  ·
    refine ⟨6246658283306773415620585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8328877711075697887494113 6246658283306773415620585)
    ·
      refine ⟨4684993712480080061715439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6246658283306773415620585 4684993712480080061715439)
      ·
        refine ⟨7027490568720120092573159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4684993712480080061715439 7027490568720120092573159)
        ·
          refine ⟨10541235853080180138859739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7027490568720120092573159 10541235853080180138859739)
          ·
            refine ⟨15811853779620270208289609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10541235853080180138859739 15811853779620270208289609)
            ·
              refine ⟨11858890334715202656217207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15811853779620270208289609 11858890334715202656217207)
              ·
                refine ⟨17788335502072803984325811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11858890334715202656217207 17788335502072803984325811)
                ·
                  refine ⟨26682503253109205976488717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17788335502072803984325811 26682503253109205976488717)
                  ·
                    refine ⟨10005938719915952241183269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26682503253109205976488717 10005938719915952241183269)
                    ·
                      refine ⟨1876113509984241045221863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10005938719915952241183269 1876113509984241045221863)
                      ·
                        rfl

theorem cell23_3653718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4].length) (baseStart_3653718 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3653718 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3653718 prefixEnd_3653718 := by exact prefixLift 3653718
  have htrace : WordTrace (prefixWord ++ tailWord_3653718) baseStart_3653718 baseEnd_3653718 := by
    simpa [prefixWord, tailWord_3653718, baseEnd_3653718] using wordTrace_append hprefix tailTrace_3653718
  have hstable : (prefixWord ++ tailWord_3653718).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3653718).length < 2 ^ (prefixWord ++ tailWord_3653718).sum := by decide
  have hdescent : baseEnd_3653718 < baseStart_3653718 := by decide
  rcases family_descends (prefixWord ++ tailWord_3653718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3653724 : List Nat := [2, 2, 4, 1, 1, 2, 1, 2, 8]
def baseStart_3653724 : Nat := 118140960795 + 3653724 * 2 ^ 59
def prefixEnd_3653724 : Nat := 4983230072969 + 3 ^ 40 * 3653724 * 2
def baseEnd_3653724 : Nat := 208457398985352002416315

theorem tailTrace_3653724 : CollatzResearch.WordTrace tailWord_3653724 prefixEnd_3653724 208457398985352002416315 := by
  unfold tailWord_3653724
  simp only [CollatzResearch.WordTrace]
  refine ⟨66631131107594714612312113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88841508143459619483082817 66631131107594714612312113)
  ·
    refine ⟨49973348330696035959234085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66631131107594714612312113 49973348330696035959234085)
    ·
      refine ⟨9370002812005506742356391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 49973348330696035959234085 9370002812005506742356391)
      ·
        refine ⟨14055004218008260113534587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9370002812005506742356391 14055004218008260113534587)
        ·
          refine ⟨21082506327012390170301881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14055004218008260113534587 21082506327012390170301881)
          ·
            refine ⟨15811879745259292627726411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21082506327012390170301881 15811879745259292627726411)
            ·
              refine ⟨23717819617888938941589617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15811879745259292627726411 23717819617888938941589617)
              ·
                refine ⟨17788364713416704206192213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23717819617888938941589617 17788364713416704206192213)
                ·
                  refine ⟨208457398985352002416315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 17788364713416704206192213 208457398985352002416315)
                  ·
                    rfl

theorem cell23_3653724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 1, 2, 8].length) (baseStart_3653724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3653724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3653724 prefixEnd_3653724 := by exact prefixLift 3653724
  have htrace : WordTrace (prefixWord ++ tailWord_3653724) baseStart_3653724 baseEnd_3653724 := by
    simpa [prefixWord, tailWord_3653724, baseEnd_3653724] using wordTrace_append hprefix tailTrace_3653724
  have hstable : (prefixWord ++ tailWord_3653724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3653724).length < 2 ^ (prefixWord ++ tailWord_3653724).sum := by decide
  have hdescent : baseEnd_3653724 < baseStart_3653724 := by decide
  rcases family_descends (prefixWord ++ tailWord_3653724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3653727 : List Nat := [1, 1, 2, 3, 1, 1, 2, 2, 1, 1, 8]
def baseStart_3653727 : Nat := 118140960795 + 3653727 * 2 ^ 59
def prefixEnd_3653727 : Nat := 4983230072969 + 3 ^ 40 * 3653727 * 2
def baseEnd_3653727 : Nat := 1876118131310131510009321

theorem tailTrace_3653727 : CollatzResearch.WordTrace tailWord_3653727 prefixEnd_3653727 1876118131310131510009321 := by
  unfold tailWord_3653727
  simp only [CollatzResearch.WordTrace]
  refine ⟨133262371634178560736983435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88841581089452373824655623 133262371634178560736983435)
  ·
    refine ⟨199893557451267841105475153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133262371634178560736983435 199893557451267841105475153)
    ·
      refine ⟨149920168088450880829106365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 199893557451267841105475153 149920168088450880829106365)
      ·
        refine ⟨56220063033169080310914887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 149920168088450880829106365 56220063033169080310914887)
        ·
          refine ⟨84330094549753620466372331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56220063033169080310914887 84330094549753620466372331)
          ·
            refine ⟨126495141824630430699558497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84330094549753620466372331 126495141824630430699558497)
            ·
              refine ⟨94871356368472823024668873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 126495141824630430699558497 94871356368472823024668873)
              ·
                refine ⟨71153517276354617268501655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 94871356368472823024668873 71153517276354617268501655)
                ·
                  refine ⟨106730275914531925902752483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 71153517276354617268501655 106730275914531925902752483)
                  ·
                    refine ⟨160095413871797888854128725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 106730275914531925902752483 160095413871797888854128725)
                    ·
                      refine ⟨1876118131310131510009321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 160095413871797888854128725 1876118131310131510009321)
                      ·
                        rfl

theorem cell23_3653727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 2, 1, 1, 8].length) (baseStart_3653727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3653727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3653727 prefixEnd_3653727 := by exact prefixLift 3653727
  have htrace : WordTrace (prefixWord ++ tailWord_3653727) baseStart_3653727 baseEnd_3653727 := by
    simpa [prefixWord, tailWord_3653727, baseEnd_3653727] using wordTrace_append hprefix tailTrace_3653727
  have hstable : (prefixWord ++ tailWord_3653727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3653727).length < 2 ^ (prefixWord ++ tailWord_3653727).sum := by decide
  have hdescent : baseEnd_3653727 < baseStart_3653727 := by decide
  rcases family_descends (prefixWord ++ tailWord_3653727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3653728 : List Nat := [2, 1, 1, 3, 2, 3, 3, 3, 1, 4]
def baseStart_3653728 : Nat := 118140960795 + 3653728 * 2 ^ 59
def prefixEnd_3653728 : Nat := 4983230072969 + 3 ^ 40 * 3653728 * 2
def baseEnd_3653728 : Nat := 625372881596928668698939

theorem tailTrace_3653728 : CollatzResearch.WordTrace tailWord_3653728 prefixEnd_3653728 625372881596928668698939 := by
  unfold tailWord_3653728
  simp only [CollatzResearch.WordTrace]
  refine ⟨66631204053587468953884919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88841605404783291938513225 66631204053587468953884919)
  ·
    refine ⟨99946806080381203430827379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66631204053587468953884919 99946806080381203430827379)
    ·
      refine ⟨149920209120571805146241069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99946806080381203430827379 149920209120571805146241069)
      ·
        refine ⟨56220078420214426929840401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 149920209120571805146241069 56220078420214426929840401)
        ·
          refine ⟨42165058815160820197380301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56220078420214426929840401 42165058815160820197380301)
          ·
            refine ⟨15811897055685307574017613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42165058815160820197380301 15811897055685307574017613)
            ·
              refine ⟨5929461395881990340256605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15811897055685307574017613 5929461395881990340256605)
              ·
                refine ⟨2223548023455746377596227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5929461395881990340256605 2223548023455746377596227)
                ·
                  refine ⟨3335322035183619566394341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2223548023455746377596227 3335322035183619566394341)
                  ·
                    refine ⟨625372881596928668698939, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3335322035183619566394341 625372881596928668698939)
                    ·
                      rfl

theorem cell23_3653728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 3, 3, 1, 4].length) (baseStart_3653728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3653728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3653728 prefixEnd_3653728 := by exact prefixLift 3653728
  have htrace : WordTrace (prefixWord ++ tailWord_3653728) baseStart_3653728 baseEnd_3653728 := by
    simpa [prefixWord, tailWord_3653728, baseEnd_3653728] using wordTrace_append hprefix tailTrace_3653728
  have hstable : (prefixWord ++ tailWord_3653728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3653728).length < 2 ^ (prefixWord ++ tailWord_3653728).sum := by decide
  have hdescent : baseEnd_3653728 < baseStart_3653728 := by decide
  rcases family_descends (prefixWord ++ tailWord_3653728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3653738 : List Nat := [3, 1, 3, 2, 3, 1, 1, 2, 2, 2, 3]
def baseStart_3653738 : Nat := 118140960795 + 3653738 * 2 ^ 59
def prefixEnd_3653738 : Nat := 4983230072969 + 3 ^ 40 * 3653738 * 2
def baseEnd_3653738 : Nat := 1876123779597330966971771

theorem tailTrace_3653738 : CollatzResearch.WordTrace tailWord_3653738 prefixEnd_3653738 1876123779597330966971771 := by
  unfold tailWord_3653738
  simp only [CollatzResearch.WordTrace]
  refine ⟨33315693209284677403908467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88841848558092473077089245 33315693209284677403908467)
  ·
    refine ⟨49973539813927016105862701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33315693209284677403908467 49973539813927016105862701)
    ·
      refine ⟨18740077430222631039698513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49973539813927016105862701 18740077430222631039698513)
      ·
        refine ⟨14055058072666973279773885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18740077430222631039698513 14055058072666973279773885)
        ·
          refine ⟨5270646777250114979915207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14055058072666973279773885 5270646777250114979915207)
          ·
            refine ⟨7905970165875172469872811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5270646777250114979915207 7905970165875172469872811)
            ·
              refine ⟨11858955248812758704809217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7905970165875172469872811 11858955248812758704809217)
              ·
                refine ⟨8894216436609569028606913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11858955248812758704809217 8894216436609569028606913)
                ·
                  refine ⟨6670662327457176771455185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8894216436609569028606913 6670662327457176771455185)
                  ·
                    refine ⟨5002996745592882578591389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6670662327457176771455185 5002996745592882578591389)
                    ·
                      refine ⟨1876123779597330966971771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5002996745592882578591389 1876123779597330966971771)
                      ·
                        rfl

theorem cell23_3653738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 1, 1, 2, 2, 2, 3].length) (baseStart_3653738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3653738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3653738 prefixEnd_3653738 := by exact prefixLift 3653738
  have htrace : WordTrace (prefixWord ++ tailWord_3653738) baseStart_3653738 baseEnd_3653738 := by
    simpa [prefixWord, tailWord_3653738, baseEnd_3653738] using wordTrace_append hprefix tailTrace_3653738
  have hstable : (prefixWord ++ tailWord_3653738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3653738).length < 2 ^ (prefixWord ++ tailWord_3653738).sum := by decide
  have hdescent : baseEnd_3653738 < baseStart_3653738 := by decide
  rcases family_descends (prefixWord ++ tailWord_3653738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3653788 : List Nat := [2, 2, 3, 2, 1, 1, 5, 1, 1, 5]
def baseStart_3653788 : Nat := 118140960795 + 3653788 * 2 ^ 59
def prefixEnd_3653788 : Nat := 4983230072969 + 3 ^ 40 * 3653788 * 2
def baseEnd_3653788 : Nat := 625383151210018590448847

theorem tailTrace_3653788 : CollatzResearch.WordTrace tailWord_3653788 prefixEnd_3653788 625383151210018590448847 := by
  unfold tailWord_3653788
  simp only [CollatzResearch.WordTrace]
  refine ⟨66632298243478784077477009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88843064324638378769969345 66632298243478784077477009)
  ·
    refine ⟨49974223682609088058107757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66632298243478784077477009 49974223682609088058107757)
    ·
      refine ⟨18740333880978408021790409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49974223682609088058107757 18740333880978408021790409)
      ·
        refine ⟨14055250410733806016342807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18740333880978408021790409 14055250410733806016342807)
        ·
          refine ⟨21082875616100709024514211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14055250410733806016342807 21082875616100709024514211)
          ·
            refine ⟨31624313424151063536771317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21082875616100709024514211 31624313424151063536771317)
            ·
              refine ⟨2964779383514162206572311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 31624313424151063536771317 2964779383514162206572311)
              ·
                refine ⟨4447169075271243309858467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2964779383514162206572311 4447169075271243309858467)
                ·
                  refine ⟨6670753612906864964787701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4447169075271243309858467 6670753612906864964787701)
                  ·
                    refine ⟨625383151210018590448847, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6670753612906864964787701 625383151210018590448847)
                    ·
                      rfl

theorem cell23_3653788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 5, 1, 1, 5].length) (baseStart_3653788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3653788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3653788 prefixEnd_3653788 := by exact prefixLift 3653788
  have htrace : WordTrace (prefixWord ++ tailWord_3653788) baseStart_3653788 baseEnd_3653788 := by
    simpa [prefixWord, tailWord_3653788, baseEnd_3653788] using wordTrace_append hprefix tailTrace_3653788
  have hstable : (prefixWord ++ tailWord_3653788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3653788).length < 2 ^ (prefixWord ++ tailWord_3653788).sum := by decide
  have hdescent : baseEnd_3653788 < baseStart_3653788 := by decide
  rcases family_descends (prefixWord ++ tailWord_3653788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3653828 : List Nat := [2, 3, 3, 1, 2, 1, 2, 1, 3, 2, 3]
def baseStart_3653828 : Nat := 118140960795 + 3653828 * 2 ^ 59
def prefixEnd_3653828 : Nat := 4983230072969 + 3 ^ 40 * 3653828 * 2
def baseEnd_3653828 : Nat := 1876169992856235614846357

theorem tailTrace_3653828 : CollatzResearch.WordTrace tailWord_3653828 prefixEnd_3653828 1876169992856235614846357 := by
  unfold tailWord_3653828
  simp only [CollatzResearch.WordTrace]
  refine ⟨66633027703406327493205069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88844036937875103324273425 66633027703406327493205069)
  ·
    refine ⟨24987385388777372809951901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66633027703406327493205069 24987385388777372809951901)
    ·
      refine ⟨9370269520791514803731963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24987385388777372809951901 9370269520791514803731963)
      ·
        refine ⟨14055404281187272205597945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9370269520791514803731963 14055404281187272205597945)
        ·
          refine ⟨10541553210890454154198459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14055404281187272205597945 10541553210890454154198459)
          ·
            refine ⟨15812329816335681231297689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10541553210890454154198459 15812329816335681231297689)
            ·
              refine ⟨11859247362251760923473267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15812329816335681231297689 11859247362251760923473267)
              ·
                refine ⟨17788871043377641385209901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11859247362251760923473267 17788871043377641385209901)
                ·
                  refine ⟨6670826641266615519453713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17788871043377641385209901 6670826641266615519453713)
                  ·
                    refine ⟨5003119980949961639590285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6670826641266615519453713 5003119980949961639590285)
                    ·
                      refine ⟨1876169992856235614846357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5003119980949961639590285 1876169992856235614846357)
                      ·
                        rfl

theorem cell23_3653828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 2, 1, 3, 2, 3].length) (baseStart_3653828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3653828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3653828 prefixEnd_3653828 := by exact prefixLift 3653828
  have htrace : WordTrace (prefixWord ++ tailWord_3653828) baseStart_3653828 baseEnd_3653828 := by
    simpa [prefixWord, tailWord_3653828, baseEnd_3653828] using wordTrace_append hprefix tailTrace_3653828
  have hstable : (prefixWord ++ tailWord_3653828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3653828).length < 2 ^ (prefixWord ++ tailWord_3653828).sum := by decide
  have hdescent : baseEnd_3653828 < baseStart_3653828 := by decide
  rcases family_descends (prefixWord ++ tailWord_3653828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3653841 : List Nat := [1, 2, 2, 1, 2, 2, 4, 2, 1, 3, 3]
def baseStart_3653841 : Nat := 118140960795 + 3653841 * 2 ^ 59
def prefixEnd_3653841 : Nat := 4983230072969 + 3 ^ 40 * 3653841 * 2
def baseEnd_3653841 : Nat := 1876176668104744063983797

theorem tailTrace_3653841 : CollatzResearch.WordTrace tailWord_3653841 prefixEnd_3653841 1876176668104744063983797 := by
  unfold tailWord_3653841
  simp only [CollatzResearch.WordTrace]
  refine ⟨133266529555765558206633377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88844353037177038804422251 133266529555765558206633377)
  ·
    refine ⟨99949897166824168654975033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133266529555765558206633377 99949897166824168654975033)
    ·
      refine ⟨74962422875118126491231275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99949897166824168654975033 74962422875118126491231275)
      ·
        refine ⟨112443634312677189736846913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74962422875118126491231275 112443634312677189736846913)
        ·
          refine ⟨84332725734507892302635185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 112443634312677189736846913 84332725734507892302635185)
          ·
            refine ⟨63249544300880919226976389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84332725734507892302635185 63249544300880919226976389)
            ·
              refine ⟨11859289556415172355058073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 63249544300880919226976389 11859289556415172355058073)
              ·
                refine ⟨8894467167311379266293555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11859289556415172355058073 8894467167311379266293555)
                ·
                  refine ⟨13341700750967068899440333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8894467167311379266293555 13341700750967068899440333)
                  ·
                    refine ⟨5003137781612650837290125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13341700750967068899440333 5003137781612650837290125)
                    ·
                      refine ⟨1876176668104744063983797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5003137781612650837290125 1876176668104744063983797)
                      ·
                        rfl

theorem cell23_3653841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 4, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 4, 2, 1, 3, 3].length) (baseStart_3653841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3653841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3653841 prefixEnd_3653841 := by exact prefixLift 3653841
  have htrace : WordTrace (prefixWord ++ tailWord_3653841) baseStart_3653841 baseEnd_3653841 := by
    simpa [prefixWord, tailWord_3653841, baseEnd_3653841] using wordTrace_append hprefix tailTrace_3653841
  have hstable : (prefixWord ++ tailWord_3653841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3653841).length < 2 ^ (prefixWord ++ tailWord_3653841).sum := by decide
  have hdescent : baseEnd_3653841 < baseStart_3653841 := by decide
  rcases family_descends (prefixWord ++ tailWord_3653841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3653842 : List Nat := [3, 2, 2, 2, 1, 2, 1, 5, 1, 2, 2]
def baseStart_3653842 : Nat := 118140960795 + 3653842 * 2 ^ 59
def prefixEnd_3653842 : Nat := 4983230072969 + 3 ^ 40 * 3653842 * 2
def baseEnd_3653842 : Nat := 1876177181585398560071293

theorem tailTrace_3653842 : CollatzResearch.WordTrace tailWord_3653842 prefixEnd_3653842 1876177181585398560071293 := by
  unfold tailWord_3653842
  simp only [CollatzResearch.WordTrace]
  refine ⟨33316641507190483844354945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88844377352507956918279853 33316641507190483844354945)
  ·
    refine ⟨24987481130392862883266209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33316641507190483844354945 24987481130392862883266209)
    ·
      refine ⟨18740610847794647162449657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24987481130392862883266209 18740610847794647162449657)
      ·
        refine ⟨14055458135845985371837243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18740610847794647162449657 14055458135845985371837243)
        ·
          refine ⟨21083187203768978057755865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14055458135845985371837243 21083187203768978057755865)
          ·
            refine ⟨15812390402826733543316899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21083187203768978057755865 15812390402826733543316899)
            ·
              refine ⟨23718585604240100314975349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15812390402826733543316899 23718585604240100314975349)
              ·
                refine ⟨2223617400397509404528939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 23718585604240100314975349 2223617400397509404528939)
                ·
                  refine ⟨3335426100596264106793409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2223617400397509404528939 3335426100596264106793409)
                  ·
                    refine ⟨2501569575447198080095057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3335426100596264106793409 2501569575447198080095057)
                    ·
                      refine ⟨1876177181585398560071293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2501569575447198080095057 1876177181585398560071293)
                      ·
                        rfl

theorem cell23_3653842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 1, 5, 1, 2, 2].length) (baseStart_3653842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3653842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3653842 prefixEnd_3653842 := by exact prefixLift 3653842
  have htrace : WordTrace (prefixWord ++ tailWord_3653842) baseStart_3653842 baseEnd_3653842 := by
    simpa [prefixWord, tailWord_3653842, baseEnd_3653842] using wordTrace_append hprefix tailTrace_3653842
  have hstable : (prefixWord ++ tailWord_3653842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3653842).length < 2 ^ (prefixWord ++ tailWord_3653842).sum := by decide
  have hdescent : baseEnd_3653842 < baseStart_3653842 := by decide
  rcases family_descends (prefixWord ++ tailWord_3653842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3653845 : List Nat := [1, 3, 2, 4, 2, 1, 1, 3, 1, 2, 3]
def baseStart_3653845 : Nat := 118140960795 + 3653845 * 2 ^ 59
def prefixEnd_3653845 : Nat := 4983230072969 + 3 ^ 40 * 3653845 * 2
def baseEnd_3653845 : Nat := 1876178722027362048333779

theorem tailTrace_3653845 : CollatzResearch.WordTrace tailWord_3653845 prefixEnd_3653845 1876178722027362048333779 := by
  unfold tailWord_3653845
  simp only [CollatzResearch.WordTrace]
  refine ⟨133266675447751066889778989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88844450298500711259852659 133266675447751066889778989)
  ·
    refine ⟨49975003292906650083667121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 133266675447751066889778989 49975003292906650083667121)
    ·
      refine ⟨37481252469679987562750341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49975003292906650083667121 37481252469679987562750341)
      ·
        refine ⟨7027734838064997668015689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 37481252469679987562750341 7027734838064997668015689)
        ·
          refine ⟨5270801128548748251011767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7027734838064997668015689 5270801128548748251011767)
          ·
            refine ⟨7906201692823122376517651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5270801128548748251011767 7906201692823122376517651)
            ·
              refine ⟨11859302539234683564776477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7906201692823122376517651 11859302539234683564776477)
              ·
                refine ⟨4447238452213006336791179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11859302539234683564776477 4447238452213006336791179)
                ·
                  refine ⟨6670857678319509505186769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4447238452213006336791179 6670857678319509505186769)
                  ·
                    refine ⟨5003143258739632128890077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6670857678319509505186769 5003143258739632128890077)
                    ·
                      refine ⟨1876178722027362048333779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5003143258739632128890077 1876178722027362048333779)
                      ·
                        rfl

theorem cell23_3653845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 1, 1, 3, 1, 2, 3].length) (baseStart_3653845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3653845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3653845 prefixEnd_3653845 := by exact prefixLift 3653845
  have htrace : WordTrace (prefixWord ++ tailWord_3653845) baseStart_3653845 baseEnd_3653845 := by
    simpa [prefixWord, tailWord_3653845, baseEnd_3653845] using wordTrace_append hprefix tailTrace_3653845
  have hstable : (prefixWord ++ tailWord_3653845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3653845).length < 2 ^ (prefixWord ++ tailWord_3653845).sum := by decide
  have hdescent : baseEnd_3653845 < baseStart_3653845 := by decide
  rcases family_descends (prefixWord ++ tailWord_3653845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3653875 : List Nat := [1, 1, 1, 2, 2, 4, 5, 1, 2, 1, 3]
def baseStart_3653875 : Nat := 118140960795 + 3653875 * 2 ^ 59
def prefixEnd_3653875 : Nat := 4983230072969 + 3 ^ 40 * 3653875 * 2
def baseEnd_3653875 : Nat := 1876194126446996930958641

theorem tailTrace_3653875 : CollatzResearch.WordTrace tailWord_3653875 prefixEnd_3653875 1876194126446996930958641 := by
  unfold tailWord_3653875
  simp only [CollatzResearch.WordTrace]
  refine ⟨133267769637642382013371079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88845179758428254675580719 133267769637642382013371079)
  ·
    refine ⟨199901654456463573020056619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133267769637642382013371079 199901654456463573020056619)
    ·
      refine ⟨299852481684695359530084929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 199901654456463573020056619 299852481684695359530084929)
      ·
        refine ⟨224889361263521519647563697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 299852481684695359530084929 224889361263521519647563697)
        ·
          refine ⟨168667020947641139735672773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 224889361263521519647563697 168667020947641139735672773)
          ·
            refine ⟨31625066427682713700438645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 168667020947641139735672773 31625066427682713700438645)
            ·
              refine ⟨2964849977595254409416123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 31625066427682713700438645 2964849977595254409416123)
              ·
                refine ⟨4447274966392881614124185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2964849977595254409416123 4447274966392881614124185)
                ·
                  refine ⟨3335456224794661210593139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4447274966392881614124185 3335456224794661210593139)
                  ·
                    refine ⟨5003184337191991815889709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3335456224794661210593139 5003184337191991815889709)
                    ·
                      refine ⟨1876194126446996930958641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5003184337191991815889709 1876194126446996930958641)
                      ·
                        rfl

theorem cell23_3653875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 5, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 5, 1, 2, 1, 3].length) (baseStart_3653875 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3653875 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3653875 prefixEnd_3653875 := by exact prefixLift 3653875
  have htrace : WordTrace (prefixWord ++ tailWord_3653875) baseStart_3653875 baseEnd_3653875 := by
    simpa [prefixWord, tailWord_3653875, baseEnd_3653875] using wordTrace_append hprefix tailTrace_3653875
  have hstable : (prefixWord ++ tailWord_3653875).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3653875).length < 2 ^ (prefixWord ++ tailWord_3653875).sum := by decide
  have hdescent : baseEnd_3653875 < baseStart_3653875 := by decide
  rcases family_descends (prefixWord ++ tailWord_3653875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3653898 : List Nat := [3, 1, 2, 2, 1, 1, 2, 4, 1, 4, 2]
def baseStart_3653898 : Nat := 118140960795 + 3653898 * 2 ^ 59
def prefixEnd_3653898 : Nat := 4983230072969 + 3 ^ 40 * 3653898 * 2
def baseEnd_3653898 : Nat := 1876205936502050340971035

theorem tailTrace_3653898 : CollatzResearch.WordTrace tailWord_3653898 prefixEnd_3653898 1876205936502050340971035 := by
  unfold tailWord_3653898
  simp only [CollatzResearch.WordTrace]
  refine ⟨33317152129139764235364587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88845739011039371294305565 33317152129139764235364587)
  ·
    refine ⟨49975728193709646353046881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33317152129139764235364587 49975728193709646353046881)
    ·
      refine ⟨37481796145282234764785161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49975728193709646353046881 37481796145282234764785161)
      ·
        refine ⟨28111347108961676073588871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37481796145282234764785161 28111347108961676073588871)
        ·
          refine ⟨42167020663442514110383307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28111347108961676073588871 42167020663442514110383307)
          ·
            refine ⟨63250530995163771165574961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42167020663442514110383307 63250530995163771165574961)
            ·
              refine ⟨47437898246372828374181221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63250530995163771165574961 47437898246372828374181221)
              ·
                refine ⟨8894605921194905320158979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 47437898246372828374181221 8894605921194905320158979)
                ·
                  refine ⟨13341908881792357980238469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8894605921194905320158979 13341908881792357980238469)
                  ·
                    refine ⟨2501607915336067121294713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 13341908881792357980238469 2501607915336067121294713)
                    ·
                      refine ⟨1876205936502050340971035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2501607915336067121294713 1876205936502050340971035)
                      ·
                        rfl

theorem cell23_3653898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 2, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 2, 4, 1, 4, 2].length) (baseStart_3653898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3653898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3653898 prefixEnd_3653898 := by exact prefixLift 3653898
  have htrace : WordTrace (prefixWord ++ tailWord_3653898) baseStart_3653898 baseEnd_3653898 := by
    simpa [prefixWord, tailWord_3653898, baseEnd_3653898] using wordTrace_append hprefix tailTrace_3653898
  have hstable : (prefixWord ++ tailWord_3653898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3653898).length < 2 ^ (prefixWord ++ tailWord_3653898).sum := by decide
  have hdescent : baseEnd_3653898 < baseStart_3653898 := by decide
  rcases family_descends (prefixWord ++ tailWord_3653898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3653921 : List Nat := [1, 2, 3, 2, 1, 1, 5, 1, 7]
def baseStart_3653921 : Nat := 118140960795 + 3653921 * 2 ^ 59
def prefixEnd_3653921 : Nat := 4983230072969 + 3 ^ 40 * 3653921 * 2
def baseEnd_3653921 : Nat := 208468638506344861220381

theorem tailTrace_3653921 : CollatzResearch.WordTrace tailWord_3653921 prefixEnd_3653921 208468638506344861220381 := by
  unfold tailWord_3653921
  simp only [CollatzResearch.WordTrace]
  refine ⟨133269447395475731869545617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88846298263650487913030411 133269447395475731869545617)
  ·
    refine ⟨99952085546606798902159213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133269447395475731869545617 99952085546606798902159213)
    ·
      refine ⟨37482032079977549588309705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 99952085546606798902159213 37482032079977549588309705)
      ·
        refine ⟨28111524059983162191232279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37482032079977549588309705 28111524059983162191232279)
        ·
          refine ⟨42167286089974743286848419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28111524059983162191232279 42167286089974743286848419)
          ·
            refine ⟨63250929134962114930272629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42167286089974743286848419 63250929134962114930272629)
            ·
              refine ⟨5929774606402698274713059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 63250929134962114930272629 5929774606402698274713059)
              ·
                refine ⟨8894661909604047412069589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5929774606402698274713059 8894661909604047412069589)
                ·
                  refine ⟨208468638506344861220381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8894661909604047412069589 208468638506344861220381)
                  ·
                    rfl

theorem cell23_3653921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 5, 1, 7].length) (baseStart_3653921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3653921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3653921 prefixEnd_3653921 := by exact prefixLift 3653921
  have htrace : WordTrace (prefixWord ++ tailWord_3653921) baseStart_3653921 baseEnd_3653921 := by
    simpa [prefixWord, tailWord_3653921, baseEnd_3653921] using wordTrace_append hprefix tailTrace_3653921
  have hstable : (prefixWord ++ tailWord_3653921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3653921).length < 2 ^ (prefixWord ++ tailWord_3653921).sum := by decide
  have hdescent : baseEnd_3653921 < baseStart_3653921 := by decide
  rcases family_descends (prefixWord ++ tailWord_3653921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3653932 : List Nat := [2, 2, 1, 1, 1, 3, 6, 1, 2, 2, 2]
def baseStart_3653932 : Nat := 118140960795 + 3653932 * 2 ^ 59
def prefixEnd_3653932 : Nat := 4983230072969 + 3 ^ 40 * 3653932 * 2
def baseEnd_3653932 : Nat := 1876223394844303207945879

theorem tailTrace_3653932 : CollatzResearch.WordTrace tailWord_3653932 prefixEnd_3653932 1876223394844303207945879 := by
  unfold tailWord_3653932
  simp only [CollatzResearch.WordTrace]
  refine ⟨66634924299217940374098025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88846565732290587165464033 66634924299217940374098025)
  ·
    refine ⟨49976193224413455280573519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66634924299217940374098025 49976193224413455280573519)
    ·
      refine ⟨74964289836620182920860279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49976193224413455280573519 74964289836620182920860279)
      ·
        refine ⟨112446434754930274381290419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74964289836620182920860279 112446434754930274381290419)
        ·
          refine ⟨168669652132395411571935629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112446434754930274381290419 168669652132395411571935629)
          ·
            refine ⟨63251119549648279339475861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 168669652132395411571935629 63251119549648279339475861)
            ·
              refine ⟨2964896228889763094037931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 63251119549648279339475861 2964896228889763094037931)
              ·
                refine ⟨4447344343334644641056897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2964896228889763094037931 4447344343334644641056897)
                ·
                  refine ⟨3335508257500983480792673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4447344343334644641056897 3335508257500983480792673)
                  ·
                    refine ⟨2501631193125737610594505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3335508257500983480792673 2501631193125737610594505)
                    ·
                      refine ⟨1876223394844303207945879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2501631193125737610594505 1876223394844303207945879)
                      ·
                        rfl

theorem cell23_3653932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 2, 2, 2].length) (baseStart_3653932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3653932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3653932 prefixEnd_3653932 := by exact prefixLift 3653932
  have htrace : WordTrace (prefixWord ++ tailWord_3653932) baseStart_3653932 baseEnd_3653932 := by
    simpa [prefixWord, tailWord_3653932, baseEnd_3653932] using wordTrace_append hprefix tailTrace_3653932
  have hstable : (prefixWord ++ tailWord_3653932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3653932).length < 2 ^ (prefixWord ++ tailWord_3653932).sum := by decide
  have hdescent : baseEnd_3653932 < baseStart_3653932 := by decide
  rcases family_descends (prefixWord ++ tailWord_3653932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3653971 : List Nat := [1, 1, 1, 2, 1, 1, 4, 3, 4, 1, 4]
def baseStart_3653971 : Nat := 118140960795 + 3653971 * 2 ^ 59
def prefixEnd_3653971 : Nat := 4983230072969 + 3 ^ 40 * 3653971 * 2
def baseEnd_3653971 : Nat := 1876243420589828555358199

theorem tailTrace_3653971 : CollatzResearch.WordTrace tailWord_3653971 prefixEnd_3653971 1876243420589828555358199 := by
  unfold tailWord_3653971
  simp only [CollatzResearch.WordTrace]
  refine ⟨133271271045294590408865767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88847514030196393605910511 133271271045294590408865767)
  ·
    refine ⟨199906906567941885613298651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133271271045294590408865767 199906906567941885613298651)
    ·
      refine ⟨299860359851912828419947977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 199906906567941885613298651 299860359851912828419947977)
      ·
        refine ⟨224895269888934621314960983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 299860359851912828419947977 224895269888934621314960983)
        ·
          refine ⟨337342904833401931972441475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 224895269888934621314960983 337342904833401931972441475)
          ·
            refine ⟨506014357250102897958662213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 337342904833401931972441475 506014357250102897958662213)
            ·
              refine ⟨94877691984394293367249165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 506014357250102897958662213 94877691984394293367249165)
              ·
                refine ⟨35579134494147860012718437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 94877691984394293367249165 35579134494147860012718437)
                ·
                  refine ⟨6671087717652723752384707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35579134494147860012718437 6671087717652723752384707)
                  ·
                    refine ⟨10006631576479085628577061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6671087717652723752384707 10006631576479085628577061)
                    ·
                      refine ⟨1876243420589828555358199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10006631576479085628577061 1876243420589828555358199)
                      ·
                        rfl

theorem cell23_3653971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 3, 4, 1, 4].length) (baseStart_3653971 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3653971 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3653971 prefixEnd_3653971 := by exact prefixLift 3653971
  have htrace : WordTrace (prefixWord ++ tailWord_3653971) baseStart_3653971 baseEnd_3653971 := by
    simpa [prefixWord, tailWord_3653971, baseEnd_3653971] using wordTrace_append hprefix tailTrace_3653971
  have hstable : (prefixWord ++ tailWord_3653971).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3653971).length < 2 ^ (prefixWord ++ tailWord_3653971).sum := by decide
  have hdescent : baseEnd_3653971 < baseStart_3653971 := by decide
  rcases family_descends (prefixWord ++ tailWord_3653971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3653972 : List Nat := [2, 4, 1, 1, 2, 4, 2, 2, 5]
def baseStart_3653972 : Nat := 118140960795 + 3653972 * 2 ^ 59
def prefixEnd_3653972 : Nat := 4983230072969 + 3 ^ 40 * 3653972 * 2
def baseEnd_3653972 : Nat := 208471548230053672382855

theorem tailTrace_3653972 : CollatzResearch.WordTrace tailWord_3653972 prefixEnd_3653972 208471548230053672382855 := by
  unfold tailWord_3653972
  simp only [CollatzResearch.WordTrace]
  refine ⟨66635653759145483789826085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88847538345527311719768113 66635653759145483789826085)
  ·
    refine ⟨12494185079839778210592391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 66635653759145483789826085 12494185079839778210592391)
    ·
      refine ⟨18741277619759667315888587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12494185079839778210592391 18741277619759667315888587)
      ·
        refine ⟨28111916429639500973832881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18741277619759667315888587 28111916429639500973832881)
        ·
          refine ⟨21083937322229625730374661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28111916429639500973832881 21083937322229625730374661)
          ·
            refine ⟨3953238247918054824445249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21083937322229625730374661 3953238247918054824445249)
            ·
              refine ⟨2964928685938541118333937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3953238247918054824445249 2964928685938541118333937)
              ·
                refine ⟨2223696514453905838750453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2964928685938541118333937 2223696514453905838750453)
                ·
                  refine ⟨208471548230053672382855, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2223696514453905838750453 208471548230053672382855)
                  ·
                    rfl

theorem cell23_3653972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 4, 2, 2, 5].length) (baseStart_3653972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3653972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3653972 prefixEnd_3653972 := by exact prefixLift 3653972
  have htrace : WordTrace (prefixWord ++ tailWord_3653972) baseStart_3653972 baseEnd_3653972 := by
    simpa [prefixWord, tailWord_3653972, baseEnd_3653972] using wordTrace_append hprefix tailTrace_3653972
  have hstable : (prefixWord ++ tailWord_3653972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3653972).length < 2 ^ (prefixWord ++ tailWord_3653972).sum := by decide
  have hdescent : baseEnd_3653972 < baseStart_3653972 := by decide
  rcases family_descends (prefixWord ++ tailWord_3653972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3654005 : List Nat := [1, 3, 4, 1, 2, 1, 3, 1, 2, 1, 4]
def baseStart_3654005 : Nat := 118140960795 + 3654005 * 2 ^ 59
def prefixEnd_3654005 : Nat := 4983230072969 + 3 ^ 40 * 3654005 * 2
def baseEnd_3654005 : Nat := 1876260878932081422333043

theorem tailTrace_3654005 : CollatzResearch.WordTrace tailWord_3654005 prefixEnd_3654005 1876260878932081422333043 := by
  unfold tailWord_3654005
  simp only [CollatzResearch.WordTrace]
  refine ⟨133272511127171414215603469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88848340751447609477068979 133272511127171414215603469)
  ·
    refine ⟨49977191672689280330851301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 133272511127171414215603469 49977191672689280330851301)
    ·
      refine ⟨9370723438629240062034619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 49977191672689280330851301 9370723438629240062034619)
      ·
        refine ⟨14056085157943860093051929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9370723438629240062034619 14056085157943860093051929)
        ·
          refine ⟨10542063868457895069788947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14056085157943860093051929 10542063868457895069788947)
          ·
            refine ⟨15813095802686842604683421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10542063868457895069788947 15813095802686842604683421)
            ·
              refine ⟨5929910926007565976756283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15813095802686842604683421 5929910926007565976756283)
              ·
                refine ⟨8894866389011348965134425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5929910926007565976756283 8894866389011348965134425)
                ·
                  refine ⟨6671149791758511723850819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8894866389011348965134425 6671149791758511723850819)
                  ·
                    refine ⟨10006724687637767585776229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6671149791758511723850819 10006724687637767585776229)
                    ·
                      refine ⟨1876260878932081422333043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10006724687637767585776229 1876260878932081422333043)
                      ·
                        rfl

theorem cell23_3654005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 3, 1, 2, 1, 4].length) (baseStart_3654005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3654005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3654005 prefixEnd_3654005 := by exact prefixLift 3654005
  have htrace : WordTrace (prefixWord ++ tailWord_3654005) baseStart_3654005 baseEnd_3654005 := by
    simpa [prefixWord, tailWord_3654005, baseEnd_3654005] using wordTrace_append hprefix tailTrace_3654005
  have hstable : (prefixWord ++ tailWord_3654005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3654005).length < 2 ^ (prefixWord ++ tailWord_3654005).sum := by decide
  have hdescent : baseEnd_3654005 < baseStart_3654005 := by decide
  rcases family_descends (prefixWord ++ tailWord_3654005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3654028 : List Nat := [2, 2, 1, 2, 1, 4, 3, 2, 6]
def baseStart_3654028 : Nat := 118140960795 + 3654028 * 2 ^ 59
def prefixEnd_3654028 : Nat := 4983230072969 + 3 ^ 40 * 3654028 * 2
def baseEnd_3654028 : Nat := 208474743220792759149493

theorem tailTrace_3654028 : CollatzResearch.WordTrace tailWord_3654028 prefixEnd_3654028 208474743220792759149493 := by
  unfold tailWord_3654028
  simp only [CollatzResearch.WordTrace]
  refine ⟨66636675003044044571845369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88848900004058726095793825 66636675003044044571845369)
  ·
    refine ⟨49977506252283033428884027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66636675003044044571845369 49977506252283033428884027)
    ·
      refine ⟨74966259378424550143326041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49977506252283033428884027 74966259378424550143326041)
      ·
        refine ⟨56224694533818412607494531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74966259378424550143326041 56224694533818412607494531)
        ·
          refine ⟨84337041800727618911241797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56224694533818412607494531 84337041800727618911241797)
          ·
            refine ⟨15813195337636428545857837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 84337041800727618911241797 15813195337636428545857837)
            ·
              refine ⟨5929948251613660704696689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15813195337636428545857837 5929948251613660704696689)
              ·
                refine ⟨4447461188710245528522517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5929948251613660704696689 4447461188710245528522517)
                ·
                  refine ⟨208474743220792759149493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4447461188710245528522517 208474743220792759149493)
                  ·
                    rfl

theorem cell23_3654028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 3, 2, 6].length) (baseStart_3654028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3654028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3654028 prefixEnd_3654028 := by exact prefixLift 3654028
  have htrace : WordTrace (prefixWord ++ tailWord_3654028) baseStart_3654028 baseEnd_3654028 := by
    simpa [prefixWord, tailWord_3654028, baseEnd_3654028] using wordTrace_append hprefix tailTrace_3654028
  have hstable : (prefixWord ++ tailWord_3654028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3654028).length < 2 ^ (prefixWord ++ tailWord_3654028).sum := by decide
  have hdescent : baseEnd_3654028 < baseStart_3654028 := by decide
  rcases family_descends (prefixWord ++ tailWord_3654028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3654065 : List Nat := [1, 2, 2, 4, 1, 2, 2, 1, 1, 5, 2]
def baseStart_3654065 : Nat := 118140960795 + 3654065 * 2 ^ 59
def prefixEnd_3654065 : Nat := 4983230072969 + 3 ^ 40 * 3654065 * 2
def baseEnd_3654065 : Nat := 1876291687771351187582767

theorem tailTrace_3654065 : CollatzResearch.WordTrace tailWord_3654065 prefixEnd_3654065 1876291687771351187582767 := by
  unfold tailWord_3654065
  simp only [CollatzResearch.WordTrace]
  refine ⟨133274699506954044462787649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88849799671302696308525099 133274699506954044462787649)
  ·
    refine ⟨99956024630215533347090737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133274699506954044462787649 99956024630215533347090737)
    ·
      refine ⟨74967018472661650010318053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99956024630215533347090737 74967018472661650010318053)
      ·
        refine ⟨14056315963624059376934635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 74967018472661650010318053 14056315963624059376934635)
        ·
          refine ⟨21084473945436089065401953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14056315963624059376934635 21084473945436089065401953)
          ·
            refine ⟨15813355459077066799051465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21084473945436089065401953 15813355459077066799051465)
            ·
              refine ⟨11860016594307800099288599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15813355459077066799051465 11860016594307800099288599)
              ·
                refine ⟨17790024891461700148932899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11860016594307800099288599 17790024891461700148932899)
                ·
                  refine ⟨26685037337192550223399349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17790024891461700148932899 26685037337192550223399349)
                  ·
                    refine ⟨2501722250361801583443689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 26685037337192550223399349 2501722250361801583443689)
                    ·
                      refine ⟨1876291687771351187582767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2501722250361801583443689 1876291687771351187582767)
                      ·
                        rfl

theorem cell23_3654065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 2, 1, 1, 5, 2].length) (baseStart_3654065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3654065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3654065 prefixEnd_3654065 := by exact prefixLift 3654065
  have htrace : WordTrace (prefixWord ++ tailWord_3654065) baseStart_3654065 baseEnd_3654065 := by
    simpa [prefixWord, tailWord_3654065, baseEnd_3654065] using wordTrace_append hprefix tailTrace_3654065
  have hstable : (prefixWord ++ tailWord_3654065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3654065).length < 2 ^ (prefixWord ++ tailWord_3654065).sum := by decide
  have hdescent : baseEnd_3654065 < baseStart_3654065 := by decide
  rcases family_descends (prefixWord ++ tailWord_3654065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3654105 : List Nat := [1, 2, 1, 2, 4, 1, 3, 3, 2, 4]
def baseStart_3654105 : Nat := 118140960795 + 3654105 * 2 ^ 59
def prefixEnd_3654105 : Nat := 4983230072969 + 3 ^ 40 * 3654105 * 2
def baseEnd_3654105 : Nat := 625437408999177010360861

theorem tailTrace_3654105 : CollatzResearch.WordTrace tailWord_3654105 prefixEnd_3654105 625437408999177010360861 := by
  unfold tailWord_3654105
  simp only [CollatzResearch.WordTrace]
  refine ⟨133276158426809131294243769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88850772284539420862829179 133276158426809131294243769)
  ·
    refine ⟨99957118820106848470682827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133276158426809131294243769 99957118820106848470682827)
    ·
      refine ⟨149935678230160272706024241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99957118820106848470682827 149935678230160272706024241)
      ·
        refine ⟨112451758672620204529518181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 149935678230160272706024241 112451758672620204529518181)
        ·
          refine ⟨21084704751116288349284659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 112451758672620204529518181 21084704751116288349284659)
          ·
            refine ⟨31627057126674432523926989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21084704751116288349284659 31627057126674432523926989)
            ·
              refine ⟨11860146422502912196472621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31627057126674432523926989 11860146422502912196472621)
              ·
                refine ⟨4447554908438592073677233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11860146422502912196472621 4447554908438592073677233)
                ·
                  refine ⟨3335666181328944055257925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4447554908438592073677233 3335666181328944055257925)
                  ·
                    refine ⟨625437408999177010360861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3335666181328944055257925 625437408999177010360861)
                    ·
                      rfl

theorem cell23_3654105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 3, 3, 2, 4].length) (baseStart_3654105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3654105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3654105 prefixEnd_3654105 := by exact prefixLift 3654105
  have htrace : WordTrace (prefixWord ++ tailWord_3654105) baseStart_3654105 baseEnd_3654105 := by
    simpa [prefixWord, tailWord_3654105, baseEnd_3654105] using wordTrace_append hprefix tailTrace_3654105
  have hstable : (prefixWord ++ tailWord_3654105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3654105).length < 2 ^ (prefixWord ++ tailWord_3654105).sum := by decide
  have hdescent : baseEnd_3654105 < baseStart_3654105 := by decide
  rcases family_descends (prefixWord ++ tailWord_3654105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3654125 : List Nat := [1, 5, 1, 3, 1, 1, 1, 1, 3, 2, 4]
def baseStart_3654125 : Nat := 118140960795 + 3654125 * 2 ^ 59
def prefixEnd_3654125 : Nat := 4983230072969 + 3 ^ 40 * 3654125 * 2
def baseEnd_3654125 : Nat := 1876322496610620952832491

theorem tailTrace_3654125 : CollatzResearch.WordTrace tailWord_3654125 prefixEnd_3654125 1876322496610620952832491 := by
  unfold tailWord_3654125
  simp only [CollatzResearch.WordTrace]
  refine ⟨133276887886736674709971829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88851258591157783139981219 133276887886736674709971829)
  ·
    refine ⟨12494708239381563254059859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 133276887886736674709971829 12494708239381563254059859)
    ·
      refine ⟨18742062359072344881089789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12494708239381563254059859 18742062359072344881089789)
      ·
        refine ⟨7028273384652129330408671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18742062359072344881089789 7028273384652129330408671)
        ·
          refine ⟨10542410076978193995613007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7028273384652129330408671 10542410076978193995613007)
          ·
            refine ⟨15813615115467290993419511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10542410076978193995613007 15813615115467290993419511)
            ·
              refine ⟨23720422673200936490129267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15813615115467290993419511 23720422673200936490129267)
              ·
                refine ⟨35580634009801404735193901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23720422673200936490129267 35580634009801404735193901)
                ·
                  refine ⟨13342737753675526775697713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35580634009801404735193901 13342737753675526775697713)
                  ·
                    refine ⟨10007053315256645081773285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13342737753675526775697713 10007053315256645081773285)
                    ·
                      refine ⟨1876322496610620952832491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10007053315256645081773285 1876322496610620952832491)
                      ·
                        rfl

theorem cell23_3654125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 1, 1, 3, 2, 4].length) (baseStart_3654125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3654125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3654125 prefixEnd_3654125 := by exact prefixLift 3654125
  have htrace : WordTrace (prefixWord ++ tailWord_3654125) baseStart_3654125 baseEnd_3654125 := by
    simpa [prefixWord, tailWord_3654125, baseEnd_3654125] using wordTrace_append hprefix tailTrace_3654125
  have hstable : (prefixWord ++ tailWord_3654125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3654125).length < 2 ^ (prefixWord ++ tailWord_3654125).sum := by decide
  have hdescent : baseEnd_3654125 < baseStart_3654125 := by decide
  rcases family_descends (prefixWord ++ tailWord_3654125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3654129 : List Nat := [1, 2, 2, 2, 3, 1, 2, 5, 1, 2, 2]
def baseStart_3654129 : Nat := 118140960795 + 3654129 * 2 ^ 59
def prefixEnd_3654129 : Nat := 4983230072969 + 3 ^ 40 * 3654129 * 2
def baseEnd_3654129 : Nat := 1876324550533238937182473

theorem tailTrace_3654129 : CollatzResearch.WordTrace tailWord_3654129 prefixEnd_3654129 1876324550533238937182473 := by
  unfold tailWord_3654129
  simp only [CollatzResearch.WordTrace]
  refine ⟨133277033778722183393117441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88851355852481455595411627 133277033778722183393117441)
  ·
    refine ⟨99957775334041637544838081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133277033778722183393117441 99957775334041637544838081)
    ·
      refine ⟨74968331500531228158628561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 99957775334041637544838081 74968331500531228158628561)
      ·
        refine ⟨56226248625398421118971421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74968331500531228158628561 56226248625398421118971421)
        ·
          refine ⟨21084843234524407919614283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56226248625398421118971421 21084843234524407919614283)
          ·
            refine ⟨31627264851786611879421425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21084843234524407919614283 31627264851786611879421425)
            ·
              refine ⟨23720448638839958909566069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31627264851786611879421425 23720448638839958909566069)
              ·
                refine ⟨2223792059891246147771819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 23720448638839958909566069 2223792059891246147771819)
                ·
                  refine ⟨3335688089836869221657729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2223792059891246147771819 3335688089836869221657729)
                  ·
                    refine ⟨2501766067377651916243297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3335688089836869221657729 2501766067377651916243297)
                    ·
                      refine ⟨1876324550533238937182473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2501766067377651916243297 1876324550533238937182473)
                      ·
                        rfl

theorem cell23_3654129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 2, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 2, 5, 1, 2, 2].length) (baseStart_3654129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3654129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3654129 prefixEnd_3654129 := by exact prefixLift 3654129
  have htrace : WordTrace (prefixWord ++ tailWord_3654129) baseStart_3654129 baseEnd_3654129 := by
    simpa [prefixWord, tailWord_3654129, baseEnd_3654129] using wordTrace_append hprefix tailTrace_3654129
  have hstable : (prefixWord ++ tailWord_3654129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3654129).length < 2 ^ (prefixWord ++ tailWord_3654129).sum := by decide
  have hdescent : baseEnd_3654129 < baseStart_3654129 := by decide
  rcases family_descends (prefixWord ++ tailWord_3654129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3654172 : List Nat := [2, 2, 3, 1, 2, 2, 2, 1, 3, 3, 2]
def baseStart_3654172 : Nat := 118140960795 + 3654172 * 2 ^ 59
def prefixEnd_3654172 : Nat := 4983230072969 + 3 ^ 40 * 3654172 * 2
def baseEnd_3654172 : Nat := 1876346630201382268944775

theorem tailTrace_3654172 : CollatzResearch.WordTrace tailWord_3654172 prefixEnd_3654172 1876346630201382268944775 := by
  unfold tailWord_3654172
  simp only [CollatzResearch.WordTrace]
  refine ⟨66639301058783200868466385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88852401411710934491288513 66639301058783200868466385)
  ·
    refine ⟨49979475794087400651349789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66639301058783200868466385 49979475794087400651349789)
    ·
      refine ⟨18742303422782775244256171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49979475794087400651349789 18742303422782775244256171)
      ·
        refine ⟨28113455134174162866384257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18742303422782775244256171 28113455134174162866384257)
        ·
          refine ⟨21085091350630622149788193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28113455134174162866384257 21085091350630622149788193)
          ·
            refine ⟨15813818512972966612341145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21085091350630622149788193 15813818512972966612341145)
            ·
              refine ⟨11860363884729724959255859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15813818512972966612341145 11860363884729724959255859)
              ·
                refine ⟨17790545827094587438883789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11860363884729724959255859 17790545827094587438883789)
                ·
                  refine ⟨6671454685160470289581421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17790545827094587438883789 6671454685160470289581421)
                  ·
                    refine ⟨2501795506935176358593033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6671454685160470289581421 2501795506935176358593033)
                    ·
                      refine ⟨1876346630201382268944775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2501795506935176358593033 1876346630201382268944775)
                      ·
                        rfl

theorem cell23_3654172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 2, 1, 3, 3, 2].length) (baseStart_3654172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3654172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3654172 prefixEnd_3654172 := by exact prefixLift 3654172
  have htrace : WordTrace (prefixWord ++ tailWord_3654172) baseStart_3654172 baseEnd_3654172 := by
    simpa [prefixWord, tailWord_3654172, baseEnd_3654172] using wordTrace_append hprefix tailTrace_3654172
  have hstable : (prefixWord ++ tailWord_3654172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3654172).length < 2 ^ (prefixWord ++ tailWord_3654172).sum := by decide
  have hdescent : baseEnd_3654172 < baseStart_3654172 := by decide
  rcases family_descends (prefixWord ++ tailWord_3654172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3654178 : List Nat := [3, 3, 1, 1, 1, 1, 1, 1, 3, 8]
def baseStart_3654178 : Nat := 118140960795 + 3654178 * 2 ^ 59
def prefixEnd_3654178 : Nat := 4983230072969 + 3 ^ 40 * 3654178 * 2
def baseEnd_3654178 : Nat := 625449903695103081823249

theorem tailTrace_3654178 : CollatzResearch.WordTrace tailWord_3654178 prefixEnd_3654178 625449903695103081823249 := by
  unfold tailWord_3654178
  simp only [CollatzResearch.WordTrace]
  refine ⟨33319705238886166190412797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88852547303696443174434125 33319705238886166190412797)
  ·
    refine ⟨12494889464582312321404799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33319705238886166190412797 12494889464582312321404799)
    ·
      refine ⟨18742334196873468482107199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12494889464582312321404799 18742334196873468482107199)
      ·
        refine ⟨28113501295310202723160799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18742334196873468482107199 28113501295310202723160799)
        ·
          refine ⟨42170251942965304084741199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28113501295310202723160799 42170251942965304084741199)
          ·
            refine ⟨63255377914447956127111799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42170251942965304084741199 63255377914447956127111799)
            ·
              refine ⟨94883066871671934190667699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63255377914447956127111799 94883066871671934190667699)
              ·
                refine ⟨142324600307507901286001549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 94883066871671934190667699 142324600307507901286001549)
                ·
                  refine ⟨53371725115315462982250581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 142324600307507901286001549 53371725115315462982250581)
                  ·
                    refine ⟨625449903695103081823249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 53371725115315462982250581 625449903695103081823249)
                    ·
                      rfl

theorem cell23_3654178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 1, 3, 8].length) (baseStart_3654178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3654178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3654178 prefixEnd_3654178 := by exact prefixLift 3654178
  have htrace : WordTrace (prefixWord ++ tailWord_3654178) baseStart_3654178 baseEnd_3654178 := by
    simpa [prefixWord, tailWord_3654178, baseEnd_3654178] using wordTrace_append hprefix tailTrace_3654178
  have hstable : (prefixWord ++ tailWord_3654178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3654178).length < 2 ^ (prefixWord ++ tailWord_3654178).sum := by decide
  have hdescent : baseEnd_3654178 < baseStart_3654178 := by decide
  rcases family_descends (prefixWord ++ tailWord_3654178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3654183 : List Nat := [1, 1, 7, 2, 1, 2, 2, 1, 1, 2, 3]
def baseStart_3654183 : Nat := 118140960795 + 3654183 * 2 ^ 59
def prefixEnd_3654183 : Nat := 4983230072969 + 3 ^ 40 * 3654183 * 2
def baseEnd_3654183 : Nat := 1876352278488581725907225

theorem tailTrace_3654183 : CollatzResearch.WordTrace tailWord_3654183 prefixEnd_3654183 1876352278488581725907225 := by
  unfold tailWord_3654183
  simp only [CollatzResearch.WordTrace]
  refine ⟨133279003320526550615583203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88852668880351033743722135 133279003320526550615583203)
  ·
    refine ⟨199918504980789825923374805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133279003320526550615583203 199918504980789825923374805)
    ·
      refine ⟨4685589960487261545079097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 199918504980789825923374805 4685589960487261545079097)
      ·
        refine ⟨3514192470365446158809323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4685589960487261545079097 3514192470365446158809323)
        ·
          refine ⟨5271288705548169238213985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3514192470365446158809323 5271288705548169238213985)
          ·
            refine ⟨3953466529161126928660489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5271288705548169238213985 3953466529161126928660489)
            ·
              refine ⟨2965099896870845196495367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3953466529161126928660489 2965099896870845196495367)
              ·
                refine ⟨4447649845306267794743051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2965099896870845196495367 4447649845306267794743051)
                ·
                  refine ⟨6671474767959401692114577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4447649845306267794743051 6671474767959401692114577)
                  ·
                    refine ⟨5003606075969551269085933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6671474767959401692114577 5003606075969551269085933)
                    ·
                      refine ⟨1876352278488581725907225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5003606075969551269085933 1876352278488581725907225)
                      ·
                        rfl

theorem cell23_3654183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 2, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 2, 2, 1, 1, 2, 3].length) (baseStart_3654183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3654183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3654183 prefixEnd_3654183 := by exact prefixLift 3654183
  have htrace : WordTrace (prefixWord ++ tailWord_3654183) baseStart_3654183 baseEnd_3654183 := by
    simpa [prefixWord, tailWord_3654183, baseEnd_3654183] using wordTrace_append hprefix tailTrace_3654183
  have hstable : (prefixWord ++ tailWord_3654183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3654183).length < 2 ^ (prefixWord ++ tailWord_3654183).sum := by decide
  have hdescent : baseEnd_3654183 < baseStart_3654183 := by decide
  rcases family_descends (prefixWord ++ tailWord_3654183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3654188 : List Nat := [2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 5]
def baseStart_3654188 : Nat := 118140960795 + 3654188 * 2 ^ 59
def prefixEnd_3654188 : Nat := 4983230072969 + 3 ^ 40 * 3654188 * 2
def baseEnd_3654188 : Nat := 1876354845891854206344701

theorem tailTrace_3654188 : CollatzResearch.WordTrace tailWord_3654188 prefixEnd_3654188 1876354845891854206344701 := by
  unfold tailWord_3654188
  simp only [CollatzResearch.WordTrace]
  refine ⟨66639592842754218234757609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88852790457005624313010145 66639592842754218234757609)
  ·
    refine ⟨49979694632065663676068207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66639592842754218234757609 49979694632065663676068207)
    ·
      refine ⟨74969541948098495514102311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49979694632065663676068207 74969541948098495514102311)
      ·
        refine ⟨112454312922147743271153467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 74969541948098495514102311 112454312922147743271153467)
        ·
          refine ⟨168681469383221614906730201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112454312922147743271153467 168681469383221614906730201)
          ·
            refine ⟨126511102037416211180047651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 168681469383221614906730201 126511102037416211180047651)
            ·
              refine ⟨189766653056124316770071477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 126511102037416211180047651 189766653056124316770071477)
              ·
                refine ⟨17790623724011654697194201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 189766653056124316770071477 17790623724011654697194201)
                ·
                  refine ⟨13342967793008741022895651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17790623724011654697194201 13342967793008741022895651)
                  ·
                    refine ⟨20014451689513111534343477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13342967793008741022895651 20014451689513111534343477)
                    ·
                      refine ⟨1876354845891854206344701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20014451689513111534343477 1876354845891854206344701)
                      ·
                        rfl

theorem cell23_3654188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 5].length) (baseStart_3654188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3654188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3654188 prefixEnd_3654188 := by exact prefixLift 3654188
  have htrace : WordTrace (prefixWord ++ tailWord_3654188) baseStart_3654188 baseEnd_3654188 := by
    simpa [prefixWord, tailWord_3654188, baseEnd_3654188] using wordTrace_append hprefix tailTrace_3654188
  have hstable : (prefixWord ++ tailWord_3654188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3654188).length < 2 ^ (prefixWord ++ tailWord_3654188).sum := by decide
  have hdescent : baseEnd_3654188 < baseStart_3654188 := by decide
  rcases family_descends (prefixWord ++ tailWord_3654188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3654196 : List Nat := [2, 5, 1, 3, 1, 1, 1, 1, 4, 1, 3]
def baseStart_3654196 : Nat := 118140960795 + 3654196 * 2 ^ 59
def prefixEnd_3654196 : Nat := 4983230072969 + 3 ^ 40 * 3654196 * 2
def baseEnd_3654196 : Nat := 1876358953737090175044665

theorem tailTrace_3654196 : CollatzResearch.WordTrace tailWord_3654196 prefixEnd_3654196 1876358953737090175044665 := by
  unfold tailWord_3654196
  simp only [CollatzResearch.WordTrace]
  refine ⟨66639738734739726917903221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88852984979652969223870961 66639738734739726917903221)
  ·
    refine ⟨6247475506381849398553427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 66639738734739726917903221 6247475506381849398553427)
    ·
      refine ⟨9371213259572774097830141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6247475506381849398553427 9371213259572774097830141)
      ·
        refine ⟨3514204972339790286686303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9371213259572774097830141 3514204972339790286686303)
        ·
          refine ⟨5271307458509685430029455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3514204972339790286686303 5271307458509685430029455)
          ·
            refine ⟨7906961187764528145044183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5271307458509685430029455 7906961187764528145044183)
            ·
              refine ⟨11860441781646792217566275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7906961187764528145044183 11860441781646792217566275)
              ·
                refine ⟨17790662672470188326349413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11860441781646792217566275 17790662672470188326349413)
                ·
                  refine ⟨3335749251088160311190515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17790662672470188326349413 3335749251088160311190515)
                  ·
                    refine ⟨5003623876632240466785773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3335749251088160311190515 5003623876632240466785773)
                    ·
                      refine ⟨1876358953737090175044665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5003623876632240466785773 1876358953737090175044665)
                      ·
                        rfl

theorem cell23_3654196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 1, 1, 1, 4, 1, 3].length) (baseStart_3654196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3654196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3654196 prefixEnd_3654196 := by exact prefixLift 3654196
  have htrace : WordTrace (prefixWord ++ tailWord_3654196) baseStart_3654196 baseEnd_3654196 := by
    simpa [prefixWord, tailWord_3654196, baseEnd_3654196] using wordTrace_append hprefix tailTrace_3654196
  have hstable : (prefixWord ++ tailWord_3654196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3654196).length < 2 ^ (prefixWord ++ tailWord_3654196).sum := by decide
  have hdescent : baseEnd_3654196 < baseStart_3654196 := by decide
  rcases family_descends (prefixWord ++ tailWord_3654196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3654208 : List Nat := [2, 1, 1, 2, 2, 2, 3, 3, 7]
def baseStart_3654208 : Nat := 118140960795 + 3654208 * 2 ^ 59
def prefixEnd_3654208 : Nat := 4983230072969 + 3 ^ 40 * 3654208 * 2
def baseEnd_3654208 : Nat := 208485012833882680899401

theorem tailTrace_3654208 : CollatzResearch.WordTrace tailWord_3654208 prefixEnd_3654208 208485012833882680899401 := by
  unfold tailWord_3654208
  simp only [CollatzResearch.WordTrace]
  refine ⟨66639957572717989942621639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88853276763623986590162185 66639957572717989942621639)
  ·
    refine ⟨99959936359076984913932459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66639957572717989942621639 99959936359076984913932459)
    ·
      refine ⟨149939904538615477370898689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99959936359076984913932459 149939904538615477370898689)
      ·
        refine ⟨112454928403961608028174017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 149939904538615477370898689 112454928403961608028174017)
        ·
          refine ⟨84341196302971206021130513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 112454928403961608028174017 84341196302971206021130513)
          ·
            refine ⟨63255897227228404515847885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84341196302971206021130513 63255897227228404515847885)
            ·
              refine ⟨23720961460210651693442957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 63255897227228404515847885 23720961460210651693442957)
              ·
                refine ⟨8895360547578994385041109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23720961460210651693442957 8895360547578994385041109)
                ·
                  refine ⟨208485012833882680899401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8895360547578994385041109 208485012833882680899401)
                  ·
                    rfl

theorem cell23_3654208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 3, 3, 7].length) (baseStart_3654208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3654208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3654208 prefixEnd_3654208 := by exact prefixLift 3654208
  have htrace : WordTrace (prefixWord ++ tailWord_3654208) baseStart_3654208 baseEnd_3654208 := by
    simpa [prefixWord, tailWord_3654208, baseEnd_3654208] using wordTrace_append hprefix tailTrace_3654208
  have hstable : (prefixWord ++ tailWord_3654208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3654208).length < 2 ^ (prefixWord ++ tailWord_3654208).sum := by decide
  have hdescent : baseEnd_3654208 < baseStart_3654208 := by decide
  rcases family_descends (prefixWord ++ tailWord_3654208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3654215 : List Nat := [1, 1, 4, 1, 4, 1, 2, 1, 2, 2, 4]
def baseStart_3654215 : Nat := 118140960795 + 3654215 * 2 ^ 59
def prefixEnd_3654215 : Nat := 4983230072969 + 3 ^ 40 * 3654215 * 2
def baseEnd_3654215 : Nat := 1876368709869525600707077

theorem tailTrace_3654215 : CollatzResearch.WordTrace tailWord_3654215 prefixEnd_3654215 1876368709869525600707077 := by
  unfold tailWord_3654215
  simp only [CollatzResearch.WordTrace]
  refine ⟨133280170456410620080748099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88853446970940413387165399 133280170456410620080748099)
  ·
    refine ⟨199920255684615930121122149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133280170456410620080748099 199920255684615930121122149)
    ·
      refine ⟨37485047940865486897710403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 199920255684615930121122149 37485047940865486897710403)
      ·
        refine ⟨56227571911298230346565605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37485047940865486897710403 56227571911298230346565605)
        ·
          refine ⟨10542669733368418189981051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 56227571911298230346565605 10542669733368418189981051)
          ·
            refine ⟨15814004600052627284971577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10542669733368418189981051 15814004600052627284971577)
            ·
              refine ⟨11860503450039470463728683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15814004600052627284971577 11860503450039470463728683)
              ·
                refine ⟨17790755175059205695593025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11860503450039470463728683 17790755175059205695593025)
                ·
                  refine ⟨13343066381294404271694769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17790755175059205695593025 13343066381294404271694769)
                  ·
                    refine ⟨10007299785970803203771077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13343066381294404271694769 10007299785970803203771077)
                    ·
                      refine ⟨1876368709869525600707077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10007299785970803203771077 1876368709869525600707077)
                      ·
                        rfl

theorem cell23_3654215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 2, 1, 2, 2, 4].length) (baseStart_3654215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3654215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3654215 prefixEnd_3654215 := by exact prefixLift 3654215
  have htrace : WordTrace (prefixWord ++ tailWord_3654215) baseStart_3654215 baseEnd_3654215 := by
    simpa [prefixWord, tailWord_3654215, baseEnd_3654215] using wordTrace_append hprefix tailTrace_3654215
  have hstable : (prefixWord ++ tailWord_3654215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3654215).length < 2 ^ (prefixWord ++ tailWord_3654215).sum := by decide
  have hdescent : baseEnd_3654215 < baseStart_3654215 := by decide
  rcases family_descends (prefixWord ++ tailWord_3654215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3654265 : List Nat := [1, 2, 1, 3, 3, 3, 1, 1, 1, 2, 5]
def baseStart_3654265 : Nat := 118140960795 + 3654265 * 2 ^ 59
def prefixEnd_3654265 : Nat := 4983230072969 + 3 ^ 40 * 3654265 * 2
def baseEnd_3654265 : Nat := 1876394383902250405081847

theorem tailTrace_3654265 : CollatzResearch.WordTrace tailWord_3654265 prefixEnd_3654265 1876394383902250405081847 := by
  unfold tailWord_3654265
  simp only [CollatzResearch.WordTrace]
  refine ⟨133281994106229478620068249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88854662737486319080045499 133281994106229478620068249)
  ·
    refine ⟨99961495579672108965051187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133281994106229478620068249 99961495579672108965051187)
    ·
      refine ⟨149942243369508163447576781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99961495579672108965051187 149942243369508163447576781)
      ·
        refine ⟨56228341263565561292841293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 149942243369508163447576781 56228341263565561292841293)
        ·
          refine ⟨21085627973837085484815485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56228341263565561292841293 21085627973837085484815485)
          ·
            refine ⟨7907110490188907056805807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21085627973837085484815485 7907110490188907056805807)
            ·
              refine ⟨11860665735283360585208711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7907110490188907056805807 11860665735283360585208711)
              ·
                refine ⟨17790998602925040877813067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11860665735283360585208711 17790998602925040877813067)
                ·
                  refine ⟨26686497904387561316719601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17790998602925040877813067 26686497904387561316719601)
                  ·
                    refine ⟨20014873428290670987539701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26686497904387561316719601 20014873428290670987539701)
                    ·
                      refine ⟨1876394383902250405081847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 20014873428290670987539701 1876394383902250405081847)
                      ·
                        rfl

theorem cell23_3654265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 3, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 3, 1, 1, 1, 2, 5].length) (baseStart_3654265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3654265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3654265 prefixEnd_3654265 := by exact prefixLift 3654265
  have htrace : WordTrace (prefixWord ++ tailWord_3654265) baseStart_3654265 baseEnd_3654265 := by
    simpa [prefixWord, tailWord_3654265, baseEnd_3654265] using wordTrace_append hprefix tailTrace_3654265
  have hstable : (prefixWord ++ tailWord_3654265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3654265).length < 2 ^ (prefixWord ++ tailWord_3654265).sum := by decide
  have hdescent : baseEnd_3654265 < baseStart_3654265 := by decide
  rcases family_descends (prefixWord ++ tailWord_3654265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3654288 : List Nat := [2, 1, 1, 1, 1, 1, 3, 1, 3, 3, 6]
def baseStart_3654288 : Nat := 118140960795 + 3654288 * 2 ^ 59
def prefixEnd_3654288 : Nat := 4983230072969 + 3 ^ 40 * 3654288 * 2
def baseEnd_3654288 : Nat := 1876406193957303815094241

theorem tailTrace_3654288 : CollatzResearch.WordTrace tailWord_3654288 prefixEnd_3654288 1876406193957303815094241 := by
  unfold tailWord_3654288
  simp only [CollatzResearch.WordTrace]
  refine ⟨66641416492573076774077759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 88855221990097435698770345 66641416492573076774077759)
  ·
    refine ⟨99962124738859615161116639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66641416492573076774077759 99962124738859615161116639)
    ·
      refine ⟨149943187108289422741674959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 99962124738859615161116639 149943187108289422741674959)
      ·
        refine ⟨224914780662434134112512439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149943187108289422741674959 224914780662434134112512439)
        ·
          refine ⟨337372170993651201168768659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 224914780662434134112512439 337372170993651201168768659)
          ·
            refine ⟨506058256490476801753152989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 337372170993651201168768659 506058256490476801753152989)
            ·
              refine ⟨189771846183928800657432371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 506058256490476801753152989 189771846183928800657432371)
              ·
                refine ⟨284657769275893200986148557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 189771846183928800657432371 284657769275893200986148557)
                ·
                  refine ⟨106746663478459950369805709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 284657769275893200986148557 106746663478459950369805709)
                  ·
                    refine ⟨40029998804422481388677141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 106746663478459950369805709 40029998804422481388677141)
                    ·
                      refine ⟨1876406193957303815094241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 40029998804422481388677141 1876406193957303815094241)
                      ·
                        rfl

theorem cell23_3654288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 1, 3, 3, 6].length) (baseStart_3654288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3654288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3654288 prefixEnd_3654288 := by exact prefixLift 3654288
  have htrace : WordTrace (prefixWord ++ tailWord_3654288) baseStart_3654288 baseEnd_3654288 := by
    simpa [prefixWord, tailWord_3654288, baseEnd_3654288] using wordTrace_append hprefix tailTrace_3654288
  have hstable : (prefixWord ++ tailWord_3654288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3654288).length < 2 ^ (prefixWord ++ tailWord_3654288).sum := by decide
  have hdescent : baseEnd_3654288 < baseStart_3654288 := by decide
  rcases family_descends (prefixWord ++ tailWord_3654288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3654319 : List Nat := [1, 1, 2, 1, 2, 6, 1, 4, 1, 4]
def baseStart_3654319 : Nat := 118140960795 + 3654319 * 2 ^ 59
def prefixEnd_3654319 : Nat := 4983230072969 + 3 ^ 40 * 3654319 * 2
def baseEnd_3654319 : Nat := 625474037285864397935533

theorem tailTrace_3654319 : CollatzResearch.WordTrace tailWord_3654319 prefixEnd_3654319 625474037285864397935533 := by
  unfold tailWord_3654319
  simp only [CollatzResearch.WordTrace]
  refine ⟨133283963648033845842534011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 88855975765355897228356007 133283963648033845842534011)
  ·
    refine ⟨199925945472050768763801017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133283963648033845842534011 199925945472050768763801017)
    ·
      refine ⟨149944459104038076572850763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 199925945472050768763801017 149944459104038076572850763)
      ·
        refine ⟨224916688656057114859276145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 149944459104038076572850763 224916688656057114859276145)
        ·
          refine ⟨168687516492042836144457109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 224916688656057114859276145 168687516492042836144457109)
          ·
            refine ⟨7907227335564507944271427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 168687516492042836144457109 7907227335564507944271427)
            ·
              refine ⟨11860841003346761916407141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7907227335564507944271427 11860841003346761916407141)
              ·
                refine ⟨2223907688127517859326339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11860841003346761916407141 2223907688127517859326339)
                ·
                  refine ⟨3335861532191276788989509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2223907688127517859326339 3335861532191276788989509)
                  ·
                    refine ⟨625474037285864397935533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3335861532191276788989509 625474037285864397935533)
                    ·
                      rfl

theorem cell23_3654319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 6, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 6, 1, 4, 1, 4].length) (baseStart_3654319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3654319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3654319 prefixEnd_3654319 := by exact prefixLift 3654319
  have htrace : WordTrace (prefixWord ++ tailWord_3654319) baseStart_3654319 baseEnd_3654319 := by
    simpa [prefixWord, tailWord_3654319, baseEnd_3654319] using wordTrace_append hprefix tailTrace_3654319
  have hstable : (prefixWord ++ tailWord_3654319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3654319).length < 2 ^ (prefixWord ++ tailWord_3654319).sum := by decide
  have hdescent : baseEnd_3654319 < baseStart_3654319 := by decide
  rcases family_descends (prefixWord ++ tailWord_3654319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3654362 : List Nat := [3, 1, 1, 2, 2, 2, 3, 3, 1, 5]
def baseStart_3654362 : Nat := 118140960795 + 3654362 * 2 ^ 59
def prefixEnd_3654362 : Nat := 4983230072969 + 3 ^ 40 * 3654362 * 2
def baseEnd_3654362 : Nat := 625481397175245508522967

theorem tailTrace_3654362 : CollatzResearch.WordTrace tailWord_3654362 prefixEnd_3654362 625481397175245508522967 := by
  unfold tailWord_3654362
  simp only [CollatzResearch.WordTrace]
  refine ⟨33321382996719516046587335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 88857021324585376124232893 33321382996719516046587335)
  ·
    refine ⟨49982074495079274069881003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33321382996719516046587335 49982074495079274069881003)
    ·
      refine ⟨74973111742618911104821505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49982074495079274069881003 74973111742618911104821505)
      ·
        refine ⟨56229833806964183328616129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 74973111742618911104821505 56229833806964183328616129)
        ·
          refine ⟨42172375355223137496462097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56229833806964183328616129 42172375355223137496462097)
          ·
            refine ⟨31629281516417353122346573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42172375355223137496462097 31629281516417353122346573)
            ·
              refine ⟨11860980568656507420879965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31629281516417353122346573 11860980568656507420879965)
              ·
                refine ⟨4447867713246190282829987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11860980568656507420879965 4447867713246190282829987)
                ·
                  refine ⟨6671801569869285424244981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4447867713246190282829987 6671801569869285424244981)
                  ·
                    refine ⟨625481397175245508522967, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6671801569869285424244981 625481397175245508522967)
                    ·
                      rfl

theorem cell23_3654362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 3, 3, 1, 5].length) (baseStart_3654362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3654362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3654362 prefixEnd_3654362 := by exact prefixLift 3654362
  have htrace : WordTrace (prefixWord ++ tailWord_3654362) baseStart_3654362 baseEnd_3654362 := by
    simpa [prefixWord, tailWord_3654362, baseEnd_3654362] using wordTrace_append hprefix tailTrace_3654362
  have hstable : (prefixWord ++ tailWord_3654362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3654362).length < 2 ^ (prefixWord ++ tailWord_3654362).sum := by decide
  have hdescent : baseEnd_3654362 < baseStart_3654362 := by decide
  rcases family_descends (prefixWord ++ tailWord_3654362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
