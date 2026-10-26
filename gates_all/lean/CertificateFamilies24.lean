import FamilyDescent

open CollatzResearch

namespace CollatzCertificate24

/-- Family 1: exact representative trace from the pinned input. -/
theorem family_1_trace : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 4] 17293822687243665435 9616903407333709291 := by
  simp only [WordTrace]
  refine ⟨25940734030865498153, ?_, ?_⟩
  · exact (by decide : ExactOddStep 1 17293822687243665435 25940734030865498153)
  · refine ⟨19455550523149123615, ?_, ?_⟩
    · exact (by decide : ExactOddStep 2 25940734030865498153 19455550523149123615)
    · refine ⟨29183325784723685423, ?_, ?_⟩
      · exact (by decide : ExactOddStep 1 19455550523149123615 29183325784723685423)
      · refine ⟨43774988677085528135, ?_, ?_⟩
        · exact (by decide : ExactOddStep 1 29183325784723685423 43774988677085528135)
        · refine ⟨65662483015628292203, ?_, ?_⟩
          · exact (by decide : ExactOddStep 1 43774988677085528135 65662483015628292203)
          · refine ⟨98493724523442438305, ?_, ?_⟩
            · exact (by decide : ExactOddStep 1 65662483015628292203 98493724523442438305)
            · refine ⟨73870293392581828729, ?_, ?_⟩
              · exact (by decide : ExactOddStep 2 98493724523442438305 73870293392581828729)
              · refine ⟨55402720044436371547, ?_, ?_⟩
                · exact (by decide : ExactOddStep 2 73870293392581828729 55402720044436371547)
                · refine ⟨83104080066654557321, ?_, ?_⟩
                  · exact (by decide : ExactOddStep 1 55402720044436371547 83104080066654557321)
                  · refine ⟨62328060049990917991, ?_, ?_⟩
                    · exact (by decide : ExactOddStep 2 83104080066654557321 62328060049990917991)
                    · refine ⟨93492090074986376987, ?_, ?_⟩
                      · exact (by decide : ExactOddStep 1 62328060049990917991 93492090074986376987)
                      · refine ⟨140238135112479565481, ?_, ?_⟩
                        · exact (by decide : ExactOddStep 1 93492090074986376987 140238135112479565481)
                        · refine ⟨105178601334359674111, ?_, ?_⟩
                          · exact (by decide : ExactOddStep 2 140238135112479565481 105178601334359674111)
                          · refine ⟨157767902001539511167, ?_, ?_⟩
                            · exact (by decide : ExactOddStep 1 105178601334359674111 157767902001539511167)
                            · refine ⟨236651853002309266751, ?_, ?_⟩
                              · exact (by decide : ExactOddStep 1 157767902001539511167 236651853002309266751)
                              · refine ⟨354977779503463900127, ?_, ?_⟩
                                · exact (by decide : ExactOddStep 1 236651853002309266751 354977779503463900127)
                                · refine ⟨532466669255195850191, ?_, ?_⟩
                                  · exact (by decide : ExactOddStep 1 354977779503463900127 532466669255195850191)
                                  · refine ⟨798700003882793775287, ?_, ?_⟩
                                    · exact (by decide : ExactOddStep 1 532466669255195850191 798700003882793775287)
                                    · refine ⟨1198050005824190662931, ?_, ?_⟩
                                      · exact (by decide : ExactOddStep 1 798700003882793775287 1198050005824190662931)
                                      · refine ⟨1797075008736285994397, ?_, ?_⟩
                                        · exact (by decide : ExactOddStep 1 1198050005824190662931 1797075008736285994397)
                                        · refine ⟨673903128276107247899, ?_, ?_⟩
                                          · exact (by decide : ExactOddStep 3 1797075008736285994397 673903128276107247899)
                                          · refine ⟨1010854692414160871849, ?_, ?_⟩
                                            · exact (by decide : ExactOddStep 1 673903128276107247899 1010854692414160871849)
                                            · refine ⟨758141019310620653887, ?_, ?_⟩
                                              · exact (by decide : ExactOddStep 2 1010854692414160871849 758141019310620653887)
                                              · refine ⟨1137211528965930980831, ?_, ?_⟩
                                                · exact (by decide : ExactOddStep 1 758141019310620653887 1137211528965930980831)
                                                · refine ⟨1705817293448896471247, ?_, ?_⟩
                                                  · exact (by decide : ExactOddStep 1 1137211528965930980831 1705817293448896471247)
                                                  · refine ⟨2558725940173344706871, ?_, ?_⟩
                                                    · exact (by decide : ExactOddStep 1 1705817293448896471247 2558725940173344706871)
                                                    · refine ⟨3838088910260017060307, ?_, ?_⟩
                                                      · exact (by decide : ExactOddStep 1 2558725940173344706871 3838088910260017060307)
                                                      · refine ⟨5757133365390025590461, ?_, ?_⟩
                                                        · exact (by decide : ExactOddStep 1 3838088910260017060307 5757133365390025590461)
                                                        · refine ⟨2158925012021259596423, ?_, ?_⟩
                                                          · exact (by decide : ExactOddStep 3 5757133365390025590461 2158925012021259596423)
                                                          · refine ⟨3238387518031889394635, ?_, ?_⟩
                                                            · exact (by decide : ExactOddStep 1 2158925012021259596423 3238387518031889394635)
                                                            · refine ⟨4857581277047834091953, ?_, ?_⟩
                                                              · exact (by decide : ExactOddStep 1 3238387518031889394635 4857581277047834091953)
                                                              · refine ⟨3643185957785875568965, ?_, ?_⟩
                                                                · exact (by decide : ExactOddStep 2 4857581277047834091953 3643185957785875568965)
                                                                · refine ⟨683097367084851669181, ?_, ?_⟩
                                                                  · exact (by decide : ExactOddStep 4 3643185957785875568965 683097367084851669181)
                                                                  · refine ⟨256161512656819375943, ?_, ?_⟩
                                                                    · exact (by decide : ExactOddStep 3 683097367084851669181 256161512656819375943)
                                                                    · refine ⟨384242268985229063915, ?_, ?_⟩
                                                                      · exact (by decide : ExactOddStep 1 256161512656819375943 384242268985229063915)
                                                                      · refine ⟨576363403477843595873, ?_, ?_⟩
                                                                        · exact (by decide : ExactOddStep 1 384242268985229063915 576363403477843595873)
                                                                        · refine ⟨432272552608382696905, ?_, ?_⟩
                                                                          · exact (by decide : ExactOddStep 2 576363403477843595873 432272552608382696905)
                                                                          · refine ⟨324204414456287022679, ?_, ?_⟩
                                                                            · exact (by decide : ExactOddStep 2 432272552608382696905 324204414456287022679)
                                                                            · refine ⟨486306621684430534019, ?_, ?_⟩
                                                                              · exact (by decide : ExactOddStep 1 324204414456287022679 486306621684430534019)
                                                                              · refine ⟨729459932526645801029, ?_, ?_⟩
                                                                                · exact (by decide : ExactOddStep 1 486306621684430534019 729459932526645801029)
                                                                                · refine ⟨136773737348746087693, ?_, ?_⟩
                                                                                  · exact (by decide : ExactOddStep 4 729459932526645801029 136773737348746087693)
                                                                                  · refine ⟨51290151505779782885, ?_, ?_⟩
                                                                                    · exact (by decide : ExactOddStep 3 136773737348746087693 51290151505779782885)
                                                                                    · refine ⟨9616903407333709291, ?_, ?_⟩
                                                                                      · exact (by decide : ExactOddStep 4 51290151505779782885 9616903407333709291)
                                                                                      · rfl

/-- Every lift of family 1 descends after its exact accelerated word. -/
theorem family_1_all_lifts (q : Nat) :
    ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 4] (17293822687243665435 + q * 2 ^ 70) endpoint ∧
      endpoint < 17293822687243665435 + q * 2 ^ 70 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 4] family_1_trace (by decide) (by decide) (by decide) q

/-- Family 2: exact representative trace from the pinned input. -/
theorem family_2_trace : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 2] 10376293659602583579 8655213106018466869 := by
  simp only [WordTrace]
  refine ⟨15564440489403875369, ?_, ?_⟩
  · exact (by decide : ExactOddStep 1 10376293659602583579 15564440489403875369)
  · refine ⟨11673330367052906527, ?_, ?_⟩
    · exact (by decide : ExactOddStep 2 15564440489403875369 11673330367052906527)
    · refine ⟨17509995550579359791, ?_, ?_⟩
      · exact (by decide : ExactOddStep 1 11673330367052906527 17509995550579359791)
      · refine ⟨26264993325869039687, ?_, ?_⟩
        · exact (by decide : ExactOddStep 1 17509995550579359791 26264993325869039687)
        · refine ⟨39397489988803559531, ?_, ?_⟩
          · exact (by decide : ExactOddStep 1 26264993325869039687 39397489988803559531)
          · refine ⟨59096234983205339297, ?_, ?_⟩
            · exact (by decide : ExactOddStep 1 39397489988803559531 59096234983205339297)
            · refine ⟨44322176237404004473, ?_, ?_⟩
              · exact (by decide : ExactOddStep 2 59096234983205339297 44322176237404004473)
              · refine ⟨33241632178053003355, ?_, ?_⟩
                · exact (by decide : ExactOddStep 2 44322176237404004473 33241632178053003355)
                · refine ⟨49862448267079505033, ?_, ?_⟩
                  · exact (by decide : ExactOddStep 1 33241632178053003355 49862448267079505033)
                  · refine ⟨37396836200309628775, ?_, ?_⟩
                    · exact (by decide : ExactOddStep 2 49862448267079505033 37396836200309628775)
                    · refine ⟨56095254300464443163, ?_, ?_⟩
                      · exact (by decide : ExactOddStep 1 37396836200309628775 56095254300464443163)
                      · refine ⟨84142881450696664745, ?_, ?_⟩
                        · exact (by decide : ExactOddStep 1 56095254300464443163 84142881450696664745)
                        · refine ⟨63107161088022498559, ?_, ?_⟩
                          · exact (by decide : ExactOddStep 2 84142881450696664745 63107161088022498559)
                          · refine ⟨94660741632033747839, ?_, ?_⟩
                            · exact (by decide : ExactOddStep 1 63107161088022498559 94660741632033747839)
                            · refine ⟨141991112448050621759, ?_, ?_⟩
                              · exact (by decide : ExactOddStep 1 94660741632033747839 141991112448050621759)
                              · refine ⟨212986668672075932639, ?_, ?_⟩
                                · exact (by decide : ExactOddStep 1 141991112448050621759 212986668672075932639)
                                · refine ⟨319480003008113898959, ?_, ?_⟩
                                  · exact (by decide : ExactOddStep 1 212986668672075932639 319480003008113898959)
                                  · refine ⟨479220004512170848439, ?_, ?_⟩
                                    · exact (by decide : ExactOddStep 1 319480003008113898959 479220004512170848439)
                                    · refine ⟨718830006768256272659, ?_, ?_⟩
                                      · exact (by decide : ExactOddStep 1 479220004512170848439 718830006768256272659)
                                      · refine ⟨1078245010152384408989, ?_, ?_⟩
                                        · exact (by decide : ExactOddStep 1 718830006768256272659 1078245010152384408989)
                                        · refine ⟨404341878807144153371, ?_, ?_⟩
                                          · exact (by decide : ExactOddStep 3 1078245010152384408989 404341878807144153371)
                                          · refine ⟨606512818210716230057, ?_, ?_⟩
                                            · exact (by decide : ExactOddStep 1 404341878807144153371 606512818210716230057)
                                            · refine ⟨454884613658037172543, ?_, ?_⟩
                                              · exact (by decide : ExactOddStep 2 606512818210716230057 454884613658037172543)
                                              · refine ⟨682326920487055758815, ?_, ?_⟩
                                                · exact (by decide : ExactOddStep 1 454884613658037172543 682326920487055758815)
                                                · refine ⟨1023490380730583638223, ?_, ?_⟩
                                                  · exact (by decide : ExactOddStep 1 682326920487055758815 1023490380730583638223)
                                                  · refine ⟨1535235571095875457335, ?_, ?_⟩
                                                    · exact (by decide : ExactOddStep 1 1023490380730583638223 1535235571095875457335)
                                                    · refine ⟨2302853356643813186003, ?_, ?_⟩
                                                      · exact (by decide : ExactOddStep 1 1535235571095875457335 2302853356643813186003)
                                                      · refine ⟨3454280034965719779005, ?_, ?_⟩
                                                        · exact (by decide : ExactOddStep 1 2302853356643813186003 3454280034965719779005)
                                                        · refine ⟨1295355013112144917127, ?_, ?_⟩
                                                          · exact (by decide : ExactOddStep 3 3454280034965719779005 1295355013112144917127)
                                                          · refine ⟨1943032519668217375691, ?_, ?_⟩
                                                            · exact (by decide : ExactOddStep 1 1295355013112144917127 1943032519668217375691)
                                                            · refine ⟨2914548779502326063537, ?_, ?_⟩
                                                              · exact (by decide : ExactOddStep 1 1943032519668217375691 2914548779502326063537)
                                                              · refine ⟨2185911584626744547653, ?_, ?_⟩
                                                                · exact (by decide : ExactOddStep 2 2914548779502326063537 2185911584626744547653)
                                                                · refine ⟨409858422117514602685, ?_, ?_⟩
                                                                  · exact (by decide : ExactOddStep 4 2185911584626744547653 409858422117514602685)
                                                                  · refine ⟨153696908294067976007, ?_, ?_⟩
                                                                    · exact (by decide : ExactOddStep 3 409858422117514602685 153696908294067976007)
                                                                    · refine ⟨230545362441101964011, ?_, ?_⟩
                                                                      · exact (by decide : ExactOddStep 1 153696908294067976007 230545362441101964011)
                                                                      · refine ⟨345818043661652946017, ?_, ?_⟩
                                                                        · exact (by decide : ExactOddStep 1 230545362441101964011 345818043661652946017)
                                                                        · refine ⟨259363532746239709513, ?_, ?_⟩
                                                                          · exact (by decide : ExactOddStep 2 345818043661652946017 259363532746239709513)
                                                                          · refine ⟨194522649559679782135, ?_, ?_⟩
                                                                            · exact (by decide : ExactOddStep 2 259363532746239709513 194522649559679782135)
                                                                            · refine ⟨291783974339519673203, ?_, ?_⟩
                                                                              · exact (by decide : ExactOddStep 1 194522649559679782135 291783974339519673203)
                                                                              · refine ⟨437675961509279509805, ?_, ?_⟩
                                                                                · exact (by decide : ExactOddStep 1 291783974339519673203 437675961509279509805)
                                                                                · refine ⟨164128485565979816177, ?_, ?_⟩
                                                                                  · exact (by decide : ExactOddStep 3 437675961509279509805 164128485565979816177)
                                                                                  · refine ⟨123096364174484862133, ?_, ?_⟩
                                                                                    · exact (by decide : ExactOddStep 2 164128485565979816177 123096364174484862133)
                                                                                    · refine ⟨11540284141357955825, ?_, ?_⟩
                                                                                      · exact (by decide : ExactOddStep 5 123096364174484862133 11540284141357955825)
                                                                                      · refine ⟨8655213106018466869, ?_, ?_⟩
                                                                                        · exact (by decide : ExactOddStep 2 11540284141357955825 8655213106018466869)
                                                                                        · rfl

/-- Every lift of family 2 descends after its exact accelerated word. -/
theorem family_2_all_lifts (q : Nat) :
    ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 2] (10376293659602583579 + q * 2 ^ 71) endpoint ∧
      endpoint < 10376293659602583579 + q * 2 ^ 71 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 2] family_2_trace (by decide) (by decide) (by decide) q

/-- Family 3: exact representative trace from the pinned input. -/
theorem family_3_trace : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 8] 12682136668816277531 587699654130324031 := by
  simp only [WordTrace]
  refine ⟨19023205003224416297, ?_, ?_⟩
  · exact (by decide : ExactOddStep 1 12682136668816277531 19023205003224416297)
  · refine ⟨14267403752418312223, ?_, ?_⟩
    · exact (by decide : ExactOddStep 2 19023205003224416297 14267403752418312223)
    · refine ⟨21401105628627468335, ?_, ?_⟩
      · exact (by decide : ExactOddStep 1 14267403752418312223 21401105628627468335)
      · refine ⟨32101658442941202503, ?_, ?_⟩
        · exact (by decide : ExactOddStep 1 21401105628627468335 32101658442941202503)
        · refine ⟨48152487664411803755, ?_, ?_⟩
          · exact (by decide : ExactOddStep 1 32101658442941202503 48152487664411803755)
          · refine ⟨72228731496617705633, ?_, ?_⟩
            · exact (by decide : ExactOddStep 1 48152487664411803755 72228731496617705633)
            · refine ⟨54171548622463279225, ?_, ?_⟩
              · exact (by decide : ExactOddStep 2 72228731496617705633 54171548622463279225)
              · refine ⟨40628661466847459419, ?_, ?_⟩
                · exact (by decide : ExactOddStep 2 54171548622463279225 40628661466847459419)
                · refine ⟨60942992200271189129, ?_, ?_⟩
                  · exact (by decide : ExactOddStep 1 40628661466847459419 60942992200271189129)
                  · refine ⟨45707244150203391847, ?_, ?_⟩
                    · exact (by decide : ExactOddStep 2 60942992200271189129 45707244150203391847)
                    · refine ⟨68560866225305087771, ?_, ?_⟩
                      · exact (by decide : ExactOddStep 1 45707244150203391847 68560866225305087771)
                      · refine ⟨102841299337957631657, ?_, ?_⟩
                        · exact (by decide : ExactOddStep 1 68560866225305087771 102841299337957631657)
                        · refine ⟨77130974503468223743, ?_, ?_⟩
                          · exact (by decide : ExactOddStep 2 102841299337957631657 77130974503468223743)
                          · refine ⟨115696461755202335615, ?_, ?_⟩
                            · exact (by decide : ExactOddStep 1 77130974503468223743 115696461755202335615)
                            · refine ⟨173544692632803503423, ?_, ?_⟩
                              · exact (by decide : ExactOddStep 1 115696461755202335615 173544692632803503423)
                              · refine ⟨260317038949205255135, ?_, ?_⟩
                                · exact (by decide : ExactOddStep 1 173544692632803503423 260317038949205255135)
                                · refine ⟨390475558423807882703, ?_, ?_⟩
                                  · exact (by decide : ExactOddStep 1 260317038949205255135 390475558423807882703)
                                  · refine ⟨585713337635711824055, ?_, ?_⟩
                                    · exact (by decide : ExactOddStep 1 390475558423807882703 585713337635711824055)
                                    · refine ⟨878570006453567736083, ?_, ?_⟩
                                      · exact (by decide : ExactOddStep 1 585713337635711824055 878570006453567736083)
                                      · refine ⟨1317855009680351604125, ?_, ?_⟩
                                        · exact (by decide : ExactOddStep 1 878570006453567736083 1317855009680351604125)
                                        · refine ⟨494195628630131851547, ?_, ?_⟩
                                          · exact (by decide : ExactOddStep 3 1317855009680351604125 494195628630131851547)
                                          · refine ⟨741293442945197777321, ?_, ?_⟩
                                            · exact (by decide : ExactOddStep 1 494195628630131851547 741293442945197777321)
                                            · refine ⟨555970082208898332991, ?_, ?_⟩
                                              · exact (by decide : ExactOddStep 2 741293442945197777321 555970082208898332991)
                                              · refine ⟨833955123313347499487, ?_, ?_⟩
                                                · exact (by decide : ExactOddStep 1 555970082208898332991 833955123313347499487)
                                                · refine ⟨1250932684970021249231, ?_, ?_⟩
                                                  · exact (by decide : ExactOddStep 1 833955123313347499487 1250932684970021249231)
                                                  · refine ⟨1876399027455031873847, ?_, ?_⟩
                                                    · exact (by decide : ExactOddStep 1 1250932684970021249231 1876399027455031873847)
                                                    · refine ⟨2814598541182547810771, ?_, ?_⟩
                                                      · exact (by decide : ExactOddStep 1 1876399027455031873847 2814598541182547810771)
                                                      · refine ⟨4221897811773821716157, ?_, ?_⟩
                                                        · exact (by decide : ExactOddStep 1 2814598541182547810771 4221897811773821716157)
                                                        · refine ⟨1583211679415183143559, ?_, ?_⟩
                                                          · exact (by decide : ExactOddStep 3 4221897811773821716157 1583211679415183143559)
                                                          · refine ⟨2374817519122774715339, ?_, ?_⟩
                                                            · exact (by decide : ExactOddStep 1 1583211679415183143559 2374817519122774715339)
                                                            · refine ⟨3562226278684162073009, ?_, ?_⟩
                                                              · exact (by decide : ExactOddStep 1 2374817519122774715339 3562226278684162073009)
                                                              · refine ⟨2671669709013121554757, ?_, ?_⟩
                                                                · exact (by decide : ExactOddStep 2 3562226278684162073009 2671669709013121554757)
                                                                · refine ⟨500938070439960291517, ?_, ?_⟩
                                                                  · exact (by decide : ExactOddStep 4 2671669709013121554757 500938070439960291517)
                                                                  · refine ⟨187851776414985109319, ?_, ?_⟩
                                                                    · exact (by decide : ExactOddStep 3 500938070439960291517 187851776414985109319)
                                                                    · refine ⟨281777664622477663979, ?_, ?_⟩
                                                                      · exact (by decide : ExactOddStep 1 187851776414985109319 281777664622477663979)
                                                                      · refine ⟨422666496933716495969, ?_, ?_⟩
                                                                        · exact (by decide : ExactOddStep 1 281777664622477663979 422666496933716495969)
                                                                        · refine ⟨316999872700287371977, ?_, ?_⟩
                                                                          · exact (by decide : ExactOddStep 2 422666496933716495969 316999872700287371977)
                                                                          · refine ⟨237749904525215528983, ?_, ?_⟩
                                                                            · exact (by decide : ExactOddStep 2 316999872700287371977 237749904525215528983)
                                                                            · refine ⟨356624856787823293475, ?_, ?_⟩
                                                                              · exact (by decide : ExactOddStep 1 237749904525215528983 356624856787823293475)
                                                                              · refine ⟨534937285181734940213, ?_, ?_⟩
                                                                                · exact (by decide : ExactOddStep 1 356624856787823293475 534937285181734940213)
                                                                                · refine ⟨50150370485787650645, ?_, ?_⟩
                                                                                  · exact (by decide : ExactOddStep 5 534937285181734940213 50150370485787650645)
                                                                                  · refine ⟨587699654130324031, ?_, ?_⟩
                                                                                    · exact (by decide : ExactOddStep 8 50150370485787650645 587699654130324031)
                                                                                    · rfl

/-- Every lift of family 3 descends after its exact accelerated word. -/
theorem family_3_all_lifts (q : Nat) :
    ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 8] (12682136668816277531 + q * 2 ^ 72) endpoint ∧
      endpoint < 12682136668816277531 + q * 2 ^ 72 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 8] family_3_trace (by decide) (by decide) (by decide) q

/-- Family 4: exact representative trace from the pinned input. -/
theorem family_4_trace : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 3] 3458764631961501723 3245704988665916027 := by
  simp only [WordTrace]
  refine ⟨5188146947942252585, ?_, ?_⟩
  · exact (by decide : ExactOddStep 1 3458764631961501723 5188146947942252585)
  · refine ⟨3891110210956689439, ?_, ?_⟩
    · exact (by decide : ExactOddStep 2 5188146947942252585 3891110210956689439)
    · refine ⟨5836665316435034159, ?_, ?_⟩
      · exact (by decide : ExactOddStep 1 3891110210956689439 5836665316435034159)
      · refine ⟨8754997974652551239, ?_, ?_⟩
        · exact (by decide : ExactOddStep 1 5836665316435034159 8754997974652551239)
        · refine ⟨13132496961978826859, ?_, ?_⟩
          · exact (by decide : ExactOddStep 1 8754997974652551239 13132496961978826859)
          · refine ⟨19698745442968240289, ?_, ?_⟩
            · exact (by decide : ExactOddStep 1 13132496961978826859 19698745442968240289)
            · refine ⟨14774059082226180217, ?_, ?_⟩
              · exact (by decide : ExactOddStep 2 19698745442968240289 14774059082226180217)
              · refine ⟨11080544311669635163, ?_, ?_⟩
                · exact (by decide : ExactOddStep 2 14774059082226180217 11080544311669635163)
                · refine ⟨16620816467504452745, ?_, ?_⟩
                  · exact (by decide : ExactOddStep 1 11080544311669635163 16620816467504452745)
                  · refine ⟨12465612350628339559, ?_, ?_⟩
                    · exact (by decide : ExactOddStep 2 16620816467504452745 12465612350628339559)
                    · refine ⟨18698418525942509339, ?_, ?_⟩
                      · exact (by decide : ExactOddStep 1 12465612350628339559 18698418525942509339)
                      · refine ⟨28047627788913764009, ?_, ?_⟩
                        · exact (by decide : ExactOddStep 1 18698418525942509339 28047627788913764009)
                        · refine ⟨21035720841685323007, ?_, ?_⟩
                          · exact (by decide : ExactOddStep 2 28047627788913764009 21035720841685323007)
                          · refine ⟨31553581262527984511, ?_, ?_⟩
                            · exact (by decide : ExactOddStep 1 21035720841685323007 31553581262527984511)
                            · refine ⟨47330371893791976767, ?_, ?_⟩
                              · exact (by decide : ExactOddStep 1 31553581262527984511 47330371893791976767)
                              · refine ⟨70995557840687965151, ?_, ?_⟩
                                · exact (by decide : ExactOddStep 1 47330371893791976767 70995557840687965151)
                                · refine ⟨106493336761031947727, ?_, ?_⟩
                                  · exact (by decide : ExactOddStep 1 70995557840687965151 106493336761031947727)
                                  · refine ⟨159740005141547921591, ?_, ?_⟩
                                    · exact (by decide : ExactOddStep 1 106493336761031947727 159740005141547921591)
                                    · refine ⟨239610007712321882387, ?_, ?_⟩
                                      · exact (by decide : ExactOddStep 1 159740005141547921591 239610007712321882387)
                                      · refine ⟨359415011568482823581, ?_, ?_⟩
                                        · exact (by decide : ExactOddStep 1 239610007712321882387 359415011568482823581)
                                        · refine ⟨134780629338181058843, ?_, ?_⟩
                                          · exact (by decide : ExactOddStep 3 359415011568482823581 134780629338181058843)
                                          · refine ⟨202170944007271588265, ?_, ?_⟩
                                            · exact (by decide : ExactOddStep 1 134780629338181058843 202170944007271588265)
                                            · refine ⟨151628208005453691199, ?_, ?_⟩
                                              · exact (by decide : ExactOddStep 2 202170944007271588265 151628208005453691199)
                                              · refine ⟨227442312008180536799, ?_, ?_⟩
                                                · exact (by decide : ExactOddStep 1 151628208005453691199 227442312008180536799)
                                                · refine ⟨341163468012270805199, ?_, ?_⟩
                                                  · exact (by decide : ExactOddStep 1 227442312008180536799 341163468012270805199)
                                                  · refine ⟨511745202018406207799, ?_, ?_⟩
                                                    · exact (by decide : ExactOddStep 1 341163468012270805199 511745202018406207799)
                                                    · refine ⟨767617803027609311699, ?_, ?_⟩
                                                      · exact (by decide : ExactOddStep 1 511745202018406207799 767617803027609311699)
                                                      · refine ⟨1151426704541413967549, ?_, ?_⟩
                                                        · exact (by decide : ExactOddStep 1 767617803027609311699 1151426704541413967549)
                                                        · refine ⟨431785014203030237831, ?_, ?_⟩
                                                          · exact (by decide : ExactOddStep 3 1151426704541413967549 431785014203030237831)
                                                          · refine ⟨647677521304545356747, ?_, ?_⟩
                                                            · exact (by decide : ExactOddStep 1 431785014203030237831 647677521304545356747)
                                                            · refine ⟨971516281956818035121, ?_, ?_⟩
                                                              · exact (by decide : ExactOddStep 1 647677521304545356747 971516281956818035121)
                                                              · refine ⟨728637211467613526341, ?_, ?_⟩
                                                                · exact (by decide : ExactOddStep 2 971516281956818035121 728637211467613526341)
                                                                · refine ⟨136619477150177536189, ?_, ?_⟩
                                                                  · exact (by decide : ExactOddStep 4 728637211467613526341 136619477150177536189)
                                                                  · refine ⟨51232303931316576071, ?_, ?_⟩
                                                                    · exact (by decide : ExactOddStep 3 136619477150177536189 51232303931316576071)
                                                                    · refine ⟨76848455896974864107, ?_, ?_⟩
                                                                      · exact (by decide : ExactOddStep 1 51232303931316576071 76848455896974864107)
                                                                      · refine ⟨115272683845462296161, ?_, ?_⟩
                                                                        · exact (by decide : ExactOddStep 1 76848455896974864107 115272683845462296161)
                                                                        · refine ⟨86454512884096722121, ?_, ?_⟩
                                                                          · exact (by decide : ExactOddStep 2 115272683845462296161 86454512884096722121)
                                                                          · refine ⟨64840884663072541591, ?_, ?_⟩
                                                                            · exact (by decide : ExactOddStep 2 86454512884096722121 64840884663072541591)
                                                                            · refine ⟨97261326994608812387, ?_, ?_⟩
                                                                              · exact (by decide : ExactOddStep 1 64840884663072541591 97261326994608812387)
                                                                              · refine ⟨145891990491913218581, ?_, ?_⟩
                                                                                · exact (by decide : ExactOddStep 1 97261326994608812387 145891990491913218581)
                                                                                · refine ⟨6838687054308432121, ?_, ?_⟩
                                                                                  · exact (by decide : ExactOddStep 6 145891990491913218581 6838687054308432121)
                                                                                  · refine ⟨5129015290731324091, ?_, ?_⟩
                                                                                    · exact (by decide : ExactOddStep 2 6838687054308432121 5129015290731324091)
                                                                                    · refine ⟨7693522936096986137, ?_, ?_⟩
                                                                                      · exact (by decide : ExactOddStep 1 5129015290731324091 7693522936096986137)
                                                                                      · refine ⟨5770142202072739603, ?_, ?_⟩
                                                                                        · exact (by decide : ExactOddStep 2 7693522936096986137 5770142202072739603)
                                                                                        · refine ⟨8655213303109109405, ?_, ?_⟩
                                                                                          · exact (by decide : ExactOddStep 1 5770142202072739603 8655213303109109405)
                                                                                          · refine ⟨3245704988665916027, ?_, ?_⟩
                                                                                            · exact (by decide : ExactOddStep 3 8655213303109109405 3245704988665916027)
                                                                                            · rfl

/-- Every lift of family 4 descends after its exact accelerated word. -/
theorem family_4_all_lifts (q : Nat) :
    ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 3] (3458764631961501723 + q * 2 ^ 74) endpoint ∧
      endpoint < 3458764631961501723 + q * 2 ^ 74 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 3] family_4_trace (by decide) (by decide) (by decide) q

/-- Family 5: exact representative trace from the pinned input. -/
theorem family_5_trace : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 8] 1152921622747807771 60105652044312757 := by
  simp only [WordTrace]
  refine ⟨1729382434121711657, ?_, ?_⟩
  · exact (by decide : ExactOddStep 1 1152921622747807771 1729382434121711657)
  · refine ⟨1297036825591283743, ?_, ?_⟩
    · exact (by decide : ExactOddStep 2 1729382434121711657 1297036825591283743)
    · refine ⟨1945555238386925615, ?_, ?_⟩
      · exact (by decide : ExactOddStep 1 1297036825591283743 1945555238386925615)
      · refine ⟨2918332857580388423, ?_, ?_⟩
        · exact (by decide : ExactOddStep 1 1945555238386925615 2918332857580388423)
        · refine ⟨4377499286370582635, ?_, ?_⟩
          · exact (by decide : ExactOddStep 1 2918332857580388423 4377499286370582635)
          · refine ⟨6566248929555873953, ?_, ?_⟩
            · exact (by decide : ExactOddStep 1 4377499286370582635 6566248929555873953)
            · refine ⟨4924686697166905465, ?_, ?_⟩
              · exact (by decide : ExactOddStep 2 6566248929555873953 4924686697166905465)
              · refine ⟨3693515022875179099, ?_, ?_⟩
                · exact (by decide : ExactOddStep 2 4924686697166905465 3693515022875179099)
                · refine ⟨5540272534312768649, ?_, ?_⟩
                  · exact (by decide : ExactOddStep 1 3693515022875179099 5540272534312768649)
                  · refine ⟨4155204400734576487, ?_, ?_⟩
                    · exact (by decide : ExactOddStep 2 5540272534312768649 4155204400734576487)
                    · refine ⟨6232806601101864731, ?_, ?_⟩
                      · exact (by decide : ExactOddStep 1 4155204400734576487 6232806601101864731)
                      · refine ⟨9349209901652797097, ?_, ?_⟩
                        · exact (by decide : ExactOddStep 1 6232806601101864731 9349209901652797097)
                        · refine ⟨7011907426239597823, ?_, ?_⟩
                          · exact (by decide : ExactOddStep 2 9349209901652797097 7011907426239597823)
                          · refine ⟨10517861139359396735, ?_, ?_⟩
                            · exact (by decide : ExactOddStep 1 7011907426239597823 10517861139359396735)
                            · refine ⟨15776791709039095103, ?_, ?_⟩
                              · exact (by decide : ExactOddStep 1 10517861139359396735 15776791709039095103)
                              · refine ⟨23665187563558642655, ?_, ?_⟩
                                · exact (by decide : ExactOddStep 1 15776791709039095103 23665187563558642655)
                                · refine ⟨35497781345337963983, ?_, ?_⟩
                                  · exact (by decide : ExactOddStep 1 23665187563558642655 35497781345337963983)
                                  · refine ⟨53246672018006945975, ?_, ?_⟩
                                    · exact (by decide : ExactOddStep 1 35497781345337963983 53246672018006945975)
                                    · refine ⟨79870008027010418963, ?_, ?_⟩
                                      · exact (by decide : ExactOddStep 1 53246672018006945975 79870008027010418963)
                                      · refine ⟨119805012040515628445, ?_, ?_⟩
                                        · exact (by decide : ExactOddStep 1 79870008027010418963 119805012040515628445)
                                        · refine ⟨44926879515193360667, ?_, ?_⟩
                                          · exact (by decide : ExactOddStep 3 119805012040515628445 44926879515193360667)
                                          · refine ⟨67390319272790041001, ?_, ?_⟩
                                            · exact (by decide : ExactOddStep 1 44926879515193360667 67390319272790041001)
                                            · refine ⟨50542739454592530751, ?_, ?_⟩
                                              · exact (by decide : ExactOddStep 2 67390319272790041001 50542739454592530751)
                                              · refine ⟨75814109181888796127, ?_, ?_⟩
                                                · exact (by decide : ExactOddStep 1 50542739454592530751 75814109181888796127)
                                                · refine ⟨113721163772833194191, ?_, ?_⟩
                                                  · exact (by decide : ExactOddStep 1 75814109181888796127 113721163772833194191)
                                                  · refine ⟨170581745659249791287, ?_, ?_⟩
                                                    · exact (by decide : ExactOddStep 1 113721163772833194191 170581745659249791287)
                                                    · refine ⟨255872618488874686931, ?_, ?_⟩
                                                      · exact (by decide : ExactOddStep 1 170581745659249791287 255872618488874686931)
                                                      · refine ⟨383808927733312030397, ?_, ?_⟩
                                                        · exact (by decide : ExactOddStep 1 255872618488874686931 383808927733312030397)
                                                        · refine ⟨143928347899992011399, ?_, ?_⟩
                                                          · exact (by decide : ExactOddStep 3 383808927733312030397 143928347899992011399)
                                                          · refine ⟨215892521849988017099, ?_, ?_⟩
                                                            · exact (by decide : ExactOddStep 1 143928347899992011399 215892521849988017099)
                                                            · refine ⟨323838782774982025649, ?_, ?_⟩
                                                              · exact (by decide : ExactOddStep 1 215892521849988017099 323838782774982025649)
                                                              · refine ⟨242879087081236519237, ?_, ?_⟩
                                                                · exact (by decide : ExactOddStep 2 323838782774982025649 242879087081236519237)
                                                                · refine ⟨45539828827731847357, ?_, ?_⟩
                                                                  · exact (by decide : ExactOddStep 4 242879087081236519237 45539828827731847357)
                                                                  · refine ⟨17077435810399442759, ?_, ?_⟩
                                                                    · exact (by decide : ExactOddStep 3 45539828827731847357 17077435810399442759)
                                                                    · refine ⟨25616153715599164139, ?_, ?_⟩
                                                                      · exact (by decide : ExactOddStep 1 17077435810399442759 25616153715599164139)
                                                                      · refine ⟨38424230573398746209, ?_, ?_⟩
                                                                        · exact (by decide : ExactOddStep 1 25616153715599164139 38424230573398746209)
                                                                        · refine ⟨28818172930049059657, ?_, ?_⟩
                                                                          · exact (by decide : ExactOddStep 2 38424230573398746209 28818172930049059657)
                                                                          · refine ⟨21613629697536794743, ?_, ?_⟩
                                                                            · exact (by decide : ExactOddStep 2 28818172930049059657 21613629697536794743)
                                                                            · refine ⟨32420444546305192115, ?_, ?_⟩
                                                                              · exact (by decide : ExactOddStep 1 21613629697536794743 32420444546305192115)
                                                                              · refine ⟨48630666819457788173, ?_, ?_⟩
                                                                                · exact (by decide : ExactOddStep 1 32420444546305192115 48630666819457788173)
                                                                                · refine ⟨18236500057296670565, ?_, ?_⟩
                                                                                  · exact (by decide : ExactOddStep 3 48630666819457788173 18236500057296670565)
                                                                                  · refine ⟨3419343760743125731, ?_, ?_⟩
                                                                                    · exact (by decide : ExactOddStep 4 18236500057296670565 3419343760743125731)
                                                                                    · refine ⟨5129015641114688597, ?_, ?_⟩
                                                                                      · exact (by decide : ExactOddStep 1 3419343760743125731 5129015641114688597)
                                                                                      · refine ⟨60105652044312757, ?_, ?_⟩
                                                                                        · exact (by decide : ExactOddStep 8 5129015641114688597 60105652044312757)
                                                                                        · rfl

/-- Every lift of family 5 descends after its exact accelerated word. -/
theorem family_5_all_lifts (q : Nat) :
    ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 8] (1152921622747807771 + q * 2 ^ 75) endpoint ∧
      endpoint < 1152921622747807771 + q * 2 ^ 75 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 8] family_5_trace (by decide) (by decide) (by decide) q

/-- Family 6: exact representative trace from the pinned input. -/
theorem family_6_trace : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 5] 11529215164209430555 2704754092551229607 := by
  simp only [WordTrace]
  refine ⟨17293822746314145833, ?_, ?_⟩
  · exact (by decide : ExactOddStep 1 11529215164209430555 17293822746314145833)
  · refine ⟨12970367059735609375, ?_, ?_⟩
    · exact (by decide : ExactOddStep 2 17293822746314145833 12970367059735609375)
    · refine ⟨19455550589603414063, ?_, ?_⟩
      · exact (by decide : ExactOddStep 1 12970367059735609375 19455550589603414063)
      · refine ⟨29183325884405121095, ?_, ?_⟩
        · exact (by decide : ExactOddStep 1 19455550589603414063 29183325884405121095)
        · refine ⟨43774988826607681643, ?_, ?_⟩
          · exact (by decide : ExactOddStep 1 29183325884405121095 43774988826607681643)
          · refine ⟨65662483239911522465, ?_, ?_⟩
            · exact (by decide : ExactOddStep 1 43774988826607681643 65662483239911522465)
            · refine ⟨49246862429933641849, ?_, ?_⟩
              · exact (by decide : ExactOddStep 2 65662483239911522465 49246862429933641849)
              · refine ⟨36935146822450231387, ?_, ?_⟩
                · exact (by decide : ExactOddStep 2 49246862429933641849 36935146822450231387)
                · refine ⟨55402720233675347081, ?_, ?_⟩
                  · exact (by decide : ExactOddStep 1 36935146822450231387 55402720233675347081)
                  · refine ⟨41552040175256510311, ?_, ?_⟩
                    · exact (by decide : ExactOddStep 2 55402720233675347081 41552040175256510311)
                    · refine ⟨62328060262884765467, ?_, ?_⟩
                      · exact (by decide : ExactOddStep 1 41552040175256510311 62328060262884765467)
                      · refine ⟨93492090394327148201, ?_, ?_⟩
                        · exact (by decide : ExactOddStep 1 62328060262884765467 93492090394327148201)
                        · refine ⟨70119067795745361151, ?_, ?_⟩
                          · exact (by decide : ExactOddStep 2 93492090394327148201 70119067795745361151)
                          · refine ⟨105178601693618041727, ?_, ?_⟩
                            · exact (by decide : ExactOddStep 1 70119067795745361151 105178601693618041727)
                            · refine ⟨157767902540427062591, ?_, ?_⟩
                              · exact (by decide : ExactOddStep 1 105178601693618041727 157767902540427062591)
                              · refine ⟨236651853810640593887, ?_, ?_⟩
                                · exact (by decide : ExactOddStep 1 157767902540427062591 236651853810640593887)
                                · refine ⟨354977780715960890831, ?_, ?_⟩
                                  · exact (by decide : ExactOddStep 1 236651853810640593887 354977780715960890831)
                                  · refine ⟨532466671073941336247, ?_, ?_⟩
                                    · exact (by decide : ExactOddStep 1 354977780715960890831 532466671073941336247)
                                    · refine ⟨798700006610912004371, ?_, ?_⟩
                                      · exact (by decide : ExactOddStep 1 532466671073941336247 798700006610912004371)
                                      · refine ⟨1198050009916368006557, ?_, ?_⟩
                                        · exact (by decide : ExactOddStep 1 798700006610912004371 1198050009916368006557)
                                        · refine ⟨449268753718638002459, ?_, ?_⟩
                                          · exact (by decide : ExactOddStep 3 1198050009916368006557 449268753718638002459)
                                          · refine ⟨673903130577957003689, ?_, ?_⟩
                                            · exact (by decide : ExactOddStep 1 449268753718638002459 673903130577957003689)
                                            · refine ⟨505427347933467752767, ?_, ?_⟩
                                              · exact (by decide : ExactOddStep 2 673903130577957003689 505427347933467752767)
                                              · refine ⟨758141021900201629151, ?_, ?_⟩
                                                · exact (by decide : ExactOddStep 1 505427347933467752767 758141021900201629151)
                                                · refine ⟨1137211532850302443727, ?_, ?_⟩
                                                  · exact (by decide : ExactOddStep 1 758141021900201629151 1137211532850302443727)
                                                  · refine ⟨1705817299275453665591, ?_, ?_⟩
                                                    · exact (by decide : ExactOddStep 1 1137211532850302443727 1705817299275453665591)
                                                    · refine ⟨2558725948913180498387, ?_, ?_⟩
                                                      · exact (by decide : ExactOddStep 1 1705817299275453665591 2558725948913180498387)
                                                      · refine ⟨3838088923369770747581, ?_, ?_⟩
                                                        · exact (by decide : ExactOddStep 1 2558725948913180498387 3838088923369770747581)
                                                        · refine ⟨1439283346263664030343, ?_, ?_⟩
                                                          · exact (by decide : ExactOddStep 3 3838088923369770747581 1439283346263664030343)
                                                          · refine ⟨2158925019395496045515, ?_, ?_⟩
                                                            · exact (by decide : ExactOddStep 1 1439283346263664030343 2158925019395496045515)
                                                            · refine ⟨3238387529093244068273, ?_, ?_⟩
                                                              · exact (by decide : ExactOddStep 1 2158925019395496045515 3238387529093244068273)
                                                              · refine ⟨2428790646819933051205, ?_, ?_⟩
                                                                · exact (by decide : ExactOddStep 2 3238387529093244068273 2428790646819933051205)
                                                                · refine ⟨455398246278737447101, ?_, ?_⟩
                                                                  · exact (by decide : ExactOddStep 4 2428790646819933051205 455398246278737447101)
                                                                  · refine ⟨170774342354526542663, ?_, ?_⟩
                                                                    · exact (by decide : ExactOddStep 3 455398246278737447101 170774342354526542663)
                                                                    · refine ⟨256161513531789813995, ?_, ?_⟩
                                                                      · exact (by decide : ExactOddStep 1 170774342354526542663 256161513531789813995)
                                                                      · refine ⟨384242270297684720993, ?_, ?_⟩
                                                                        · exact (by decide : ExactOddStep 1 256161513531789813995 384242270297684720993)
                                                                        · refine ⟨288181702723263540745, ?_, ?_⟩
                                                                          · exact (by decide : ExactOddStep 2 384242270297684720993 288181702723263540745)
                                                                          · refine ⟨216136277042447655559, ?_, ?_⟩
                                                                            · exact (by decide : ExactOddStep 2 288181702723263540745 216136277042447655559)
                                                                            · refine ⟨324204415563671483339, ?_, ?_⟩
                                                                              · exact (by decide : ExactOddStep 1 216136277042447655559 324204415563671483339)
                                                                              · refine ⟨486306623345507225009, ?_, ?_⟩
                                                                                · exact (by decide : ExactOddStep 1 324204415563671483339 486306623345507225009)
                                                                                · refine ⟨364729967509130418757, ?_, ?_⟩
                                                                                  · exact (by decide : ExactOddStep 2 486306623345507225009 364729967509130418757)
                                                                                  · refine ⟨68386868907961953517, ?_, ?_⟩
                                                                                    · exact (by decide : ExactOddStep 4 364729967509130418757 68386868907961953517)
                                                                                    · refine ⟨25645075840485732569, ?_, ?_⟩
                                                                                      · exact (by decide : ExactOddStep 3 68386868907961953517 25645075840485732569)
                                                                                      · refine ⟨19233806880364299427, ?_, ?_⟩
                                                                                        · exact (by decide : ExactOddStep 2 25645075840485732569 19233806880364299427)
                                                                                        · refine ⟨28850710320546449141, ?_, ?_⟩
                                                                                          · exact (by decide : ExactOddStep 1 19233806880364299427 28850710320546449141)
                                                                                          · refine ⟨2704754092551229607, ?_, ?_⟩
                                                                                            · exact (by decide : ExactOddStep 5 28850710320546449141 2704754092551229607)
                                                                                            · rfl

/-- Every lift of family 6 descends after its exact accelerated word. -/
theorem family_6_all_lifts (q : Nat) :
    ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 5] (11529215164209430555 + q * 2 ^ 76) endpoint ∧
      endpoint < 11529215164209430555 + q * 2 ^ 76 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 5] family_6_trace (by decide) (by decide) (by decide) q

/-- Family 7: exact representative trace from the pinned input. -/
theorem family_7_trace : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 5] 13258597421119701019 3110467202276533307 := by
  simp only [WordTrace]
  refine ⟨19887896131679551529, ?_, ?_⟩
  · exact (by decide : ExactOddStep 1 13258597421119701019 19887896131679551529)
  · refine ⟨14915922098759663647, ?_, ?_⟩
    · exact (by decide : ExactOddStep 2 19887896131679551529 14915922098759663647)
    · refine ⟨22373883148139495471, ?_, ?_⟩
      · exact (by decide : ExactOddStep 1 14915922098759663647 22373883148139495471)
      · refine ⟨33560824722209243207, ?_, ?_⟩
        · exact (by decide : ExactOddStep 1 22373883148139495471 33560824722209243207)
        · refine ⟨50341237083313864811, ?_, ?_⟩
          · exact (by decide : ExactOddStep 1 33560824722209243207 50341237083313864811)
          · refine ⟨75511855624970797217, ?_, ?_⟩
            · exact (by decide : ExactOddStep 1 50341237083313864811 75511855624970797217)
            · refine ⟨56633891718728097913, ?_, ?_⟩
              · exact (by decide : ExactOddStep 2 75511855624970797217 56633891718728097913)
              · refine ⟨42475418789046073435, ?_, ?_⟩
                · exact (by decide : ExactOddStep 2 56633891718728097913 42475418789046073435)
                · refine ⟨63713128183569110153, ?_, ?_⟩
                  · exact (by decide : ExactOddStep 1 42475418789046073435 63713128183569110153)
                  · refine ⟨47784846137676832615, ?_, ?_⟩
                    · exact (by decide : ExactOddStep 2 63713128183569110153 47784846137676832615)
                    · refine ⟨71677269206515248923, ?_, ?_⟩
                      · exact (by decide : ExactOddStep 1 47784846137676832615 71677269206515248923)
                      · refine ⟨107515903809772873385, ?_, ?_⟩
                        · exact (by decide : ExactOddStep 1 71677269206515248923 107515903809772873385)
                        · refine ⟨80636927857329655039, ?_, ?_⟩
                          · exact (by decide : ExactOddStep 2 107515903809772873385 80636927857329655039)
                          · refine ⟨120955391785994482559, ?_, ?_⟩
                            · exact (by decide : ExactOddStep 1 80636927857329655039 120955391785994482559)
                            · refine ⟨181433087678991723839, ?_, ?_⟩
                              · exact (by decide : ExactOddStep 1 120955391785994482559 181433087678991723839)
                              · refine ⟨272149631518487585759, ?_, ?_⟩
                                · exact (by decide : ExactOddStep 1 181433087678991723839 272149631518487585759)
                                · refine ⟨408224447277731378639, ?_, ?_⟩
                                  · exact (by decide : ExactOddStep 1 272149631518487585759 408224447277731378639)
                                  · refine ⟨612336670916597067959, ?_, ?_⟩
                                    · exact (by decide : ExactOddStep 1 408224447277731378639 612336670916597067959)
                                    · refine ⟨918505006374895601939, ?_, ?_⟩
                                      · exact (by decide : ExactOddStep 1 612336670916597067959 918505006374895601939)
                                      · refine ⟨1377757509562343402909, ?_, ?_⟩
                                        · exact (by decide : ExactOddStep 1 918505006374895601939 1377757509562343402909)
                                        · refine ⟨516659066085878776091, ?_, ?_⟩
                                          · exact (by decide : ExactOddStep 3 1377757509562343402909 516659066085878776091)
                                          · refine ⟨774988599128818164137, ?_, ?_⟩
                                            · exact (by decide : ExactOddStep 1 516659066085878776091 774988599128818164137)
                                            · refine ⟨581241449346613623103, ?_, ?_⟩
                                              · exact (by decide : ExactOddStep 2 774988599128818164137 581241449346613623103)
                                              · refine ⟨871862174019920434655, ?_, ?_⟩
                                                · exact (by decide : ExactOddStep 1 581241449346613623103 871862174019920434655)
                                                · refine ⟨1307793261029880651983, ?_, ?_⟩
                                                  · exact (by decide : ExactOddStep 1 871862174019920434655 1307793261029880651983)
                                                  · refine ⟨1961689891544820977975, ?_, ?_⟩
                                                    · exact (by decide : ExactOddStep 1 1307793261029880651983 1961689891544820977975)
                                                    · refine ⟨2942534837317231466963, ?_, ?_⟩
                                                      · exact (by decide : ExactOddStep 1 1961689891544820977975 2942534837317231466963)
                                                      · refine ⟨4413802255975847200445, ?_, ?_⟩
                                                        · exact (by decide : ExactOddStep 1 2942534837317231466963 4413802255975847200445)
                                                        · refine ⟨1655175845990942700167, ?_, ?_⟩
                                                          · exact (by decide : ExactOddStep 3 4413802255975847200445 1655175845990942700167)
                                                          · refine ⟨2482763768986414050251, ?_, ?_⟩
                                                            · exact (by decide : ExactOddStep 1 1655175845990942700167 2482763768986414050251)
                                                            · refine ⟨3724145653479621075377, ?_, ?_⟩
                                                              · exact (by decide : ExactOddStep 1 2482763768986414050251 3724145653479621075377)
                                                              · refine ⟨2793109240109715806533, ?_, ?_⟩
                                                                · exact (by decide : ExactOddStep 2 3724145653479621075377 2793109240109715806533)
                                                                · refine ⟨523707982520571713725, ?_, ?_⟩
                                                                  · exact (by decide : ExactOddStep 4 2793109240109715806533 523707982520571713725)
                                                                  · refine ⟨196390493445214392647, ?_, ?_⟩
                                                                    · exact (by decide : ExactOddStep 3 523707982520571713725 196390493445214392647)
                                                                    · refine ⟨294585740167821588971, ?_, ?_⟩
                                                                      · exact (by decide : ExactOddStep 1 196390493445214392647 294585740167821588971)
                                                                      · refine ⟨441878610251732383457, ?_, ?_⟩
                                                                        · exact (by decide : ExactOddStep 1 294585740167821588971 441878610251732383457)
                                                                        · refine ⟨331408957688799287593, ?_, ?_⟩
                                                                          · exact (by decide : ExactOddStep 2 441878610251732383457 331408957688799287593)
                                                                          · refine ⟨248556718266599465695, ?_, ?_⟩
                                                                            · exact (by decide : ExactOddStep 2 331408957688799287593 248556718266599465695)
                                                                            · refine ⟨372835077399899198543, ?_, ?_⟩
                                                                              · exact (by decide : ExactOddStep 1 248556718266599465695 372835077399899198543)
                                                                              · refine ⟨559252616099848797815, ?_, ?_⟩
                                                                                · exact (by decide : ExactOddStep 1 372835077399899198543 559252616099848797815)
                                                                                · refine ⟨838878924149773196723, ?_, ?_⟩
                                                                                  · exact (by decide : ExactOddStep 1 559252616099848797815 838878924149773196723)
                                                                                  · refine ⟨1258318386224659795085, ?_, ?_⟩
                                                                                    · exact (by decide : ExactOddStep 1 838878924149773196723 1258318386224659795085)
                                                                                    · refine ⟨471869394834247423157, ?_, ?_⟩
                                                                                      · exact (by decide : ExactOddStep 3 1258318386224659795085 471869394834247423157)
                                                                                      · refine ⟨44237755765710695921, ?_, ?_⟩
                                                                                        · exact (by decide : ExactOddStep 5 471869394834247423157 44237755765710695921)
                                                                                        · refine ⟨33178316824283021941, ?_, ?_⟩
                                                                                          · exact (by decide : ExactOddStep 2 44237755765710695921 33178316824283021941)
                                                                                          · refine ⟨3110467202276533307, ?_, ?_⟩
                                                                                            · exact (by decide : ExactOddStep 5 33178316824283021941 3110467202276533307)
                                                                                            · rfl

/-- Every lift of family 7 descends after its exact accelerated word. -/
theorem family_7_all_lifts (q : Nat) :
    ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 5] (13258597421119701019 + q * 2 ^ 76) endpoint ∧
      endpoint < 13258597421119701019 + q * 2 ^ 76 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 5] family_7_trace (by decide) (by decide) (by decide) q

/-- Family 8: exact representative trace from the pinned input. -/
theorem family_8_trace : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 2, 1, 5] 2305843127354654747 405713130512207405 := by
  simp only [WordTrace]
  refine ⟨3458764691031982121, ?_, ?_⟩
  · exact (by decide : ExactOddStep 1 2305843127354654747 3458764691031982121)
  · refine ⟨2594073518273986591, ?_, ?_⟩
    · exact (by decide : ExactOddStep 2 3458764691031982121 2594073518273986591)
    · refine ⟨3891110277410979887, ?_, ?_⟩
      · exact (by decide : ExactOddStep 1 2594073518273986591 3891110277410979887)
      · refine ⟨5836665416116469831, ?_, ?_⟩
        · exact (by decide : ExactOddStep 1 3891110277410979887 5836665416116469831)
        · refine ⟨8754998124174704747, ?_, ?_⟩
          · exact (by decide : ExactOddStep 1 5836665416116469831 8754998124174704747)
          · refine ⟨13132497186262057121, ?_, ?_⟩
            · exact (by decide : ExactOddStep 1 8754998124174704747 13132497186262057121)
            · refine ⟨9849372889696542841, ?_, ?_⟩
              · exact (by decide : ExactOddStep 2 13132497186262057121 9849372889696542841)
              · refine ⟨7387029667272407131, ?_, ?_⟩
                · exact (by decide : ExactOddStep 2 9849372889696542841 7387029667272407131)
                · refine ⟨11080544500908610697, ?_, ?_⟩
                  · exact (by decide : ExactOddStep 1 7387029667272407131 11080544500908610697)
                  · refine ⟨8310408375681458023, ?_, ?_⟩
                    · exact (by decide : ExactOddStep 2 11080544500908610697 8310408375681458023)
                    · refine ⟨12465612563522187035, ?_, ?_⟩
                      · exact (by decide : ExactOddStep 1 8310408375681458023 12465612563522187035)
                      · refine ⟨18698418845283280553, ?_, ?_⟩
                        · exact (by decide : ExactOddStep 1 12465612563522187035 18698418845283280553)
                        · refine ⟨14023814133962460415, ?_, ?_⟩
                          · exact (by decide : ExactOddStep 2 18698418845283280553 14023814133962460415)
                          · refine ⟨21035721200943690623, ?_, ?_⟩
                            · exact (by decide : ExactOddStep 1 14023814133962460415 21035721200943690623)
                            · refine ⟨31553581801415535935, ?_, ?_⟩
                              · exact (by decide : ExactOddStep 1 21035721200943690623 31553581801415535935)
                              · refine ⟨47330372702123303903, ?_, ?_⟩
                                · exact (by decide : ExactOddStep 1 31553581801415535935 47330372702123303903)
                                · refine ⟨70995559053184955855, ?_, ?_⟩
                                  · exact (by decide : ExactOddStep 1 47330372702123303903 70995559053184955855)
                                  · refine ⟨106493338579777433783, ?_, ?_⟩
                                    · exact (by decide : ExactOddStep 1 70995559053184955855 106493338579777433783)
                                    · refine ⟨159740007869666150675, ?_, ?_⟩
                                      · exact (by decide : ExactOddStep 1 106493338579777433783 159740007869666150675)
                                      · refine ⟨239610011804499226013, ?_, ?_⟩
                                        · exact (by decide : ExactOddStep 1 159740007869666150675 239610011804499226013)
                                        · refine ⟨89853754426687209755, ?_, ?_⟩
                                          · exact (by decide : ExactOddStep 3 239610011804499226013 89853754426687209755)
                                          · refine ⟨134780631640030814633, ?_, ?_⟩
                                            · exact (by decide : ExactOddStep 1 89853754426687209755 134780631640030814633)
                                            · refine ⟨101085473730023110975, ?_, ?_⟩
                                              · exact (by decide : ExactOddStep 2 134780631640030814633 101085473730023110975)
                                              · refine ⟨151628210595034666463, ?_, ?_⟩
                                                · exact (by decide : ExactOddStep 1 101085473730023110975 151628210595034666463)
                                                · refine ⟨227442315892551999695, ?_, ?_⟩
                                                  · exact (by decide : ExactOddStep 1 151628210595034666463 227442315892551999695)
                                                  · refine ⟨341163473838827999543, ?_, ?_⟩
                                                    · exact (by decide : ExactOddStep 1 227442315892551999695 341163473838827999543)
                                                    · refine ⟨511745210758241999315, ?_, ?_⟩
                                                      · exact (by decide : ExactOddStep 1 341163473838827999543 511745210758241999315)
                                                      · refine ⟨767617816137362998973, ?_, ?_⟩
                                                        · exact (by decide : ExactOddStep 1 511745210758241999315 767617816137362998973)
                                                        · refine ⟨287856681051511124615, ?_, ?_⟩
                                                          · exact (by decide : ExactOddStep 3 767617816137362998973 287856681051511124615)
                                                          · refine ⟨431785021577266686923, ?_, ?_⟩
                                                            · exact (by decide : ExactOddStep 1 287856681051511124615 431785021577266686923)
                                                            · refine ⟨647677532365900030385, ?_, ?_⟩
                                                              · exact (by decide : ExactOddStep 1 431785021577266686923 647677532365900030385)
                                                              · refine ⟨485758149274425022789, ?_, ?_⟩
                                                                · exact (by decide : ExactOddStep 2 647677532365900030385 485758149274425022789)
                                                                · refine ⟨91079652988954691773, ?_, ?_⟩
                                                                  · exact (by decide : ExactOddStep 4 485758149274425022789 91079652988954691773)
                                                                  · refine ⟨34154869870858009415, ?_, ?_⟩
                                                                    · exact (by decide : ExactOddStep 3 91079652988954691773 34154869870858009415)
                                                                    · refine ⟨51232304806287014123, ?_, ?_⟩
                                                                      · exact (by decide : ExactOddStep 1 34154869870858009415 51232304806287014123)
                                                                      · refine ⟨76848457209430521185, ?_, ?_⟩
                                                                        · exact (by decide : ExactOddStep 1 51232304806287014123 76848457209430521185)
                                                                        · refine ⟨57636342907072890889, ?_, ?_⟩
                                                                          · exact (by decide : ExactOddStep 2 76848457209430521185 57636342907072890889)
                                                                          · refine ⟨43227257180304668167, ?_, ?_⟩
                                                                            · exact (by decide : ExactOddStep 2 57636342907072890889 43227257180304668167)
                                                                            · refine ⟨64840885770457002251, ?_, ?_⟩
                                                                              · exact (by decide : ExactOddStep 1 43227257180304668167 64840885770457002251)
                                                                              · refine ⟨97261328655685503377, ?_, ?_⟩
                                                                                · exact (by decide : ExactOddStep 1 64840885770457002251 97261328655685503377)
                                                                                · refine ⟨72945996491764127533, ?_, ?_⟩
                                                                                  · exact (by decide : ExactOddStep 2 97261328655685503377 72945996491764127533)
                                                                                  · refine ⟨27354748684411547825, ?_, ?_⟩
                                                                                    · exact (by decide : ExactOddStep 3 72945996491764127533 27354748684411547825)
                                                                                    · refine ⟨20516061513308660869, ?_, ?_⟩
                                                                                      · exact (by decide : ExactOddStep 2 27354748684411547825 20516061513308660869)
                                                                                      · refine ⟨3846761533745373913, ?_, ?_⟩
                                                                                        · exact (by decide : ExactOddStep 4 20516061513308660869 3846761533745373913)
                                                                                        · refine ⟨2885071150309030435, ?_, ?_⟩
                                                                                          · exact (by decide : ExactOddStep 2 3846761533745373913 2885071150309030435)
                                                                                          · refine ⟨4327606725463545653, ?_, ?_⟩
                                                                                            · exact (by decide : ExactOddStep 1 2885071150309030435 4327606725463545653)
                                                                                            · refine ⟨405713130512207405, ?_, ?_⟩
                                                                                              · exact (by decide : ExactOddStep 5 4327606725463545653 405713130512207405)
                                                                                              · rfl

/-- Every lift of family 8 descends after its exact accelerated word. -/
theorem family_8_all_lifts (q : Nat) :
    ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 2, 1, 5] (2305843127354654747 + q * 2 ^ 78) endpoint ∧
      endpoint < 2305843127354654747 + q * 2 ^ 78 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 2, 1, 5] family_8_trace (by decide) (by decide) (by decide) q

/-- Family 9: exact representative trace from the pinned input. -/
theorem family_9_trace : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 3, 2, 1, 3] 16717361934940241947 13236390298329099887 := by
  simp only [WordTrace]
  refine ⟨25076042902410362921, ?_, ?_⟩
  · exact (by decide : ExactOddStep 1 16717361934940241947 25076042902410362921)
  · refine ⟨18807032176807772191, ?_, ?_⟩
    · exact (by decide : ExactOddStep 2 25076042902410362921 18807032176807772191)
    · refine ⟨28210548265211658287, ?_, ?_⟩
      · exact (by decide : ExactOddStep 1 18807032176807772191 28210548265211658287)
      · refine ⟨42315822397817487431, ?_, ?_⟩
        · exact (by decide : ExactOddStep 1 28210548265211658287 42315822397817487431)
        · refine ⟨63473733596726231147, ?_, ?_⟩
          · exact (by decide : ExactOddStep 1 42315822397817487431 63473733596726231147)
          · refine ⟨95210600395089346721, ?_, ?_⟩
            · exact (by decide : ExactOddStep 1 63473733596726231147 95210600395089346721)
            · refine ⟨71407950296317010041, ?_, ?_⟩
              · exact (by decide : ExactOddStep 2 95210600395089346721 71407950296317010041)
              · refine ⟨53555962722237757531, ?_, ?_⟩
                · exact (by decide : ExactOddStep 2 71407950296317010041 53555962722237757531)
                · refine ⟨80333944083356636297, ?_, ?_⟩
                  · exact (by decide : ExactOddStep 1 53555962722237757531 80333944083356636297)
                  · refine ⟨60250458062517477223, ?_, ?_⟩
                    · exact (by decide : ExactOddStep 2 80333944083356636297 60250458062517477223)
                    · refine ⟨90375687093776215835, ?_, ?_⟩
                      · exact (by decide : ExactOddStep 1 60250458062517477223 90375687093776215835)
                      · refine ⟨135563530640664323753, ?_, ?_⟩
                        · exact (by decide : ExactOddStep 1 90375687093776215835 135563530640664323753)
                        · refine ⟨101672647980498242815, ?_, ?_⟩
                          · exact (by decide : ExactOddStep 2 135563530640664323753 101672647980498242815)
                          · refine ⟨152508971970747364223, ?_, ?_⟩
                            · exact (by decide : ExactOddStep 1 101672647980498242815 152508971970747364223)
                            · refine ⟨228763457956121046335, ?_, ?_⟩
                              · exact (by decide : ExactOddStep 1 152508971970747364223 228763457956121046335)
                              · refine ⟨343145186934181569503, ?_, ?_⟩
                                · exact (by decide : ExactOddStep 1 228763457956121046335 343145186934181569503)
                                · refine ⟨514717780401272354255, ?_, ?_⟩
                                  · exact (by decide : ExactOddStep 1 343145186934181569503 514717780401272354255)
                                  · refine ⟨772076670601908531383, ?_, ?_⟩
                                    · exact (by decide : ExactOddStep 1 514717780401272354255 772076670601908531383)
                                    · refine ⟨1158115005902862797075, ?_, ?_⟩
                                      · exact (by decide : ExactOddStep 1 772076670601908531383 1158115005902862797075)
                                      · refine ⟨1737172508854294195613, ?_, ?_⟩
                                        · exact (by decide : ExactOddStep 1 1158115005902862797075 1737172508854294195613)
                                        · refine ⟨651439690820360323355, ?_, ?_⟩
                                          · exact (by decide : ExactOddStep 3 1737172508854294195613 651439690820360323355)
                                          · refine ⟨977159536230540485033, ?_, ?_⟩
                                            · exact (by decide : ExactOddStep 1 651439690820360323355 977159536230540485033)
                                            · refine ⟨732869652172905363775, ?_, ?_⟩
                                              · exact (by decide : ExactOddStep 2 977159536230540485033 732869652172905363775)
                                              · refine ⟨1099304478259358045663, ?_, ?_⟩
                                                · exact (by decide : ExactOddStep 1 732869652172905363775 1099304478259358045663)
                                                · refine ⟨1648956717389037068495, ?_, ?_⟩
                                                  · exact (by decide : ExactOddStep 1 1099304478259358045663 1648956717389037068495)
                                                  · refine ⟨2473435076083555602743, ?_, ?_⟩
                                                    · exact (by decide : ExactOddStep 1 1648956717389037068495 2473435076083555602743)
                                                    · refine ⟨3710152614125333404115, ?_, ?_⟩
                                                      · exact (by decide : ExactOddStep 1 2473435076083555602743 3710152614125333404115)
                                                      · refine ⟨5565228921188000106173, ?_, ?_⟩
                                                        · exact (by decide : ExactOddStep 1 3710152614125333404115 5565228921188000106173)
                                                        · refine ⟨2086960845445500039815, ?_, ?_⟩
                                                          · exact (by decide : ExactOddStep 3 5565228921188000106173 2086960845445500039815)
                                                          · refine ⟨3130441268168250059723, ?_, ?_⟩
                                                            · exact (by decide : ExactOddStep 1 2086960845445500039815 3130441268168250059723)
                                                            · refine ⟨4695661902252375089585, ?_, ?_⟩
                                                              · exact (by decide : ExactOddStep 1 3130441268168250059723 4695661902252375089585)
                                                              · refine ⟨3521746426689281317189, ?_, ?_⟩
                                                                · exact (by decide : ExactOddStep 2 4695661902252375089585 3521746426689281317189)
                                                                · refine ⟨660327455004240246973, ?_, ?_⟩
                                                                  · exact (by decide : ExactOddStep 4 3521746426689281317189 660327455004240246973)
                                                                  · refine ⟨247622795626590092615, ?_, ?_⟩
                                                                    · exact (by decide : ExactOddStep 3 660327455004240246973 247622795626590092615)
                                                                    · refine ⟨371434193439885138923, ?_, ?_⟩
                                                                      · exact (by decide : ExactOddStep 1 247622795626590092615 371434193439885138923)
                                                                      · refine ⟨557151290159827708385, ?_, ?_⟩
                                                                        · exact (by decide : ExactOddStep 1 371434193439885138923 557151290159827708385)
                                                                        · refine ⟨417863467619870781289, ?_, ?_⟩
                                                                          · exact (by decide : ExactOddStep 2 557151290159827708385 417863467619870781289)
                                                                          · refine ⟨313397600714903085967, ?_, ?_⟩
                                                                            · exact (by decide : ExactOddStep 2 417863467619870781289 313397600714903085967)
                                                                            · refine ⟨470096401072354628951, ?_, ?_⟩
                                                                              · exact (by decide : ExactOddStep 1 313397600714903085967 470096401072354628951)
                                                                              · refine ⟨705144601608531943427, ?_, ?_⟩
                                                                                · exact (by decide : ExactOddStep 1 470096401072354628951 705144601608531943427)
                                                                                · refine ⟨1057716902412797915141, ?_, ?_⟩
                                                                                  · exact (by decide : ExactOddStep 1 705144601608531943427 1057716902412797915141)
                                                                                  · refine ⟨198321919202399609089, ?_, ?_⟩
                                                                                    · exact (by decide : ExactOddStep 4 1057716902412797915141 198321919202399609089)
                                                                                    · refine ⟨148741439401799706817, ?_, ?_⟩
                                                                                      · exact (by decide : ExactOddStep 2 198321919202399609089 148741439401799706817)
                                                                                      · refine ⟨111556079551349780113, ?_, ?_⟩
                                                                                        · exact (by decide : ExactOddStep 2 148741439401799706817 111556079551349780113)
                                                                                        · refine ⟨83667059663512335085, ?_, ?_⟩
                                                                                          · exact (by decide : ExactOddStep 2 111556079551349780113 83667059663512335085)
                                                                                          · refine ⟨31375147373817125657, ?_, ?_⟩
                                                                                            · exact (by decide : ExactOddStep 3 83667059663512335085 31375147373817125657)
                                                                                            · refine ⟨23531360530362844243, ?_, ?_⟩
                                                                                              · exact (by decide : ExactOddStep 2 31375147373817125657 23531360530362844243)
                                                                                              · refine ⟨35297040795544266365, ?_, ?_⟩
                                                                                                · exact (by decide : ExactOddStep 1 23531360530362844243 35297040795544266365)
                                                                                                · refine ⟨13236390298329099887, ?_, ?_⟩
                                                                                                  · exact (by decide : ExactOddStep 3 35297040795544266365 13236390298329099887)
                                                                                                  · rfl

/-- Every lift of family 9 descends after its exact accelerated word. -/
theorem family_9_all_lifts (q : Nat) :
    ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 3, 2, 1, 3] (16717361934940241947 + q * 2 ^ 79) endpoint ∧
      endpoint < 16717361934940241947 + q * 2 ^ 79 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 3, 2, 1, 3] family_9_trace (by decide) (by decide) (by decide) q

/-- Family 10: exact representative trace from the pinned input. -/
theorem family_10_trace : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 2, 1, 1, 5] 7493989898085466139 2966777161636816643 := by
  simp only [WordTrace]
  refine ⟨11240984847128199209, ?_, ?_⟩
  · exact (by decide : ExactOddStep 1 7493989898085466139 11240984847128199209)
  · refine ⟨8430738635346149407, ?_, ?_⟩
    · exact (by decide : ExactOddStep 2 11240984847128199209 8430738635346149407)
    · refine ⟨12646107953019224111, ?_, ?_⟩
      · exact (by decide : ExactOddStep 1 8430738635346149407 12646107953019224111)
      · refine ⟨18969161929528836167, ?_, ?_⟩
        · exact (by decide : ExactOddStep 1 12646107953019224111 18969161929528836167)
        · refine ⟨28453742894293254251, ?_, ?_⟩
          · exact (by decide : ExactOddStep 1 18969161929528836167 28453742894293254251)
          · refine ⟨42680614341439881377, ?_, ?_⟩
            · exact (by decide : ExactOddStep 1 28453742894293254251 42680614341439881377)
            · refine ⟨32010460756079911033, ?_, ?_⟩
              · exact (by decide : ExactOddStep 2 42680614341439881377 32010460756079911033)
              · refine ⟨24007845567059933275, ?_, ?_⟩
                · exact (by decide : ExactOddStep 2 32010460756079911033 24007845567059933275)
                · refine ⟨36011768350589899913, ?_, ?_⟩
                  · exact (by decide : ExactOddStep 1 24007845567059933275 36011768350589899913)
                  · refine ⟨27008826262942424935, ?_, ?_⟩
                    · exact (by decide : ExactOddStep 2 36011768350589899913 27008826262942424935)
                    · refine ⟨40513239394413637403, ?_, ?_⟩
                      · exact (by decide : ExactOddStep 1 27008826262942424935 40513239394413637403)
                      · refine ⟨60769859091620456105, ?_, ?_⟩
                        · exact (by decide : ExactOddStep 1 40513239394413637403 60769859091620456105)
                        · refine ⟨45577394318715342079, ?_, ?_⟩
                          · exact (by decide : ExactOddStep 2 60769859091620456105 45577394318715342079)
                          · refine ⟨68366091478073013119, ?_, ?_⟩
                            · exact (by decide : ExactOddStep 1 45577394318715342079 68366091478073013119)
                            · refine ⟨102549137217109519679, ?_, ?_⟩
                              · exact (by decide : ExactOddStep 1 68366091478073013119 102549137217109519679)
                              · refine ⟨153823705825664279519, ?_, ?_⟩
                                · exact (by decide : ExactOddStep 1 102549137217109519679 153823705825664279519)
                                · refine ⟨230735558738496419279, ?_, ?_⟩
                                  · exact (by decide : ExactOddStep 1 153823705825664279519 230735558738496419279)
                                  · refine ⟨346103338107744628919, ?_, ?_⟩
                                    · exact (by decide : ExactOddStep 1 230735558738496419279 346103338107744628919)
                                    · refine ⟨519155007161616943379, ?_, ?_⟩
                                      · exact (by decide : ExactOddStep 1 346103338107744628919 519155007161616943379)
                                      · refine ⟨778732510742425415069, ?_, ?_⟩
                                        · exact (by decide : ExactOddStep 1 519155007161616943379 778732510742425415069)
                                        · refine ⟨292024691528409530651, ?_, ?_⟩
                                          · exact (by decide : ExactOddStep 3 778732510742425415069 292024691528409530651)
                                          · refine ⟨438037037292614295977, ?_, ?_⟩
                                            · exact (by decide : ExactOddStep 1 292024691528409530651 438037037292614295977)
                                            · refine ⟨328527777969460721983, ?_, ?_⟩
                                              · exact (by decide : ExactOddStep 2 438037037292614295977 328527777969460721983)
                                              · refine ⟨492791666954191082975, ?_, ?_⟩
                                                · exact (by decide : ExactOddStep 1 328527777969460721983 492791666954191082975)
                                                · refine ⟨739187500431286624463, ?_, ?_⟩
                                                  · exact (by decide : ExactOddStep 1 492791666954191082975 739187500431286624463)
                                                  · refine ⟨1108781250646929936695, ?_, ?_⟩
                                                    · exact (by decide : ExactOddStep 1 739187500431286624463 1108781250646929936695)
                                                    · refine ⟨1663171875970394905043, ?_, ?_⟩
                                                      · exact (by decide : ExactOddStep 1 1108781250646929936695 1663171875970394905043)
                                                      · refine ⟨2494757813955592357565, ?_, ?_⟩
                                                        · exact (by decide : ExactOddStep 1 1663171875970394905043 2494757813955592357565)
                                                        · refine ⟨935534180233347134087, ?_, ?_⟩
                                                          · exact (by decide : ExactOddStep 3 2494757813955592357565 935534180233347134087)
                                                          · refine ⟨1403301270350020701131, ?_, ?_⟩
                                                            · exact (by decide : ExactOddStep 1 935534180233347134087 1403301270350020701131)
                                                            · refine ⟨2104951905525031051697, ?_, ?_⟩
                                                              · exact (by decide : ExactOddStep 1 1403301270350020701131 2104951905525031051697)
                                                              · refine ⟨1578713929143773288773, ?_, ?_⟩
                                                                · exact (by decide : ExactOddStep 2 2104951905525031051697 1578713929143773288773)
                                                                · refine ⟨296008861714457491645, ?_, ?_⟩
                                                                  · exact (by decide : ExactOddStep 4 1578713929143773288773 296008861714457491645)
                                                                  · refine ⟨111003323142921559367, ?_, ?_⟩
                                                                    · exact (by decide : ExactOddStep 3 296008861714457491645 111003323142921559367)
                                                                    · refine ⟨166504984714382339051, ?_, ?_⟩
                                                                      · exact (by decide : ExactOddStep 1 111003323142921559367 166504984714382339051)
                                                                      · refine ⟨249757477071573508577, ?_, ?_⟩
                                                                        · exact (by decide : ExactOddStep 1 166504984714382339051 249757477071573508577)
                                                                        · refine ⟨187318107803680131433, ?_, ?_⟩
                                                                          · exact (by decide : ExactOddStep 2 249757477071573508577 187318107803680131433)
                                                                          · refine ⟨140488580852760098575, ?_, ?_⟩
                                                                            · exact (by decide : ExactOddStep 2 187318107803680131433 140488580852760098575)
                                                                            · refine ⟨210732871279140147863, ?_, ?_⟩
                                                                              · exact (by decide : ExactOddStep 1 140488580852760098575 210732871279140147863)
                                                                              · refine ⟨316099306918710221795, ?_, ?_⟩
                                                                                · exact (by decide : ExactOddStep 1 210732871279140147863 316099306918710221795)
                                                                                · refine ⟨474148960378065332693, ?_, ?_⟩
                                                                                  · exact (by decide : ExactOddStep 1 316099306918710221795 474148960378065332693)
                                                                                  · refine ⟨11112866258860906235, ?_, ?_⟩
                                                                                    · exact (by decide : ExactOddStep 7 474148960378065332693 11112866258860906235)
                                                                                    · refine ⟨16669299388291359353, ?_, ?_⟩
                                                                                      · exact (by decide : ExactOddStep 1 11112866258860906235 16669299388291359353)
                                                                                      · refine ⟨12501974541218519515, ?_, ?_⟩
                                                                                        · exact (by decide : ExactOddStep 2 16669299388291359353 12501974541218519515)
                                                                                        · refine ⟨18752961811827779273, ?_, ?_⟩
                                                                                          · exact (by decide : ExactOddStep 1 12501974541218519515 18752961811827779273)
                                                                                          · refine ⟨14064721358870834455, ?_, ?_⟩
                                                                                            · exact (by decide : ExactOddStep 2 18752961811827779273 14064721358870834455)
                                                                                            · refine ⟨21097082038306251683, ?_, ?_⟩
                                                                                              · exact (by decide : ExactOddStep 1 14064721358870834455 21097082038306251683)
                                                                                              · refine ⟨31645623057459377525, ?_, ?_⟩
                                                                                                · exact (by decide : ExactOddStep 1 21097082038306251683 31645623057459377525)
                                                                                                · refine ⟨2966777161636816643, ?_, ?_⟩
                                                                                                  · exact (by decide : ExactOddStep 5 31645623057459377525 2966777161636816643)
                                                                                                  · rfl

/-- Every lift of family 10 descends after its exact accelerated word. -/
theorem family_10_all_lifts (q : Nat) :
    ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 2, 1, 1, 5] (7493989898085466139 + q * 2 ^ 80) endpoint ∧
      endpoint < 7493989898085466139 + q * 2 ^ 80 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 2, 1, 1, 5] family_10_trace (by decide) (by decide) (by decide) q

/-- Family 11: exact representative trace from the pinned input. -/
theorem family_11_trace : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 2, 4, 5] 8070450650388889627 1597495392928649987 := by
  simp only [WordTrace]
  refine ⟨12105675975583334441, ?_, ?_⟩
  · exact (by decide : ExactOddStep 1 8070450650388889627 12105675975583334441)
  · refine ⟨9079256981687500831, ?_, ?_⟩
    · exact (by decide : ExactOddStep 2 12105675975583334441 9079256981687500831)
    · refine ⟨13618885472531251247, ?_, ?_⟩
      · exact (by decide : ExactOddStep 1 9079256981687500831 13618885472531251247)
      · refine ⟨20428328208796876871, ?_, ?_⟩
        · exact (by decide : ExactOddStep 1 13618885472531251247 20428328208796876871)
        · refine ⟨30642492313195315307, ?_, ?_⟩
          · exact (by decide : ExactOddStep 1 20428328208796876871 30642492313195315307)
          · refine ⟨45963738469792972961, ?_, ?_⟩
            · exact (by decide : ExactOddStep 1 30642492313195315307 45963738469792972961)
            · refine ⟨34472803852344729721, ?_, ?_⟩
              · exact (by decide : ExactOddStep 2 45963738469792972961 34472803852344729721)
              · refine ⟨25854602889258547291, ?_, ?_⟩
                · exact (by decide : ExactOddStep 2 34472803852344729721 25854602889258547291)
                · refine ⟨38781904333887820937, ?_, ?_⟩
                  · exact (by decide : ExactOddStep 1 25854602889258547291 38781904333887820937)
                  · refine ⟨29086428250415865703, ?_, ?_⟩
                    · exact (by decide : ExactOddStep 2 38781904333887820937 29086428250415865703)
                    · refine ⟨43629642375623798555, ?_, ?_⟩
                      · exact (by decide : ExactOddStep 1 29086428250415865703 43629642375623798555)
                      · refine ⟨65444463563435697833, ?_, ?_⟩
                        · exact (by decide : ExactOddStep 1 43629642375623798555 65444463563435697833)
                        · refine ⟨49083347672576773375, ?_, ?_⟩
                          · exact (by decide : ExactOddStep 2 65444463563435697833 49083347672576773375)
                          · refine ⟨73625021508865160063, ?_, ?_⟩
                            · exact (by decide : ExactOddStep 1 49083347672576773375 73625021508865160063)
                            · refine ⟨110437532263297740095, ?_, ?_⟩
                              · exact (by decide : ExactOddStep 1 73625021508865160063 110437532263297740095)
                              · refine ⟨165656298394946610143, ?_, ?_⟩
                                · exact (by decide : ExactOddStep 1 110437532263297740095 165656298394946610143)
                                · refine ⟨248484447592419915215, ?_, ?_⟩
                                  · exact (by decide : ExactOddStep 1 165656298394946610143 248484447592419915215)
                                  · refine ⟨372726671388629872823, ?_, ?_⟩
                                    · exact (by decide : ExactOddStep 1 248484447592419915215 372726671388629872823)
                                    · refine ⟨559090007082944809235, ?_, ?_⟩
                                      · exact (by decide : ExactOddStep 1 372726671388629872823 559090007082944809235)
                                      · refine ⟨838635010624417213853, ?_, ?_⟩
                                        · exact (by decide : ExactOddStep 1 559090007082944809235 838635010624417213853)
                                        · refine ⟨314488128984156455195, ?_, ?_⟩
                                          · exact (by decide : ExactOddStep 3 838635010624417213853 314488128984156455195)
                                          · refine ⟨471732193476234682793, ?_, ?_⟩
                                            · exact (by decide : ExactOddStep 1 314488128984156455195 471732193476234682793)
                                            · refine ⟨353799145107176012095, ?_, ?_⟩
                                              · exact (by decide : ExactOddStep 2 471732193476234682793 353799145107176012095)
                                              · refine ⟨530698717660764018143, ?_, ?_⟩
                                                · exact (by decide : ExactOddStep 1 353799145107176012095 530698717660764018143)
                                                · refine ⟨796048076491146027215, ?_, ?_⟩
                                                  · exact (by decide : ExactOddStep 1 530698717660764018143 796048076491146027215)
                                                  · refine ⟨1194072114736719040823, ?_, ?_⟩
                                                    · exact (by decide : ExactOddStep 1 796048076491146027215 1194072114736719040823)
                                                    · refine ⟨1791108172105078561235, ?_, ?_⟩
                                                      · exact (by decide : ExactOddStep 1 1194072114736719040823 1791108172105078561235)
                                                      · refine ⟨2686662258157617841853, ?_, ?_⟩
                                                        · exact (by decide : ExactOddStep 1 1791108172105078561235 2686662258157617841853)
                                                        · refine ⟨1007498346809106690695, ?_, ?_⟩
                                                          · exact (by decide : ExactOddStep 3 2686662258157617841853 1007498346809106690695)
                                                          · refine ⟨1511247520213660036043, ?_, ?_⟩
                                                            · exact (by decide : ExactOddStep 1 1007498346809106690695 1511247520213660036043)
                                                            · refine ⟨2266871280320490054065, ?_, ?_⟩
                                                              · exact (by decide : ExactOddStep 1 1511247520213660036043 2266871280320490054065)
                                                              · refine ⟨1700153460240367540549, ?_, ?_⟩
                                                                · exact (by decide : ExactOddStep 2 2266871280320490054065 1700153460240367540549)
                                                                · refine ⟨318778773795068913853, ?_, ?_⟩
                                                                  · exact (by decide : ExactOddStep 4 1700153460240367540549 318778773795068913853)
                                                                  · refine ⟨119542040173150842695, ?_, ?_⟩
                                                                    · exact (by decide : ExactOddStep 3 318778773795068913853 119542040173150842695)
                                                                    · refine ⟨179313060259726264043, ?_, ?_⟩
                                                                      · exact (by decide : ExactOddStep 1 119542040173150842695 179313060259726264043)
                                                                      · refine ⟨268969590389589396065, ?_, ?_⟩
                                                                        · exact (by decide : ExactOddStep 1 179313060259726264043 268969590389589396065)
                                                                        · refine ⟨201727192792192047049, ?_, ?_⟩
                                                                          · exact (by decide : ExactOddStep 2 268969590389589396065 201727192792192047049)
                                                                          · refine ⟨151295394594144035287, ?_, ?_⟩
                                                                            · exact (by decide : ExactOddStep 2 201727192792192047049 151295394594144035287)
                                                                            · refine ⟨226943091891216052931, ?_, ?_⟩
                                                                              · exact (by decide : ExactOddStep 1 151295394594144035287 226943091891216052931)
                                                                              · refine ⟨340414637836824079397, ?_, ?_⟩
                                                                                · exact (by decide : ExactOddStep 1 226943091891216052931 340414637836824079397)
                                                                                · refine ⟨63827744594404514887, ?_, ?_⟩
                                                                                  · exact (by decide : ExactOddStep 4 340414637836824079397 63827744594404514887)
                                                                                  · refine ⟨95741616891606772331, ?_, ?_⟩
                                                                                    · exact (by decide : ExactOddStep 1 63827744594404514887 95741616891606772331)
                                                                                    · refine ⟨143612425337410158497, ?_, ?_⟩
                                                                                      · exact (by decide : ExactOddStep 1 95741616891606772331 143612425337410158497)
                                                                                      · refine ⟨107709319003057618873, ?_, ?_⟩
                                                                                        · exact (by decide : ExactOddStep 2 143612425337410158497 107709319003057618873)
                                                                                        · refine ⟨80781989252293214155, ?_, ?_⟩
                                                                                          · exact (by decide : ExactOddStep 2 107709319003057618873 80781989252293214155)
                                                                                          · refine ⟨121172983878439821233, ?_, ?_⟩
                                                                                            · exact (by decide : ExactOddStep 1 80781989252293214155 121172983878439821233)
                                                                                            · refine ⟨90879737908829865925, ?_, ?_⟩
                                                                                              · exact (by decide : ExactOddStep 2 121172983878439821233 90879737908829865925)
                                                                                              · refine ⟨17039950857905599861, ?_, ?_⟩
                                                                                                · exact (by decide : ExactOddStep 4 90879737908829865925 17039950857905599861)
                                                                                                · refine ⟨1597495392928649987, ?_, ?_⟩
                                                                                                  · exact (by decide : ExactOddStep 5 17039950857905599861 1597495392928649987)
                                                                                                  · rfl

/-- Every lift of family 11 descends after its exact accelerated word. -/
theorem family_11_all_lifts (q : Nat) :
    ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 2, 4, 5] (8070450650388889627 + q * 2 ^ 81) endpoint ∧
      endpoint < 8070450650388889627 + q * 2 ^ 81 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 2, 4, 5] family_11_trace (by decide) (by decide) (by decide) q

/-- Family 12: exact representative trace from the pinned input. -/
theorem family_12_trace : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 2, 3, 1, 1, 4] 2882303879658078235 2567403377714137483 := by
  simp only [WordTrace]
  refine ⟨4323455819487117353, ?_, ?_⟩
  · exact (by decide : ExactOddStep 1 2882303879658078235 4323455819487117353)
  · refine ⟨3242591864615338015, ?_, ?_⟩
    · exact (by decide : ExactOddStep 2 4323455819487117353 3242591864615338015)
    · refine ⟨4863887796923007023, ?_, ?_⟩
      · exact (by decide : ExactOddStep 1 3242591864615338015 4863887796923007023)
      · refine ⟨7295831695384510535, ?_, ?_⟩
        · exact (by decide : ExactOddStep 1 4863887796923007023 7295831695384510535)
        · refine ⟨10943747543076765803, ?_, ?_⟩
          · exact (by decide : ExactOddStep 1 7295831695384510535 10943747543076765803)
          · refine ⟨16415621314615148705, ?_, ?_⟩
            · exact (by decide : ExactOddStep 1 10943747543076765803 16415621314615148705)
            · refine ⟨12311715985961361529, ?_, ?_⟩
              · exact (by decide : ExactOddStep 2 16415621314615148705 12311715985961361529)
              · refine ⟨9233786989471021147, ?_, ?_⟩
                · exact (by decide : ExactOddStep 2 12311715985961361529 9233786989471021147)
                · refine ⟨13850680484206531721, ?_, ?_⟩
                  · exact (by decide : ExactOddStep 1 9233786989471021147 13850680484206531721)
                  · refine ⟨10388010363154898791, ?_, ?_⟩
                    · exact (by decide : ExactOddStep 2 13850680484206531721 10388010363154898791)
                    · refine ⟨15582015544732348187, ?_, ?_⟩
                      · exact (by decide : ExactOddStep 1 10388010363154898791 15582015544732348187)
                      · refine ⟨23373023317098522281, ?_, ?_⟩
                        · exact (by decide : ExactOddStep 1 15582015544732348187 23373023317098522281)
                        · refine ⟨17529767487823891711, ?_, ?_⟩
                          · exact (by decide : ExactOddStep 2 23373023317098522281 17529767487823891711)
                          · refine ⟨26294651231735837567, ?_, ?_⟩
                            · exact (by decide : ExactOddStep 1 17529767487823891711 26294651231735837567)
                            · refine ⟨39441976847603756351, ?_, ?_⟩
                              · exact (by decide : ExactOddStep 1 26294651231735837567 39441976847603756351)
                              · refine ⟨59162965271405634527, ?_, ?_⟩
                                · exact (by decide : ExactOddStep 1 39441976847603756351 59162965271405634527)
                                · refine ⟨88744447907108451791, ?_, ?_⟩
                                  · exact (by decide : ExactOddStep 1 59162965271405634527 88744447907108451791)
                                  · refine ⟨133116671860662677687, ?_, ?_⟩
                                    · exact (by decide : ExactOddStep 1 88744447907108451791 133116671860662677687)
                                    · refine ⟨199675007790994016531, ?_, ?_⟩
                                      · exact (by decide : ExactOddStep 1 133116671860662677687 199675007790994016531)
                                      · refine ⟨299512511686491024797, ?_, ?_⟩
                                        · exact (by decide : ExactOddStep 1 199675007790994016531 299512511686491024797)
                                        · refine ⟨112317191882434134299, ?_, ?_⟩
                                          · exact (by decide : ExactOddStep 3 299512511686491024797 112317191882434134299)
                                          · refine ⟨168475787823651201449, ?_, ?_⟩
                                            · exact (by decide : ExactOddStep 1 112317191882434134299 168475787823651201449)
                                            · refine ⟨126356840867738401087, ?_, ?_⟩
                                              · exact (by decide : ExactOddStep 2 168475787823651201449 126356840867738401087)
                                              · refine ⟨189535261301607601631, ?_, ?_⟩
                                                · exact (by decide : ExactOddStep 1 126356840867738401087 189535261301607601631)
                                                · refine ⟨284302891952411402447, ?_, ?_⟩
                                                  · exact (by decide : ExactOddStep 1 189535261301607601631 284302891952411402447)
                                                  · refine ⟨426454337928617103671, ?_, ?_⟩
                                                    · exact (by decide : ExactOddStep 1 284302891952411402447 426454337928617103671)
                                                    · refine ⟨639681506892925655507, ?_, ?_⟩
                                                      · exact (by decide : ExactOddStep 1 426454337928617103671 639681506892925655507)
                                                      · refine ⟨959522260339388483261, ?_, ?_⟩
                                                        · exact (by decide : ExactOddStep 1 639681506892925655507 959522260339388483261)
                                                        · refine ⟨359820847627270681223, ?_, ?_⟩
                                                          · exact (by decide : ExactOddStep 3 959522260339388483261 359820847627270681223)
                                                          · refine ⟨539731271440906021835, ?_, ?_⟩
                                                            · exact (by decide : ExactOddStep 1 359820847627270681223 539731271440906021835)
                                                            · refine ⟨809596907161359032753, ?_, ?_⟩
                                                              · exact (by decide : ExactOddStep 1 539731271440906021835 809596907161359032753)
                                                              · refine ⟨607197680371019274565, ?_, ?_⟩
                                                                · exact (by decide : ExactOddStep 2 809596907161359032753 607197680371019274565)
                                                                · refine ⟨113849565069566113981, ?_, ?_⟩
                                                                  · exact (by decide : ExactOddStep 4 607197680371019274565 113849565069566113981)
                                                                  · refine ⟨42693586901087292743, ?_, ?_⟩
                                                                    · exact (by decide : ExactOddStep 3 113849565069566113981 42693586901087292743)
                                                                    · refine ⟨64040380351630939115, ?_, ?_⟩
                                                                      · exact (by decide : ExactOddStep 1 42693586901087292743 64040380351630939115)
                                                                      · refine ⟨96060570527446408673, ?_, ?_⟩
                                                                        · exact (by decide : ExactOddStep 1 64040380351630939115 96060570527446408673)
                                                                        · refine ⟨72045427895584806505, ?_, ?_⟩
                                                                          · exact (by decide : ExactOddStep 2 96060570527446408673 72045427895584806505)
                                                                          · refine ⟨54034070921688604879, ?_, ?_⟩
                                                                            · exact (by decide : ExactOddStep 2 72045427895584806505 54034070921688604879)
                                                                            · refine ⟨81051106382532907319, ?_, ?_⟩
                                                                              · exact (by decide : ExactOddStep 1 54034070921688604879 81051106382532907319)
                                                                              · refine ⟨121576659573799360979, ?_, ?_⟩
                                                                                · exact (by decide : ExactOddStep 1 81051106382532907319 121576659573799360979)
                                                                                · refine ⟨182364989360699041469, ?_, ?_⟩
                                                                                  · exact (by decide : ExactOddStep 1 121576659573799360979 182364989360699041469)
                                                                                  · refine ⟨68386871010262140551, ?_, ?_⟩
                                                                                    · exact (by decide : ExactOddStep 3 182364989360699041469 68386871010262140551)
                                                                                    · refine ⟨102580306515393210827, ?_, ?_⟩
                                                                                      · exact (by decide : ExactOddStep 1 68386871010262140551 102580306515393210827)
                                                                                      · refine ⟨153870459773089816241, ?_, ?_⟩
                                                                                        · exact (by decide : ExactOddStep 1 102580306515393210827 153870459773089816241)
                                                                                        · refine ⟨115402844829817362181, ?_, ?_⟩
                                                                                          · exact (by decide : ExactOddStep 2 153870459773089816241 115402844829817362181)
                                                                                          · refine ⟨21638033405590755409, ?_, ?_⟩
                                                                                            · exact (by decide : ExactOddStep 4 115402844829817362181 21638033405590755409)
                                                                                            · refine ⟨16228525054193066557, ?_, ?_⟩
                                                                                              · exact (by decide : ExactOddStep 2 21638033405590755409 16228525054193066557)
                                                                                              · refine ⟨6085696895322399959, ?_, ?_⟩
                                                                                                · exact (by decide : ExactOddStep 3 16228525054193066557 6085696895322399959)
                                                                                                · refine ⟨9128545342983599939, ?_, ?_⟩
                                                                                                  · exact (by decide : ExactOddStep 1 6085696895322399959 9128545342983599939)
                                                                                                  · refine ⟨13692818014475399909, ?_, ?_⟩
                                                                                                    · exact (by decide : ExactOddStep 1 9128545342983599939 13692818014475399909)
                                                                                                    · refine ⟨2567403377714137483, ?_, ?_⟩
                                                                                                      · exact (by decide : ExactOddStep 4 13692818014475399909 2567403377714137483)
                                                                                                      · rfl

/-- Every lift of family 12 descends after its exact accelerated word. -/
theorem family_12_all_lifts (q : Nat) :
    ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 2, 3, 1, 1, 4] (2882303879658078235 + q * 2 ^ 82) endpoint ∧
      endpoint < 2882303879658078235 + q * 2 ^ 82 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 2, 3, 1, 1, 4] family_12_trace (by decide) (by decide) (by decide) q

/-- Family 13: exact representative trace from the pinned input. -/
theorem family_13_trace : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 1, 10] 16140901182636818459 532498460412005551 := by
  simp only [WordTrace]
  refine ⟨24211351773955227689, ?_, ?_⟩
  · exact (by decide : ExactOddStep 1 16140901182636818459 24211351773955227689)
  · refine ⟨18158513830466420767, ?_, ?_⟩
    · exact (by decide : ExactOddStep 2 24211351773955227689 18158513830466420767)
    · refine ⟨27237770745699631151, ?_, ?_⟩
      · exact (by decide : ExactOddStep 1 18158513830466420767 27237770745699631151)
      · refine ⟨40856656118549446727, ?_, ?_⟩
        · exact (by decide : ExactOddStep 1 27237770745699631151 40856656118549446727)
        · refine ⟨61284984177824170091, ?_, ?_⟩
          · exact (by decide : ExactOddStep 1 40856656118549446727 61284984177824170091)
          · refine ⟨91927476266736255137, ?_, ?_⟩
            · exact (by decide : ExactOddStep 1 61284984177824170091 91927476266736255137)
            · refine ⟨68945607200052191353, ?_, ?_⟩
              · exact (by decide : ExactOddStep 2 91927476266736255137 68945607200052191353)
              · refine ⟨51709205400039143515, ?_, ?_⟩
                · exact (by decide : ExactOddStep 2 68945607200052191353 51709205400039143515)
                · refine ⟨77563808100058715273, ?_, ?_⟩
                  · exact (by decide : ExactOddStep 1 51709205400039143515 77563808100058715273)
                  · refine ⟨58172856075044036455, ?_, ?_⟩
                    · exact (by decide : ExactOddStep 2 77563808100058715273 58172856075044036455)
                    · refine ⟨87259284112566054683, ?_, ?_⟩
                      · exact (by decide : ExactOddStep 1 58172856075044036455 87259284112566054683)
                      · refine ⟨130888926168849082025, ?_, ?_⟩
                        · exact (by decide : ExactOddStep 1 87259284112566054683 130888926168849082025)
                        · refine ⟨98166694626636811519, ?_, ?_⟩
                          · exact (by decide : ExactOddStep 2 130888926168849082025 98166694626636811519)
                          · refine ⟨147250041939955217279, ?_, ?_⟩
                            · exact (by decide : ExactOddStep 1 98166694626636811519 147250041939955217279)
                            · refine ⟨220875062909932825919, ?_, ?_⟩
                              · exact (by decide : ExactOddStep 1 147250041939955217279 220875062909932825919)
                              · refine ⟨331312594364899238879, ?_, ?_⟩
                                · exact (by decide : ExactOddStep 1 220875062909932825919 331312594364899238879)
                                · refine ⟨496968891547348858319, ?_, ?_⟩
                                  · exact (by decide : ExactOddStep 1 331312594364899238879 496968891547348858319)
                                  · refine ⟨745453337321023287479, ?_, ?_⟩
                                    · exact (by decide : ExactOddStep 1 496968891547348858319 745453337321023287479)
                                    · refine ⟨1118180005981534931219, ?_, ?_⟩
                                      · exact (by decide : ExactOddStep 1 745453337321023287479 1118180005981534931219)
                                      · refine ⟨1677270008972302396829, ?_, ?_⟩
                                        · exact (by decide : ExactOddStep 1 1118180005981534931219 1677270008972302396829)
                                        · refine ⟨628976253364613398811, ?_, ?_⟩
                                          · exact (by decide : ExactOddStep 3 1677270008972302396829 628976253364613398811)
                                          · refine ⟨943464380046920098217, ?_, ?_⟩
                                            · exact (by decide : ExactOddStep 1 628976253364613398811 943464380046920098217)
                                            · refine ⟨707598285035190073663, ?_, ?_⟩
                                              · exact (by decide : ExactOddStep 2 943464380046920098217 707598285035190073663)
                                              · refine ⟨1061397427552785110495, ?_, ?_⟩
                                                · exact (by decide : ExactOddStep 1 707598285035190073663 1061397427552785110495)
                                                · refine ⟨1592096141329177665743, ?_, ?_⟩
                                                  · exact (by decide : ExactOddStep 1 1061397427552785110495 1592096141329177665743)
                                                  · refine ⟨2388144211993766498615, ?_, ?_⟩
                                                    · exact (by decide : ExactOddStep 1 1592096141329177665743 2388144211993766498615)
                                                    · refine ⟨3582216317990649747923, ?_, ?_⟩
                                                      · exact (by decide : ExactOddStep 1 2388144211993766498615 3582216317990649747923)
                                                      · refine ⟨5373324476985974621885, ?_, ?_⟩
                                                        · exact (by decide : ExactOddStep 1 3582216317990649747923 5373324476985974621885)
                                                        · refine ⟨2014996678869740483207, ?_, ?_⟩
                                                          · exact (by decide : ExactOddStep 3 5373324476985974621885 2014996678869740483207)
                                                          · refine ⟨3022495018304610724811, ?_, ?_⟩
                                                            · exact (by decide : ExactOddStep 1 2014996678869740483207 3022495018304610724811)
                                                            · refine ⟨4533742527456916087217, ?_, ?_⟩
                                                              · exact (by decide : ExactOddStep 1 3022495018304610724811 4533742527456916087217)
                                                              · refine ⟨3400306895592687065413, ?_, ?_⟩
                                                                · exact (by decide : ExactOddStep 2 4533742527456916087217 3400306895592687065413)
                                                                · refine ⟨637557542923628824765, ?_, ?_⟩
                                                                  · exact (by decide : ExactOddStep 4 3400306895592687065413 637557542923628824765)
                                                                  · refine ⟨239084078596360809287, ?_, ?_⟩
                                                                    · exact (by decide : ExactOddStep 3 637557542923628824765 239084078596360809287)
                                                                    · refine ⟨358626117894541213931, ?_, ?_⟩
                                                                      · exact (by decide : ExactOddStep 1 239084078596360809287 358626117894541213931)
                                                                      · refine ⟨537939176841811820897, ?_, ?_⟩
                                                                        · exact (by decide : ExactOddStep 1 358626117894541213931 537939176841811820897)
                                                                        · refine ⟨403454382631358865673, ?_, ?_⟩
                                                                          · exact (by decide : ExactOddStep 2 537939176841811820897 403454382631358865673)
                                                                          · refine ⟨302590786973519149255, ?_, ?_⟩
                                                                            · exact (by decide : ExactOddStep 2 403454382631358865673 302590786973519149255)
                                                                            · refine ⟨453886180460278723883, ?_, ?_⟩
                                                                              · exact (by decide : ExactOddStep 1 302590786973519149255 453886180460278723883)
                                                                              · refine ⟨680829270690418085825, ?_, ?_⟩
                                                                                · exact (by decide : ExactOddStep 1 453886180460278723883 680829270690418085825)
                                                                                · refine ⟨510621953017813564369, ?_, ?_⟩
                                                                                  · exact (by decide : ExactOddStep 2 680829270690418085825 510621953017813564369)
                                                                                  · refine ⟨382966464763360173277, ?_, ?_⟩
                                                                                    · exact (by decide : ExactOddStep 2 510621953017813564369 382966464763360173277)
                                                                                    · refine ⟨143612424286260064979, ?_, ?_⟩
                                                                                      · exact (by decide : ExactOddStep 3 382966464763360173277 143612424286260064979)
                                                                                      · refine ⟨215418636429390097469, ?_, ?_⟩
                                                                                        · exact (by decide : ExactOddStep 1 143612424286260064979 215418636429390097469)
                                                                                        · refine ⟨80781988661021286551, ?_, ?_⟩
                                                                                          · exact (by decide : ExactOddStep 3 215418636429390097469 80781988661021286551)
                                                                                          · refine ⟨121172982991531929827, ?_, ?_⟩
                                                                                            · exact (by decide : ExactOddStep 1 80781988661021286551 121172982991531929827)
                                                                                            · refine ⟨181759474487297894741, ?_, ?_⟩
                                                                                              · exact (by decide : ExactOddStep 1 121172982991531929827 181759474487297894741)
                                                                                              · refine ⟨532498460412005551, ?_, ?_⟩
                                                                                                · exact (by decide : ExactOddStep 10 181759474487297894741 532498460412005551)
                                                                                                · rfl

/-- Every lift of family 13 descends after its exact accelerated word. -/
theorem family_13_all_lifts (q : Nat) :
    ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 1, 10] (16140901182636818459 + q * 2 ^ 82) endpoint ∧
      endpoint < 16140901182636818459 + q * 2 ^ 82 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 1, 10] family_13_trace (by decide) (by decide) (by decide) q

/-- Family 14: exact representative trace from the pinned input. -/
theorem family_14_trace : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 3, 1, 2, 1, 3, 5] 576460870444384283 192555284898670313 := by
  simp only [WordTrace]
  refine ⟨864691305666576425, ?_, ?_⟩
  · exact (by decide : ExactOddStep 1 576460870444384283 864691305666576425)
  · refine ⟨648518479249932319, ?_, ?_⟩
    · exact (by decide : ExactOddStep 2 864691305666576425 648518479249932319)
    · refine ⟨972777718874898479, ?_, ?_⟩
      · exact (by decide : ExactOddStep 1 648518479249932319 972777718874898479)
      · refine ⟨1459166578312347719, ?_, ?_⟩
        · exact (by decide : ExactOddStep 1 972777718874898479 1459166578312347719)
        · refine ⟨2188749867468521579, ?_, ?_⟩
          · exact (by decide : ExactOddStep 1 1459166578312347719 2188749867468521579)
          · refine ⟨3283124801202782369, ?_, ?_⟩
            · exact (by decide : ExactOddStep 1 2188749867468521579 3283124801202782369)
            · refine ⟨2462343600902086777, ?_, ?_⟩
              · exact (by decide : ExactOddStep 2 3283124801202782369 2462343600902086777)
              · refine ⟨1846757700676565083, ?_, ?_⟩
                · exact (by decide : ExactOddStep 2 2462343600902086777 1846757700676565083)
                · refine ⟨2770136551014847625, ?_, ?_⟩
                  · exact (by decide : ExactOddStep 1 1846757700676565083 2770136551014847625)
                  · refine ⟨2077602413261135719, ?_, ?_⟩
                    · exact (by decide : ExactOddStep 2 2770136551014847625 2077602413261135719)
                    · refine ⟨3116403619891703579, ?_, ?_⟩
                      · exact (by decide : ExactOddStep 1 2077602413261135719 3116403619891703579)
                      · refine ⟨4674605429837555369, ?_, ?_⟩
                        · exact (by decide : ExactOddStep 1 3116403619891703579 4674605429837555369)
                        · refine ⟨3505954072378166527, ?_, ?_⟩
                          · exact (by decide : ExactOddStep 2 4674605429837555369 3505954072378166527)
                          · refine ⟨5258931108567249791, ?_, ?_⟩
                            · exact (by decide : ExactOddStep 1 3505954072378166527 5258931108567249791)
                            · refine ⟨7888396662850874687, ?_, ?_⟩
                              · exact (by decide : ExactOddStep 1 5258931108567249791 7888396662850874687)
                              · refine ⟨11832594994276312031, ?_, ?_⟩
                                · exact (by decide : ExactOddStep 1 7888396662850874687 11832594994276312031)
                                · refine ⟨17748892491414468047, ?_, ?_⟩
                                  · exact (by decide : ExactOddStep 1 11832594994276312031 17748892491414468047)
                                  · refine ⟨26623338737121702071, ?_, ?_⟩
                                    · exact (by decide : ExactOddStep 1 17748892491414468047 26623338737121702071)
                                    · refine ⟨39935008105682553107, ?_, ?_⟩
                                      · exact (by decide : ExactOddStep 1 26623338737121702071 39935008105682553107)
                                      · refine ⟨59902512158523829661, ?_, ?_⟩
                                        · exact (by decide : ExactOddStep 1 39935008105682553107 59902512158523829661)
                                        · refine ⟨22463442059446436123, ?_, ?_⟩
                                          · exact (by decide : ExactOddStep 3 59902512158523829661 22463442059446436123)
                                          · refine ⟨33695163089169654185, ?_, ?_⟩
                                            · exact (by decide : ExactOddStep 1 22463442059446436123 33695163089169654185)
                                            · refine ⟨25271372316877240639, ?_, ?_⟩
                                              · exact (by decide : ExactOddStep 2 33695163089169654185 25271372316877240639)
                                              · refine ⟨37907058475315860959, ?_, ?_⟩
                                                · exact (by decide : ExactOddStep 1 25271372316877240639 37907058475315860959)
                                                · refine ⟨56860587712973791439, ?_, ?_⟩
                                                  · exact (by decide : ExactOddStep 1 37907058475315860959 56860587712973791439)
                                                  · refine ⟨85290881569460687159, ?_, ?_⟩
                                                    · exact (by decide : ExactOddStep 1 56860587712973791439 85290881569460687159)
                                                    · refine ⟨127936322354191030739, ?_, ?_⟩
                                                      · exact (by decide : ExactOddStep 1 85290881569460687159 127936322354191030739)
                                                      · refine ⟨191904483531286546109, ?_, ?_⟩
                                                        · exact (by decide : ExactOddStep 1 127936322354191030739 191904483531286546109)
                                                        · refine ⟨71964181324232454791, ?_, ?_⟩
                                                          · exact (by decide : ExactOddStep 3 191904483531286546109 71964181324232454791)
                                                          · refine ⟨107946271986348682187, ?_, ?_⟩
                                                            · exact (by decide : ExactOddStep 1 71964181324232454791 107946271986348682187)
                                                            · refine ⟨161919407979523023281, ?_, ?_⟩
                                                              · exact (by decide : ExactOddStep 1 107946271986348682187 161919407979523023281)
                                                              · refine ⟨121439555984642267461, ?_, ?_⟩
                                                                · exact (by decide : ExactOddStep 2 161919407979523023281 121439555984642267461)
                                                                · refine ⟨22769916747120425149, ?_, ?_⟩
                                                                  · exact (by decide : ExactOddStep 4 121439555984642267461 22769916747120425149)
                                                                  · refine ⟨8538718780170159431, ?_, ?_⟩
                                                                    · exact (by decide : ExactOddStep 3 22769916747120425149 8538718780170159431)
                                                                    · refine ⟨12808078170255239147, ?_, ?_⟩
                                                                      · exact (by decide : ExactOddStep 1 8538718780170159431 12808078170255239147)
                                                                      · refine ⟨19212117255382858721, ?_, ?_⟩
                                                                        · exact (by decide : ExactOddStep 1 12808078170255239147 19212117255382858721)
                                                                        · refine ⟨14409087941537144041, ?_, ?_⟩
                                                                          · exact (by decide : ExactOddStep 2 19212117255382858721 14409087941537144041)
                                                                          · refine ⟨10806815956152858031, ?_, ?_⟩
                                                                            · exact (by decide : ExactOddStep 2 14409087941537144041 10806815956152858031)
                                                                            · refine ⟨16210223934229287047, ?_, ?_⟩
                                                                              · exact (by decide : ExactOddStep 1 10806815956152858031 16210223934229287047)
                                                                              · refine ⟨24315335901343930571, ?_, ?_⟩
                                                                                · exact (by decide : ExactOddStep 1 16210223934229287047 24315335901343930571)
                                                                                · refine ⟨36473003852015895857, ?_, ?_⟩
                                                                                  · exact (by decide : ExactOddStep 1 24315335901343930571 36473003852015895857)
                                                                                  · refine ⟨27354752889011921893, ?_, ?_⟩
                                                                                    · exact (by decide : ExactOddStep 2 36473003852015895857 27354752889011921893)
                                                                                    · refine ⟨5129016166689735355, ?_, ?_⟩
                                                                                      · exact (by decide : ExactOddStep 4 27354752889011921893 5129016166689735355)
                                                                                      · refine ⟨7693524250034603033, ?_, ?_⟩
                                                                                        · exact (by decide : ExactOddStep 1 5129016166689735355 7693524250034603033)
                                                                                        · refine ⟨5770143187525952275, ?_, ?_⟩
                                                                                          · exact (by decide : ExactOddStep 2 7693524250034603033 5770143187525952275)
                                                                                          · refine ⟨8655214781288928413, ?_, ?_⟩
                                                                                            · exact (by decide : ExactOddStep 1 5770143187525952275 8655214781288928413)
                                                                                            · refine ⟨3245705542983348155, ?_, ?_⟩
                                                                                              · exact (by decide : ExactOddStep 3 8655214781288928413 3245705542983348155)
                                                                                              · refine ⟨4868558314475022233, ?_, ?_⟩
                                                                                                · exact (by decide : ExactOddStep 1 3245705542983348155 4868558314475022233)
                                                                                                · refine ⟨3651418735856266675, ?_, ?_⟩
                                                                                                  · exact (by decide : ExactOddStep 2 4868558314475022233 3651418735856266675)
                                                                                                  · refine ⟨5477128103784400013, ?_, ?_⟩
                                                                                                    · exact (by decide : ExactOddStep 1 3651418735856266675 5477128103784400013)
                                                                                                    · refine ⟨2053923038919150005, ?_, ?_⟩
                                                                                                      · exact (by decide : ExactOddStep 3 5477128103784400013 2053923038919150005)
                                                                                                      · refine ⟨192555284898670313, ?_, ?_⟩
                                                                                                        · exact (by decide : ExactOddStep 5 2053923038919150005 192555284898670313)
                                                                                                        · rfl

/-- Every lift of family 14 descends after its exact accelerated word. -/
theorem family_14_all_lifts (q : Nat) :
    ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 3, 1, 2, 1, 3, 5] (576460870444384283 + q * 2 ^ 85) endpoint ∧
      endpoint < 576460870444384283 + q * 2 ^ 85 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 3, 1, 2, 1, 3, 5] family_14_trace (by decide) (by decide) (by decide) q

/-- Family 15: exact representative trace from the pinned input. -/
theorem family_15_trace : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 1, 2, 2, 2, 2, 2, 1, 2, 5] 6341068393478619163 3574306809999559835 := by
  simp only [WordTrace]
  refine ⟨9511602590217928745, ?_, ?_⟩
  · exact (by decide : ExactOddStep 1 6341068393478619163 9511602590217928745)
  · refine ⟨7133701942663446559, ?_, ?_⟩
    · exact (by decide : ExactOddStep 2 9511602590217928745 7133701942663446559)
    · refine ⟨10700552913995169839, ?_, ?_⟩
      · exact (by decide : ExactOddStep 1 7133701942663446559 10700552913995169839)
      · refine ⟨16050829370992754759, ?_, ?_⟩
        · exact (by decide : ExactOddStep 1 10700552913995169839 16050829370992754759)
        · refine ⟨24076244056489132139, ?_, ?_⟩
          · exact (by decide : ExactOddStep 1 16050829370992754759 24076244056489132139)
          · refine ⟨36114366084733698209, ?_, ?_⟩
            · exact (by decide : ExactOddStep 1 24076244056489132139 36114366084733698209)
            · refine ⟨27085774563550273657, ?_, ?_⟩
              · exact (by decide : ExactOddStep 2 36114366084733698209 27085774563550273657)
              · refine ⟨20314330922662705243, ?_, ?_⟩
                · exact (by decide : ExactOddStep 2 27085774563550273657 20314330922662705243)
                · refine ⟨30471496383994057865, ?_, ?_⟩
                  · exact (by decide : ExactOddStep 1 20314330922662705243 30471496383994057865)
                  · refine ⟨22853622287995543399, ?_, ?_⟩
                    · exact (by decide : ExactOddStep 2 30471496383994057865 22853622287995543399)
                    · refine ⟨34280433431993315099, ?_, ?_⟩
                      · exact (by decide : ExactOddStep 1 22853622287995543399 34280433431993315099)
                      · refine ⟨51420650147989972649, ?_, ?_⟩
                        · exact (by decide : ExactOddStep 1 34280433431993315099 51420650147989972649)
                        · refine ⟨38565487610992479487, ?_, ?_⟩
                          · exact (by decide : ExactOddStep 2 51420650147989972649 38565487610992479487)
                          · refine ⟨57848231416488719231, ?_, ?_⟩
                            · exact (by decide : ExactOddStep 1 38565487610992479487 57848231416488719231)
                            · refine ⟨86772347124733078847, ?_, ?_⟩
                              · exact (by decide : ExactOddStep 1 57848231416488719231 86772347124733078847)
                              · refine ⟨130158520687099618271, ?_, ?_⟩
                                · exact (by decide : ExactOddStep 1 86772347124733078847 130158520687099618271)
                                · refine ⟨195237781030649427407, ?_, ?_⟩
                                  · exact (by decide : ExactOddStep 1 130158520687099618271 195237781030649427407)
                                  · refine ⟨292856671545974141111, ?_, ?_⟩
                                    · exact (by decide : ExactOddStep 1 195237781030649427407 292856671545974141111)
                                    · refine ⟨439285007318961211667, ?_, ?_⟩
                                      · exact (by decide : ExactOddStep 1 292856671545974141111 439285007318961211667)
                                      · refine ⟨658927510978441817501, ?_, ?_⟩
                                        · exact (by decide : ExactOddStep 1 439285007318961211667 658927510978441817501)
                                        · refine ⟨247097816616915681563, ?_, ?_⟩
                                          · exact (by decide : ExactOddStep 3 658927510978441817501 247097816616915681563)
                                          · refine ⟨370646724925373522345, ?_, ?_⟩
                                            · exact (by decide : ExactOddStep 1 247097816616915681563 370646724925373522345)
                                            · refine ⟨277985043694030141759, ?_, ?_⟩
                                              · exact (by decide : ExactOddStep 2 370646724925373522345 277985043694030141759)
                                              · refine ⟨416977565541045212639, ?_, ?_⟩
                                                · exact (by decide : ExactOddStep 1 277985043694030141759 416977565541045212639)
                                                · refine ⟨625466348311567818959, ?_, ?_⟩
                                                  · exact (by decide : ExactOddStep 1 416977565541045212639 625466348311567818959)
                                                  · refine ⟨938199522467351728439, ?_, ?_⟩
                                                    · exact (by decide : ExactOddStep 1 625466348311567818959 938199522467351728439)
                                                    · refine ⟨1407299283701027592659, ?_, ?_⟩
                                                      · exact (by decide : ExactOddStep 1 938199522467351728439 1407299283701027592659)
                                                      · refine ⟨2110948925551541388989, ?_, ?_⟩
                                                        · exact (by decide : ExactOddStep 1 1407299283701027592659 2110948925551541388989)
                                                        · refine ⟨791605847081828020871, ?_, ?_⟩
                                                          · exact (by decide : ExactOddStep 3 2110948925551541388989 791605847081828020871)
                                                          · refine ⟨1187408770622742031307, ?_, ?_⟩
                                                            · exact (by decide : ExactOddStep 1 791605847081828020871 1187408770622742031307)
                                                            · refine ⟨1781113155934113046961, ?_, ?_⟩
                                                              · exact (by decide : ExactOddStep 1 1187408770622742031307 1781113155934113046961)
                                                              · refine ⟨1335834866950584785221, ?_, ?_⟩
                                                                · exact (by decide : ExactOddStep 2 1781113155934113046961 1335834866950584785221)
                                                                · refine ⟨250469037553234647229, ?_, ?_⟩
                                                                  · exact (by decide : ExactOddStep 4 1335834866950584785221 250469037553234647229)
                                                                  · refine ⟨93925889082462992711, ?_, ?_⟩
                                                                    · exact (by decide : ExactOddStep 3 250469037553234647229 93925889082462992711)
                                                                    · refine ⟨140888833623694489067, ?_, ?_⟩
                                                                      · exact (by decide : ExactOddStep 1 93925889082462992711 140888833623694489067)
                                                                      · refine ⟨211333250435541733601, ?_, ?_⟩
                                                                        · exact (by decide : ExactOddStep 1 140888833623694489067 211333250435541733601)
                                                                        · refine ⟨158499937826656300201, ?_, ?_⟩
                                                                          · exact (by decide : ExactOddStep 2 211333250435541733601 158499937826656300201)
                                                                          · refine ⟨118874953369992225151, ?_, ?_⟩
                                                                            · exact (by decide : ExactOddStep 2 158499937826656300201 118874953369992225151)
                                                                            · refine ⟨178312430054988337727, ?_, ?_⟩
                                                                              · exact (by decide : ExactOddStep 1 118874953369992225151 178312430054988337727)
                                                                              · refine ⟨267468645082482506591, ?_, ?_⟩
                                                                                · exact (by decide : ExactOddStep 1 178312430054988337727 267468645082482506591)
                                                                                · refine ⟨401202967623723759887, ?_, ?_⟩
                                                                                  · exact (by decide : ExactOddStep 1 267468645082482506591 401202967623723759887)
                                                                                  · refine ⟨601804451435585639831, ?_, ?_⟩
                                                                                    · exact (by decide : ExactOddStep 1 401202967623723759887 601804451435585639831)
                                                                                    · refine ⟨902706677153378459747, ?_, ?_⟩
                                                                                      · exact (by decide : ExactOddStep 1 601804451435585639831 902706677153378459747)
                                                                                      · refine ⟨1354060015730067689621, ?_, ?_⟩
                                                                                        · exact (by decide : ExactOddStep 1 902706677153378459747 1354060015730067689621)
                                                                                        · refine ⟨63471563237346922951, ?_, ?_⟩
                                                                                          · exact (by decide : ExactOddStep 6 1354060015730067689621 63471563237346922951)
                                                                                          · refine ⟨95207344856020384427, ?_, ?_⟩
                                                                                            · exact (by decide : ExactOddStep 1 63471563237346922951 95207344856020384427)
                                                                                            · refine ⟨142811017284030576641, ?_, ?_⟩
                                                                                              · exact (by decide : ExactOddStep 1 95207344856020384427 142811017284030576641)
                                                                                              · refine ⟨107108262963022932481, ?_, ?_⟩
                                                                                                · exact (by decide : ExactOddStep 2 142811017284030576641 107108262963022932481)
                                                                                                · refine ⟨80331197222267199361, ?_, ?_⟩
                                                                                                  · exact (by decide : ExactOddStep 2 107108262963022932481 80331197222267199361)
                                                                                                  · refine ⟨60248397916700399521, ?_, ?_⟩
                                                                                                    · exact (by decide : ExactOddStep 2 80331197222267199361 60248397916700399521)
                                                                                                    · refine ⟨45186298437525299641, ?_, ?_⟩
                                                                                                      · exact (by decide : ExactOddStep 2 60248397916700399521 45186298437525299641)
                                                                                                      · refine ⟨33889723828143974731, ?_, ?_⟩
                                                                                                        · exact (by decide : ExactOddStep 2 45186298437525299641 33889723828143974731)
                                                                                                        · refine ⟨50834585742215962097, ?_, ?_⟩
                                                                                                          · exact (by decide : ExactOddStep 1 33889723828143974731 50834585742215962097)
                                                                                                          · refine ⟨38125939306661971573, ?_, ?_⟩
                                                                                                            · exact (by decide : ExactOddStep 2 50834585742215962097 38125939306661971573)
                                                                                                            · refine ⟨3574306809999559835, ?_, ?_⟩
                                                                                                              · exact (by decide : ExactOddStep 5 38125939306661971573 3574306809999559835)
                                                                                                              · rfl

/-- Every lift of family 15 descends after its exact accelerated word. -/
theorem family_15_all_lifts (q : Nat) :
    ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 1, 2, 2, 2, 2, 2, 1, 2, 5] (6341068393478619163 + q * 2 ^ 89) endpoint ∧
      endpoint < 6341068393478619163 + q * 2 ^ 89 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 1, 2, 2, 2, 2, 2, 1, 2, 5] family_15_trace (by decide) (by decide) (by decide) q

/-- Family 16: exact representative trace from the pinned input. -/
theorem family_16_trace : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 1, 1, 1, 1, 2, 2, 1, 2, 3, 4] 12105675916512854043 6823676576732613517 := by
  simp only [WordTrace]
  refine ⟨18158513874769281065, ?_, ?_⟩
  · exact (by decide : ExactOddStep 1 12105675916512854043 18158513874769281065)
  · refine ⟨13618885406076960799, ?_, ?_⟩
    · exact (by decide : ExactOddStep 2 18158513874769281065 13618885406076960799)
    · refine ⟨20428328109115441199, ?_, ?_⟩
      · exact (by decide : ExactOddStep 1 13618885406076960799 20428328109115441199)
      · refine ⟨30642492163673161799, ?_, ?_⟩
        · exact (by decide : ExactOddStep 1 20428328109115441199 30642492163673161799)
        · refine ⟨45963738245509742699, ?_, ?_⟩
          · exact (by decide : ExactOddStep 1 30642492163673161799 45963738245509742699)
          · refine ⟨68945607368264614049, ?_, ?_⟩
            · exact (by decide : ExactOddStep 1 45963738245509742699 68945607368264614049)
            · refine ⟨51709205526198460537, ?_, ?_⟩
              · exact (by decide : ExactOddStep 2 68945607368264614049 51709205526198460537)
              · refine ⟨38781904144648845403, ?_, ?_⟩
                · exact (by decide : ExactOddStep 2 51709205526198460537 38781904144648845403)
                · refine ⟨58172856216973268105, ?_, ?_⟩
                  · exact (by decide : ExactOddStep 1 38781904144648845403 58172856216973268105)
                  · refine ⟨43629642162729951079, ?_, ?_⟩
                    · exact (by decide : ExactOddStep 2 58172856216973268105 43629642162729951079)
                    · refine ⟨65444463244094926619, ?_, ?_⟩
                      · exact (by decide : ExactOddStep 1 43629642162729951079 65444463244094926619)
                      · refine ⟨98166694866142389929, ?_, ?_⟩
                        · exact (by decide : ExactOddStep 1 65444463244094926619 98166694866142389929)
                        · refine ⟨73625021149606792447, ?_, ?_⟩
                          · exact (by decide : ExactOddStep 2 98166694866142389929 73625021149606792447)
                          · refine ⟨110437531724410188671, ?_, ?_⟩
                            · exact (by decide : ExactOddStep 1 73625021149606792447 110437531724410188671)
                            · refine ⟨165656297586615283007, ?_, ?_⟩
                              · exact (by decide : ExactOddStep 1 110437531724410188671 165656297586615283007)
                              · refine ⟨248484446379922924511, ?_, ?_⟩
                                · exact (by decide : ExactOddStep 1 165656297586615283007 248484446379922924511)
                                · refine ⟨372726669569884386767, ?_, ?_⟩
                                  · exact (by decide : ExactOddStep 1 248484446379922924511 372726669569884386767)
                                  · refine ⟨559090004354826580151, ?_, ?_⟩
                                    · exact (by decide : ExactOddStep 1 372726669569884386767 559090004354826580151)
                                    · refine ⟨838635006532239870227, ?_, ?_⟩
                                      · exact (by decide : ExactOddStep 1 559090004354826580151 838635006532239870227)
                                      · refine ⟨1257952509798359805341, ?_, ?_⟩
                                        · exact (by decide : ExactOddStep 1 838635006532239870227 1257952509798359805341)
                                        · refine ⟨471732191174384927003, ?_, ?_⟩
                                          · exact (by decide : ExactOddStep 3 1257952509798359805341 471732191174384927003)
                                          · refine ⟨707598286761577390505, ?_, ?_⟩
                                            · exact (by decide : ExactOddStep 1 471732191174384927003 707598286761577390505)
                                            · refine ⟨530698715071183042879, ?_, ?_⟩
                                              · exact (by decide : ExactOddStep 2 707598286761577390505 530698715071183042879)
                                              · refine ⟨796048072606774564319, ?_, ?_⟩
                                                · exact (by decide : ExactOddStep 1 530698715071183042879 796048072606774564319)
                                                · refine ⟨1194072108910161846479, ?_, ?_⟩
                                                  · exact (by decide : ExactOddStep 1 796048072606774564319 1194072108910161846479)
                                                  · refine ⟨1791108163365242769719, ?_, ?_⟩
                                                    · exact (by decide : ExactOddStep 1 1194072108910161846479 1791108163365242769719)
                                                    · refine ⟨2686662245047864154579, ?_, ?_⟩
                                                      · exact (by decide : ExactOddStep 1 1791108163365242769719 2686662245047864154579)
                                                      · refine ⟨4029993367571796231869, ?_, ?_⟩
                                                        · exact (by decide : ExactOddStep 1 2686662245047864154579 4029993367571796231869)
                                                        · refine ⟨1511247512839423586951, ?_, ?_⟩
                                                          · exact (by decide : ExactOddStep 3 4029993367571796231869 1511247512839423586951)
                                                          · refine ⟨2266871269259135380427, ?_, ?_⟩
                                                            · exact (by decide : ExactOddStep 1 1511247512839423586951 2266871269259135380427)
                                                            · refine ⟨3400306903888703070641, ?_, ?_⟩
                                                              · exact (by decide : ExactOddStep 1 2266871269259135380427 3400306903888703070641)
                                                              · refine ⟨2550230177916527302981, ?_, ?_⟩
                                                                · exact (by decide : ExactOddStep 2 3400306903888703070641 2550230177916527302981)
                                                                · refine ⟨478168158359348869309, ?_, ?_⟩
                                                                  · exact (by decide : ExactOddStep 4 2550230177916527302981 478168158359348869309)
                                                                  · refine ⟨179313059384755825991, ?_, ?_⟩
                                                                    · exact (by decide : ExactOddStep 3 478168158359348869309 179313059384755825991)
                                                                    · refine ⟨268969589077133738987, ?_, ?_⟩
                                                                      · exact (by decide : ExactOddStep 1 179313059384755825991 268969589077133738987)
                                                                      · refine ⟨403454383615700608481, ?_, ?_⟩
                                                                        · exact (by decide : ExactOddStep 1 268969589077133738987 403454383615700608481)
                                                                        · refine ⟨302590787711775456361, ?_, ?_⟩
                                                                          · exact (by decide : ExactOddStep 2 403454383615700608481 302590787711775456361)
                                                                          · refine ⟨226943090783831592271, ?_, ?_⟩
                                                                            · exact (by decide : ExactOddStep 2 302590787711775456361 226943090783831592271)
                                                                            · refine ⟨340414636175747388407, ?_, ?_⟩
                                                                              · exact (by decide : ExactOddStep 1 226943090783831592271 340414636175747388407)
                                                                              · refine ⟨510621954263621082611, ?_, ?_⟩
                                                                                · exact (by decide : ExactOddStep 1 340414636175747388407 510621954263621082611)
                                                                                · refine ⟨765932931395431623917, ?_, ?_⟩
                                                                                  · exact (by decide : ExactOddStep 1 510621954263621082611 765932931395431623917)
                                                                                  · refine ⟨287224849273286858969, ?_, ?_⟩
                                                                                    · exact (by decide : ExactOddStep 3 765932931395431623917 287224849273286858969)
                                                                                    · refine ⟨215418636954965144227, ?_, ?_⟩
                                                                                      · exact (by decide : ExactOddStep 2 287224849273286858969 215418636954965144227)
                                                                                      · refine ⟨323127955432447716341, ?_, ?_⟩
                                                                                        · exact (by decide : ExactOddStep 1 215418636954965144227 323127955432447716341)
                                                                                        · refine ⟨30293245821791973407, ?_, ?_⟩
                                                                                          · exact (by decide : ExactOddStep 5 323127955432447716341 30293245821791973407)
                                                                                          · refine ⟨45439868732687960111, ?_, ?_⟩
                                                                                            · exact (by decide : ExactOddStep 1 30293245821791973407 45439868732687960111)
                                                                                            · refine ⟨68159803099031940167, ?_, ?_⟩
                                                                                              · exact (by decide : ExactOddStep 1 45439868732687960111 68159803099031940167)
                                                                                              · refine ⟨102239704648547910251, ?_, ?_⟩
                                                                                                · exact (by decide : ExactOddStep 1 68159803099031940167 102239704648547910251)
                                                                                                · refine ⟨153359556972821865377, ?_, ?_⟩
                                                                                                  · exact (by decide : ExactOddStep 1 102239704648547910251 153359556972821865377)
                                                                                                  · refine ⟨115019667729616399033, ?_, ?_⟩
                                                                                                    · exact (by decide : ExactOddStep 2 153359556972821865377 115019667729616399033)
                                                                                                    · refine ⟨86264750797212299275, ?_, ?_⟩
                                                                                                      · exact (by decide : ExactOddStep 2 115019667729616399033 86264750797212299275)
                                                                                                      · refine ⟨129397126195818448913, ?_, ?_⟩
                                                                                                        · exact (by decide : ExactOddStep 1 86264750797212299275 129397126195818448913)
                                                                                                        · refine ⟨97047844646863836685, ?_, ?_⟩
                                                                                                          · exact (by decide : ExactOddStep 2 129397126195818448913 97047844646863836685)
                                                                                                          · refine ⟨36392941742573938757, ?_, ?_⟩
                                                                                                            · exact (by decide : ExactOddStep 3 97047844646863836685 36392941742573938757)
                                                                                                            · refine ⟨6823676576732613517, ?_, ?_⟩
                                                                                                              · exact (by decide : ExactOddStep 4 36392941742573938757 6823676576732613517)
                                                                                                              · rfl

/-- Every lift of family 16 descends after its exact accelerated word. -/
theorem family_16_all_lifts (q : Nat) :
    ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 1, 1, 1, 1, 2, 2, 1, 2, 3, 4] (12105675916512854043 + q * 2 ^ 89) endpoint ∧
      endpoint < 12105675916512854043 + q * 2 ^ 89 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 1, 1, 1, 1, 2, 2, 1, 2, 3, 4] family_16_trace (by decide) (by decide) (by decide) q

/-- Family 17: exact representative trace from the pinned input. -/
theorem family_17_trace : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 3, 2, 1, 1, 2, 4, 1, 1, 4, 2] 10952754411906007067 9260703935079004171 := by
  simp only [WordTrace]
  refine ⟨16429131617859010601, ?_, ?_⟩
  · exact (by decide : ExactOddStep 1 10952754411906007067 16429131617859010601)
  · refine ⟨12321848713394257951, ?_, ?_⟩
    · exact (by decide : ExactOddStep 2 16429131617859010601 12321848713394257951)
    · refine ⟨18482773070091386927, ?_, ?_⟩
      · exact (by decide : ExactOddStep 1 12321848713394257951 18482773070091386927)
      · refine ⟨27724159605137080391, ?_, ?_⟩
        · exact (by decide : ExactOddStep 1 18482773070091386927 27724159605137080391)
        · refine ⟨41586239407705620587, ?_, ?_⟩
          · exact (by decide : ExactOddStep 1 27724159605137080391 41586239407705620587)
          · refine ⟨62379359111558430881, ?_, ?_⟩
            · exact (by decide : ExactOddStep 1 41586239407705620587 62379359111558430881)
            · refine ⟨46784519333668823161, ?_, ?_⟩
              · exact (by decide : ExactOddStep 2 62379359111558430881 46784519333668823161)
              · refine ⟨35088389500251617371, ?_, ?_⟩
                · exact (by decide : ExactOddStep 2 46784519333668823161 35088389500251617371)
                · refine ⟨52632584250377426057, ?_, ?_⟩
                  · exact (by decide : ExactOddStep 1 35088389500251617371 52632584250377426057)
                  · refine ⟨39474438187783069543, ?_, ?_⟩
                    · exact (by decide : ExactOddStep 2 52632584250377426057 39474438187783069543)
                    · refine ⟨59211657281674604315, ?_, ?_⟩
                      · exact (by decide : ExactOddStep 1 39474438187783069543 59211657281674604315)
                      · refine ⟨88817485922511906473, ?_, ?_⟩
                        · exact (by decide : ExactOddStep 1 59211657281674604315 88817485922511906473)
                        · refine ⟨66613114441883929855, ?_, ?_⟩
                          · exact (by decide : ExactOddStep 2 88817485922511906473 66613114441883929855)
                          · refine ⟨99919671662825894783, ?_, ?_⟩
                            · exact (by decide : ExactOddStep 1 66613114441883929855 99919671662825894783)
                            · refine ⟨149879507494238842175, ?_, ?_⟩
                              · exact (by decide : ExactOddStep 1 99919671662825894783 149879507494238842175)
                              · refine ⟨224819261241358263263, ?_, ?_⟩
                                · exact (by decide : ExactOddStep 1 149879507494238842175 224819261241358263263)
                                · refine ⟨337228891862037394895, ?_, ?_⟩
                                  · exact (by decide : ExactOddStep 1 224819261241358263263 337228891862037394895)
                                  · refine ⟨505843337793056092343, ?_, ?_⟩
                                    · exact (by decide : ExactOddStep 1 337228891862037394895 505843337793056092343)
                                    · refine ⟨758765006689584138515, ?_, ?_⟩
                                      · exact (by decide : ExactOddStep 1 505843337793056092343 758765006689584138515)
                                      · refine ⟨1138147510034376207773, ?_, ?_⟩
                                        · exact (by decide : ExactOddStep 1 758765006689584138515 1138147510034376207773)
                                        · refine ⟨426805316262891077915, ?_, ?_⟩
                                          · exact (by decide : ExactOddStep 3 1138147510034376207773 426805316262891077915)
                                          · refine ⟨640207974394336616873, ?_, ?_⟩
                                            · exact (by decide : ExactOddStep 1 426805316262891077915 640207974394336616873)
                                            · refine ⟨480155980795752462655, ?_, ?_⟩
                                              · exact (by decide : ExactOddStep 2 640207974394336616873 480155980795752462655)
                                              · refine ⟨720233971193628693983, ?_, ?_⟩
                                                · exact (by decide : ExactOddStep 1 480155980795752462655 720233971193628693983)
                                                · refine ⟨1080350956790443040975, ?_, ?_⟩
                                                  · exact (by decide : ExactOddStep 1 720233971193628693983 1080350956790443040975)
                                                  · refine ⟨1620526435185664561463, ?_, ?_⟩
                                                    · exact (by decide : ExactOddStep 1 1080350956790443040975 1620526435185664561463)
                                                    · refine ⟨2430789652778496842195, ?_, ?_⟩
                                                      · exact (by decide : ExactOddStep 1 1620526435185664561463 2430789652778496842195)
                                                      · refine ⟨3646184479167745263293, ?_, ?_⟩
                                                        · exact (by decide : ExactOddStep 1 2430789652778496842195 3646184479167745263293)
                                                        · refine ⟨1367319179687904473735, ?_, ?_⟩
                                                          · exact (by decide : ExactOddStep 3 3646184479167745263293 1367319179687904473735)
                                                          · refine ⟨2050978769531856710603, ?_, ?_⟩
                                                            · exact (by decide : ExactOddStep 1 1367319179687904473735 2050978769531856710603)
                                                            · refine ⟨3076468154297785065905, ?_, ?_⟩
                                                              · exact (by decide : ExactOddStep 1 2050978769531856710603 3076468154297785065905)
                                                              · refine ⟨2307351115723338799429, ?_, ?_⟩
                                                                · exact (by decide : ExactOddStep 2 3076468154297785065905 2307351115723338799429)
                                                                · refine ⟨432628334198126024893, ?_, ?_⟩
                                                                  · exact (by decide : ExactOddStep 4 2307351115723338799429 432628334198126024893)
                                                                  · refine ⟨162235625324297259335, ?_, ?_⟩
                                                                    · exact (by decide : ExactOddStep 3 432628334198126024893 162235625324297259335)
                                                                    · refine ⟨243353437986445889003, ?_, ?_⟩
                                                                      · exact (by decide : ExactOddStep 1 162235625324297259335 243353437986445889003)
                                                                      · refine ⟨365030156979668833505, ?_, ?_⟩
                                                                        · exact (by decide : ExactOddStep 1 243353437986445889003 365030156979668833505)
                                                                        · refine ⟨273772617734751625129, ?_, ?_⟩
                                                                          · exact (by decide : ExactOddStep 2 365030156979668833505 273772617734751625129)
                                                                          · refine ⟨205329463301063718847, ?_, ?_⟩
                                                                            · exact (by decide : ExactOddStep 2 273772617734751625129 205329463301063718847)
                                                                            · refine ⟨307994194951595578271, ?_, ?_⟩
                                                                              · exact (by decide : ExactOddStep 1 205329463301063718847 307994194951595578271)
                                                                              · refine ⟨461991292427393367407, ?_, ?_⟩
                                                                                · exact (by decide : ExactOddStep 1 307994194951595578271 461991292427393367407)
                                                                                · refine ⟨692986938641090051111, ?_, ?_⟩
                                                                                  · exact (by decide : ExactOddStep 1 461991292427393367407 692986938641090051111)
                                                                                  · refine ⟨1039480407961635076667, ?_, ?_⟩
                                                                                    · exact (by decide : ExactOddStep 1 692986938641090051111 1039480407961635076667)
                                                                                    · refine ⟨1559220611942452615001, ?_, ?_⟩
                                                                                      · exact (by decide : ExactOddStep 1 1039480407961635076667 1559220611942452615001)
                                                                                      · refine ⟨1169415458956839461251, ?_, ?_⟩
                                                                                        · exact (by decide : ExactOddStep 2 1559220611942452615001 1169415458956839461251)
                                                                                        · refine ⟨1754123188435259191877, ?_, ?_⟩
                                                                                          · exact (by decide : ExactOddStep 1 1169415458956839461251 1754123188435259191877)
                                                                                          · refine ⟨328898097831611098477, ?_, ?_⟩
                                                                                            · exact (by decide : ExactOddStep 4 1754123188435259191877 328898097831611098477)
                                                                                            · refine ⟨123336786686854161929, ?_, ?_⟩
                                                                                              · exact (by decide : ExactOddStep 3 328898097831611098477 123336786686854161929)
                                                                                              · refine ⟨92502590015140621447, ?_, ?_⟩
                                                                                                · exact (by decide : ExactOddStep 2 123336786686854161929 92502590015140621447)
                                                                                                · refine ⟨138753885022710932171, ?_, ?_⟩
                                                                                                  · exact (by decide : ExactOddStep 1 92502590015140621447 138753885022710932171)
                                                                                                  · refine ⟨208130827534066398257, ?_, ?_⟩
                                                                                                    · exact (by decide : ExactOddStep 1 138753885022710932171 208130827534066398257)
                                                                                                    · refine ⟨156098120650549798693, ?_, ?_⟩
                                                                                                      · exact (by decide : ExactOddStep 2 208130827534066398257 156098120650549798693)
                                                                                                      · refine ⟨29268397621978087255, ?_, ?_⟩
                                                                                                        · exact (by decide : ExactOddStep 4 156098120650549798693 29268397621978087255)
                                                                                                        · refine ⟨43902596432967130883, ?_, ?_⟩
                                                                                                          · exact (by decide : ExactOddStep 1 29268397621978087255 43902596432967130883)
                                                                                                          · refine ⟨65853894649450696325, ?_, ?_⟩
                                                                                                            · exact (by decide : ExactOddStep 1 43902596432967130883 65853894649450696325)
                                                                                                            · refine ⟨12347605246772005561, ?_, ?_⟩
                                                                                                              · exact (by decide : ExactOddStep 4 65853894649450696325 12347605246772005561)
                                                                                                              · refine ⟨9260703935079004171, ?_, ?_⟩
                                                                                                                · exact (by decide : ExactOddStep 2 12347605246772005561 9260703935079004171)
                                                                                                                · rfl

/-- Every lift of family 17 descends after its exact accelerated word. -/
theorem family_17_all_lifts (q : Nat) :
    ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 3, 2, 1, 1, 2, 4, 1, 1, 4, 2] (10952754411906007067 + q * 2 ^ 90) endpoint ∧
      endpoint < 10952754411906007067 + q * 2 ^ 90 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 3, 2, 1, 1, 2, 4, 1, 1, 4, 2] family_17_trace (by decide) (by decide) (by decide) q

/-- Family 18: exact representative trace from the pinned input. -/
theorem family_18_trace : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 2, 2, 1, 1, 1, 4, 1, 3, 4] 14987979678029971483 4224180730049570179 := by
  simp only [WordTrace]
  refine ⟨22481969517044957225, ?_, ?_⟩
  · exact (by decide : ExactOddStep 1 14987979678029971483 22481969517044957225)
  · refine ⟨16861477137783717919, ?_, ?_⟩
    · exact (by decide : ExactOddStep 2 22481969517044957225 16861477137783717919)
    · refine ⟨25292215706675576879, ?_, ?_⟩
      · exact (by decide : ExactOddStep 1 16861477137783717919 25292215706675576879)
      · refine ⟨37938323560013365319, ?_, ?_⟩
        · exact (by decide : ExactOddStep 1 25292215706675576879 37938323560013365319)
        · refine ⟨56907485340020047979, ?_, ?_⟩
          · exact (by decide : ExactOddStep 1 37938323560013365319 56907485340020047979)
          · refine ⟨85361228010030071969, ?_, ?_⟩
            · exact (by decide : ExactOddStep 1 56907485340020047979 85361228010030071969)
            · refine ⟨64020921007522553977, ?_, ?_⟩
              · exact (by decide : ExactOddStep 2 85361228010030071969 64020921007522553977)
              · refine ⟨48015690755641915483, ?_, ?_⟩
                · exact (by decide : ExactOddStep 2 64020921007522553977 48015690755641915483)
                · refine ⟨72023536133462873225, ?_, ?_⟩
                  · exact (by decide : ExactOddStep 1 48015690755641915483 72023536133462873225)
                  · refine ⟨54017652100097154919, ?_, ?_⟩
                    · exact (by decide : ExactOddStep 2 72023536133462873225 54017652100097154919)
                    · refine ⟨81026478150145732379, ?_, ?_⟩
                      · exact (by decide : ExactOddStep 1 54017652100097154919 81026478150145732379)
                      · refine ⟨121539717225218598569, ?_, ?_⟩
                        · exact (by decide : ExactOddStep 1 81026478150145732379 121539717225218598569)
                        · refine ⟨91154787918913948927, ?_, ?_⟩
                          · exact (by decide : ExactOddStep 2 121539717225218598569 91154787918913948927)
                          · refine ⟨136732181878370923391, ?_, ?_⟩
                            · exact (by decide : ExactOddStep 1 91154787918913948927 136732181878370923391)
                            · refine ⟨205098272817556385087, ?_, ?_⟩
                              · exact (by decide : ExactOddStep 1 136732181878370923391 205098272817556385087)
                              · refine ⟨307647409226334577631, ?_, ?_⟩
                                · exact (by decide : ExactOddStep 1 205098272817556385087 307647409226334577631)
                                · refine ⟨461471113839501866447, ?_, ?_⟩
                                  · exact (by decide : ExactOddStep 1 307647409226334577631 461471113839501866447)
                                  · refine ⟨692206670759252799671, ?_, ?_⟩
                                    · exact (by decide : ExactOddStep 1 461471113839501866447 692206670759252799671)
                                    · refine ⟨1038310006138879199507, ?_, ?_⟩
                                      · exact (by decide : ExactOddStep 1 692206670759252799671 1038310006138879199507)
                                      · refine ⟨1557465009208318799261, ?_, ?_⟩
                                        · exact (by decide : ExactOddStep 1 1038310006138879199507 1557465009208318799261)
                                        · refine ⟨584049378453119549723, ?_, ?_⟩
                                          · exact (by decide : ExactOddStep 3 1557465009208318799261 584049378453119549723)
                                          · refine ⟨876074067679679324585, ?_, ?_⟩
                                            · exact (by decide : ExactOddStep 1 584049378453119549723 876074067679679324585)
                                            · refine ⟨657055550759759493439, ?_, ?_⟩
                                              · exact (by decide : ExactOddStep 2 876074067679679324585 657055550759759493439)
                                              · refine ⟨985583326139639240159, ?_, ?_⟩
                                                · exact (by decide : ExactOddStep 1 657055550759759493439 985583326139639240159)
                                                · refine ⟨1478374989209458860239, ?_, ?_⟩
                                                  · exact (by decide : ExactOddStep 1 985583326139639240159 1478374989209458860239)
                                                  · refine ⟨2217562483814188290359, ?_, ?_⟩
                                                    · exact (by decide : ExactOddStep 1 1478374989209458860239 2217562483814188290359)
                                                    · refine ⟨3326343725721282435539, ?_, ?_⟩
                                                      · exact (by decide : ExactOddStep 1 2217562483814188290359 3326343725721282435539)
                                                      · refine ⟨4989515588581923653309, ?_, ?_⟩
                                                        · exact (by decide : ExactOddStep 1 3326343725721282435539 4989515588581923653309)
                                                        · refine ⟨1871068345718221369991, ?_, ?_⟩
                                                          · exact (by decide : ExactOddStep 3 4989515588581923653309 1871068345718221369991)
                                                          · refine ⟨2806602518577332054987, ?_, ?_⟩
                                                            · exact (by decide : ExactOddStep 1 1871068345718221369991 2806602518577332054987)
                                                            · refine ⟨4209903777865998082481, ?_, ?_⟩
                                                              · exact (by decide : ExactOddStep 1 2806602518577332054987 4209903777865998082481)
                                                              · refine ⟨3157427833399498561861, ?_, ?_⟩
                                                                · exact (by decide : ExactOddStep 2 4209903777865998082481 3157427833399498561861)
                                                                · refine ⟨592017718762405980349, ?_, ?_⟩
                                                                  · exact (by decide : ExactOddStep 4 3157427833399498561861 592017718762405980349)
                                                                  · refine ⟨222006644535902242631, ?_, ?_⟩
                                                                    · exact (by decide : ExactOddStep 3 592017718762405980349 222006644535902242631)
                                                                    · refine ⟨333009966803853363947, ?_, ?_⟩
                                                                      · exact (by decide : ExactOddStep 1 222006644535902242631 333009966803853363947)
                                                                      · refine ⟨499514950205780045921, ?_, ?_⟩
                                                                        · exact (by decide : ExactOddStep 1 333009966803853363947 499514950205780045921)
                                                                        · refine ⟨374636212654335034441, ?_, ?_⟩
                                                                          · exact (by decide : ExactOddStep 2 499514950205780045921 374636212654335034441)
                                                                          · refine ⟨280977159490751275831, ?_, ?_⟩
                                                                            · exact (by decide : ExactOddStep 2 374636212654335034441 280977159490751275831)
                                                                            · refine ⟨421465739236126913747, ?_, ?_⟩
                                                                              · exact (by decide : ExactOddStep 1 280977159490751275831 421465739236126913747)
                                                                              · refine ⟨632198608854190370621, ?_, ?_⟩
                                                                                · exact (by decide : ExactOddStep 1 421465739236126913747 632198608854190370621)
                                                                                · refine ⟨237074478320321388983, ?_, ?_⟩
                                                                                  · exact (by decide : ExactOddStep 3 632198608854190370621 237074478320321388983)
                                                                                  · refine ⟨355611717480482083475, ?_, ?_⟩
                                                                                    · exact (by decide : ExactOddStep 1 237074478320321388983 355611717480482083475)
                                                                                    · refine ⟨533417576220723125213, ?_, ?_⟩
                                                                                      · exact (by decide : ExactOddStep 1 355611717480482083475 533417576220723125213)
                                                                                      · refine ⟨200031591082771171955, ?_, ?_⟩
                                                                                        · exact (by decide : ExactOddStep 3 533417576220723125213 200031591082771171955)
                                                                                        · refine ⟨300047386624156757933, ?_, ?_⟩
                                                                                          · exact (by decide : ExactOddStep 1 200031591082771171955 300047386624156757933)
                                                                                          · refine ⟨112517769984058784225, ?_, ?_⟩
                                                                                            · exact (by decide : ExactOddStep 3 300047386624156757933 112517769984058784225)
                                                                                            · refine ⟨84388327488044088169, ?_, ?_⟩
                                                                                              · exact (by decide : ExactOddStep 2 112517769984058784225 84388327488044088169)
                                                                                              · refine ⟨63291245616033066127, ?_, ?_⟩
                                                                                                · exact (by decide : ExactOddStep 2 84388327488044088169 63291245616033066127)
                                                                                                · refine ⟨94936868424049599191, ?_, ?_⟩
                                                                                                  · exact (by decide : ExactOddStep 1 63291245616033066127 94936868424049599191)
                                                                                                  · refine ⟨142405302636074398787, ?_, ?_⟩
                                                                                                    · exact (by decide : ExactOddStep 1 94936868424049599191 142405302636074398787)
                                                                                                    · refine ⟨213607953954111598181, ?_, ?_⟩
                                                                                                      · exact (by decide : ExactOddStep 1 142405302636074398787 213607953954111598181)
                                                                                                      · refine ⟨40051491366395924659, ?_, ?_⟩
                                                                                                        · exact (by decide : ExactOddStep 4 213607953954111598181 40051491366395924659)
                                                                                                        · refine ⟨60077237049593886989, ?_, ?_⟩
                                                                                                          · exact (by decide : ExactOddStep 1 40051491366395924659 60077237049593886989)
                                                                                                          · refine ⟨22528963893597707621, ?_, ?_⟩
                                                                                                            · exact (by decide : ExactOddStep 3 60077237049593886989 22528963893597707621)
                                                                                                            · refine ⟨4224180730049570179, ?_, ?_⟩
                                                                                                              · exact (by decide : ExactOddStep 4 22528963893597707621 4224180730049570179)
                                                                                                              · rfl

/-- Every lift of family 18 descends after its exact accelerated word. -/
theorem family_18_all_lifts (q : Nat) :
    ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 2, 2, 1, 1, 1, 4, 1, 3, 4] (14987979678029971483 + q * 2 ^ 90) endpoint ∧
      endpoint < 14987979678029971483 + q * 2 ^ 90 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 2, 2, 1, 1, 1, 4, 1, 3, 4] family_18_trace (by decide) (by decide) (by decide) q

/-- Family 19: exact representative trace from the pinned input. -/
theorem family_19_trace : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 2, 1, 2, 4, 3, 1, 1, 2, 1, 1, 6] 1729382375051231259 1644993556784634751 := by
  simp only [WordTrace]
  refine ⟨2594073562576846889, ?_, ?_⟩
  · exact (by decide : ExactOddStep 1 1729382375051231259 2594073562576846889)
  · refine ⟨1945555171932635167, ?_, ?_⟩
    · exact (by decide : ExactOddStep 2 2594073562576846889 1945555171932635167)
    · refine ⟨2918332757898952751, ?_, ?_⟩
      · exact (by decide : ExactOddStep 1 1945555171932635167 2918332757898952751)
      · refine ⟨4377499136848429127, ?_, ?_⟩
        · exact (by decide : ExactOddStep 1 2918332757898952751 4377499136848429127)
        · refine ⟨6566248705272643691, ?_, ?_⟩
          · exact (by decide : ExactOddStep 1 4377499136848429127 6566248705272643691)
          · refine ⟨9849373057908965537, ?_, ?_⟩
            · exact (by decide : ExactOddStep 1 6566248705272643691 9849373057908965537)
            · refine ⟨7387029793431724153, ?_, ?_⟩
              · exact (by decide : ExactOddStep 2 9849373057908965537 7387029793431724153)
              · refine ⟨5540272345073793115, ?_, ?_⟩
                · exact (by decide : ExactOddStep 2 7387029793431724153 5540272345073793115)
                · refine ⟨8310408517610689673, ?_, ?_⟩
                  · exact (by decide : ExactOddStep 1 5540272345073793115 8310408517610689673)
                  · refine ⟨6232806388208017255, ?_, ?_⟩
                    · exact (by decide : ExactOddStep 2 8310408517610689673 6232806388208017255)
                    · refine ⟨9349209582312025883, ?_, ?_⟩
                      · exact (by decide : ExactOddStep 1 6232806388208017255 9349209582312025883)
                      · refine ⟨14023814373468038825, ?_, ?_⟩
                        · exact (by decide : ExactOddStep 1 9349209582312025883 14023814373468038825)
                        · refine ⟨10517860780101029119, ?_, ?_⟩
                          · exact (by decide : ExactOddStep 2 14023814373468038825 10517860780101029119)
                          · refine ⟨15776791170151543679, ?_, ?_⟩
                            · exact (by decide : ExactOddStep 1 10517860780101029119 15776791170151543679)
                            · refine ⟨23665186755227315519, ?_, ?_⟩
                              · exact (by decide : ExactOddStep 1 15776791170151543679 23665186755227315519)
                              · refine ⟨35497780132840973279, ?_, ?_⟩
                                · exact (by decide : ExactOddStep 1 23665186755227315519 35497780132840973279)
                                · refine ⟨53246670199261459919, ?_, ?_⟩
                                  · exact (by decide : ExactOddStep 1 35497780132840973279 53246670199261459919)
                                  · refine ⟨79870005298892189879, ?_, ?_⟩
                                    · exact (by decide : ExactOddStep 1 53246670199261459919 79870005298892189879)
                                    · refine ⟨119805007948338284819, ?_, ?_⟩
                                      · exact (by decide : ExactOddStep 1 79870005298892189879 119805007948338284819)
                                      · refine ⟨179707511922507427229, ?_, ?_⟩
                                        · exact (by decide : ExactOddStep 1 119805007948338284819 179707511922507427229)
                                        · refine ⟨67390316970940285211, ?_, ?_⟩
                                          · exact (by decide : ExactOddStep 3 179707511922507427229 67390316970940285211)
                                          · refine ⟨101085475456410427817, ?_, ?_⟩
                                            · exact (by decide : ExactOddStep 1 67390316970940285211 101085475456410427817)
                                            · refine ⟨75814106592307820863, ?_, ?_⟩
                                              · exact (by decide : ExactOddStep 2 101085475456410427817 75814106592307820863)
                                              · refine ⟨113721159888461731295, ?_, ?_⟩
                                                · exact (by decide : ExactOddStep 1 75814106592307820863 113721159888461731295)
                                                · refine ⟨170581739832692596943, ?_, ?_⟩
                                                  · exact (by decide : ExactOddStep 1 113721159888461731295 170581739832692596943)
                                                  · refine ⟨255872609749038895415, ?_, ?_⟩
                                                    · exact (by decide : ExactOddStep 1 170581739832692596943 255872609749038895415)
                                                    · refine ⟨383808914623558343123, ?_, ?_⟩
                                                      · exact (by decide : ExactOddStep 1 255872609749038895415 383808914623558343123)
                                                      · refine ⟨575713371935337514685, ?_, ?_⟩
                                                        · exact (by decide : ExactOddStep 1 383808914623558343123 575713371935337514685)
                                                        · refine ⟨215892514475751568007, ?_, ?_⟩
                                                          · exact (by decide : ExactOddStep 3 575713371935337514685 215892514475751568007)
                                                          · refine ⟨323838771713627352011, ?_, ?_⟩
                                                            · exact (by decide : ExactOddStep 1 215892514475751568007 323838771713627352011)
                                                            · refine ⟨485758157570441028017, ?_, ?_⟩
                                                              · exact (by decide : ExactOddStep 1 323838771713627352011 485758157570441028017)
                                                              · refine ⟨364318618177830771013, ?_, ?_⟩
                                                                · exact (by decide : ExactOddStep 2 485758157570441028017 364318618177830771013)
                                                                · refine ⟨68309740908343269565, ?_, ?_⟩
                                                                  · exact (by decide : ExactOddStep 4 364318618177830771013 68309740908343269565)
                                                                  · refine ⟨25616152840628726087, ?_, ?_⟩
                                                                    · exact (by decide : ExactOddStep 3 68309740908343269565 25616152840628726087)
                                                                    · refine ⟨38424229260943089131, ?_, ?_⟩
                                                                      · exact (by decide : ExactOddStep 1 25616152840628726087 38424229260943089131)
                                                                      · refine ⟨57636343891414633697, ?_, ?_⟩
                                                                        · exact (by decide : ExactOddStep 1 38424229260943089131 57636343891414633697)
                                                                        · refine ⟨43227257918560975273, ?_, ?_⟩
                                                                          · exact (by decide : ExactOddStep 2 57636343891414633697 43227257918560975273)
                                                                          · refine ⟨32420443438920731455, ?_, ?_⟩
                                                                            · exact (by decide : ExactOddStep 2 43227257918560975273 32420443438920731455)
                                                                            · refine ⟨48630665158381097183, ?_, ?_⟩
                                                                              · exact (by decide : ExactOddStep 1 32420443438920731455 48630665158381097183)
                                                                              · refine ⟨72945997737571645775, ?_, ?_⟩
                                                                                · exact (by decide : ExactOddStep 1 48630665158381097183 72945997737571645775)
                                                                                · refine ⟨109418996606357468663, ?_, ?_⟩
                                                                                  · exact (by decide : ExactOddStep 1 72945997737571645775 109418996606357468663)
                                                                                  · refine ⟨164128494909536202995, ?_, ?_⟩
                                                                                    · exact (by decide : ExactOddStep 1 109418996606357468663 164128494909536202995)
                                                                                    · refine ⟨246192742364304304493, ?_, ?_⟩
                                                                                      · exact (by decide : ExactOddStep 1 164128494909536202995 246192742364304304493)
                                                                                      · refine ⟨92322278386614114185, ?_, ?_⟩
                                                                                        · exact (by decide : ExactOddStep 3 246192742364304304493 92322278386614114185)
                                                                                        · refine ⟨69241708789960585639, ?_, ?_⟩
                                                                                          · exact (by decide : ExactOddStep 2 92322278386614114185 69241708789960585639)
                                                                                          · refine ⟨103862563184940878459, ?_, ?_⟩
                                                                                            · exact (by decide : ExactOddStep 1 69241708789960585639 103862563184940878459)
                                                                                            · refine ⟨155793844777411317689, ?_, ?_⟩
                                                                                              · exact (by decide : ExactOddStep 1 103862563184940878459 155793844777411317689)
                                                                                              · refine ⟨116845383583058488267, ?_, ?_⟩
                                                                                                · exact (by decide : ExactOddStep 2 155793844777411317689 116845383583058488267)
                                                                                                · refine ⟨175268075374587732401, ?_, ?_⟩
                                                                                                  · exact (by decide : ExactOddStep 1 116845383583058488267 175268075374587732401)
                                                                                                  · refine ⟨131451056530940799301, ?_, ?_⟩
                                                                                                    · exact (by decide : ExactOddStep 2 175268075374587732401 131451056530940799301)
                                                                                                    · refine ⟨24647073099551399869, ?_, ?_⟩
                                                                                                      · exact (by decide : ExactOddStep 4 131451056530940799301 24647073099551399869)
                                                                                                      · refine ⟨9242652412331774951, ?_, ?_⟩
                                                                                                        · exact (by decide : ExactOddStep 3 24647073099551399869 9242652412331774951)
                                                                                                        · refine ⟨13863978618497662427, ?_, ?_⟩
                                                                                                          · exact (by decide : ExactOddStep 1 9242652412331774951 13863978618497662427)
                                                                                                          · refine ⟨20795967927746493641, ?_, ?_⟩
                                                                                                            · exact (by decide : ExactOddStep 1 13863978618497662427 20795967927746493641)
                                                                                                            · refine ⟨15596975945809870231, ?_, ?_⟩
                                                                                                              · exact (by decide : ExactOddStep 2 20795967927746493641 15596975945809870231)
                                                                                                              · refine ⟨23395463918714805347, ?_, ?_⟩
                                                                                                                · exact (by decide : ExactOddStep 1 15596975945809870231 23395463918714805347)
                                                                                                                · refine ⟨35093195878072208021, ?_, ?_⟩
                                                                                                                  · exact (by decide : ExactOddStep 1 23395463918714805347 35093195878072208021)
                                                                                                                  · refine ⟨1644993556784634751, ?_, ?_⟩
                                                                                                                    · exact (by decide : ExactOddStep 6 35093195878072208021 1644993556784634751)
                                                                                                                    · rfl

/-- Every lift of family 19 descends after its exact accelerated word. -/
theorem family_19_all_lifts (q : Nat) :
    ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 2, 1, 2, 4, 3, 1, 1, 2, 1, 1, 6] (1729382375051231259 + q * 2 ^ 93) endpoint ∧
      endpoint < 1729382375051231259 + q * 2 ^ 93 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 2, 1, 2, 4, 3, 1, 1, 2, 1, 1, 6] family_19_trace (by decide) (by decide) (by decide) q

/-- Family 20: exact representative trace from the pinned input. -/
theorem family_20_trace : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 1, 1, 1, 1, 1, 5, 1, 1, 1, 3, 4, 4, 2, 3] 14411518925726547995 5783180125407650105 := by
  simp only [WordTrace]
  refine ⟨21617278388589821993, ?_, ?_⟩
  · exact (by decide : ExactOddStep 1 14411518925726547995 21617278388589821993)
  · refine ⟨16212958791442366495, ?_, ?_⟩
    · exact (by decide : ExactOddStep 2 21617278388589821993 16212958791442366495)
    · refine ⟨24319438187163549743, ?_, ?_⟩
      · exact (by decide : ExactOddStep 1 16212958791442366495 24319438187163549743)
      · refine ⟨36479157280745324615, ?_, ?_⟩
        · exact (by decide : ExactOddStep 1 24319438187163549743 36479157280745324615)
        · refine ⟨54718735921117986923, ?_, ?_⟩
          · exact (by decide : ExactOddStep 1 36479157280745324615 54718735921117986923)
          · refine ⟨82078103881676980385, ?_, ?_⟩
            · exact (by decide : ExactOddStep 1 54718735921117986923 82078103881676980385)
            · refine ⟨61558577911257735289, ?_, ?_⟩
              · exact (by decide : ExactOddStep 2 82078103881676980385 61558577911257735289)
              · refine ⟨46168933433443301467, ?_, ?_⟩
                · exact (by decide : ExactOddStep 2 61558577911257735289 46168933433443301467)
                · refine ⟨69253400150164952201, ?_, ?_⟩
                  · exact (by decide : ExactOddStep 1 46168933433443301467 69253400150164952201)
                  · refine ⟨51940050112623714151, ?_, ?_⟩
                    · exact (by decide : ExactOddStep 2 69253400150164952201 51940050112623714151)
                    · refine ⟨77910075168935571227, ?_, ?_⟩
                      · exact (by decide : ExactOddStep 1 51940050112623714151 77910075168935571227)
                      · refine ⟨116865112753403356841, ?_, ?_⟩
                        · exact (by decide : ExactOddStep 1 77910075168935571227 116865112753403356841)
                        · refine ⟨87648834565052517631, ?_, ?_⟩
                          · exact (by decide : ExactOddStep 2 116865112753403356841 87648834565052517631)
                          · refine ⟨131473251847578776447, ?_, ?_⟩
                            · exact (by decide : ExactOddStep 1 87648834565052517631 131473251847578776447)
                            · refine ⟨197209877771368164671, ?_, ?_⟩
                              · exact (by decide : ExactOddStep 1 131473251847578776447 197209877771368164671)
                              · refine ⟨295814816657052247007, ?_, ?_⟩
                                · exact (by decide : ExactOddStep 1 197209877771368164671 295814816657052247007)
                                · refine ⟨443722224985578370511, ?_, ?_⟩
                                  · exact (by decide : ExactOddStep 1 295814816657052247007 443722224985578370511)
                                  · refine ⟨665583337478367555767, ?_, ?_⟩
                                    · exact (by decide : ExactOddStep 1 443722224985578370511 665583337478367555767)
                                    · refine ⟨998375006217551333651, ?_, ?_⟩
                                      · exact (by decide : ExactOddStep 1 665583337478367555767 998375006217551333651)
                                      · refine ⟨1497562509326327000477, ?_, ?_⟩
                                        · exact (by decide : ExactOddStep 1 998375006217551333651 1497562509326327000477)
                                        · refine ⟨561585940997372625179, ?_, ?_⟩
                                          · exact (by decide : ExactOddStep 3 1497562509326327000477 561585940997372625179)
                                          · refine ⟨842378911496058937769, ?_, ?_⟩
                                            · exact (by decide : ExactOddStep 1 561585940997372625179 842378911496058937769)
                                            · refine ⟨631784183622044203327, ?_, ?_⟩
                                              · exact (by decide : ExactOddStep 2 842378911496058937769 631784183622044203327)
                                              · refine ⟨947676275433066304991, ?_, ?_⟩
                                                · exact (by decide : ExactOddStep 1 631784183622044203327 947676275433066304991)
                                                · refine ⟨1421514413149599457487, ?_, ?_⟩
                                                  · exact (by decide : ExactOddStep 1 947676275433066304991 1421514413149599457487)
                                                  · refine ⟨2132271619724399186231, ?_, ?_⟩
                                                    · exact (by decide : ExactOddStep 1 1421514413149599457487 2132271619724399186231)
                                                    · refine ⟨3198407429586598779347, ?_, ?_⟩
                                                      · exact (by decide : ExactOddStep 1 2132271619724399186231 3198407429586598779347)
                                                      · refine ⟨4797611144379898169021, ?_, ?_⟩
                                                        · exact (by decide : ExactOddStep 1 3198407429586598779347 4797611144379898169021)
                                                        · refine ⟨1799104179142461813383, ?_, ?_⟩
                                                          · exact (by decide : ExactOddStep 3 4797611144379898169021 1799104179142461813383)
                                                          · refine ⟨2698656268713692720075, ?_, ?_⟩
                                                            · exact (by decide : ExactOddStep 1 1799104179142461813383 2698656268713692720075)
                                                            · refine ⟨4047984403070539080113, ?_, ?_⟩
                                                              · exact (by decide : ExactOddStep 1 2698656268713692720075 4047984403070539080113)
                                                              · refine ⟨3035988302302904310085, ?_, ?_⟩
                                                                · exact (by decide : ExactOddStep 2 4047984403070539080113 3035988302302904310085)
                                                                · refine ⟨569247806681794558141, ?_, ?_⟩
                                                                  · exact (by decide : ExactOddStep 4 3035988302302904310085 569247806681794558141)
                                                                  · refine ⟨213467927505672959303, ?_, ?_⟩
                                                                    · exact (by decide : ExactOddStep 3 569247806681794558141 213467927505672959303)
                                                                    · refine ⟨320201891258509438955, ?_, ?_⟩
                                                                      · exact (by decide : ExactOddStep 1 213467927505672959303 320201891258509438955)
                                                                      · refine ⟨480302836887764158433, ?_, ?_⟩
                                                                        · exact (by decide : ExactOddStep 1 320201891258509438955 480302836887764158433)
                                                                        · refine ⟨360227127665823118825, ?_, ?_⟩
                                                                          · exact (by decide : ExactOddStep 2 480302836887764158433 360227127665823118825)
                                                                          · refine ⟨270170345749367339119, ?_, ?_⟩
                                                                            · exact (by decide : ExactOddStep 2 360227127665823118825 270170345749367339119)
                                                                            · refine ⟨405255518624051008679, ?_, ?_⟩
                                                                              · exact (by decide : ExactOddStep 1 270170345749367339119 405255518624051008679)
                                                                              · refine ⟨607883277936076513019, ?_, ?_⟩
                                                                                · exact (by decide : ExactOddStep 1 405255518624051008679 607883277936076513019)
                                                                                · refine ⟨911824916904114769529, ?_, ?_⟩
                                                                                  · exact (by decide : ExactOddStep 1 607883277936076513019 911824916904114769529)
                                                                                  · refine ⟨683868687678086077147, ?_, ?_⟩
                                                                                    · exact (by decide : ExactOddStep 2 911824916904114769529 683868687678086077147)
                                                                                    · refine ⟨1025803031517129115721, ?_, ?_⟩
                                                                                      · exact (by decide : ExactOddStep 1 683868687678086077147 1025803031517129115721)
                                                                                      · refine ⟨769352273637846836791, ?_, ?_⟩
                                                                                        · exact (by decide : ExactOddStep 2 1025803031517129115721 769352273637846836791)
                                                                                        · refine ⟨1154028410456770255187, ?_, ?_⟩
                                                                                          · exact (by decide : ExactOddStep 1 769352273637846836791 1154028410456770255187)
                                                                                          · refine ⟨1731042615685155382781, ?_, ?_⟩
                                                                                            · exact (by decide : ExactOddStep 1 1154028410456770255187 1731042615685155382781)
                                                                                            · refine ⟨649140980881933268543, ?_, ?_⟩
                                                                                              · exact (by decide : ExactOddStep 3 1731042615685155382781 649140980881933268543)
                                                                                              · refine ⟨973711471322899902815, ?_, ?_⟩
                                                                                                · exact (by decide : ExactOddStep 1 649140980881933268543 973711471322899902815)
                                                                                                · refine ⟨1460567206984349854223, ?_, ?_⟩
                                                                                                  · exact (by decide : ExactOddStep 1 973711471322899902815 1460567206984349854223)
                                                                                                  · refine ⟨2190850810476524781335, ?_, ?_⟩
                                                                                                    · exact (by decide : ExactOddStep 1 1460567206984349854223 2190850810476524781335)
                                                                                                    · refine ⟨3286276215714787172003, ?_, ?_⟩
                                                                                                      · exact (by decide : ExactOddStep 1 2190850810476524781335 3286276215714787172003)
                                                                                                      · refine ⟨4929414323572180758005, ?_, ?_⟩
                                                                                                        · exact (by decide : ExactOddStep 1 3286276215714787172003 4929414323572180758005)
                                                                                                        · refine ⟨462132592834891946063, ?_, ?_⟩
                                                                                                          · exact (by decide : ExactOddStep 5 4929414323572180758005 462132592834891946063)
                                                                                                          · refine ⟨693198889252337919095, ?_, ?_⟩
                                                                                                            · exact (by decide : ExactOddStep 1 462132592834891946063 693198889252337919095)
                                                                                                            · refine ⟨1039798333878506878643, ?_, ?_⟩
                                                                                                              · exact (by decide : ExactOddStep 1 693198889252337919095 1039798333878506878643)
                                                                                                              · refine ⟨1559697500817760317965, ?_, ?_⟩
                                                                                                                · exact (by decide : ExactOddStep 1 1039798333878506878643 1559697500817760317965)
                                                                                                                · refine ⟨584886562806660119237, ?_, ?_⟩
                                                                                                                  · exact (by decide : ExactOddStep 3 1559697500817760317965 584886562806660119237)
                                                                                                                  · refine ⟨109666230526248772357, ?_, ?_⟩
                                                                                                                    · exact (by decide : ExactOddStep 4 584886562806660119237 109666230526248772357)
                                                                                                                    · refine ⟨20562418223671644817, ?_, ?_⟩
                                                                                                                      · exact (by decide : ExactOddStep 4 109666230526248772357 20562418223671644817)
                                                                                                                      · refine ⟨15421813667753733613, ?_, ?_⟩
                                                                                                                        · exact (by decide : ExactOddStep 2 20562418223671644817 15421813667753733613)
                                                                                                                        · refine ⟨5783180125407650105, ?_, ?_⟩
                                                                                                                          · exact (by decide : ExactOddStep 3 15421813667753733613 5783180125407650105)
                                                                                                                          · rfl

/-- Every lift of family 20 descends after its exact accelerated word. -/
theorem family_20_all_lifts (q : Nat) :
    ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 1, 1, 1, 1, 1, 5, 1, 1, 1, 3, 4, 4, 2, 3] (14411518925726547995 + q * 2 ^ 99) endpoint ∧
      endpoint < 14411518925726547995 + q * 2 ^ 99 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 1, 1, 1, 1, 1, 5, 1, 1, 1, 3, 4, 4, 2, 3] family_20_trace (by decide) (by decide) (by decide) q

/-- Family 21: exact representative trace from the pinned input. -/
theorem family_21_trace : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 2, 2, 5, 1, 1, 6, 3, 2, 3] 8646911402692313115 4391602431732056327 := by
  simp only [WordTrace]
  refine ⟨12970367104038469673, ?_, ?_⟩
  · exact (by decide : ExactOddStep 1 8646911402692313115 12970367104038469673)
  · refine ⟨9727775328028852255, ?_, ?_⟩
    · exact (by decide : ExactOddStep 2 12970367104038469673 9727775328028852255)
    · refine ⟨14591662992043278383, ?_, ?_⟩
      · exact (by decide : ExactOddStep 1 9727775328028852255 14591662992043278383)
      · refine ⟨21887494488064917575, ?_, ?_⟩
        · exact (by decide : ExactOddStep 1 14591662992043278383 21887494488064917575)
        · refine ⟨32831241732097376363, ?_, ?_⟩
          · exact (by decide : ExactOddStep 1 21887494488064917575 32831241732097376363)
          · refine ⟨49246862598146064545, ?_, ?_⟩
            · exact (by decide : ExactOddStep 1 32831241732097376363 49246862598146064545)
            · refine ⟨36935146948609548409, ?_, ?_⟩
              · exact (by decide : ExactOddStep 2 49246862598146064545 36935146948609548409)
              · refine ⟨27701360211457161307, ?_, ?_⟩
                · exact (by decide : ExactOddStep 2 36935146948609548409 27701360211457161307)
                · refine ⟨41552040317185741961, ?_, ?_⟩
                  · exact (by decide : ExactOddStep 1 27701360211457161307 41552040317185741961)
                  · refine ⟨31164030237889306471, ?_, ?_⟩
                    · exact (by decide : ExactOddStep 2 41552040317185741961 31164030237889306471)
                    · refine ⟨46746045356833959707, ?_, ?_⟩
                      · exact (by decide : ExactOddStep 1 31164030237889306471 46746045356833959707)
                      · refine ⟨70119068035250939561, ?_, ?_⟩
                        · exact (by decide : ExactOddStep 1 46746045356833959707 70119068035250939561)
                        · refine ⟨52589301026438204671, ?_, ?_⟩
                          · exact (by decide : ExactOddStep 2 70119068035250939561 52589301026438204671)
                          · refine ⟨78883951539657307007, ?_, ?_⟩
                            · exact (by decide : ExactOddStep 1 52589301026438204671 78883951539657307007)
                            · refine ⟨118325927309485960511, ?_, ?_⟩
                              · exact (by decide : ExactOddStep 1 78883951539657307007 118325927309485960511)
                              · refine ⟨177488890964228940767, ?_, ?_⟩
                                · exact (by decide : ExactOddStep 1 118325927309485960511 177488890964228940767)
                                · refine ⟨266233336446343411151, ?_, ?_⟩
                                  · exact (by decide : ExactOddStep 1 177488890964228940767 266233336446343411151)
                                  · refine ⟨399350004669515116727, ?_, ?_⟩
                                    · exact (by decide : ExactOddStep 1 266233336446343411151 399350004669515116727)
                                    · refine ⟨599025007004272675091, ?_, ?_⟩
                                      · exact (by decide : ExactOddStep 1 399350004669515116727 599025007004272675091)
                                      · refine ⟨898537510506409012637, ?_, ?_⟩
                                        · exact (by decide : ExactOddStep 1 599025007004272675091 898537510506409012637)
                                        · refine ⟨336951566439903379739, ?_, ?_⟩
                                          · exact (by decide : ExactOddStep 3 898537510506409012637 336951566439903379739)
                                          · refine ⟨505427349659855069609, ?_, ?_⟩
                                            · exact (by decide : ExactOddStep 1 336951566439903379739 505427349659855069609)
                                            · refine ⟨379070512244891302207, ?_, ?_⟩
                                              · exact (by decide : ExactOddStep 2 505427349659855069609 379070512244891302207)
                                              · refine ⟨568605768367336953311, ?_, ?_⟩
                                                · exact (by decide : ExactOddStep 1 379070512244891302207 568605768367336953311)
                                                · refine ⟨852908652551005429967, ?_, ?_⟩
                                                  · exact (by decide : ExactOddStep 1 568605768367336953311 852908652551005429967)
                                                  · refine ⟨1279362978826508144951, ?_, ?_⟩
                                                    · exact (by decide : ExactOddStep 1 852908652551005429967 1279362978826508144951)
                                                    · refine ⟨1919044468239762217427, ?_, ?_⟩
                                                      · exact (by decide : ExactOddStep 1 1279362978826508144951 1919044468239762217427)
                                                      · refine ⟨2878566702359643326141, ?_, ?_⟩
                                                        · exact (by decide : ExactOddStep 1 1919044468239762217427 2878566702359643326141)
                                                        · refine ⟨1079462513384866247303, ?_, ?_⟩
                                                          · exact (by decide : ExactOddStep 3 2878566702359643326141 1079462513384866247303)
                                                          · refine ⟨1619193770077299370955, ?_, ?_⟩
                                                            · exact (by decide : ExactOddStep 1 1079462513384866247303 1619193770077299370955)
                                                            · refine ⟨2428790655115949056433, ?_, ?_⟩
                                                              · exact (by decide : ExactOddStep 1 1619193770077299370955 2428790655115949056433)
                                                              · refine ⟨1821592991336961792325, ?_, ?_⟩
                                                                · exact (by decide : ExactOddStep 2 2428790655115949056433 1821592991336961792325)
                                                                · refine ⟨341548685875680336061, ?_, ?_⟩
                                                                  · exact (by decide : ExactOddStep 4 1821592991336961792325 341548685875680336061)
                                                                  · refine ⟨128080757203380126023, ?_, ?_⟩
                                                                    · exact (by decide : ExactOddStep 3 341548685875680336061 128080757203380126023)
                                                                    · refine ⟨192121135805070189035, ?_, ?_⟩
                                                                      · exact (by decide : ExactOddStep 1 128080757203380126023 192121135805070189035)
                                                                      · refine ⟨288181703707605283553, ?_, ?_⟩
                                                                        · exact (by decide : ExactOddStep 1 192121135805070189035 288181703707605283553)
                                                                        · refine ⟨216136277780703962665, ?_, ?_⟩
                                                                          · exact (by decide : ExactOddStep 2 288181703707605283553 216136277780703962665)
                                                                          · refine ⟨162102208335527971999, ?_, ?_⟩
                                                                            · exact (by decide : ExactOddStep 2 216136277780703962665 162102208335527971999)
                                                                            · refine ⟨243153312503291957999, ?_, ?_⟩
                                                                              · exact (by decide : ExactOddStep 1 162102208335527971999 243153312503291957999)
                                                                              · refine ⟨364729968754937936999, ?_, ?_⟩
                                                                                · exact (by decide : ExactOddStep 1 243153312503291957999 364729968754937936999)
                                                                                · refine ⟨547094953132406905499, ?_, ?_⟩
                                                                                  · exact (by decide : ExactOddStep 1 364729968754937936999 547094953132406905499)
                                                                                  · refine ⟨820642429698610358249, ?_, ?_⟩
                                                                                    · exact (by decide : ExactOddStep 1 547094953132406905499 820642429698610358249)
                                                                                    · refine ⟨615481822273957768687, ?_, ?_⟩
                                                                                      · exact (by decide : ExactOddStep 2 820642429698610358249 615481822273957768687)
                                                                                      · refine ⟨923222733410936653031, ?_, ?_⟩
                                                                                        · exact (by decide : ExactOddStep 1 615481822273957768687 923222733410936653031)
                                                                                        · refine ⟨1384834100116404979547, ?_, ?_⟩
                                                                                          · exact (by decide : ExactOddStep 1 923222733410936653031 1384834100116404979547)
                                                                                          · refine ⟨2077251150174607469321, ?_, ?_⟩
                                                                                            · exact (by decide : ExactOddStep 1 1384834100116404979547 2077251150174607469321)
                                                                                            · refine ⟨1557938362630955601991, ?_, ?_⟩
                                                                                              · exact (by decide : ExactOddStep 2 2077251150174607469321 1557938362630955601991)
                                                                                              · refine ⟨2336907543946433402987, ?_, ?_⟩
                                                                                                · exact (by decide : ExactOddStep 1 1557938362630955601991 2336907543946433402987)
                                                                                                · refine ⟨3505361315919650104481, ?_, ?_⟩
                                                                                                  · exact (by decide : ExactOddStep 1 2336907543946433402987 3505361315919650104481)
                                                                                                  · refine ⟨2629020986939737578361, ?_, ?_⟩
                                                                                                    · exact (by decide : ExactOddStep 2 3505361315919650104481 2629020986939737578361)
                                                                                                    · refine ⟨1971765740204803183771, ?_, ?_⟩
                                                                                                      · exact (by decide : ExactOddStep 2 2629020986939737578361 1971765740204803183771)
                                                                                                      · refine ⟨2957648610307204775657, ?_, ?_⟩
                                                                                                        · exact (by decide : ExactOddStep 1 1971765740204803183771 2957648610307204775657)
                                                                                                        · refine ⟨2218236457730403581743, ?_, ?_⟩
                                                                                                          · exact (by decide : ExactOddStep 2 2957648610307204775657 2218236457730403581743)
                                                                                                          · refine ⟨3327354686595605372615, ?_, ?_⟩
                                                                                                            · exact (by decide : ExactOddStep 1 2218236457730403581743 3327354686595605372615)
                                                                                                            · refine ⟨4991032029893408058923, ?_, ?_⟩
                                                                                                              · exact (by decide : ExactOddStep 1 3327354686595605372615 4991032029893408058923)
                                                                                                              · refine ⟨7486548044840112088385, ?_, ?_⟩
                                                                                                                · exact (by decide : ExactOddStep 1 4991032029893408058923 7486548044840112088385)
                                                                                                                · refine ⟨5614911033630084066289, ?_, ?_⟩
                                                                                                                  · exact (by decide : ExactOddStep 2 7486548044840112088385 5614911033630084066289)
                                                                                                                  · refine ⟨4211183275222563049717, ?_, ?_⟩
                                                                                                                    · exact (by decide : ExactOddStep 2 5614911033630084066289 4211183275222563049717)
                                                                                                                    · refine ⟨394798432052115285911, ?_, ?_⟩
                                                                                                                      · exact (by decide : ExactOddStep 5 4211183275222563049717 394798432052115285911)
                                                                                                                      · refine ⟨592197648078172928867, ?_, ?_⟩
                                                                                                                        · exact (by decide : ExactOddStep 1 394798432052115285911 592197648078172928867)
                                                                                                                        · refine ⟨888296472117259393301, ?_, ?_⟩
                                                                                                                          · exact (by decide : ExactOddStep 1 592197648078172928867 888296472117259393301)
                                                                                                                          · refine ⟨41638897130496534061, ?_, ?_⟩
                                                                                                                            · exact (by decide : ExactOddStep 6 888296472117259393301 41638897130496534061)
                                                                                                                            · refine ⟨15614586423936200273, ?_, ?_⟩
                                                                                                                              · exact (by decide : ExactOddStep 3 41638897130496534061 15614586423936200273)
                                                                                                                              · refine ⟨11710939817952150205, ?_, ?_⟩
                                                                                                                                · exact (by decide : ExactOddStep 2 15614586423936200273 11710939817952150205)
                                                                                                                                · refine ⟨4391602431732056327, ?_, ?_⟩
                                                                                                                                  · exact (by decide : ExactOddStep 3 11710939817952150205 4391602431732056327)
                                                                                                                                  · rfl

/-- Every lift of family 21 descends after its exact accelerated word. -/
theorem family_21_all_lifts (q : Nat) :
    ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 2, 2, 5, 1, 1, 6, 3, 2, 3] (8646911402692313115 + q * 2 ^ 105) endpoint ∧
      endpoint < 8646911402692313115 + q * 2 ^ 105 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 2, 2, 5, 1, 1, 6, 3, 2, 3] family_21_trace (by decide) (by decide) (by decide) q

/-- Family 22: exact representative trace from the pinned input. -/
theorem family_22_trace : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 1, 3, 1, 1, 1, 1, 2, 1, 1, 1, 3, 1, 3, 3, 1, 2, 1, 3, 3, 1, 3] 4035225384264925211 2305591312660262615 := by
  simp only [WordTrace]
  refine ⟨6052838076397387817, ?_, ?_⟩
  · exact (by decide : ExactOddStep 1 4035225384264925211 6052838076397387817)
  · refine ⟨4539628557298040863, ?_, ?_⟩
    · exact (by decide : ExactOddStep 2 6052838076397387817 4539628557298040863)
    · refine ⟨6809442835947061295, ?_, ?_⟩
      · exact (by decide : ExactOddStep 1 4539628557298040863 6809442835947061295)
      · refine ⟨10214164253920591943, ?_, ?_⟩
        · exact (by decide : ExactOddStep 1 6809442835947061295 10214164253920591943)
        · refine ⟨15321246380880887915, ?_, ?_⟩
          · exact (by decide : ExactOddStep 1 10214164253920591943 15321246380880887915)
          · refine ⟨22981869571321331873, ?_, ?_⟩
            · exact (by decide : ExactOddStep 1 15321246380880887915 22981869571321331873)
            · refine ⟨17236402178490998905, ?_, ?_⟩
              · exact (by decide : ExactOddStep 2 22981869571321331873 17236402178490998905)
              · refine ⟨12927301633868249179, ?_, ?_⟩
                · exact (by decide : ExactOddStep 2 17236402178490998905 12927301633868249179)
                · refine ⟨19390952450802373769, ?_, ?_⟩
                  · exact (by decide : ExactOddStep 1 12927301633868249179 19390952450802373769)
                  · refine ⟨14543214338101780327, ?_, ?_⟩
                    · exact (by decide : ExactOddStep 2 19390952450802373769 14543214338101780327)
                    · refine ⟨21814821507152670491, ?_, ?_⟩
                      · exact (by decide : ExactOddStep 1 14543214338101780327 21814821507152670491)
                      · refine ⟨32722232260729005737, ?_, ?_⟩
                        · exact (by decide : ExactOddStep 1 21814821507152670491 32722232260729005737)
                        · refine ⟨24541674195546754303, ?_, ?_⟩
                          · exact (by decide : ExactOddStep 2 32722232260729005737 24541674195546754303)
                          · refine ⟨36812511293320131455, ?_, ?_⟩
                            · exact (by decide : ExactOddStep 1 24541674195546754303 36812511293320131455)
                            · refine ⟨55218766939980197183, ?_, ?_⟩
                              · exact (by decide : ExactOddStep 1 36812511293320131455 55218766939980197183)
                              · refine ⟨82828150409970295775, ?_, ?_⟩
                                · exact (by decide : ExactOddStep 1 55218766939980197183 82828150409970295775)
                                · refine ⟨124242225614955443663, ?_, ?_⟩
                                  · exact (by decide : ExactOddStep 1 82828150409970295775 124242225614955443663)
                                  · refine ⟨186363338422433165495, ?_, ?_⟩
                                    · exact (by decide : ExactOddStep 1 124242225614955443663 186363338422433165495)
                                    · refine ⟨279545007633649748243, ?_, ?_⟩
                                      · exact (by decide : ExactOddStep 1 186363338422433165495 279545007633649748243)
                                      · refine ⟨419317511450474622365, ?_, ?_⟩
                                        · exact (by decide : ExactOddStep 1 279545007633649748243 419317511450474622365)
                                        · refine ⟨157244066793927983387, ?_, ?_⟩
                                          · exact (by decide : ExactOddStep 3 419317511450474622365 157244066793927983387)
                                          · refine ⟨235866100190891975081, ?_, ?_⟩
                                            · exact (by decide : ExactOddStep 1 157244066793927983387 235866100190891975081)
                                            · refine ⟨176899575143168981311, ?_, ?_⟩
                                              · exact (by decide : ExactOddStep 2 235866100190891975081 176899575143168981311)
                                              · refine ⟨265349362714753471967, ?_, ?_⟩
                                                · exact (by decide : ExactOddStep 1 176899575143168981311 265349362714753471967)
                                                · refine ⟨398024044072130207951, ?_, ?_⟩
                                                  · exact (by decide : ExactOddStep 1 265349362714753471967 398024044072130207951)
                                                  · refine ⟨597036066108195311927, ?_, ?_⟩
                                                    · exact (by decide : ExactOddStep 1 398024044072130207951 597036066108195311927)
                                                    · refine ⟨895554099162292967891, ?_, ?_⟩
                                                      · exact (by decide : ExactOddStep 1 597036066108195311927 895554099162292967891)
                                                      · refine ⟨1343331148743439451837, ?_, ?_⟩
                                                        · exact (by decide : ExactOddStep 1 895554099162292967891 1343331148743439451837)
                                                        · refine ⟨503749180778789794439, ?_, ?_⟩
                                                          · exact (by decide : ExactOddStep 3 1343331148743439451837 503749180778789794439)
                                                          · refine ⟨755623771168184691659, ?_, ?_⟩
                                                            · exact (by decide : ExactOddStep 1 503749180778789794439 755623771168184691659)
                                                            · refine ⟨1133435656752277037489, ?_, ?_⟩
                                                              · exact (by decide : ExactOddStep 1 755623771168184691659 1133435656752277037489)
                                                              · refine ⟨850076742564207778117, ?_, ?_⟩
                                                                · exact (by decide : ExactOddStep 2 1133435656752277037489 850076742564207778117)
                                                                · refine ⟨159389389230788958397, ?_, ?_⟩
                                                                  · exact (by decide : ExactOddStep 4 850076742564207778117 159389389230788958397)
                                                                  · refine ⟨59771020961545859399, ?_, ?_⟩
                                                                    · exact (by decide : ExactOddStep 3 159389389230788958397 59771020961545859399)
                                                                    · refine ⟨89656531442318789099, ?_, ?_⟩
                                                                      · exact (by decide : ExactOddStep 1 59771020961545859399 89656531442318789099)
                                                                      · refine ⟨134484797163478183649, ?_, ?_⟩
                                                                        · exact (by decide : ExactOddStep 1 89656531442318789099 134484797163478183649)
                                                                        · refine ⟨100863597872608637737, ?_, ?_⟩
                                                                          · exact (by decide : ExactOddStep 2 134484797163478183649 100863597872608637737)
                                                                          · refine ⟨75647698404456478303, ?_, ?_⟩
                                                                            · exact (by decide : ExactOddStep 2 100863597872608637737 75647698404456478303)
                                                                            · refine ⟨113471547606684717455, ?_, ?_⟩
                                                                              · exact (by decide : ExactOddStep 1 75647698404456478303 113471547606684717455)
                                                                              · refine ⟨170207321410027076183, ?_, ?_⟩
                                                                                · exact (by decide : ExactOddStep 1 113471547606684717455 170207321410027076183)
                                                                                · refine ⟨255310982115040614275, ?_, ?_⟩
                                                                                  · exact (by decide : ExactOddStep 1 170207321410027076183 255310982115040614275)
                                                                                  · refine ⟨382966473172560921413, ?_, ?_⟩
                                                                                    · exact (by decide : ExactOddStep 1 255310982115040614275 382966473172560921413)
                                                                                    · refine ⟨71806213719855172765, ?_, ?_⟩
                                                                                      · exact (by decide : ExactOddStep 4 382966473172560921413 71806213719855172765)
                                                                                      · refine ⟨26927330144945689787, ?_, ?_⟩
                                                                                        · exact (by decide : ExactOddStep 3 71806213719855172765 26927330144945689787)
                                                                                        · refine ⟨40390995217418534681, ?_, ?_⟩
                                                                                          · exact (by decide : ExactOddStep 1 26927330144945689787 40390995217418534681)
                                                                                          · refine ⟨30293246413063901011, ?_, ?_⟩
                                                                                            · exact (by decide : ExactOddStep 2 40390995217418534681 30293246413063901011)
                                                                                            · refine ⟨45439869619595851517, ?_, ?_⟩
                                                                                              · exact (by decide : ExactOddStep 1 30293246413063901011 45439869619595851517)
                                                                                              · refine ⟨17039951107348444319, ?_, ?_⟩
                                                                                                · exact (by decide : ExactOddStep 3 45439869619595851517 17039951107348444319)
                                                                                                · refine ⟨25559926661022666479, ?_, ?_⟩
                                                                                                  · exact (by decide : ExactOddStep 1 17039951107348444319 25559926661022666479)
                                                                                                  · refine ⟨38339889991533999719, ?_, ?_⟩
                                                                                                    · exact (by decide : ExactOddStep 1 25559926661022666479 38339889991533999719)
                                                                                                    · refine ⟨57509834987300999579, ?_, ?_⟩
                                                                                                      · exact (by decide : ExactOddStep 1 38339889991533999719 57509834987300999579)
                                                                                                      · refine ⟨86264752480951499369, ?_, ?_⟩
                                                                                                        · exact (by decide : ExactOddStep 1 57509834987300999579 86264752480951499369)
                                                                                                        · refine ⟨64698564360713624527, ?_, ?_⟩
                                                                                                          · exact (by decide : ExactOddStep 2 86264752480951499369 64698564360713624527)
                                                                                                          · refine ⟨97047846541070436791, ?_, ?_⟩
                                                                                                            · exact (by decide : ExactOddStep 1 64698564360713624527 97047846541070436791)
                                                                                                            · refine ⟨145571769811605655187, ?_, ?_⟩
                                                                                                              · exact (by decide : ExactOddStep 1 97047846541070436791 145571769811605655187)
                                                                                                              · refine ⟨218357654717408482781, ?_, ?_⟩
                                                                                                                · exact (by decide : ExactOddStep 1 145571769811605655187 218357654717408482781)
                                                                                                                · refine ⟨81884120519028181043, ?_, ?_⟩
                                                                                                                  · exact (by decide : ExactOddStep 3 218357654717408482781 81884120519028181043)
                                                                                                                  · refine ⟨122826180778542271565, ?_, ?_⟩
                                                                                                                    · exact (by decide : ExactOddStep 1 81884120519028181043 122826180778542271565)
                                                                                                                    · refine ⟨46059817791953351837, ?_, ?_⟩
                                                                                                                      · exact (by decide : ExactOddStep 3 122826180778542271565 46059817791953351837)
                                                                                                                      · refine ⟨17272431671982506939, ?_, ?_⟩
                                                                                                                        · exact (by decide : ExactOddStep 3 46059817791953351837 17272431671982506939)
                                                                                                                        · refine ⟨25908647507973760409, ?_, ?_⟩
                                                                                                                          · exact (by decide : ExactOddStep 1 17272431671982506939 25908647507973760409)
                                                                                                                          · refine ⟨19431485630980320307, ?_, ?_⟩
                                                                                                                            · exact (by decide : ExactOddStep 2 25908647507973760409 19431485630980320307)
                                                                                                                            · refine ⟨29147228446470480461, ?_, ?_⟩
                                                                                                                              · exact (by decide : ExactOddStep 1 19431485630980320307 29147228446470480461)
                                                                                                                              · refine ⟨10930210667426430173, ?_, ?_⟩
                                                                                                                                · exact (by decide : ExactOddStep 3 29147228446470480461 10930210667426430173)
                                                                                                                                · refine ⟨4098829000284911315, ?_, ?_⟩
                                                                                                                                  · exact (by decide : ExactOddStep 3 10930210667426430173 4098829000284911315)
                                                                                                                                  · refine ⟨6148243500427366973, ?_, ?_⟩
                                                                                                                                    · exact (by decide : ExactOddStep 1 4098829000284911315 6148243500427366973)
                                                                                                                                    · refine ⟨2305591312660262615, ?_, ?_⟩
                                                                                                                                      · exact (by decide : ExactOddStep 3 6148243500427366973 2305591312660262615)
                                                                                                                                      · rfl

/-- Every lift of family 22 descends after its exact accelerated word. -/
theorem family_22_all_lifts (q : Nat) :
    ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 1, 3, 1, 1, 1, 1, 2, 1, 1, 1, 3, 1, 3, 3, 1, 2, 1, 3, 3, 1, 3] (4035225384264925211 + q * 2 ^ 108) endpoint ∧
      endpoint < 4035225384264925211 + q * 2 ^ 108 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 1, 3, 1, 1, 1, 1, 2, 1, 1, 1, 3, 1, 3, 3, 1, 2, 1, 3, 3, 1, 3] family_22_trace (by decide) (by decide) (by decide) q

/-- Family 23: exact representative trace from the pinned input. -/
theorem family_23_trace : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 3, 2, 2, 1, 2, 1, 2, 1, 2, 1, 2, 1, 1, 1, 3, 2, 1, 3, 2, 2, 4] 6917529145782042651 1976221101029600293 := by
  simp only [WordTrace]
  refine ⟨10376293718673063977, ?_, ?_⟩
  · exact (by decide : ExactOddStep 1 6917529145782042651 10376293718673063977)
  · refine ⟨7782220289004797983, ?_, ?_⟩
    · exact (by decide : ExactOddStep 2 10376293718673063977 7782220289004797983)
    · refine ⟨11673330433507196975, ?_, ?_⟩
      · exact (by decide : ExactOddStep 1 7782220289004797983 11673330433507196975)
      · refine ⟨17509995650260795463, ?_, ?_⟩
        · exact (by decide : ExactOddStep 1 11673330433507196975 17509995650260795463)
        · refine ⟨26264993475391193195, ?_, ?_⟩
          · exact (by decide : ExactOddStep 1 17509995650260795463 26264993475391193195)
          · refine ⟨39397490213086789793, ?_, ?_⟩
            · exact (by decide : ExactOddStep 1 26264993475391193195 39397490213086789793)
            · refine ⟨29548117659815092345, ?_, ?_⟩
              · exact (by decide : ExactOddStep 2 39397490213086789793 29548117659815092345)
              · refine ⟨22161088244861319259, ?_, ?_⟩
                · exact (by decide : ExactOddStep 2 29548117659815092345 22161088244861319259)
                · refine ⟨33241632367291978889, ?_, ?_⟩
                  · exact (by decide : ExactOddStep 1 22161088244861319259 33241632367291978889)
                  · refine ⟨24931224275468984167, ?_, ?_⟩
                    · exact (by decide : ExactOddStep 2 33241632367291978889 24931224275468984167)
                    · refine ⟨37396836413203476251, ?_, ?_⟩
                      · exact (by decide : ExactOddStep 1 24931224275468984167 37396836413203476251)
                      · refine ⟨56095254619805214377, ?_, ?_⟩
                        · exact (by decide : ExactOddStep 1 37396836413203476251 56095254619805214377)
                        · refine ⟨42071440964853910783, ?_, ?_⟩
                          · exact (by decide : ExactOddStep 2 56095254619805214377 42071440964853910783)
                          · refine ⟨63107161447280866175, ?_, ?_⟩
                            · exact (by decide : ExactOddStep 1 42071440964853910783 63107161447280866175)
                            · refine ⟨94660742170921299263, ?_, ?_⟩
                              · exact (by decide : ExactOddStep 1 63107161447280866175 94660742170921299263)
                              · refine ⟨141991113256381948895, ?_, ?_⟩
                                · exact (by decide : ExactOddStep 1 94660742170921299263 141991113256381948895)
                                · refine ⟨212986669884572923343, ?_, ?_⟩
                                  · exact (by decide : ExactOddStep 1 141991113256381948895 212986669884572923343)
                                  · refine ⟨319480004826859385015, ?_, ?_⟩
                                    · exact (by decide : ExactOddStep 1 212986669884572923343 319480004826859385015)
                                    · refine ⟨479220007240289077523, ?_, ?_⟩
                                      · exact (by decide : ExactOddStep 1 319480004826859385015 479220007240289077523)
                                      · refine ⟨718830010860433616285, ?_, ?_⟩
                                        · exact (by decide : ExactOddStep 1 479220007240289077523 718830010860433616285)
                                        · refine ⟨269561254072662606107, ?_, ?_⟩
                                          · exact (by decide : ExactOddStep 3 718830010860433616285 269561254072662606107)
                                          · refine ⟨404341881108993909161, ?_, ?_⟩
                                            · exact (by decide : ExactOddStep 1 269561254072662606107 404341881108993909161)
                                            · refine ⟨303256410831745431871, ?_, ?_⟩
                                              · exact (by decide : ExactOddStep 2 404341881108993909161 303256410831745431871)
                                              · refine ⟨454884616247618147807, ?_, ?_⟩
                                                · exact (by decide : ExactOddStep 1 303256410831745431871 454884616247618147807)
                                                · refine ⟨682326924371427221711, ?_, ?_⟩
                                                  · exact (by decide : ExactOddStep 1 454884616247618147807 682326924371427221711)
                                                  · refine ⟨1023490386557140832567, ?_, ?_⟩
                                                    · exact (by decide : ExactOddStep 1 682326924371427221711 1023490386557140832567)
                                                    · refine ⟨1535235579835711248851, ?_, ?_⟩
                                                      · exact (by decide : ExactOddStep 1 1023490386557140832567 1535235579835711248851)
                                                      · refine ⟨2302853369753566873277, ?_, ?_⟩
                                                        · exact (by decide : ExactOddStep 1 1535235579835711248851 2302853369753566873277)
                                                        · refine ⟨863570013657587577479, ?_, ?_⟩
                                                          · exact (by decide : ExactOddStep 3 2302853369753566873277 863570013657587577479)
                                                          · refine ⟨1295355020486381366219, ?_, ?_⟩
                                                            · exact (by decide : ExactOddStep 1 863570013657587577479 1295355020486381366219)
                                                            · refine ⟨1943032530729572049329, ?_, ?_⟩
                                                              · exact (by decide : ExactOddStep 1 1295355020486381366219 1943032530729572049329)
                                                              · refine ⟨1457274398047179036997, ?_, ?_⟩
                                                                · exact (by decide : ExactOddStep 2 1943032530729572049329 1457274398047179036997)
                                                                · refine ⟨273238949633846069437, ?_, ?_⟩
                                                                  · exact (by decide : ExactOddStep 4 1457274398047179036997 273238949633846069437)
                                                                  · refine ⟨102464606112692276039, ?_, ?_⟩
                                                                    · exact (by decide : ExactOddStep 3 273238949633846069437 102464606112692276039)
                                                                    · refine ⟨153696909169038414059, ?_, ?_⟩
                                                                      · exact (by decide : ExactOddStep 1 102464606112692276039 153696909169038414059)
                                                                      · refine ⟨230545363753557621089, ?_, ?_⟩
                                                                        · exact (by decide : ExactOddStep 1 153696909169038414059 230545363753557621089)
                                                                        · refine ⟨172909022815168215817, ?_, ?_⟩
                                                                          · exact (by decide : ExactOddStep 2 230545363753557621089 172909022815168215817)
                                                                          · refine ⟨129681767111376161863, ?_, ?_⟩
                                                                            · exact (by decide : ExactOddStep 2 172909022815168215817 129681767111376161863)
                                                                            · refine ⟨194522650667064242795, ?_, ?_⟩
                                                                              · exact (by decide : ExactOddStep 1 129681767111376161863 194522650667064242795)
                                                                              · refine ⟨291783976000596364193, ?_, ?_⟩
                                                                                · exact (by decide : ExactOddStep 1 194522650667064242795 291783976000596364193)
                                                                                · refine ⟨218837982000447273145, ?_, ?_⟩
                                                                                  · exact (by decide : ExactOddStep 2 291783976000596364193 218837982000447273145)
                                                                                  · refine ⟨164128486500335454859, ?_, ?_⟩
                                                                                    · exact (by decide : ExactOddStep 2 218837982000447273145 164128486500335454859)
                                                                                    · refine ⟨246192729750503182289, ?_, ?_⟩
                                                                                      · exact (by decide : ExactOddStep 1 164128486500335454859 246192729750503182289)
                                                                                      · refine ⟨184644547312877386717, ?_, ?_⟩
                                                                                        · exact (by decide : ExactOddStep 2 246192729750503182289 184644547312877386717)
                                                                                        · refine ⟨69241705242329020019, ?_, ?_⟩
                                                                                          · exact (by decide : ExactOddStep 3 184644547312877386717 69241705242329020019)
                                                                                          · refine ⟨103862557863493530029, ?_, ?_⟩
                                                                                            · exact (by decide : ExactOddStep 1 69241705242329020019 103862557863493530029)
                                                                                            · refine ⟨38948459198810073761, ?_, ?_⟩
                                                                                              · exact (by decide : ExactOddStep 3 103862557863493530029 38948459198810073761)
                                                                                              · refine ⟨29211344399107555321, ?_, ?_⟩
                                                                                                · exact (by decide : ExactOddStep 2 38948459198810073761 29211344399107555321)
                                                                                                · refine ⟨21908508299330666491, ?_, ?_⟩
                                                                                                  · exact (by decide : ExactOddStep 2 29211344399107555321 21908508299330666491)
                                                                                                  · refine ⟨32862762448995999737, ?_, ?_⟩
                                                                                                    · exact (by decide : ExactOddStep 1 21908508299330666491 32862762448995999737)
                                                                                                    · refine ⟨24647071836746999803, ?_, ?_⟩
                                                                                                      · exact (by decide : ExactOddStep 2 32862762448995999737 24647071836746999803)
                                                                                                      · refine ⟨36970607755120499705, ?_, ?_⟩
                                                                                                        · exact (by decide : ExactOddStep 1 24647071836746999803 36970607755120499705)
                                                                                                        · refine ⟨27727955816340374779, ?_, ?_⟩
                                                                                                          · exact (by decide : ExactOddStep 2 36970607755120499705 27727955816340374779)
                                                                                                          · refine ⟨41591933724510562169, ?_, ?_⟩
                                                                                                            · exact (by decide : ExactOddStep 1 27727955816340374779 41591933724510562169)
                                                                                                            · refine ⟨31193950293382921627, ?_, ?_⟩
                                                                                                              · exact (by decide : ExactOddStep 2 41591933724510562169 31193950293382921627)
                                                                                                              · refine ⟨46790925440074382441, ?_, ?_⟩
                                                                                                                · exact (by decide : ExactOddStep 1 31193950293382921627 46790925440074382441)
                                                                                                                · refine ⟨35093194080055786831, ?_, ?_⟩
                                                                                                                  · exact (by decide : ExactOddStep 2 46790925440074382441 35093194080055786831)
                                                                                                                  · refine ⟨52639791120083680247, ?_, ?_⟩
                                                                                                                    · exact (by decide : ExactOddStep 1 35093194080055786831 52639791120083680247)
                                                                                                                    · refine ⟨78959686680125520371, ?_, ?_⟩
                                                                                                                      · exact (by decide : ExactOddStep 1 52639791120083680247 78959686680125520371)
                                                                                                                      · refine ⟨118439530020188280557, ?_, ?_⟩
                                                                                                                        · exact (by decide : ExactOddStep 1 78959686680125520371 118439530020188280557)
                                                                                                                        · refine ⟨44414823757570605209, ?_, ?_⟩
                                                                                                                          · exact (by decide : ExactOddStep 3 118439530020188280557 44414823757570605209)
                                                                                                                          · refine ⟨33311117818177953907, ?_, ?_⟩
                                                                                                                            · exact (by decide : ExactOddStep 2 44414823757570605209 33311117818177953907)
                                                                                                                            · refine ⟨49966676727266930861, ?_, ?_⟩
                                                                                                                              · exact (by decide : ExactOddStep 1 33311117818177953907 49966676727266930861)
                                                                                                                              · refine ⟨18737503772725099073, ?_, ?_⟩
                                                                                                                                · exact (by decide : ExactOddStep 3 49966676727266930861 18737503772725099073)
                                                                                                                                · refine ⟨14053127829543824305, ?_, ?_⟩
                                                                                                                                  · exact (by decide : ExactOddStep 2 18737503772725099073 14053127829543824305)
                                                                                                                                  · refine ⟨10539845872157868229, ?_, ?_⟩
                                                                                                                                    · exact (by decide : ExactOddStep 2 14053127829543824305 10539845872157868229)
                                                                                                                                    · refine ⟨1976221101029600293, ?_, ?_⟩
                                                                                                                                      · exact (by decide : ExactOddStep 4 10539845872157868229 1976221101029600293)
                                                                                                                                      · rfl

/-- Every lift of family 23 descends after its exact accelerated word. -/
theorem family_23_all_lifts (q : Nat) :
    ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 3, 2, 2, 1, 2, 1, 2, 1, 2, 1, 2, 1, 1, 1, 3, 2, 1, 3, 2, 2, 4] (6917529145782042651 + q * 2 ^ 109) endpoint ∧
      endpoint < 6917529145782042651 + q * 2 ^ 109 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 3, 2, 2, 1, 2, 1, 2, 1, 2, 1, 2, 1, 1, 1, 3, 2, 1, 3, 2, 2, 4] family_23_trace (by decide) (by decide) (by decide) q

/-- Family 24: exact representative trace from the pinned input. -/
theorem family_24_trace : WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 1, 1, 2, 1, 2, 3, 1, 2, 3, 1, 3, 1, 3, 2, 1, 1, 1, 2, 1, 3, 2, 1, 4] 4611686136568348699 1482165838428778243 := by
  simp only [WordTrace]
  refine ⟨6917529204852523049, ?_, ?_⟩
  · exact (by decide : ExactOddStep 1 4611686136568348699 6917529204852523049)
  · refine ⟨5188146903639392287, ?_, ?_⟩
    · exact (by decide : ExactOddStep 2 6917529204852523049 5188146903639392287)
    · refine ⟨7782220355459088431, ?_, ?_⟩
      · exact (by decide : ExactOddStep 1 5188146903639392287 7782220355459088431)
      · refine ⟨11673330533188632647, ?_, ?_⟩
        · exact (by decide : ExactOddStep 1 7782220355459088431 11673330533188632647)
        · refine ⟨17509995799782948971, ?_, ?_⟩
          · exact (by decide : ExactOddStep 1 11673330533188632647 17509995799782948971)
          · refine ⟨26264993699674423457, ?_, ?_⟩
            · exact (by decide : ExactOddStep 1 17509995799782948971 26264993699674423457)
            · refine ⟨19698745274755817593, ?_, ?_⟩
              · exact (by decide : ExactOddStep 2 26264993699674423457 19698745274755817593)
              · refine ⟨14774058956066863195, ?_, ?_⟩
                · exact (by decide : ExactOddStep 2 19698745274755817593 14774058956066863195)
                · refine ⟨22161088434100294793, ?_, ?_⟩
                  · exact (by decide : ExactOddStep 1 14774058956066863195 22161088434100294793)
                  · refine ⟨16620816325575221095, ?_, ?_⟩
                    · exact (by decide : ExactOddStep 2 22161088434100294793 16620816325575221095)
                    · refine ⟨24931224488362831643, ?_, ?_⟩
                      · exact (by decide : ExactOddStep 1 16620816325575221095 24931224488362831643)
                      · refine ⟨37396836732544247465, ?_, ?_⟩
                        · exact (by decide : ExactOddStep 1 24931224488362831643 37396836732544247465)
                        · refine ⟨28047627549408185599, ?_, ?_⟩
                          · exact (by decide : ExactOddStep 2 37396836732544247465 28047627549408185599)
                          · refine ⟨42071441324112278399, ?_, ?_⟩
                            · exact (by decide : ExactOddStep 1 28047627549408185599 42071441324112278399)
                            · refine ⟨63107161986168417599, ?_, ?_⟩
                              · exact (by decide : ExactOddStep 1 42071441324112278399 63107161986168417599)
                              · refine ⟨94660742979252626399, ?_, ?_⟩
                                · exact (by decide : ExactOddStep 1 63107161986168417599 94660742979252626399)
                                · refine ⟨141991114468878939599, ?_, ?_⟩
                                  · exact (by decide : ExactOddStep 1 94660742979252626399 141991114468878939599)
                                  · refine ⟨212986671703318409399, ?_, ?_⟩
                                    · exact (by decide : ExactOddStep 1 141991114468878939599 212986671703318409399)
                                    · refine ⟨319480007554977614099, ?_, ?_⟩
                                      · exact (by decide : ExactOddStep 1 212986671703318409399 319480007554977614099)
                                      · refine ⟨479220011332466421149, ?_, ?_⟩
                                        · exact (by decide : ExactOddStep 1 319480007554977614099 479220011332466421149)
                                        · refine ⟨179707504249674907931, ?_, ?_⟩
                                          · exact (by decide : ExactOddStep 3 479220011332466421149 179707504249674907931)
                                          · refine ⟨269561256374512361897, ?_, ?_⟩
                                            · exact (by decide : ExactOddStep 1 179707504249674907931 269561256374512361897)
                                            · refine ⟨202170942280884271423, ?_, ?_⟩
                                              · exact (by decide : ExactOddStep 2 269561256374512361897 202170942280884271423)
                                              · refine ⟨303256413421326407135, ?_, ?_⟩
                                                · exact (by decide : ExactOddStep 1 202170942280884271423 303256413421326407135)
                                                · refine ⟨454884620131989610703, ?_, ?_⟩
                                                  · exact (by decide : ExactOddStep 1 303256413421326407135 454884620131989610703)
                                                  · refine ⟨682326930197984416055, ?_, ?_⟩
                                                    · exact (by decide : ExactOddStep 1 454884620131989610703 682326930197984416055)
                                                    · refine ⟨1023490395296976624083, ?_, ?_⟩
                                                      · exact (by decide : ExactOddStep 1 682326930197984416055 1023490395296976624083)
                                                      · refine ⟨1535235592945464936125, ?_, ?_⟩
                                                        · exact (by decide : ExactOddStep 1 1023490395296976624083 1535235592945464936125)
                                                        · refine ⟨575713347354549351047, ?_, ?_⟩
                                                          · exact (by decide : ExactOddStep 3 1535235592945464936125 575713347354549351047)
                                                          · refine ⟨863570021031824026571, ?_, ?_⟩
                                                            · exact (by decide : ExactOddStep 1 575713347354549351047 863570021031824026571)
                                                            · refine ⟨1295355031547736039857, ?_, ?_⟩
                                                              · exact (by decide : ExactOddStep 1 863570021031824026571 1295355031547736039857)
                                                              · refine ⟨971516273660802029893, ?_, ?_⟩
                                                                · exact (by decide : ExactOddStep 2 1295355031547736039857 971516273660802029893)
                                                                · refine ⟨182159301311400380605, ?_, ?_⟩
                                                                  · exact (by decide : ExactOddStep 4 971516273660802029893 182159301311400380605)
                                                                  · refine ⟨68309737991775142727, ?_, ?_⟩
                                                                    · exact (by decide : ExactOddStep 3 182159301311400380605 68309737991775142727)
                                                                    · refine ⟨102464606987662714091, ?_, ?_⟩
                                                                      · exact (by decide : ExactOddStep 1 68309737991775142727 102464606987662714091)
                                                                      · refine ⟨153696910481494071137, ?_, ?_⟩
                                                                        · exact (by decide : ExactOddStep 1 102464606987662714091 153696910481494071137)
                                                                        · refine ⟨115272682861120553353, ?_, ?_⟩
                                                                          · exact (by decide : ExactOddStep 2 153696910481494071137 115272682861120553353)
                                                                          · refine ⟨86454512145840415015, ?_, ?_⟩
                                                                            · exact (by decide : ExactOddStep 2 115272682861120553353 86454512145840415015)
                                                                            · refine ⟨129681768218760622523, ?_, ?_⟩
                                                                              · exact (by decide : ExactOddStep 1 86454512145840415015 129681768218760622523)
                                                                              · refine ⟨194522652328140933785, ?_, ?_⟩
                                                                                · exact (by decide : ExactOddStep 1 129681768218760622523 194522652328140933785)
                                                                                · refine ⟨145891989246105700339, ?_, ?_⟩
                                                                                  · exact (by decide : ExactOddStep 2 194522652328140933785 145891989246105700339)
                                                                                  · refine ⟨218837983869158550509, ?_, ?_⟩
                                                                                    · exact (by decide : ExactOddStep 1 145891989246105700339 218837983869158550509)
                                                                                    · refine ⟨82064243950934456441, ?_, ?_⟩
                                                                                      · exact (by decide : ExactOddStep 3 218837983869158550509 82064243950934456441)
                                                                                      · refine ⟨61548182963200842331, ?_, ?_⟩
                                                                                        · exact (by decide : ExactOddStep 2 82064243950934456441 61548182963200842331)
                                                                                        · refine ⟨92322274444801263497, ?_, ?_⟩
                                                                                          · exact (by decide : ExactOddStep 1 61548182963200842331 92322274444801263497)
                                                                                          · refine ⟨69241705833600947623, ?_, ?_⟩
                                                                                            · exact (by decide : ExactOddStep 2 92322274444801263497 69241705833600947623)
                                                                                            · refine ⟨103862558750401421435, ?_, ?_⟩
                                                                                              · exact (by decide : ExactOddStep 1 69241705833600947623 103862558750401421435)
                                                                                              · refine ⟨155793838125602132153, ?_, ?_⟩
                                                                                                · exact (by decide : ExactOddStep 1 103862558750401421435 155793838125602132153)
                                                                                                · refine ⟨116845378594201599115, ?_, ?_⟩
                                                                                                  · exact (by decide : ExactOddStep 2 155793838125602132153 116845378594201599115)
                                                                                                  · refine ⟨175268067891302398673, ?_, ?_⟩
                                                                                                    · exact (by decide : ExactOddStep 1 116845378594201599115 175268067891302398673)
                                                                                                    · refine ⟨131451050918476799005, ?_, ?_⟩
                                                                                                      · exact (by decide : ExactOddStep 2 175268067891302398673 131451050918476799005)
                                                                                                      · refine ⟨49294144094428799627, ?_, ?_⟩
                                                                                                        · exact (by decide : ExactOddStep 3 131451050918476799005 49294144094428799627)
                                                                                                        · refine ⟨73941216141643199441, ?_, ?_⟩
                                                                                                          · exact (by decide : ExactOddStep 1 49294144094428799627 73941216141643199441)
                                                                                                          · refine ⟨55455912106232399581, ?_, ?_⟩
                                                                                                            · exact (by decide : ExactOddStep 2 73941216141643199441 55455912106232399581)
                                                                                                            · refine ⟨20795967039837149843, ?_, ?_⟩
                                                                                                              · exact (by decide : ExactOddStep 3 55455912106232399581 20795967039837149843)
                                                                                                              · refine ⟨31193950559755724765, ?_, ?_⟩
                                                                                                                · exact (by decide : ExactOddStep 1 20795967039837149843 31193950559755724765)
                                                                                                                · refine ⟨11697731459908396787, ?_, ?_⟩
                                                                                                                  · exact (by decide : ExactOddStep 3 31193950559755724765 11697731459908396787)
                                                                                                                  · refine ⟨17546597189862595181, ?_, ?_⟩
                                                                                                                    · exact (by decide : ExactOddStep 1 11697731459908396787 17546597189862595181)
                                                                                                                    · refine ⟨6579973946198473193, ?_, ?_⟩
                                                                                                                      · exact (by decide : ExactOddStep 3 17546597189862595181 6579973946198473193)
                                                                                                                      · refine ⟨4934980459648854895, ?_, ?_⟩
                                                                                                                        · exact (by decide : ExactOddStep 2 6579973946198473193 4934980459648854895)
                                                                                                                        · refine ⟨7402470689473282343, ?_, ?_⟩
                                                                                                                          · exact (by decide : ExactOddStep 1 4934980459648854895 7402470689473282343)
                                                                                                                          · refine ⟨11103706034209923515, ?_, ?_⟩
                                                                                                                            · exact (by decide : ExactOddStep 1 7402470689473282343 11103706034209923515)
                                                                                                                            · refine ⟨16655559051314885273, ?_, ?_⟩
                                                                                                                              · exact (by decide : ExactOddStep 1 11103706034209923515 16655559051314885273)
                                                                                                                              · refine ⟨12491669288486163955, ?_, ?_⟩
                                                                                                                                · exact (by decide : ExactOddStep 2 16655559051314885273 12491669288486163955)
                                                                                                                                · refine ⟨18737503932729245933, ?_, ?_⟩
                                                                                                                                  · exact (by decide : ExactOddStep 1 12491669288486163955 18737503932729245933)
                                                                                                                                  · refine ⟨7026563974773467225, ?_, ?_⟩
                                                                                                                                    · exact (by decide : ExactOddStep 3 18737503932729245933 7026563974773467225)
                                                                                                                                    · refine ⟨5269922981080100419, ?_, ?_⟩
                                                                                                                                      · exact (by decide : ExactOddStep 2 7026563974773467225 5269922981080100419)
                                                                                                                                      · refine ⟨7904884471620150629, ?_, ?_⟩
                                                                                                                                        · exact (by decide : ExactOddStep 1 5269922981080100419 7904884471620150629)
                                                                                                                                        · refine ⟨1482165838428778243, ?_, ?_⟩
                                                                                                                                          · exact (by decide : ExactOddStep 4 7904884471620150629 1482165838428778243)
                                                                                                                                          · rfl

/-- Every lift of family 24 descends after its exact accelerated word. -/
theorem family_24_all_lifts (q : Nat) :
    ∃ endpoint, WordTrace [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 1, 1, 2, 1, 2, 3, 1, 2, 3, 1, 3, 1, 3, 2, 1, 1, 1, 2, 1, 3, 2, 1, 4] (4611686136568348699 + q * 2 ^ 112) endpoint ∧
      endpoint < 4611686136568348699 + q * 2 ^ 112 := by
  exact family_descends [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 1, 1, 2, 1, 2, 3, 1, 2, 3, 1, 3, 1, 3, 2, 1, 1, 1, 2, 1, 3, 2, 1, 4] family_24_trace (by decide) (by decide) (by decide) q

#print axioms family_1_all_lifts
#print axioms family_2_all_lifts
#print axioms family_3_all_lifts
#print axioms family_4_all_lifts
#print axioms family_5_all_lifts
#print axioms family_6_all_lifts
#print axioms family_7_all_lifts
#print axioms family_8_all_lifts
#print axioms family_9_all_lifts
#print axioms family_10_all_lifts
#print axioms family_11_all_lifts
#print axioms family_12_all_lifts
#print axioms family_13_all_lifts
#print axioms family_14_all_lifts
#print axioms family_15_all_lifts
#print axioms family_16_all_lifts
#print axioms family_17_all_lifts
#print axioms family_18_all_lifts
#print axioms family_19_all_lifts
#print axioms family_20_all_lifts
#print axioms family_21_all_lifts
#print axioms family_22_all_lifts
#print axioms family_23_all_lifts
#print axioms family_24_all_lifts

end CollatzCertificate24
