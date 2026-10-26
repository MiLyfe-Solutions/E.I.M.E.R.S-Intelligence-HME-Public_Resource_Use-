import V185TrunkScan23Chunk0063

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_378455 : List Nat := [1, 1, 3, 2, 2, 3, 2, 2, 2, 5]
def baseStart_378455 : Nat := 118140960795 + 378455 * 2 ^ 59
def prefixEnd_378455 : Nat := 4983230072969 + 3 ^ 40 * 378455 * 2
def baseEnd_378455 : Nat := 64776440365807342257341

theorem tailTrace_378455 : CollatzResearch.WordTrace tailWord_378455 prefixEnd_378455 64776440365807342257341 := by
  unfold tailWord_378455
  simp only [CollatzResearch.WordTrace]
  refine ⟨13803387843929644813256819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9202258562619763208837879 13803387843929644813256819)
  ·
    refine ⟨20705081765894467219885229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13803387843929644813256819 20705081765894467219885229)
    ·
      refine ⟨7764405662210425207456961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20705081765894467219885229 7764405662210425207456961)
      ·
        refine ⟨5823304246657818905592721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7764405662210425207456961 5823304246657818905592721)
        ·
          refine ⟨4367478184993364179194541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5823304246657818905592721 4367478184993364179194541)
          ·
            refine ⟨1637804319372511567197953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4367478184993364179194541 1637804319372511567197953)
            ·
              refine ⟨1228353239529383675398465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1637804319372511567197953 1228353239529383675398465)
              ·
                refine ⟨921264929647037756548849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1228353239529383675398465 921264929647037756548849)
                ·
                  refine ⟨690948697235278317411637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 921264929647037756548849 690948697235278317411637)
                  ·
                    refine ⟨64776440365807342257341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 690948697235278317411637 64776440365807342257341)
                    ·
                      rfl

theorem cell23_378455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 2, 2, 2, 5].length) (baseStart_378455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_378455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_378455 prefixEnd_378455 := by exact prefixLift 378455
  have htrace : WordTrace (prefixWord ++ tailWord_378455) baseStart_378455 baseEnd_378455 := by
    simpa [prefixWord, tailWord_378455, baseEnd_378455] using wordTrace_append hprefix tailTrace_378455
  have hstable : (prefixWord ++ tailWord_378455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_378455).length < 2 ^ (prefixWord ++ tailWord_378455).sum := by decide
  have hdescent : baseEnd_378455 < baseStart_378455 := by decide
  rcases family_descends (prefixWord ++ tailWord_378455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_378488 : List Nat := [2, 1, 2, 1, 1, 1, 2, 1, 3, 3, 6]
def baseStart_378488 : Nat := 118140960795 + 378488 * 2 ^ 59
def prefixEnd_378488 : Nat := 4983230072969 + 3 ^ 40 * 378488 * 2
def baseEnd_378488 : Nat := 194346265959020397659371

theorem tailTrace_378488 : CollatzResearch.WordTrace tailWord_378488 prefixEnd_378488 194346265959020397659371 := by
  unfold tailWord_378488
  simp only [CollatzResearch.WordTrace]
  refine ⟨6902295726405045724604059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9203060968540060966138745 6902295726405045724604059)
  ·
    refine ⟨10353443589607568586906089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6902295726405045724604059 10353443589607568586906089)
    ·
      refine ⟨7765082692205676440179567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10353443589607568586906089 7765082692205676440179567)
      ·
        refine ⟨11647624038308514660269351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7765082692205676440179567 11647624038308514660269351)
        ·
          refine ⟨17471436057462771990404027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11647624038308514660269351 17471436057462771990404027)
          ·
            refine ⟨26207154086194157985606041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17471436057462771990404027 26207154086194157985606041)
            ·
              refine ⟨19655365564645618489204531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26207154086194157985606041 19655365564645618489204531)
              ·
                refine ⟨29483048346968427733806797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19655365564645618489204531 29483048346968427733806797)
                ·
                  refine ⟨11056143130113160400177549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29483048346968427733806797 11056143130113160400177549)
                  ·
                    refine ⟨4146053673792435150066581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11056143130113160400177549 4146053673792435150066581)
                    ·
                      refine ⟨194346265959020397659371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 4146053673792435150066581 194346265959020397659371)
                      ·
                        rfl

theorem cell23_378488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 1, 3, 3, 6].length) (baseStart_378488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_378488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_378488 prefixEnd_378488 := by exact prefixLift 378488
  have htrace : WordTrace (prefixWord ++ tailWord_378488) baseStart_378488 baseEnd_378488 := by
    simpa [prefixWord, tailWord_378488, baseEnd_378488] using wordTrace_append hprefix tailTrace_378488
  have hstable : (prefixWord ++ tailWord_378488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_378488).length < 2 ^ (prefixWord ++ tailWord_378488).sum := by decide
  have hdescent : baseEnd_378488 < baseStart_378488 := by decide
  rcases family_descends (prefixWord ++ tailWord_378488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_378519 : List Nat := [1, 1, 3, 3, 2, 2, 2, 4, 1, 4]
def baseStart_378519 : Nat := 118140960795 + 378519 * 2 ^ 59
def prefixEnd_378519 : Nat := 4983230072969 + 3 ^ 40 * 378519 * 2
def baseEnd_378519 : Nat := 64787394619769925457243

theorem tailTrace_378519 : CollatzResearch.WordTrace tailWord_378519 prefixEnd_378519 64787394619769925457243 := by
  unfold tailWord_378519
  simp only [CollatzResearch.WordTrace]
  refine ⟨13805722115697783743586611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9203814743798522495724407 13805722115697783743586611)
  ·
    refine ⟨20708583173546675615379917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13805722115697783743586611 20708583173546675615379917)
    ·
      refine ⟨7765718690080003355767469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20708583173546675615379917 7765718690080003355767469)
      ·
        refine ⟨2912144508780001258412801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7765718690080003355767469 2912144508780001258412801)
        ·
          refine ⟨2184108381585000943809601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2912144508780001258412801 2184108381585000943809601)
          ·
            refine ⟨1638081286188750707857201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2184108381585000943809601 1638081286188750707857201)
            ·
              refine ⟨1228560964641563030892901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1638081286188750707857201 1228560964641563030892901)
              ·
                refine ⟨230355180870293068292419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1228560964641563030892901 230355180870293068292419)
                ·
                  refine ⟨345532771305439602438629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 230355180870293068292419 345532771305439602438629)
                  ·
                    refine ⟨64787394619769925457243, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 345532771305439602438629 64787394619769925457243)
                    ·
                      rfl

theorem cell23_378519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 2, 4, 1, 4].length) (baseStart_378519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_378519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_378519 prefixEnd_378519 := by exact prefixLift 378519
  have htrace : WordTrace (prefixWord ++ tailWord_378519) baseStart_378519 baseEnd_378519 := by
    simpa [prefixWord, tailWord_378519, baseEnd_378519] using wordTrace_append hprefix tailTrace_378519
  have hstable : (prefixWord ++ tailWord_378519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_378519).length < 2 ^ (prefixWord ++ tailWord_378519).sum := by decide
  have hdescent : baseEnd_378519 < baseStart_378519 := by decide
  rcases family_descends (prefixWord ++ tailWord_378519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_378552 : List Nat := [2, 1, 2, 1, 2, 1, 1, 2, 6, 3, 2]
def baseStart_378552 : Nat := 118140960795 + 378552 * 2 ^ 59
def prefixEnd_378552 : Nat := 4983230072969 + 3 ^ 40 * 378552 * 2
def baseEnd_378552 : Nat := 194379128720908147259077

theorem tailTrace_378552 : CollatzResearch.WordTrace tailWord_378552 prefixEnd_378552 194379128720908147259077 := by
  unfold tailWord_378552
  simp only [CollatzResearch.WordTrace]
  refine ⟨6903462862289115189768955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9204617149718820253025273 6903462862289115189768955)
  ·
    refine ⟨10355194293433672784653433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6903462862289115189768955 10355194293433672784653433)
    ·
      refine ⟨7766395720075254588490075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10355194293433672784653433 7766395720075254588490075)
      ·
        refine ⟨11649593580112881882735113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7766395720075254588490075 11649593580112881882735113)
        ·
          refine ⟨8737195185084661412051335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11649593580112881882735113 8737195185084661412051335)
          ·
            refine ⟨13105792777626992118077003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8737195185084661412051335 13105792777626992118077003)
            ·
              refine ⟨19658689166440488177115505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13105792777626992118077003 19658689166440488177115505)
              ·
                refine ⟨14744016874830366132836629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19658689166440488177115505 14744016874830366132836629)
                ·
                  refine ⟨691125791007673412476717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 14744016874830366132836629 691125791007673412476717)
                  ·
                    refine ⟨259172171627877529678769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 691125791007673412476717 259172171627877529678769)
                    ·
                      refine ⟨194379128720908147259077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 259172171627877529678769 194379128720908147259077)
                      ·
                        rfl

theorem cell23_378552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 2, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 2, 6, 3, 2].length) (baseStart_378552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_378552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_378552 prefixEnd_378552 := by exact prefixLift 378552
  have htrace : WordTrace (prefixWord ++ tailWord_378552) baseStart_378552 baseEnd_378552 := by
    simpa [prefixWord, tailWord_378552, baseEnd_378552] using wordTrace_append hprefix tailTrace_378552
  have hstable : (prefixWord ++ tailWord_378552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_378552).length < 2 ^ (prefixWord ++ tailWord_378552).sum := by decide
  have hdescent : baseEnd_378552 < baseStart_378552 := by decide
  rcases family_descends (prefixWord ++ tailWord_378552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_378622 : List Nat := [4, 2, 2, 1, 3, 11]
def baseStart_378622 : Nat := 118140960795 + 378622 * 2 ^ 59
def prefixEnd_378622 : Nat := 4983230072969 + 3 ^ 40 * 378622 * 2
def baseEnd_378622 : Nat := 800062026200505651785

theorem tailTrace_378622 : CollatzResearch.WordTrace tailWord_378622 prefixEnd_378622 800062026200505651785 := by
  unfold tailWord_378622
  simp only [CollatzResearch.WordTrace]
  refine ⟨1726184854290579041823265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9206319222883088223057413 1726184854290579041823265)
  ·
    refine ⟨1294638640717934281367449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1726184854290579041823265 1294638640717934281367449)
    ·
      refine ⟨970978980538450711025587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1294638640717934281367449 970978980538450711025587)
      ·
        refine ⟨1456468470807676066538381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 970978980538450711025587 1456468470807676066538381)
        ·
          refine ⟨546175676552878524951893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1456468470807676066538381 546175676552878524951893)
          ·
            refine ⟨800062026200505651785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 546175676552878524951893 800062026200505651785)
            ·
              rfl

theorem cell23_378622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 11].length) (baseStart_378622 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_378622 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_378622 prefixEnd_378622 := by exact prefixLift 378622
  have htrace : WordTrace (prefixWord ++ tailWord_378622) baseStart_378622 baseEnd_378622 := by
    simpa [prefixWord, tailWord_378622, baseEnd_378622] using wordTrace_append hprefix tailTrace_378622
  have hstable : (prefixWord ++ tailWord_378622).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_378622).length < 2 ^ (prefixWord ++ tailWord_378622).sum := by decide
  have hdescent : baseEnd_378622 < baseStart_378622 := by decide
  rcases family_descends (prefixWord ++ tailWord_378622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_378626 : List Nat := [3, 4, 1, 1, 1, 1, 4, 2, 2, 4]
def baseStart_378626 : Nat := 118140960795 + 378626 * 2 ^ 59
def prefixEnd_378626 : Nat := 4983230072969 + 3 ^ 40 * 378626 * 2
def baseEnd_378626 : Nat := 64805708763113619244579

theorem tailTrace_378626 : CollatzResearch.WordTrace tailWord_378626 prefixEnd_378626 64805708763113619244579 := by
  unfold tailWord_378626
  simp only [CollatzResearch.WordTrace]
  refine ⟨3452406181577535254432933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9206416484206760678487821 3452406181577535254432933)
  ·
    refine ⟨647326159045787860206175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3452406181577535254432933 647326159045787860206175)
    ·
      refine ⟨970989238568681790309263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 647326159045787860206175 970989238568681790309263)
      ·
        refine ⟨1456483857853022685463895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 970989238568681790309263 1456483857853022685463895)
        ·
          refine ⟨2184725786779534028195843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1456483857853022685463895 2184725786779534028195843)
          ·
            refine ⟨3277088680169301042293765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2184725786779534028195843 3277088680169301042293765)
            ·
              refine ⟨614454127531743945430081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3277088680169301042293765 614454127531743945430081)
              ·
                refine ⟨460840595648807959072561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 614454127531743945430081 460840595648807959072561)
                ·
                  refine ⟨345630446736605969304421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 460840595648807959072561 345630446736605969304421)
                  ·
                    refine ⟨64805708763113619244579, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 345630446736605969304421 64805708763113619244579)
                    ·
                      rfl

theorem cell23_378626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 4, 2, 2, 4].length) (baseStart_378626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_378626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_378626 prefixEnd_378626 := by exact prefixLift 378626
  have htrace : WordTrace (prefixWord ++ tailWord_378626) baseStart_378626 baseEnd_378626 := by
    simpa [prefixWord, tailWord_378626, baseEnd_378626] using wordTrace_append hprefix tailTrace_378626
  have hstable : (prefixWord ++ tailWord_378626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_378626).length < 2 ^ (prefixWord ++ tailWord_378626).sum := by decide
  have hdescent : baseEnd_378626 < baseStart_378626 := by decide
  rcases family_descends (prefixWord ++ tailWord_378626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_378632 : List Nat := [2, 1, 3, 2, 2, 1, 1, 2, 3, 3, 3]
def baseStart_378632 : Nat := 118140960795 + 378632 * 2 ^ 59
def prefixEnd_378632 : Nat := 4983230072969 + 3 ^ 40 * 378632 * 2
def baseEnd_378632 : Nat := 194420207173267834258709

theorem tailTrace_378632 : CollatzResearch.WordTrace tailWord_378632 prefixEnd_378632 194420207173267834258709 := by
  unfold tailWord_378632
  simp only [CollatzResearch.WordTrace]
  refine ⟨6904921782144202021225075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9206562376192269361633433 6904921782144202021225075)
  ·
    refine ⟨10357382673216303031837613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6904921782144202021225075 10357382673216303031837613)
    ·
      refine ⟨3884018502456113636939105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10357382673216303031837613 3884018502456113636939105)
      ·
        refine ⟨2913013876842085227704329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3884018502456113636939105 2913013876842085227704329)
        ·
          refine ⟨2184760407631563920778247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2913013876842085227704329 2184760407631563920778247)
          ·
            refine ⟨3277140611447345881167371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2184760407631563920778247 3277140611447345881167371)
            ·
              refine ⟨4915710917171018821751057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3277140611447345881167371 4915710917171018821751057)
              ·
                refine ⟨3686783187878264116313293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4915710917171018821751057 3686783187878264116313293)
                ·
                  refine ⟨1382543695454349043617485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3686783187878264116313293 1382543695454349043617485)
                  ·
                    refine ⟨518453885795380891356557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1382543695454349043617485 518453885795380891356557)
                    ·
                      refine ⟨194420207173267834258709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 518453885795380891356557 194420207173267834258709)
                      ·
                        rfl

theorem cell23_378632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 1, 2, 3, 3, 3].length) (baseStart_378632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_378632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_378632 prefixEnd_378632 := by exact prefixLift 378632
  have htrace : WordTrace (prefixWord ++ tailWord_378632) baseStart_378632 baseEnd_378632 := by
    simpa [prefixWord, tailWord_378632, baseEnd_378632] using wordTrace_append hprefix tailTrace_378632
  have hstable : (prefixWord ++ tailWord_378632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_378632).length < 2 ^ (prefixWord ++ tailWord_378632).sum := by decide
  have hdescent : baseEnd_378632 < baseStart_378632 := by decide
  rcases family_descends (prefixWord ++ tailWord_378632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_378635 : List Nat := [1, 1, 1, 1, 5, 1, 3, 1, 2, 7]
def baseStart_378635 : Nat := 118140960795 + 378635 * 2 ^ 59
def prefixEnd_378635 : Nat := 4983230072969 + 3 ^ 40 * 378635 * 2
def baseEnd_378635 : Nat := 64807249205077107507065

theorem tailTrace_378635 : CollatzResearch.WordTrace tailWord_378635 prefixEnd_378635 64807249205077107507065 := by
  unfold tailWord_378635
  simp only [CollatzResearch.WordTrace]
  refine ⟨13809952983277535554809359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9206635322185023703206239 13809952983277535554809359)
  ·
    refine ⟨20714929474916303332214039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13809952983277535554809359 20714929474916303332214039)
    ·
      refine ⟨31072394212374454998321059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20714929474916303332214039 31072394212374454998321059)
      ·
        refine ⟨46608591318561682497481589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31072394212374454998321059 46608591318561682497481589)
        ·
          refine ⟨4369555436115157734138899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 46608591318561682497481589 4369555436115157734138899)
          ·
            refine ⟨6554333154172736601208349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4369555436115157734138899 6554333154172736601208349)
            ·
              refine ⟨2457874932814776225453131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6554333154172736601208349 2457874932814776225453131)
              ·
                refine ⟨3686812399222164338179697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2457874932814776225453131 3686812399222164338179697)
                ·
                  refine ⟨2765109299416623253634773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3686812399222164338179697 2765109299416623253634773)
                  ·
                    refine ⟨64807249205077107507065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 2765109299416623253634773 64807249205077107507065)
                    ·
                      rfl

theorem cell23_378635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 3, 1, 2, 7].length) (baseStart_378635 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_378635 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_378635 prefixEnd_378635 := by exact prefixLift 378635
  have htrace : WordTrace (prefixWord ++ tailWord_378635) baseStart_378635 baseEnd_378635 := by
    simpa [prefixWord, tailWord_378635, baseEnd_378635] using wordTrace_append hprefix tailTrace_378635
  have hstable : (prefixWord ++ tailWord_378635).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_378635).length < 2 ^ (prefixWord ++ tailWord_378635).sum := by decide
  have hdescent : baseEnd_378635 < baseStart_378635 := by decide
  rcases family_descends (prefixWord ++ tailWord_378635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_378659 : List Nat := [1, 1, 1, 4, 2, 1, 4, 1, 3, 3, 2]
def baseStart_378659 : Nat := 118140960795 + 378659 * 2 ^ 59
def prefixEnd_378659 : Nat := 4983230072969 + 3 ^ 40 * 378659 * 2
def baseEnd_378659 : Nat := 194434071150939228621085

theorem tailTrace_378659 : CollatzResearch.WordTrace tailWord_378659 prefixEnd_378659 194434071150939228621085 := by
  unfold tailWord_378659
  simp only [CollatzResearch.WordTrace]
  refine ⟨13810828335190587653683031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9207218890127058435788687 13810828335190587653683031)
  ·
    refine ⟨20716242502785881480524547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13810828335190587653683031 20716242502785881480524547)
    ·
      refine ⟨31074363754178822220786821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20716242502785881480524547 31074363754178822220786821)
      ·
        refine ⟨5826443203908529166397529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 31074363754178822220786821 5826443203908529166397529)
        ·
          refine ⟨4369832402931396874798147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5826443203908529166397529 4369832402931396874798147)
          ·
            refine ⟨6554748604397095312197221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4369832402931396874798147 6554748604397095312197221)
            ·
              refine ⟨1229015363324455371036979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6554748604397095312197221 1229015363324455371036979)
              ·
                refine ⟨1843523044986683056555469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1229015363324455371036979 1843523044986683056555469)
                ·
                  refine ⟨691321141870006146208301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1843523044986683056555469 691321141870006146208301)
                  ·
                    refine ⟨259245428201252304828113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 691321141870006146208301 259245428201252304828113)
                    ·
                      refine ⟨194434071150939228621085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 259245428201252304828113 194434071150939228621085)
                      ·
                        rfl

theorem cell23_378659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 4, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 4, 1, 3, 3, 2].length) (baseStart_378659 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_378659 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_378659 prefixEnd_378659 := by exact prefixLift 378659
  have htrace : WordTrace (prefixWord ++ tailWord_378659) baseStart_378659 baseEnd_378659 := by
    simpa [prefixWord, tailWord_378659, baseEnd_378659] using wordTrace_append hprefix tailTrace_378659
  have hstable : (prefixWord ++ tailWord_378659).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_378659).length < 2 ^ (prefixWord ++ tailWord_378659).sum := by decide
  have hdescent : baseEnd_378659 < baseStart_378659 := by decide
  rcases family_descends (prefixWord ++ tailWord_378659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_378665 : List Nat := [1, 2, 1, 1, 1, 1, 1, 3, 6, 6]
def baseStart_378665 : Nat := 118140960795 + 378665 * 2 ^ 59
def prefixEnd_378665 : Nat := 4983230072969 + 3 ^ 40 * 378665 * 2
def baseEnd_378665 : Nat := 64812384011622068382019

theorem tailTrace_378665 : CollatzResearch.WordTrace tailWord_378665 prefixEnd_378665 64812384011622068382019 := by
  unfold tailWord_378665
  simp only [CollatzResearch.WordTrace]
  refine ⟨13811047173168850678401449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9207364782112567118934299 13811047173168850678401449)
  ·
    refine ⟨10358285379876638008801087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13811047173168850678401449 10358285379876638008801087)
    ·
      refine ⟨15537428069814957013201631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10358285379876638008801087 15537428069814957013201631)
      ·
        refine ⟨23306142104722435519802447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15537428069814957013201631 23306142104722435519802447)
        ·
          refine ⟨34959213157083653279703671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23306142104722435519802447 34959213157083653279703671)
          ·
            refine ⟨52438819735625479919555507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34959213157083653279703671 52438819735625479919555507)
            ·
              refine ⟨78658229603438219879333261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52438819735625479919555507 78658229603438219879333261)
              ·
                refine ⟨29496836101289332454749973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 78658229603438219879333261 29496836101289332454749973)
                ·
                  refine ⟨1382664192247937458816405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 29496836101289332454749973 1382664192247937458816405)
                  ·
                    refine ⟨64812384011622068382019, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1382664192247937458816405 64812384011622068382019)
                    ·
                      rfl

theorem cell23_378665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 3, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 3, 6, 6].length) (baseStart_378665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_378665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_378665 prefixEnd_378665 := by exact prefixLift 378665
  have htrace : WordTrace (prefixWord ++ tailWord_378665) baseStart_378665 baseEnd_378665 := by
    simpa [prefixWord, tailWord_378665, baseEnd_378665] using wordTrace_append hprefix tailTrace_378665
  have hstable : (prefixWord ++ tailWord_378665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_378665).length < 2 ^ (prefixWord ++ tailWord_378665).sum := by decide
  have hdescent : baseEnd_378665 < baseStart_378665 := by decide
  rcases family_descends (prefixWord ++ tailWord_378665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_378670 : List Nat := [4, 1, 3, 2, 2, 2, 2, 1, 1, 2, 3]
def baseStart_378670 : Nat := 118140960795 + 378670 * 2 ^ 59
def prefixEnd_378670 : Nat := 4983230072969 + 3 ^ 40 * 378670 * 2
def baseEnd_378670 : Nat := 194439719438138685583535

theorem tailTrace_378670 : CollatzResearch.WordTrace tailWord_378670 prefixEnd_378670 194439719438138685583535 := by
  unfold tailWord_378670
  simp only [CollatzResearch.WordTrace]
  refine ⟨1726403692268842066541683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9207486358767157688222309 1726403692268842066541683)
  ·
    refine ⟨2589605538403263099812525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1726403692268842066541683 2589605538403263099812525)
    ·
      refine ⟨971102076901223662429697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2589605538403263099812525 971102076901223662429697)
      ·
        refine ⟨728326557675917746822273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 971102076901223662429697 728326557675917746822273)
        ·
          refine ⟨546244918256938310116705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 728326557675917746822273 546244918256938310116705)
          ·
            refine ⟨409683688692703732587529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 546244918256938310116705 409683688692703732587529)
            ·
              refine ⟨307262766519527799440647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 409683688692703732587529 307262766519527799440647)
              ·
                refine ⟨460894149779291699160971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 307262766519527799440647 460894149779291699160971)
                ·
                  refine ⟨691341224668937548741457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 460894149779291699160971 691341224668937548741457)
                  ·
                    refine ⟨518505918501703161556093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 691341224668937548741457 518505918501703161556093)
                    ·
                      refine ⟨194439719438138685583535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 518505918501703161556093 194439719438138685583535)
                      ·
                        rfl

theorem cell23_378670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 2, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 2, 2, 1, 1, 2, 3].length) (baseStart_378670 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_378670 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_378670 prefixEnd_378670 := by exact prefixLift 378670
  have htrace : WordTrace (prefixWord ++ tailWord_378670) baseStart_378670 baseEnd_378670 := by
    simpa [prefixWord, tailWord_378670, baseEnd_378670] using wordTrace_append hprefix tailTrace_378670
  have hstable : (prefixWord ++ tailWord_378670).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_378670).length < 2 ^ (prefixWord ++ tailWord_378670).sum := by decide
  have hdescent : baseEnd_378670 < baseStart_378670 := by decide
  rcases family_descends (prefixWord ++ tailWord_378670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_378682 : List Nat := [3, 1, 1, 1, 5, 1, 1, 2, 2, 6]
def baseStart_378682 : Nat := 118140960795 + 378682 * 2 ^ 59
def prefixEnd_378682 : Nat := 4983230072969 + 3 ^ 40 * 378682 * 2
def baseEnd_378682 : Nat := 64815293735330879544493

theorem tailTrace_378682 : CollatzResearch.WordTrace tailWord_378682 prefixEnd_378682 64815293735330879544493 := by
  unfold tailWord_378682
  simp only [CollatzResearch.WordTrace]
  refine ⟨3452916803526815645442575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9207778142738175054513533 3452916803526815645442575)
  ·
    refine ⟨5179375205290223468163863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3452916803526815645442575 5179375205290223468163863)
    ·
      refine ⟨7769062807935335202245795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5179375205290223468163863 7769062807935335202245795)
      ·
        refine ⟨11653594211903002803368693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7769062807935335202245795 11653594211903002803368693)
        ·
          refine ⟨1092524457365906512815815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 11653594211903002803368693 1092524457365906512815815)
          ·
            refine ⟨1638786686048859769223723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1092524457365906512815815 1638786686048859769223723)
            ·
              refine ⟨2458180029073289653835585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1638786686048859769223723 2458180029073289653835585)
              ·
                refine ⟨1843635021804967240376689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2458180029073289653835585 1843635021804967240376689)
                ·
                  refine ⟨1382726266353725430282517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1843635021804967240376689 1382726266353725430282517)
                  ·
                    refine ⟨64815293735330879544493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1382726266353725430282517 64815293735330879544493)
                    ·
                      rfl

theorem cell23_378682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 1, 2, 2, 6].length) (baseStart_378682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_378682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_378682 prefixEnd_378682 := by exact prefixLift 378682
  have htrace : WordTrace (prefixWord ++ tailWord_378682) baseStart_378682 baseEnd_378682 := by
    simpa [prefixWord, tailWord_378682, baseEnd_378682] using wordTrace_append hprefix tailTrace_378682
  have hstable : (prefixWord ++ tailWord_378682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_378682).length < 2 ^ (prefixWord ++ tailWord_378682).sum := by decide
  have hdescent : baseEnd_378682 < baseStart_378682 := by decide
  rcases family_descends (prefixWord ++ tailWord_378682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_378706 : List Nat := [3, 2, 2, 1, 1, 3, 3, 1, 1, 4, 2]
def baseStart_378706 : Nat := 118140960795 + 378706 * 2 ^ 59
def prefixEnd_378706 : Nat := 4983230072969 + 3 ^ 40 * 378706 * 2
def baseEnd_378706 : Nat := 194458204741700544733369

theorem tailTrace_378706 : CollatzResearch.WordTrace tailWord_378706 prefixEnd_378706 194458204741700544733369 := by
  unfold tailWord_378706
  simp only [CollatzResearch.WordTrace]
  refine ⟨3453135641505078670160993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9208361710680209787095981 3453135641505078670160993)
  ·
    refine ⟨2589851731128809002620745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3453135641505078670160993 2589851731128809002620745)
    ·
      refine ⟨1942388798346606751965559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2589851731128809002620745 1942388798346606751965559)
      ·
        refine ⟨2913583197519910127948339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1942388798346606751965559 2913583197519910127948339)
        ·
          refine ⟨4370374796279865191922509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2913583197519910127948339 4370374796279865191922509)
          ·
            refine ⟨1638890548604949446970941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4370374796279865191922509 1638890548604949446970941)
            ·
              refine ⟨614583955726856042614103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1638890548604949446970941 614583955726856042614103)
              ·
                refine ⟨921875933590284063921155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 614583955726856042614103 921875933590284063921155)
                ·
                  refine ⟨1382813900385426095881733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 921875933590284063921155 1382813900385426095881733)
                  ·
                    refine ⟨259277606322267392977825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1382813900385426095881733 259277606322267392977825)
                    ·
                      refine ⟨194458204741700544733369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 259277606322267392977825 194458204741700544733369)
                      ·
                        rfl

theorem cell23_378706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 3, 1, 1, 4, 2].length) (baseStart_378706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_378706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_378706 prefixEnd_378706 := by exact prefixLift 378706
  have htrace : WordTrace (prefixWord ++ tailWord_378706) baseStart_378706 baseEnd_378706 := by
    simpa [prefixWord, tailWord_378706, baseEnd_378706] using wordTrace_append hprefix tailTrace_378706
  have hstable : (prefixWord ++ tailWord_378706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_378706).length < 2 ^ (prefixWord ++ tailWord_378706).sum := by decide
  have hdescent : baseEnd_378706 < baseStart_378706 := by decide
  rcases family_descends (prefixWord ++ tailWord_378706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_378749 : List Nat := [1, 4, 1, 1, 2, 1, 1, 3, 2, 5, 2]
def baseStart_378749 : Nat := 118140960795 + 378749 * 2 ^ 59
def prefixEnd_378749 : Nat := 4983230072969 + 3 ^ 40 * 378749 * 2
def baseEnd_378749 : Nat := 194480284409843876495671

theorem tailTrace_378749 : CollatzResearch.WordTrace tailWord_378749 prefixEnd_378749 194480284409843876495671 := by
  unfold tailWord_378749
  simp only [CollatzResearch.WordTrace]
  refine ⟨13814110904864533024459301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9209407269909688682972867 13814110904864533024459301)
  ·
    refine ⟨2590145794662099942086119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13814110904864533024459301 2590145794662099942086119)
    ·
      refine ⟨3885218691993149913129179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2590145794662099942086119 3885218691993149913129179)
      ·
        refine ⟨5827828037989724869693769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3885218691993149913129179 5827828037989724869693769)
        ·
          refine ⟨4370871028492293652270327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5827828037989724869693769 4370871028492293652270327)
          ·
            refine ⟨6556306542738440478405491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4370871028492293652270327 6556306542738440478405491)
            ·
              refine ⟨9834459814107660717608237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6556306542738440478405491 9834459814107660717608237)
              ·
                refine ⟨3687922430290372769103089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9834459814107660717608237 3687922430290372769103089)
                ·
                  refine ⟨2765941822717779576827317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3687922430290372769103089 2765941822717779576827317)
                  ·
                    refine ⟨259307045879791835327561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2765941822717779576827317 259307045879791835327561)
                    ·
                      refine ⟨194480284409843876495671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 259307045879791835327561 194480284409843876495671)
                      ·
                        rfl

theorem cell23_378749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 3, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 3, 2, 5, 2].length) (baseStart_378749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_378749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_378749 prefixEnd_378749 := by exact prefixLift 378749
  have htrace : WordTrace (prefixWord ++ tailWord_378749) baseStart_378749 baseEnd_378749 := by
    simpa [prefixWord, tailWord_378749, baseEnd_378749] using wordTrace_append hprefix tailTrace_378749
  have hstable : (prefixWord ++ tailWord_378749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_378749).length < 2 ^ (prefixWord ++ tailWord_378749).sum := by decide
  have hdescent : baseEnd_378749 < baseStart_378749 := by decide
  rcases family_descends (prefixWord ++ tailWord_378749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_378752 : List Nat := [2, 1, 1, 2, 1, 2, 5, 1, 1, 2, 5]
def baseStart_378752 : Nat := 118140960795 + 378752 * 2 ^ 59
def prefixEnd_378752 : Nat := 4983230072969 + 3 ^ 40 * 378752 * 2
def baseEnd_378752 : Nat := 194481824851807364758157

theorem tailTrace_378752 : CollatzResearch.WordTrace tailWord_378752 prefixEnd_378752 194481824851807364758157 := by
  unfold tailWord_378752
  simp only [CollatzResearch.WordTrace]
  refine ⟨6907110161926832268409255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9209480215902443024545673 6907110161926832268409255)
  ·
    refine ⟨10360665242890248402613883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6907110161926832268409255 10360665242890248402613883)
    ·
      refine ⟨15540997864335372603920825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10360665242890248402613883 15540997864335372603920825)
      ·
        refine ⟨11655748398251529452940619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15540997864335372603920825 11655748398251529452940619)
        ·
          refine ⟨17483622597377294179410929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11655748398251529452940619 17483622597377294179410929)
          ·
            refine ⟨13112716948032970634558197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17483622597377294179410929 13112716948032970634558197)
            ·
              refine ⟨1229317213878090996989831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 13112716948032970634558197 1229317213878090996989831)
              ·
                refine ⟨1843975820817136495484747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1229317213878090996989831 1843975820817136495484747)
                ·
                  refine ⟨2765963731225704743227121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1843975820817136495484747 2765963731225704743227121)
                  ·
                    refine ⟨2074472798419278557420341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2765963731225704743227121 2074472798419278557420341)
                    ·
                      refine ⟨194481824851807364758157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2074472798419278557420341 194481824851807364758157)
                      ·
                        rfl

theorem cell23_378752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 5, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 5, 1, 1, 2, 5].length) (baseStart_378752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_378752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_378752 prefixEnd_378752 := by exact prefixLift 378752
  have htrace : WordTrace (prefixWord ++ tailWord_378752) baseStart_378752 baseEnd_378752 := by
    simpa [prefixWord, tailWord_378752, baseEnd_378752] using wordTrace_append hprefix tailTrace_378752
  have hstable : (prefixWord ++ tailWord_378752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_378752).length < 2 ^ (prefixWord ++ tailWord_378752).sum := by decide
  have hdescent : baseEnd_378752 < baseStart_378752 := by decide
  rcases family_descends (prefixWord ++ tailWord_378752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_378799 : List Nat := [1, 1, 2, 1, 2, 2, 3, 4, 2, 2, 3]
def baseStart_378799 : Nat := 118140960795 + 378799 * 2 ^ 59
def prefixEnd_378799 : Nat := 4983230072969 + 3 ^ 40 * 378799 * 2
def baseEnd_378799 : Nat := 194505958442568680870441

theorem tailTrace_378799 : CollatzResearch.WordTrace tailWord_378799 prefixEnd_378799 194505958442568680870441 := by
  unfold tailWord_378799
  simp only [CollatzResearch.WordTrace]
  refine ⟨13815934554683391563779451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9210623036455594375852967 13815934554683391563779451)
  ·
    refine ⟨20723901832025087345669177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13815934554683391563779451 20723901832025087345669177)
    ·
      refine ⟨15542926374018815509251883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20723901832025087345669177 15542926374018815509251883)
      ·
        refine ⟨23314389561028223263877825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15542926374018815509251883 23314389561028223263877825)
        ·
          refine ⟨17485792170771167447908369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23314389561028223263877825 17485792170771167447908369)
          ·
            refine ⟨13114344128078375585931277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17485792170771167447908369 13114344128078375585931277)
            ·
              refine ⟨4917879048029390844724229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13114344128078375585931277 4917879048029390844724229)
              ·
                refine ⟨922102321505510783385793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4917879048029390844724229 922102321505510783385793)
                ·
                  refine ⟨691576741129133087539345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 922102321505510783385793 691576741129133087539345)
                  ·
                    refine ⟨518682555846849815654509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 691576741129133087539345 518682555846849815654509)
                    ·
                      refine ⟨194505958442568680870441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 518682555846849815654509 194505958442568680870441)
                      ·
                        rfl

theorem cell23_378799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 3, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 3, 4, 2, 2, 3].length) (baseStart_378799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_378799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_378799 prefixEnd_378799 := by exact prefixLift 378799
  have htrace : WordTrace (prefixWord ++ tailWord_378799) baseStart_378799 baseEnd_378799 := by
    simpa [prefixWord, tailWord_378799, baseEnd_378799] using wordTrace_append hprefix tailTrace_378799
  have hstable : (prefixWord ++ tailWord_378799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_378799).length < 2 ^ (prefixWord ++ tailWord_378799).sum := by decide
  have hdescent : baseEnd_378799 < baseStart_378799 := by decide
  rcases family_descends (prefixWord ++ tailWord_378799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_378802 : List Nat := [3, 2, 1, 1, 1, 1, 1, 5, 8]
def baseStart_378802 : Nat := 118140960795 + 378802 * 2 ^ 59
def prefixEnd_378802 : Nat := 4983230072969 + 3 ^ 40 * 378802 * 2
def baseEnd_378802 : Nat := 21611944320503574348103

theorem tailTrace_378802 : CollatzResearch.WordTrace tailWord_378802 prefixEnd_378802 21611944320503574348103 := by
  unfold tailWord_378802
  simp only [CollatzResearch.WordTrace]
  refine ⟨3454010993418130769034665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9210695982448348717425773 3454010993418130769034665)
  ·
    refine ⟨2590508245063598076775999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3454010993418130769034665 2590508245063598076775999)
    ·
      refine ⟨3885762367595397115163999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2590508245063598076775999 3885762367595397115163999)
      ·
        refine ⟨5828643551393095672745999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3885762367595397115163999 5828643551393095672745999)
        ·
          refine ⟨8742965327089643509118999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5828643551393095672745999 8742965327089643509118999)
          ·
            refine ⟨13114447990634465263678499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8742965327089643509118999 13114447990634465263678499)
            ·
              refine ⟨19671671985951697895517749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13114447990634465263678499 19671671985951697895517749)
              ·
                refine ⟨1844219248682971677704789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 19671671985951697895517749 1844219248682971677704789)
                ·
                  refine ⟨21611944320503574348103, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 1844219248682971677704789 21611944320503574348103)
                  ·
                    rfl

theorem cell23_378802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 5, 8].length) (baseStart_378802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_378802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_378802 prefixEnd_378802 := by exact prefixLift 378802
  have htrace : WordTrace (prefixWord ++ tailWord_378802) baseStart_378802 baseEnd_378802 := by
    simpa [prefixWord, tailWord_378802, baseEnd_378802] using wordTrace_append hprefix tailTrace_378802
  have hstable : (prefixWord ++ tailWord_378802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_378802).length < 2 ^ (prefixWord ++ tailWord_378802).sum := by decide
  have hdescent : baseEnd_378802 < baseStart_378802 := by decide
  rcases family_descends (prefixWord ++ tailWord_378802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_378856 : List Nat := [2, 1, 4, 1, 1, 1, 1, 3, 4, 3, 2]
def baseStart_378856 : Nat := 118140960795 + 378856 * 2 ^ 59
def prefixEnd_378856 : Nat := 4983230072969 + 3 ^ 40 * 378856 * 2
def baseEnd_378856 : Nat := 194535226839874957857679

theorem tailTrace_378856 : CollatzResearch.WordTrace tailWord_378856 prefixEnd_378856 194535226839874957857679 := by
  unfold tailWord_378856
  simp only [CollatzResearch.WordTrace]
  refine ⟨6909006757738445149302211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9212009010317926865736281 6909006757738445149302211)
  ·
    refine ⟨10363510136607667723953317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6909006757738445149302211 10363510136607667723953317)
    ·
      refine ⟨1943158150613937698241247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10363510136607667723953317 1943158150613937698241247)
      ·
        refine ⟨2914737225920906547361871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1943158150613937698241247 2914737225920906547361871)
        ·
          refine ⟨4372105838881359821042807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2914737225920906547361871 4372105838881359821042807)
          ·
            refine ⟨6558158758322039731564211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4372105838881359821042807 6558158758322039731564211)
            ·
              refine ⟨9837238137483059597346317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6558158758322039731564211 9837238137483059597346317)
              ·
                refine ⟨3688964301556147349004869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9837238137483059597346317 3688964301556147349004869)
                ·
                  refine ⟨691680806541777627938413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3688964301556147349004869 691680806541777627938413)
                  ·
                    refine ⟨259380302453166610476905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 691680806541777627938413 259380302453166610476905)
                    ·
                      refine ⟨194535226839874957857679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 259380302453166610476905 194535226839874957857679)
                      ·
                        rfl

theorem cell23_378856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 3, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 3, 4, 3, 2].length) (baseStart_378856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_378856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_378856 prefixEnd_378856 := by exact prefixLift 378856
  have htrace : WordTrace (prefixWord ++ tailWord_378856) baseStart_378856 baseEnd_378856 := by
    simpa [prefixWord, tailWord_378856, baseEnd_378856] using wordTrace_append hprefix tailTrace_378856
  have hstable : (prefixWord ++ tailWord_378856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_378856).length < 2 ^ (prefixWord ++ tailWord_378856).sum := by decide
  have hdescent : baseEnd_378856 < baseStart_378856 := by decide
  rcases family_descends (prefixWord ++ tailWord_378856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_378863 : List Nat := [1, 1, 2, 1, 4, 2, 1, 6, 1, 1, 3]
def baseStart_378863 : Nat := 118140960795 + 378863 * 2 ^ 59
def prefixEnd_378863 : Nat := 4983230072969 + 3 ^ 40 * 378863 * 2
def baseEnd_378863 : Nat := 194538821204456430470147

theorem tailTrace_378863 : CollatzResearch.WordTrace tailWord_378863 prefixEnd_378863 194538821204456430470147 := by
  unfold tailWord_378863
  simp only [CollatzResearch.WordTrace]
  refine ⟨13818268826451530494109243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9212179217634353662739495 13818268826451530494109243)
  ·
    refine ⟨20727403239677295741163865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13818268826451530494109243 20727403239677295741163865)
    ·
      refine ⟨15545552429757971805872899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20727403239677295741163865 15545552429757971805872899)
      ·
        refine ⟨23318328644636957708809349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15545552429757971805872899 23318328644636957708809349)
        ·
          refine ⟨4372186620869429570401753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23318328644636957708809349 4372186620869429570401753)
          ·
            refine ⟨3279139965652072177801315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4372186620869429570401753 3279139965652072177801315)
            ·
              refine ⟨4918709948478108266701973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3279139965652072177801315 4918709948478108266701973)
              ·
                refine ⟨230564528834911325001655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 4918709948478108266701973 230564528834911325001655)
                ·
                  refine ⟨345846793252366987502483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 230564528834911325001655 345846793252366987502483)
                  ·
                    refine ⟨518770189878550481253725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 345846793252366987502483 518770189878550481253725)
                    ·
                      refine ⟨194538821204456430470147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 518770189878550481253725 194538821204456430470147)
                      ·
                        rfl

theorem cell23_378863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 1, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 1, 6, 1, 1, 3].length) (baseStart_378863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_378863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_378863 prefixEnd_378863 := by exact prefixLift 378863
  have htrace : WordTrace (prefixWord ++ tailWord_378863) baseStart_378863 baseEnd_378863 := by
    simpa [prefixWord, tailWord_378863, baseEnd_378863] using wordTrace_append hprefix tailTrace_378863
  have hstable : (prefixWord ++ tailWord_378863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_378863).length < 2 ^ (prefixWord ++ tailWord_378863).sum := by decide
  have hdescent : baseEnd_378863 < baseStart_378863 := by decide
  rcases family_descends (prefixWord ++ tailWord_378863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_378899 : List Nat := [1, 1, 1, 2, 1, 4, 2, 4, 1, 2, 4]
def baseStart_378899 : Nat := 118140960795 + 378899 * 2 ^ 59
def prefixEnd_378899 : Nat := 4983230072969 + 3 ^ 40 * 378899 * 2
def baseEnd_378899 : Nat := 194557306508018289619981

theorem tailTrace_378899 : CollatzResearch.WordTrace tailWord_378899 prefixEnd_378899 194557306508018289619981 := by
  unfold tailWord_378899
  simp only [CollatzResearch.WordTrace]
  refine ⟨13819581854321108642419751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9213054569547405761613167 13819581854321108642419751)
  ·
    refine ⟨20729372781481662963629627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13819581854321108642419751 20729372781481662963629627)
    ·
      refine ⟨31094059172222494445444441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20729372781481662963629627 31094059172222494445444441)
      ·
        refine ⟨23320544379166870834083331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31094059172222494445444441 23320544379166870834083331)
        ·
          refine ⟨34980816568750306251124997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23320544379166870834083331 34980816568750306251124997)
          ·
            refine ⟨6558903106640682422085937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 34980816568750306251124997 6558903106640682422085937)
            ·
              refine ⟨4919177329980511816564453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6558903106640682422085937 4919177329980511816564453)
              ·
                refine ⟨922345749371345965605835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4919177329980511816564453 922345749371345965605835)
                ·
                  refine ⟨1383518624057018948408753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 922345749371345965605835 1383518624057018948408753)
                  ·
                    refine ⟨1037638968042764211306565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1383518624057018948408753 1037638968042764211306565)
                    ·
                      refine ⟨194557306508018289619981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1037638968042764211306565 194557306508018289619981)
                      ·
                        rfl

theorem cell23_378899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 2, 4, 1, 2, 4].length) (baseStart_378899 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_378899 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_378899 prefixEnd_378899 := by exact prefixLift 378899
  have htrace : WordTrace (prefixWord ++ tailWord_378899) baseStart_378899 baseEnd_378899 := by
    simpa [prefixWord, tailWord_378899, baseEnd_378899] using wordTrace_append hprefix tailTrace_378899
  have hstable : (prefixWord ++ tailWord_378899).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_378899).length < 2 ^ (prefixWord ++ tailWord_378899).sum := by decide
  have hdescent : baseEnd_378899 < baseStart_378899 := by decide
  rcases family_descends (prefixWord ++ tailWord_378899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_378906 : List Nat := [3, 1, 1, 3, 1, 4, 2, 1, 1, 1, 5]
def baseStart_378906 : Nat := 118140960795 + 378906 * 2 ^ 59
def prefixEnd_378906 : Nat := 4983230072969 + 3 ^ 40 * 378906 * 2
def baseEnd_378906 : Nat := 194560900872599762232449

theorem tailTrace_378906 : CollatzResearch.WordTrace tailWord_378906 prefixEnd_378906 194560900872599762232449 := by
  unfold tailWord_378906
  simp only [CollatzResearch.WordTrace]
  refine ⟨3454959291323937209481143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9213224776863832558616381 3454959291323937209481143)
  ·
    refine ⟨5182438936985905814221715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3454959291323937209481143 5182438936985905814221715)
    ·
      refine ⟨7773658405478858721332573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5182438936985905814221715 7773658405478858721332573)
      ·
        refine ⟨2915121902054572020499715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7773658405478858721332573 2915121902054572020499715)
        ·
          refine ⟨4372682853081858030749573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2915121902054572020499715 4372682853081858030749573)
          ·
            refine ⟨819878034952848380765545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4372682853081858030749573 819878034952848380765545)
            ·
              refine ⟨614908526214636285574159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 819878034952848380765545 614908526214636285574159)
              ·
                refine ⟨922362789321954428361239, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 614908526214636285574159 922362789321954428361239)
                ·
                  refine ⟨1383544183982931642541859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 922362789321954428361239 1383544183982931642541859)
                  ·
                    refine ⟨2075316275974397463812789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1383544183982931642541859 2075316275974397463812789)
                    ·
                      refine ⟨194560900872599762232449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2075316275974397463812789 194560900872599762232449)
                      ·
                        rfl

theorem cell23_378906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 4, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 4, 2, 1, 1, 1, 5].length) (baseStart_378906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_378906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_378906 prefixEnd_378906 := by exact prefixLift 378906
  have htrace : WordTrace (prefixWord ++ tailWord_378906) baseStart_378906 baseEnd_378906 := by
    simpa [prefixWord, tailWord_378906, baseEnd_378906] using wordTrace_append hprefix tailTrace_378906
  have hstable : (prefixWord ++ tailWord_378906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_378906).length < 2 ^ (prefixWord ++ tailWord_378906).sum := by decide
  have hdescent : baseEnd_378906 < baseStart_378906 := by decide
  rcases family_descends (prefixWord ++ tailWord_378906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_378909 : List Nat := [1, 4, 2, 2, 2, 1, 11]
def baseStart_378909 : Nat := 118140960795 + 378909 * 2 ^ 59
def prefixEnd_378909 : Nat := 4983230072969 + 3 ^ 40 * 378909 * 2
def baseEnd_378909 : Nat := 2402005448327941364135

theorem tailTrace_378909 : CollatzResearch.WordTrace tailWord_378909 prefixEnd_378909 2402005448327941364135 := by
  unfold tailWord_378909
  simp only [CollatzResearch.WordTrace]
  refine ⟨13819946584284880350283781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9213297722856586900189187 13819946584284880350283781)
  ·
    refine ⟨2591239984553415065678209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13819946584284880350283781 2591239984553415065678209)
    ·
      refine ⟨1943429988415061299258657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2591239984553415065678209 1943429988415061299258657)
      ·
        refine ⟨1457572491311295974443993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1943429988415061299258657 1457572491311295974443993)
        ·
          refine ⟨1093179368483471980832995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1457572491311295974443993 1093179368483471980832995)
          ·
            refine ⟨1639769052725207971249493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1093179368483471980832995 1639769052725207971249493)
            ·
              refine ⟨2402005448327941364135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 1639769052725207971249493 2402005448327941364135)
              ·
                rfl

theorem cell23_378909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 11].length) (baseStart_378909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_378909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_378909 prefixEnd_378909 := by exact prefixLift 378909
  have htrace : WordTrace (prefixWord ++ tailWord_378909) baseStart_378909 baseEnd_378909 := by
    simpa [prefixWord, tailWord_378909, baseEnd_378909] using wordTrace_append hprefix tailTrace_378909
  have hstable : (prefixWord ++ tailWord_378909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_378909).length < 2 ^ (prefixWord ++ tailWord_378909).sum := by decide
  have hdescent : baseEnd_378909 < baseStart_378909 := by decide
  rcases family_descends (prefixWord ++ tailWord_378909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_378926 : List Nat := [4, 1, 3, 1, 1, 3, 2, 8]
def baseStart_378926 : Nat := 118140960795 + 378926 * 2 ^ 59
def prefixEnd_378926 : Nat := 4983230072969 + 3 ^ 40 * 378926 * 2
def baseEnd_378926 : Nat := 7206339647618136443791

theorem tailTrace_378926 : CollatzResearch.WordTrace tailWord_378926 prefixEnd_378926 7206339647618136443791 := by
  unfold tailWord_378926
  simp only [CollatzResearch.WordTrace]
  refine ⟨1727570828152911531706579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9213711083482194835768421 1727570828152911531706579)
  ·
    refine ⟨2591356242229367297559869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1727570828152911531706579 2591356242229367297559869)
    ·
      refine ⟨971758590836012736584951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2591356242229367297559869 971758590836012736584951)
      ·
        refine ⟨1457637886254019104877427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 971758590836012736584951 1457637886254019104877427)
        ·
          refine ⟨2186456829381028657316141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1457637886254019104877427 2186456829381028657316141)
          ·
            refine ⟨819921311017885746493553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2186456829381028657316141 819921311017885746493553)
            ·
              refine ⟨614940983263414309870165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 819921311017885746493553 614940983263414309870165)
              ·
                refine ⟨7206339647618136443791, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 614940983263414309870165 7206339647618136443791)
                ·
                  rfl

theorem cell23_378926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 3, 2, 8].length) (baseStart_378926 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_378926 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_378926 prefixEnd_378926 := by exact prefixLift 378926
  have htrace : WordTrace (prefixWord ++ tailWord_378926) baseStart_378926 baseEnd_378926 := by
    simpa [prefixWord, tailWord_378926, baseEnd_378926] using wordTrace_append hprefix tailTrace_378926
  have hstable : (prefixWord ++ tailWord_378926).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_378926).length < 2 ^ (prefixWord ++ tailWord_378926).sum := by decide
  have hdescent : baseEnd_378926 < baseStart_378926 := by decide
  rcases family_descends (prefixWord ++ tailWord_378926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_378930 : List Nat := [3, 2, 1, 1, 2, 5, 2, 1, 2, 4]
def baseStart_378930 : Nat := 118140960795 + 378930 * 2 ^ 59
def prefixEnd_378930 : Nat := 4983230072969 + 3 ^ 40 * 378930 * 2
def baseEnd_378930 : Nat := 64857741469435889444113

theorem tailTrace_378930 : CollatzResearch.WordTrace tailWord_378930 prefixEnd_378930 64857741469435889444113 := by
  unfold tailWord_378930
  simp only [CollatzResearch.WordTrace]
  refine ⟨3455178129302200234199561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9213808344805867291198829 3455178129302200234199561)
  ·
    refine ⟨2591383596976650175649671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3455178129302200234199561 2591383596976650175649671)
    ·
      refine ⟨3887075395464975263474507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2591383596976650175649671 3887075395464975263474507)
      ·
        refine ⟨5830613093197462895211761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3887075395464975263474507 5830613093197462895211761)
        ·
          refine ⟨4372959819898097171408821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5830613093197462895211761 4372959819898097171408821)
          ·
            refine ⟨409964983115446609819577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 4372959819898097171408821 409964983115446609819577)
            ·
              refine ⟨307473737336584957364683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 409964983115446609819577 307473737336584957364683)
              ·
                refine ⟨461210606004877436047025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 307473737336584957364683 461210606004877436047025)
                ·
                  refine ⟨345907954503658077035269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 461210606004877436047025 345907954503658077035269)
                  ·
                    refine ⟨64857741469435889444113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 345907954503658077035269 64857741469435889444113)
                    ·
                      rfl

theorem cell23_378930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 5, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 5, 2, 1, 2, 4].length) (baseStart_378930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_378930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_378930 prefixEnd_378930 := by exact prefixLift 378930
  have htrace : WordTrace (prefixWord ++ tailWord_378930) baseStart_378930 baseEnd_378930 := by
    simpa [prefixWord, tailWord_378930, baseEnd_378930] using wordTrace_append hprefix tailTrace_378930
  have hstable : (prefixWord ++ tailWord_378930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_378930).length < 2 ^ (prefixWord ++ tailWord_378930).sum := by decide
  have hdescent : baseEnd_378930 < baseStart_378930 := by decide
  rcases family_descends (prefixWord ++ tailWord_378930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_378969 : List Nat := [1, 2, 1, 2, 2, 1, 4, 2, 2, 6]
def baseStart_378969 : Nat := 118140960795 + 378969 * 2 ^ 59
def prefixEnd_378969 : Nat := 4983230072969 + 3 ^ 40 * 378969 * 2
def baseEnd_378969 : Nat := 64864416717944338581553

theorem tailTrace_378969 : CollatzResearch.WordTrace tailWord_378969 prefixEnd_378969 64864416717944338581553 := by
  unfold tailWord_378969
  simp only [CollatzResearch.WordTrace]
  refine ⟨13822134964067510597467961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9214756642711673731645307 13822134964067510597467961)
  ·
    refine ⟨10366601223050632948100971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13822134964067510597467961 10366601223050632948100971)
    ·
      refine ⟨15549901834575949422151457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10366601223050632948100971 15549901834575949422151457)
      ·
        refine ⟨11662426375931962066613593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15549901834575949422151457 11662426375931962066613593)
        ·
          refine ⟨8746819781948971549960195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11662426375931962066613593 8746819781948971549960195)
          ·
            refine ⟨13120229672923457324940293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8746819781948971549960195 13120229672923457324940293)
            ·
              refine ⟨2460043063673148248426305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13120229672923457324940293 2460043063673148248426305)
              ·
                refine ⟨1845032297754861186319729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2460043063673148248426305 1845032297754861186319729)
                ·
                  refine ⟨1383774223316145889739797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1845032297754861186319729 1383774223316145889739797)
                  ·
                    refine ⟨64864416717944338581553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1383774223316145889739797 64864416717944338581553)
                    ·
                      rfl

theorem cell23_378969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 4, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 4, 2, 2, 6].length) (baseStart_378969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_378969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_378969 prefixEnd_378969 := by exact prefixLift 378969
  have htrace : WordTrace (prefixWord ++ tailWord_378969) baseStart_378969 baseEnd_378969 := by
    simpa [prefixWord, tailWord_378969, baseEnd_378969] using wordTrace_append hprefix tailTrace_378969
  have hstable : (prefixWord ++ tailWord_378969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_378969).length < 2 ^ (prefixWord ++ tailWord_378969).sum := by decide
  have hdescent : baseEnd_378969 < baseStart_378969 := by decide
  rcases family_descends (prefixWord ++ tailWord_378969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_378979 : List Nat := [1, 1, 1, 5, 1, 1, 2, 2, 1, 3, 5]
def baseStart_378979 : Nat := 118140960795 + 378979 * 2 ^ 59
def prefixEnd_378979 : Nat := 4983230072969 + 3 ^ 40 * 378979 * 2
def baseEnd_378979 : Nat := 194598384960377976619613

theorem tailTrace_378979 : CollatzResearch.WordTrace tailWord_378979 prefixEnd_378979 194598384960377976619613 := by
  unfold tailWord_378979
  simp only [CollatzResearch.WordTrace]
  refine ⟨13822499694031282305331991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9214999796020854870221327 13822499694031282305331991)
  ·
    refine ⟨20733749541046923457997987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13822499694031282305331991 20733749541046923457997987)
    ·
      refine ⟨31100624311570385186996981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20733749541046923457997987 31100624311570385186996981)
      ·
        refine ⟨2915683529209723611280967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 31100624311570385186996981 2915683529209723611280967)
        ·
          refine ⟨4373525293814585416921451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2915683529209723611280967 4373525293814585416921451)
          ·
            refine ⟨6560287940721878125382177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4373525293814585416921451 6560287940721878125382177)
            ·
              refine ⟨4920215955541408594036633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6560287940721878125382177 4920215955541408594036633)
              ·
                refine ⟨3690161966656056445527475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4920215955541408594036633 3690161966656056445527475)
                ·
                  refine ⟨5535242949984084668291213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3690161966656056445527475 5535242949984084668291213)
                  ·
                    refine ⟨2075716106244031750609205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5535242949984084668291213 2075716106244031750609205)
                    ·
                      refine ⟨194598384960377976619613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2075716106244031750609205 194598384960377976619613)
                      ·
                        rfl

theorem cell23_378979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 2, 2, 1, 3, 5].length) (baseStart_378979 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_378979 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_378979 prefixEnd_378979 := by exact prefixLift 378979
  have htrace : WordTrace (prefixWord ++ tailWord_378979) baseStart_378979 baseEnd_378979 := by
    simpa [prefixWord, tailWord_378979, baseEnd_378979] using wordTrace_append hprefix tailTrace_378979
  have hstable : (prefixWord ++ tailWord_378979).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_378979).length < 2 ^ (prefixWord ++ tailWord_378979).sum := by decide
  have hdescent : baseEnd_378979 < baseStart_378979 := by decide
  rcases family_descends (prefixWord ++ tailWord_378979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_378993 : List Nat := [1, 2, 2, 2, 1, 1, 6, 1, 1, 4, 2]
def baseStart_378993 : Nat := 118140960795 + 378993 * 2 ^ 59
def prefixEnd_378993 : Nat := 4983230072969 + 3 ^ 40 * 378993 * 2
def baseEnd_378993 : Nat := 194605573689540921844549

theorem tailTrace_378993 : CollatzResearch.WordTrace tailWord_378993 prefixEnd_378993 194605573689540921844549 := by
  unfold tailWord_378993
  simp only [CollatzResearch.WordTrace]
  refine ⟨13823010315980562696341633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9215340210653708464227755 13823010315980562696341633)
  ·
    refine ⟨10367257736985422022256225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13823010315980562696341633 10367257736985422022256225)
    ·
      refine ⟨7775443302739066516692169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10367257736985422022256225 7775443302739066516692169)
      ·
        refine ⟨5831582477054299887519127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7775443302739066516692169 5831582477054299887519127)
        ·
          refine ⟨8747373715581449831278691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5831582477054299887519127 8747373715581449831278691)
          ·
            refine ⟨13121060573372174746918037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8747373715581449831278691 13121060573372174746918037)
            ·
              refine ⟨615049714376820691261783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 13121060573372174746918037 615049714376820691261783)
              ·
                refine ⟨922574571565231036892675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 615049714376820691261783 922574571565231036892675)
                ·
                  refine ⟨1383861857347846555339013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 922574571565231036892675 1383861857347846555339013)
                  ·
                    refine ⟨259474098252721229126065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1383861857347846555339013 259474098252721229126065)
                    ·
                      refine ⟨194605573689540921844549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 259474098252721229126065 194605573689540921844549)
                      ·
                        rfl

theorem cell23_378993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 6, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 6, 1, 1, 4, 2].length) (baseStart_378993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_378993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_378993 prefixEnd_378993 := by exact prefixLift 378993
  have htrace : WordTrace (prefixWord ++ tailWord_378993) baseStart_378993 baseEnd_378993 := by
    simpa [prefixWord, tailWord_378993, baseEnd_378993] using wordTrace_append hprefix tailTrace_378993
  have hstable : (prefixWord ++ tailWord_378993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_378993).length < 2 ^ (prefixWord ++ tailWord_378993).sum := by decide
  have hdescent : baseEnd_378993 < baseStart_378993 := by decide
  rcases family_descends (prefixWord ++ tailWord_378993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_378999 : List Nat := [1, 1, 3, 1, 1, 5, 1, 1, 9]
def baseStart_378999 : Nat := 118140960795 + 378999 * 2 ^ 59
def prefixEnd_378999 : Nat := 4983230072969 + 3 ^ 40 * 378999 * 2
def baseEnd_378999 : Nat := 21623183841496433152169

theorem tailTrace_378999 : CollatzResearch.WordTrace tailWord_378999 prefixEnd_378999 21623183841496433152169 := by
  unfold tailWord_378999
  simp only [CollatzResearch.WordTrace]
  refine ⟨13823229153958825721060051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9215486102639217147373367 13823229153958825721060051)
  ·
    refine ⟨20734843730938238581590077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13823229153958825721060051 20734843730938238581590077)
    ·
      refine ⟨7775566399101839468096279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20734843730938238581590077 7775566399101839468096279)
      ·
        refine ⟨11663349598652759202144419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7775566399101839468096279 11663349598652759202144419)
        ·
          refine ⟨17495024397979138803216629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11663349598652759202144419 17495024397979138803216629)
          ·
            refine ⟨1640158537310544262801559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 17495024397979138803216629 1640158537310544262801559)
            ·
              refine ⟨2460237805965816394202339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1640158537310544262801559 2460237805965816394202339)
              ·
                refine ⟨3690356708948724591303509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2460237805965816394202339 3690356708948724591303509)
                ·
                  refine ⟨21623183841496433152169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 3690356708948724591303509 21623183841496433152169)
                  ·
                    rfl

theorem cell23_378999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 1, 1, 9].length) (baseStart_378999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_378999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_378999 prefixEnd_378999 := by exact prefixLift 378999
  have htrace : WordTrace (prefixWord ++ tailWord_378999) baseStart_378999 baseEnd_378999 := by
    simpa [prefixWord, tailWord_378999, baseEnd_378999] using wordTrace_append hprefix tailTrace_378999
  have hstable : (prefixWord ++ tailWord_378999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_378999).length < 2 ^ (prefixWord ++ tailWord_378999).sum := by decide
  have hdescent : baseEnd_378999 < baseStart_378999 := by decide
  rcases family_descends (prefixWord ++ tailWord_378999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_379044 : List Nat := [2, 3, 1, 2, 4, 1, 3, 1, 2, 2, 2]
def baseStart_379044 : Nat := 118140960795 + 379044 * 2 ^ 59
def prefixEnd_379044 : Nat := 4983230072969 + 3 ^ 40 * 379044 * 2
def baseEnd_379044 : Nat := 194631761202920222306815

theorem tailTrace_379044 : CollatzResearch.WordTrace tailWord_379044 prefixEnd_379044 194631761202920222306815 := by
  unfold tailWord_379044
  simp only [CollatzResearch.WordTrace]
  refine ⟨6912435219397899203224093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9216580292530532270965457 6912435219397899203224093)
  ·
    refine ⟨2592163207274212201209035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6912435219397899203224093 2592163207274212201209035)
    ·
      refine ⟨3888244810911318301813553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2592163207274212201209035 3888244810911318301813553)
      ·
        refine ⟨2916183608183488726360165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3888244810911318301813553 2916183608183488726360165)
        ·
          refine ⟨546784426534404136192531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2916183608183488726360165 546784426534404136192531)
          ·
            refine ⟨820176639801606204288797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 546784426534404136192531 820176639801606204288797)
            ·
              refine ⟨307566239925602326608299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 820176639801606204288797 307566239925602326608299)
              ·
                refine ⟨461349359888403489912449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 307566239925602326608299 461349359888403489912449)
                ·
                  refine ⟨346012019916302617434337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 461349359888403489912449 346012019916302617434337)
                  ·
                    refine ⟨259509014937226963075753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 346012019916302617434337 259509014937226963075753)
                    ·
                      refine ⟨194631761202920222306815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 259509014937226963075753 194631761202920222306815)
                      ·
                        rfl

theorem cell23_379044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 1, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 1, 3, 1, 2, 2, 2].length) (baseStart_379044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_379044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_379044 prefixEnd_379044 := by exact prefixLift 379044
  have htrace : WordTrace (prefixWord ++ tailWord_379044) baseStart_379044 baseEnd_379044 := by
    simpa [prefixWord, tailWord_379044, baseEnd_379044] using wordTrace_append hprefix tailTrace_379044
  have hstable : (prefixWord ++ tailWord_379044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_379044).length < 2 ^ (prefixWord ++ tailWord_379044).sum := by decide
  have hdescent : baseEnd_379044 < baseStart_379044 := by decide
  rcases family_descends (prefixWord ++ tailWord_379044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_379059 : List Nat := [1, 1, 1, 2, 3, 2, 1, 1, 1, 10]
def baseStart_379059 : Nat := 118140960795 + 379059 * 2 ^ 59
def prefixEnd_379059 : Nat := 4983230072969 + 3 ^ 40 * 379059 * 2
def baseEnd_379059 : Nat := 64879821137579221206415

theorem tailTrace_379059 : CollatzResearch.WordTrace tailWord_379059 prefixEnd_379059 64879821137579221206415 := by
  unfold tailWord_379059
  simp only [CollatzResearch.WordTrace]
  refine ⟨13825417533741455968244231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9216945022494303978829487 13825417533741455968244231)
  ·
    refine ⟨20738126300612183952366347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13825417533741455968244231 20738126300612183952366347)
    ·
      refine ⟨31107189450918275928549521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20738126300612183952366347 31107189450918275928549521)
      ·
        refine ⟨23330392088188706946412141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31107189450918275928549521 23330392088188706946412141)
        ·
          refine ⟨8748897033070765104904553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23330392088188706946412141 8748897033070765104904553)
          ·
            refine ⟨6561672774803073828678415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8748897033070765104904553 6561672774803073828678415)
            ·
              refine ⟨9842509162204610743017623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6561672774803073828678415 9842509162204610743017623)
              ·
                refine ⟨14763763743306916114526435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9842509162204610743017623 14763763743306916114526435)
                ·
                  refine ⟨22145645614960374171789653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14763763743306916114526435 22145645614960374171789653)
                  ·
                    refine ⟨64879821137579221206415, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 22145645614960374171789653 64879821137579221206415)
                    ·
                      rfl

theorem cell23_379059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 1, 1, 10].length) (baseStart_379059 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_379059 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_379059 prefixEnd_379059 := by exact prefixLift 379059
  have htrace : WordTrace (prefixWord ++ tailWord_379059) baseStart_379059 baseEnd_379059 := by
    simpa [prefixWord, tailWord_379059, baseEnd_379059] using wordTrace_append hprefix tailTrace_379059
  have hstable : (prefixWord ++ tailWord_379059).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_379059).length < 2 ^ (prefixWord ++ tailWord_379059).sum := by decide
  have hdescent : baseEnd_379059 < baseStart_379059 := by decide
  rcases family_descends (prefixWord ++ tailWord_379059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_379066 : List Nat := [3, 1, 1, 1, 2, 2, 4, 1, 1, 3, 4]
def baseStart_379066 : Nat := 118140960795 + 379066 * 2 ^ 59
def prefixEnd_379066 : Nat := 4983230072969 + 3 ^ 40 * 379066 * 2
def baseEnd_379066 : Nat := 194643057777319136231713

theorem tailTrace_379066 : CollatzResearch.WordTrace tailWord_379066 prefixEnd_379066 194643057777319136231713 := by
  unfold tailWord_379066
  simp only [CollatzResearch.WordTrace]
  refine ⟨3456418211179024040937263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9217115229810730775832701 3456418211179024040937263)
  ·
    refine ⟨5184627316768536061405895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3456418211179024040937263 5184627316768536061405895)
    ·
      refine ⟨7776940975152804092108843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5184627316768536061405895 7776940975152804092108843)
      ·
        refine ⟨11665411462729206138163265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7776940975152804092108843 11665411462729206138163265)
        ·
          refine ⟨8749058597046904603622449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11665411462729206138163265 8749058597046904603622449)
          ·
            refine ⟨6561793947785178452716837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8749058597046904603622449 6561793947785178452716837)
            ·
              refine ⟨1230336365209720959884407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6561793947785178452716837 1230336365209720959884407)
              ·
                refine ⟨1845504547814581439826611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1230336365209720959884407 1845504547814581439826611)
                ·
                  refine ⟨2768256821721872159739917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1845504547814581439826611 2768256821721872159739917)
                  ·
                    refine ⟨1038096308145702059902469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2768256821721872159739917 1038096308145702059902469)
                    ·
                      refine ⟨194643057777319136231713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1038096308145702059902469 194643057777319136231713)
                      ·
                        rfl

theorem cell23_379066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 4, 1, 1, 3, 4].length) (baseStart_379066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_379066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_379066 prefixEnd_379066 := by exact prefixLift 379066
  have htrace : WordTrace (prefixWord ++ tailWord_379066) baseStart_379066 baseEnd_379066 := by
    simpa [prefixWord, tailWord_379066, baseEnd_379066] using wordTrace_append hprefix tailTrace_379066
  have hstable : (prefixWord ++ tailWord_379066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_379066).length < 2 ^ (prefixWord ++ tailWord_379066).sum := by decide
  have hdescent : baseEnd_379066 < baseStart_379066 := by decide
  rcases family_descends (prefixWord ++ tailWord_379066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_379140 : List Nat := [2, 3, 2, 2, 3, 1, 2, 2, 6]
def baseStart_379140 : Nat := 118140960795 + 379140 * 2 ^ 59
def prefixEnd_379140 : Nat := 4983230072969 + 3 ^ 40 * 379140 * 2
def baseEnd_379140 : Nat := 21631228371750205189597

theorem tailTrace_379140 : CollatzResearch.WordTrace tailWord_379140 prefixEnd_379140 21631228371750205189597 := by
  unfold tailWord_379140
  simp only [CollatzResearch.WordTrace]
  refine ⟨6914185923224003400971437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9218914564298671201295249 6914185923224003400971437)
  ·
    refine ⟨2592819721209001275364289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6914185923224003400971437 2592819721209001275364289)
    ·
      refine ⟨1944614790906750956523217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2592819721209001275364289 1944614790906750956523217)
      ·
        refine ⟨1458461093180063217392413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1944614790906750956523217 1458461093180063217392413)
        ·
          refine ⟨546922909942523706522155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1458461093180063217392413 546922909942523706522155)
          ·
            refine ⟨820384364913785559783233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 546922909942523706522155 820384364913785559783233)
            ·
              refine ⟨615288273685339169837425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 820384364913785559783233 615288273685339169837425)
              ·
                refine ⟨461466205264004377378069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 615288273685339169837425 461466205264004377378069)
                ·
                  refine ⟨21631228371750205189597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 461466205264004377378069 21631228371750205189597)
                  ·
                    rfl

theorem cell23_379140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 1, 2, 2, 6].length) (baseStart_379140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_379140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_379140 prefixEnd_379140 := by exact prefixLift 379140
  have htrace : WordTrace (prefixWord ++ tailWord_379140) baseStart_379140 baseEnd_379140 := by
    simpa [prefixWord, tailWord_379140, baseEnd_379140] using wordTrace_append hprefix tailTrace_379140
  have hstable : (prefixWord ++ tailWord_379140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_379140).length < 2 ^ (prefixWord ++ tailWord_379140).sum := by decide
  have hdescent : baseEnd_379140 < baseStart_379140 := by decide
  rcases family_descends (prefixWord ++ tailWord_379140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_379144 : List Nat := [2, 1, 3, 2, 3, 3, 2, 2, 1, 4]
def baseStart_379144 : Nat := 118140960795 + 379144 * 2 ^ 59
def prefixEnd_379144 : Nat := 4983230072969 + 3 ^ 40 * 379144 * 2
def baseEnd_379144 : Nat := 64894369756123277018785

theorem tailTrace_379144 : CollatzResearch.WordTrace tailWord_379144 prefixEnd_379144 64894369756123277018785 := by
  unfold tailWord_379144
  simp only [CollatzResearch.WordTrace]
  refine ⟨6914258869216757742544243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9219011825622343656725657 6914258869216757742544243)
  ·
    refine ⟨10371388303825136613816365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6914258869216757742544243 10371388303825136613816365)
    ·
      refine ⟨3889270613934426230181137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10371388303825136613816365 3889270613934426230181137)
      ·
        refine ⟨2916952960450819672635853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3889270613934426230181137 2916952960450819672635853)
        ·
          refine ⟨1093857360169057377238445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2916952960450819672635853 1093857360169057377238445)
          ·
            refine ⟨410196510063396516464417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1093857360169057377238445 410196510063396516464417)
            ·
              refine ⟨307647382547547387348313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 410196510063396516464417 307647382547547387348313)
              ·
                refine ⟨230735536910660540511235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 307647382547547387348313 230735536910660540511235)
                ·
                  refine ⟨346103305365990810766853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 230735536910660540511235 346103305365990810766853)
                  ·
                    refine ⟨64894369756123277018785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 346103305365990810766853 64894369756123277018785)
                    ·
                      rfl

theorem cell23_379144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 3, 2, 2, 1, 4].length) (baseStart_379144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_379144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_379144 prefixEnd_379144 := by exact prefixLift 379144
  have htrace : WordTrace (prefixWord ++ tailWord_379144) baseStart_379144 baseEnd_379144 := by
    simpa [prefixWord, tailWord_379144, baseEnd_379144] using wordTrace_append hprefix tailTrace_379144
  have hstable : (prefixWord ++ tailWord_379144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_379144).length < 2 ^ (prefixWord ++ tailWord_379144).sum := by decide
  have hdescent : baseEnd_379144 < baseStart_379144 := by decide
  rcases family_descends (prefixWord ++ tailWord_379144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_379150 : List Nat := [4, 1, 1, 2, 1, 2, 2, 3, 3, 1, 3]
def baseStart_379150 : Nat := 118140960795 + 379150 * 2 ^ 59
def prefixEnd_379150 : Nat := 4983230072969 + 3 ^ 40 * 379150 * 2
def baseEnd_379150 : Nat := 194686190152296807581327

theorem tailTrace_379150 : CollatzResearch.WordTrace tailWord_379150 prefixEnd_379150 194686190152296807581327 := by
  unfold tailWord_379150
  simp only [CollatzResearch.WordTrace]
  refine ⟨1728592072051472313725863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9219157717607852339871269 1728592072051472313725863)
  ·
    refine ⟨2592888108077208470588795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1728592072051472313725863 2592888108077208470588795)
    ·
      refine ⟨3889332162115812705883193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2592888108077208470588795 3889332162115812705883193)
      ·
        refine ⟨2916999121586859529412395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3889332162115812705883193 2916999121586859529412395)
        ·
          refine ⟨4375498682380289294118593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2916999121586859529412395 4375498682380289294118593)
          ·
            refine ⟨3281624011785216970588945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4375498682380289294118593 3281624011785216970588945)
            ·
              refine ⟨2461218008838912727941709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3281624011785216970588945 2461218008838912727941709)
              ·
                refine ⟨922956753314592272978141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2461218008838912727941709 922956753314592272978141)
                ·
                  refine ⟨346108782492972102366803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 922956753314592272978141 346108782492972102366803)
                  ·
                    refine ⟨519163173739458153550205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 346108782492972102366803 519163173739458153550205)
                    ·
                      refine ⟨194686190152296807581327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 519163173739458153550205 194686190152296807581327)
                      ·
                        rfl

theorem cell23_379150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 2, 3, 3, 1, 3].length) (baseStart_379150 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_379150 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_379150 prefixEnd_379150 := by exact prefixLift 379150
  have htrace : WordTrace (prefixWord ++ tailWord_379150) baseStart_379150 baseEnd_379150 := by
    simpa [prefixWord, tailWord_379150, baseEnd_379150] using wordTrace_append hprefix tailTrace_379150
  have hstable : (prefixWord ++ tailWord_379150).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_379150).length < 2 ^ (prefixWord ++ tailWord_379150).sum := by decide
  have hdescent : baseEnd_379150 < baseStart_379150 := by decide
  rcases family_descends (prefixWord ++ tailWord_379150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_379196 : List Nat := [2, 2, 2, 2, 1, 2, 12]
def baseStart_379196 : Nat := 118140960795 + 379196 * 2 ^ 59
def prefixEnd_379196 : Nat := 4983230072969 + 3 ^ 40 * 379196 * 2
def baseEnd_379196 : Nat := 2403824818054365772915

theorem tailTrace_379196 : CollatzResearch.WordTrace tailWord_379196 prefixEnd_379196 2403824818054365772915 := by
  unfold tailWord_379196
  simp only [CollatzResearch.WordTrace]
  refine ⟨6915207167122564182990721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9220276222830085577320961 6915207167122564182990721)
  ·
    refine ⟨5186405375341923137243041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6915207167122564182990721 5186405375341923137243041)
    ·
      refine ⟨3889804031506442352932281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5186405375341923137243041 3889804031506442352932281)
      ·
        refine ⟨2917353023629831764699211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3889804031506442352932281 2917353023629831764699211)
        ·
          refine ⟨4376029535444747647048817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2917353023629831764699211 4376029535444747647048817)
          ·
            refine ⟨3282022151583560735286613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4376029535444747647048817 3282022151583560735286613)
            ·
              refine ⟨2403824818054365772915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 3282022151583560735286613 2403824818054365772915)
              ·
                rfl

theorem cell23_379196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 12].length) (baseStart_379196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_379196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_379196 prefixEnd_379196 := by exact prefixLift 379196
  have htrace : WordTrace (prefixWord ++ tailWord_379196) baseStart_379196 baseEnd_379196 := by
    simpa [prefixWord, tailWord_379196, baseEnd_379196] using wordTrace_append hprefix tailTrace_379196
  have hstable : (prefixWord ++ tailWord_379196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_379196).length < 2 ^ (prefixWord ++ tailWord_379196).sum := by decide
  have hdescent : baseEnd_379196 < baseStart_379196 := by decide
  rcases family_descends (prefixWord ++ tailWord_379196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_379207 : List Nat := [1, 1, 4, 1, 2, 2, 4, 1, 3, 2, 2]
def baseStart_379207 : Nat := 118140960795 + 379207 * 2 ^ 59
def prefixEnd_379207 : Nat := 4983230072969 + 3 ^ 40 * 379207 * 2
def baseEnd_379207 : Nat := 194715458549603084568565

theorem tailTrace_379207 : CollatzResearch.WordTrace tailWord_379207 prefixEnd_379207 194715458549603084568565 := by
  unfold tailWord_379207
  simp only [CollatzResearch.WordTrace]
  refine ⟨13830815537205277244631875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9220543691470184829754583 13830815537205277244631875)
  ·
    refine ⟨20746223305807915866947813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13830815537205277244631875 20746223305807915866947813)
    ·
      refine ⟨3889916869838984225052715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20746223305807915866947813 3889916869838984225052715)
      ·
        refine ⟨5834875304758476337579073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3889916869838984225052715 5834875304758476337579073)
        ·
          refine ⟨4376156478568857253184305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5834875304758476337579073 4376156478568857253184305)
          ·
            refine ⟨3282117358926642939888229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4376156478568857253184305 3282117358926642939888229)
            ·
              refine ⟨615397004798745551229043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3282117358926642939888229 615397004798745551229043)
              ·
                refine ⟨923095507198118326843565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 615397004798745551229043 923095507198118326843565)
                ·
                  refine ⟨346160815199294372566337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 923095507198118326843565 346160815199294372566337)
                  ·
                    refine ⟨259620611399470779424753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 346160815199294372566337 259620611399470779424753)
                    ·
                      refine ⟨194715458549603084568565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 259620611399470779424753 194715458549603084568565)
                      ·
                        rfl

theorem cell23_379207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 4, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 4, 1, 3, 2, 2].length) (baseStart_379207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_379207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_379207 prefixEnd_379207 := by exact prefixLift 379207
  have htrace : WordTrace (prefixWord ++ tailWord_379207) baseStart_379207 baseEnd_379207 := by
    simpa [prefixWord, tailWord_379207, baseEnd_379207] using wordTrace_append hprefix tailTrace_379207
  have hstable : (prefixWord ++ tailWord_379207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_379207).length < 2 ^ (prefixWord ++ tailWord_379207).sum := by decide
  have hdescent : baseEnd_379207 < baseStart_379207 := by decide
  rcases family_descends (prefixWord ++ tailWord_379207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_379217 : List Nat := [1, 2, 2, 1, 4, 3, 3, 1, 2, 4]
def baseStart_379217 : Nat := 118140960795 + 379217 * 2 ^ 59
def prefixEnd_379217 : Nat := 4983230072969 + 3 ^ 40 * 379217 * 2
def baseEnd_379217 : Nat := 64906864452049348481173

theorem tailTrace_379217 : CollatzResearch.WordTrace tailWord_379217 prefixEnd_379217 64906864452049348481173 := by
  unfold tailWord_379217
  simp only [CollatzResearch.WordTrace]
  refine ⟨13831180267169048952495905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9220786844779365968330603 13831180267169048952495905)
  ·
    refine ⟨10373385200376786714371929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13831180267169048952495905 10373385200376786714371929)
    ·
      refine ⟨7780038900282590035778947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10373385200376786714371929 7780038900282590035778947)
      ·
        refine ⟨11670058350423885053668421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7780038900282590035778947 11670058350423885053668421)
        ·
          refine ⟨2188135940704478447562829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11670058350423885053668421 2188135940704478447562829)
          ·
            refine ⟨820550977764179417836061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2188135940704478447562829 820550977764179417836061)
            ·
              refine ⟨307706616661567281688523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 820550977764179417836061 307706616661567281688523)
              ·
                refine ⟨461559924992350922532785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 307706616661567281688523 461559924992350922532785)
                ·
                  refine ⟨346169943744263191899589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 461559924992350922532785 346169943744263191899589)
                  ·
                    refine ⟨64906864452049348481173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 346169943744263191899589 64906864452049348481173)
                    ·
                      rfl

theorem cell23_379217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 3, 3, 1, 2, 4].length) (baseStart_379217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_379217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_379217 prefixEnd_379217 := by exact prefixLift 379217
  have htrace : WordTrace (prefixWord ++ tailWord_379217) baseStart_379217 baseEnd_379217 := by
    simpa [prefixWord, tailWord_379217, baseEnd_379217] using wordTrace_append hprefix tailTrace_379217
  have hstable : (prefixWord ++ tailWord_379217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_379217).length < 2 ^ (prefixWord ++ tailWord_379217).sum := by decide
  have hdescent : baseEnd_379217 < baseStart_379217 := by decide
  rcases family_descends (prefixWord ++ tailWord_379217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_379220 : List Nat := [2, 4, 1, 1, 2, 2, 3, 1, 1, 2, 4]
def baseStart_379220 : Nat := 118140960795 + 379220 * 2 ^ 59
def prefixEnd_379220 : Nat := 4983230072969 + 3 ^ 40 * 379220 * 2
def baseEnd_379220 : Nat := 194722133798111533706005

theorem tailTrace_379220 : CollatzResearch.WordTrace tailWord_379220 prefixEnd_379220 194722133798111533706005 := by
  unfold tailWord_379220
  simp only [CollatzResearch.WordTrace]
  refine ⟨6915644843079090232427557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9220859790772120309903409 6915644843079090232427557)
  ·
    refine ⟨1296683408077329418580167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6915644843079090232427557 1296683408077329418580167)
    ·
      refine ⟨1945025112115994127870251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1296683408077329418580167 1945025112115994127870251)
      ·
        refine ⟨2917537668173991191805377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1945025112115994127870251 2917537668173991191805377)
        ·
          refine ⟨2188153251130493393854033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2917537668173991191805377 2188153251130493393854033)
          ·
            refine ⟨1641114938347870045390525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2188153251130493393854033 1641114938347870045390525)
            ·
              refine ⟨615418101880451267021447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1641114938347870045390525 615418101880451267021447)
              ·
                refine ⟨923127152820676900532171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 615418101880451267021447 923127152820676900532171)
                ·
                  refine ⟨1384690729231015350798257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 923127152820676900532171 1384690729231015350798257)
                  ·
                    refine ⟨1038518046923261513098693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1384690729231015350798257 1038518046923261513098693)
                    ·
                      refine ⟨194722133798111533706005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1038518046923261513098693 194722133798111533706005)
                      ·
                        rfl

theorem cell23_379220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 3, 1, 1, 2, 4].length) (baseStart_379220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_379220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_379220 prefixEnd_379220 := by exact prefixLift 379220
  have htrace : WordTrace (prefixWord ++ tailWord_379220) baseStart_379220 baseEnd_379220 := by
    simpa [prefixWord, tailWord_379220, baseEnd_379220] using wordTrace_append hprefix tailTrace_379220
  have hstable : (prefixWord ++ tailWord_379220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_379220).length < 2 ^ (prefixWord ++ tailWord_379220).sum := by decide
  have hdescent : baseEnd_379220 < baseStart_379220 := by decide
  rcases family_descends (prefixWord ++ tailWord_379220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_379284 : List Nat := [2, 4, 2, 1, 3, 1, 1, 1, 3, 3, 2]
def baseStart_379284 : Nat := 118140960795 + 379284 * 2 ^ 59
def prefixEnd_379284 : Nat := 4983230072969 + 3 ^ 40 * 379284 * 2
def baseEnd_379284 : Nat := 194754996559999283305711

theorem tailTrace_379284 : CollatzResearch.WordTrace tailWord_379284 prefixEnd_379284 194754996559999283305711 := by
  unfold tailWord_379284
  simp only [CollatzResearch.WordTrace]
  refine ⟨6916811978963159697592453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9222415971950879596789937 6916811978963159697592453)
  ·
    refine ⟨1296902246055592443298585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6916811978963159697592453 1296902246055592443298585)
    ·
      refine ⟨972676684541694332473939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1296902246055592443298585 972676684541694332473939)
      ·
        refine ⟨1459015026812541498710909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 972676684541694332473939 1459015026812541498710909)
        ·
          refine ⟨547130635054703062016591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1459015026812541498710909 547130635054703062016591)
          ·
            refine ⟨820695952582054593024887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 547130635054703062016591 820695952582054593024887)
            ·
              refine ⟨1231043928873081889537331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 820695952582054593024887 1231043928873081889537331)
              ·
                refine ⟨1846565893309622834305997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1231043928873081889537331 1846565893309622834305997)
                ·
                  refine ⟨692462209991108562864749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1846565893309622834305997 692462209991108562864749)
                  ·
                    refine ⟨259673328746665711074281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 692462209991108562864749 259673328746665711074281)
                    ·
                      refine ⟨194754996559999283305711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 259673328746665711074281 194754996559999283305711)
                      ·
                        rfl

theorem cell23_379284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 1, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 1, 1, 1, 3, 3, 2].length) (baseStart_379284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_379284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_379284 prefixEnd_379284 := by exact prefixLift 379284
  have htrace : WordTrace (prefixWord ++ tailWord_379284) baseStart_379284 baseEnd_379284 := by
    simpa [prefixWord, tailWord_379284, baseEnd_379284] using wordTrace_append hprefix tailTrace_379284
  have hstable : (prefixWord ++ tailWord_379284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_379284).length < 2 ^ (prefixWord ++ tailWord_379284).sum := by decide
  have hdescent : baseEnd_379284 < baseStart_379284 := by decide
  rcases family_descends (prefixWord ++ tailWord_379284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_379314 : List Nat := [3, 2, 1, 1, 1, 1, 6, 2, 2, 2, 2]
def baseStart_379314 : Nat := 118140960795 + 379314 * 2 ^ 59
def prefixEnd_379314 : Nat := 4983230072969 + 3 ^ 40 * 379314 * 2
def baseEnd_379314 : Nat := 194770400979634165930573

theorem tailTrace_379314 : CollatzResearch.WordTrace tailWord_379314 prefixEnd_379314 194770400979634165930573 := by
  unfold tailWord_379314
  simp only [CollatzResearch.WordTrace]
  refine ⟨3458679536954408629694249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9223145431878423012517997 3458679536954408629694249)
  ·
    refine ⟨2594009652715806472270687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3458679536954408629694249 2594009652715806472270687)
    ·
      refine ⟨3891014479073709708406031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2594009652715806472270687 3891014479073709708406031)
      ·
        refine ⟨5836521718610564562609047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3891014479073709708406031 5836521718610564562609047)
        ·
          refine ⟨8754782577915846843913571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5836521718610564562609047 8754782577915846843913571)
          ·
            refine ⟨13132173866873770265870357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8754782577915846843913571 13132173866873770265870357)
            ·
              refine ⟨615570650009707981212673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 13132173866873770265870357 615570650009707981212673)
              ·
                refine ⟨461677987507280985909505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 615570650009707981212673 461677987507280985909505)
                ·
                  refine ⟨346258490630460739432129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 461677987507280985909505 346258490630460739432129)
                  ·
                    refine ⟨259693867972845554574097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 346258490630460739432129 259693867972845554574097)
                    ·
                      refine ⟨194770400979634165930573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 259693867972845554574097 194770400979634165930573)
                      ·
                        rfl

theorem cell23_379314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 6, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 6, 2, 2, 2, 2].length) (baseStart_379314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_379314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_379314 prefixEnd_379314 := by exact prefixLift 379314
  have htrace : WordTrace (prefixWord ++ tailWord_379314) baseStart_379314 baseEnd_379314 := by
    simpa [prefixWord, tailWord_379314, baseEnd_379314] using wordTrace_append hprefix tailTrace_379314
  have hstable : (prefixWord ++ tailWord_379314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_379314).length < 2 ^ (prefixWord ++ tailWord_379314).sum := by decide
  have hdescent : baseEnd_379314 < baseStart_379314 := by decide
  rcases family_descends (prefixWord ++ tailWord_379314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_379424 : List Nat := [2, 1, 1, 6, 2, 1, 1, 2, 2, 2, 3]
def baseStart_379424 : Nat := 118140960795 + 379424 * 2 ^ 59
def prefixEnd_379424 : Nat := 4983230072969 + 3 ^ 40 * 379424 * 2
def baseEnd_379424 : Nat := 194826883851628735555067

theorem tailTrace_379424 : CollatzResearch.WordTrace tailWord_379424 prefixEnd_379424 194826883851628735555067 := by
  unfold tailWord_379424
  simp only [CollatzResearch.WordTrace]
  refine ⟨6919365088709561652640663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9225820118279415536854217 6919365088709561652640663)
  ·
    refine ⟨10379047633064342478960995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6919365088709561652640663 10379047633064342478960995)
    ·
      refine ⟨15568571449596513718441493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10379047633064342478960995 15568571449596513718441493)
      ·
        refine ⟨729776786699836580551945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 15568571449596513718441493 729776786699836580551945)
        ·
          refine ⟨547332590024877435413959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 729776786699836580551945 547332590024877435413959)
          ·
            refine ⟨820998885037316153120939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 547332590024877435413959 820998885037316153120939)
            ·
              refine ⟨1231498327555974229681409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 820998885037316153120939 1231498327555974229681409)
              ·
                refine ⟨923623745666980672261057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1231498327555974229681409 923623745666980672261057)
                ·
                  refine ⟨692717809250235504195793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 923623745666980672261057 692717809250235504195793)
                  ·
                    refine ⟨519538356937676628146845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 692717809250235504195793 519538356937676628146845)
                    ·
                      refine ⟨194826883851628735555067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 519538356937676628146845 194826883851628735555067)
                      ·
                        rfl

theorem cell23_379424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 1, 1, 2, 2, 2, 3].length) (baseStart_379424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_379424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_379424 prefixEnd_379424 := by exact prefixLift 379424
  have htrace : WordTrace (prefixWord ++ tailWord_379424) baseStart_379424 baseEnd_379424 := by
    simpa [prefixWord, tailWord_379424, baseEnd_379424] using wordTrace_append hprefix tailTrace_379424
  have hstable : (prefixWord ++ tailWord_379424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_379424).length < 2 ^ (prefixWord ++ tailWord_379424).sum := by decide
  have hdescent : baseEnd_379424 < baseStart_379424 := by decide
  rcases family_descends (prefixWord ++ tailWord_379424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_379447 : List Nat := [1, 1, 3, 1, 2, 3, 1, 2, 4, 3, 2]
def baseStart_379447 : Nat := 118140960795 + 379447 * 2 ^ 59
def prefixEnd_379447 : Nat := 4983230072969 + 3 ^ 40 * 379447 * 2
def baseEnd_379447 : Nat := 194838693906682145567461

theorem tailTrace_379447 : CollatzResearch.WordTrace tailWord_379447 prefixEnd_379447 194838693906682145567461 := by
  unfold tailWord_379447
  simp only [CollatzResearch.WordTrace]
  refine ⟨13839569056335798233368595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9226379370890532155579063 13839569056335798233368595)
  ·
    refine ⟨20759353584503697350052893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13839569056335798233368595 20759353584503697350052893)
    ·
      refine ⟨7784757594188886506269835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20759353584503697350052893 7784757594188886506269835)
      ·
        refine ⟨11677136391283329759404753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7784757594188886506269835 11677136391283329759404753)
        ·
          refine ⟨8757852293462497319553565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11677136391283329759404753 8757852293462497319553565)
          ·
            refine ⟨3284194610048436494832587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8757852293462497319553565 3284194610048436494832587)
            ·
              refine ⟨4926291915072654742248881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3284194610048436494832587 4926291915072654742248881)
              ·
                refine ⟨3694718936304491056686661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4926291915072654742248881 3694718936304491056686661)
                ·
                  refine ⟨692759800557092073128749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3694718936304491056686661 692759800557092073128749)
                  ·
                    refine ⟨259784925208909527423281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 692759800557092073128749 259784925208909527423281)
                    ·
                      refine ⟨194838693906682145567461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 259784925208909527423281 194838693906682145567461)
                      ·
                        rfl

theorem cell23_379447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 1, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 1, 2, 4, 3, 2].length) (baseStart_379447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_379447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_379447 prefixEnd_379447 := by exact prefixLift 379447
  have htrace : WordTrace (prefixWord ++ tailWord_379447) baseStart_379447 baseEnd_379447 := by
    simpa [prefixWord, tailWord_379447, baseEnd_379447] using wordTrace_append hprefix tailTrace_379447
  have hstable : (prefixWord ++ tailWord_379447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_379447).length < 2 ^ (prefixWord ++ tailWord_379447).sum := by decide
  have hdescent : baseEnd_379447 < baseStart_379447 := by decide
  rcases family_descends (prefixWord ++ tailWord_379447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_379457 : List Nat := [1, 2, 5, 1, 1, 3, 1, 1, 3, 5]
def baseStart_379457 : Nat := 118140960795 + 379457 * 2 ^ 59
def prefixEnd_379457 : Nat := 4983230072969 + 3 ^ 40 * 379457 * 2
def baseEnd_379457 : Nat := 64947942904409035480805

theorem tailTrace_379457 : CollatzResearch.WordTrace tailWord_379457 prefixEnd_379457 64947942904409035480805 := by
  unfold tailWord_379457
  simp only [CollatzResearch.WordTrace]
  refine ⟨13839933786299569941232625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9226622524199713294155083 13839933786299569941232625)
  ·
    refine ⟨10379950339724677455924469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13839933786299569941232625 10379950339724677455924469)
    ·
      refine ⟨973120344349188511492919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 10379950339724677455924469 973120344349188511492919)
      ·
        refine ⟨1459680516523782767239379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 973120344349188511492919 1459680516523782767239379)
        ·
          refine ⟨2189520774785674150859069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1459680516523782767239379 2189520774785674150859069)
          ·
            refine ⟨821070290544627806572151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2189520774785674150859069 821070290544627806572151)
            ·
              refine ⟨1231605435816941709858227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 821070290544627806572151 1231605435816941709858227)
              ·
                refine ⟨1847408153725412564787341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1231605435816941709858227 1847408153725412564787341)
                ·
                  refine ⟨692778057647029711795253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1847408153725412564787341 692778057647029711795253)
                  ·
                    refine ⟨64947942904409035480805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 692778057647029711795253 64947942904409035480805)
                    ·
                      rfl

theorem cell23_379457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 3, 1, 1, 3, 5].length) (baseStart_379457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_379457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_379457 prefixEnd_379457 := by exact prefixLift 379457
  have htrace : WordTrace (prefixWord ++ tailWord_379457) baseStart_379457 baseEnd_379457 := by
    simpa [prefixWord, tailWord_379457, baseEnd_379457] using wordTrace_append hprefix tailTrace_379457
  have hstable : (prefixWord ++ tailWord_379457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_379457).length < 2 ^ (prefixWord ++ tailWord_379457).sum := by decide
  have hdescent : baseEnd_379457 < baseStart_379457 := by decide
  rcases family_descends (prefixWord ++ tailWord_379457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_379470 : List Nat := [4, 1, 1, 1, 1, 2, 3, 1, 3, 6]
def baseStart_379470 : Nat := 118140960795 + 379470 * 2 ^ 59
def prefixEnd_379470 : Nat := 4983230072969 + 3 ^ 40 * 379470 * 2
def baseEnd_379470 : Nat := 64950167987245185193285

theorem tailTrace_379470 : CollatzResearch.WordTrace tailWord_379470 prefixEnd_379470 64950167987245185193285 := by
  unfold tailWord_379470
  simp only [CollatzResearch.WordTrace]
  refine ⟨1730050991906559145181983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9226938623501648774303909 1730050991906559145181983)
  ·
    refine ⟨2595076487859838717772975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1730050991906559145181983 2595076487859838717772975)
    ·
      refine ⟨3892614731789758076659463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2595076487859838717772975 3892614731789758076659463)
      ·
        refine ⟨5838922097684637114989195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3892614731789758076659463 5838922097684637114989195)
        ·
          refine ⟨8758383146526955672483793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5838922097684637114989195 8758383146526955672483793)
          ·
            refine ⟨6568787359895216754362845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8758383146526955672483793 6568787359895216754362845)
            ·
              refine ⟨2463295259960706282886067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6568787359895216754362845 2463295259960706282886067)
              ·
                refine ⟨3694942889941059424329101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2463295259960706282886067 3694942889941059424329101)
                ·
                  refine ⟨1385603583727897284123413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3694942889941059424329101 1385603583727897284123413)
                  ·
                    refine ⟨64950167987245185193285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1385603583727897284123413 64950167987245185193285)
                    ·
                      rfl

theorem cell23_379470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 3, 1, 3, 6].length) (baseStart_379470 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_379470 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_379470 prefixEnd_379470 := by exact prefixLift 379470
  have htrace : WordTrace (prefixWord ++ tailWord_379470) baseStart_379470 baseEnd_379470 := by
    simpa [prefixWord, tailWord_379470, baseEnd_379470] using wordTrace_append hprefix tailTrace_379470
  have hstable : (prefixWord ++ tailWord_379470).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_379470).length < 2 ^ (prefixWord ++ tailWord_379470).sum := by decide
  have hdescent : baseEnd_379470 < baseStart_379470 := by decide
  rcases family_descends (prefixWord ++ tailWord_379470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_379474 : List Nat := [3, 2, 2, 1, 2, 1, 5, 1, 1, 5]
def baseStart_379474 : Nat := 118140960795 + 379474 * 2 ^ 59
def prefixEnd_379474 : Nat := 4983230072969 + 3 ^ 40 * 379474 * 2
def baseEnd_379474 : Nat := 64950852628117846643279

theorem tailTrace_379474 : CollatzResearch.WordTrace tailWord_379474 prefixEnd_379474 64950852628117846643279 := by
  unfold tailWord_379474
  simp only [CollatzResearch.WordTrace]
  refine ⟨3460138456809495461150369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9227035884825321229734317 3460138456809495461150369)
  ·
    refine ⟨2595103842607121595862777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3460138456809495461150369 2595103842607121595862777)
    ·
      refine ⟨1946327881955341196897083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2595103842607121595862777 1946327881955341196897083)
      ·
        refine ⟨2919491822933011795345625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1946327881955341196897083 2919491822933011795345625)
        ·
          refine ⟨2189618867199758846509219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2919491822933011795345625 2189618867199758846509219)
          ·
            refine ⟨3284428300799638269763829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2189618867199758846509219 3284428300799638269763829)
            ·
              refine ⟨307915153199966087790359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3284428300799638269763829 307915153199966087790359)
              ·
                refine ⟨461872729799949131685539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 307915153199966087790359 461872729799949131685539)
                ·
                  refine ⟨692809094699923697528309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 461872729799949131685539 692809094699923697528309)
                  ·
                    refine ⟨64950852628117846643279, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 692809094699923697528309 64950852628117846643279)
                    ·
                      rfl

theorem cell23_379474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 5, 1, 1, 5].length) (baseStart_379474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_379474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_379474 prefixEnd_379474 := by exact prefixLift 379474
  have htrace : WordTrace (prefixWord ++ tailWord_379474) baseStart_379474 baseEnd_379474 := by
    simpa [prefixWord, tailWord_379474, baseEnd_379474] using wordTrace_append hprefix tailTrace_379474
  have hstable : (prefixWord ++ tailWord_379474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_379474).length < 2 ^ (prefixWord ++ tailWord_379474).sum := by decide
  have hdescent : baseEnd_379474 < baseStart_379474 := by decide
  rcases family_descends (prefixWord ++ tailWord_379474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_379477 : List Nat := [1, 3, 2, 2, 1, 1, 2, 5, 1, 1, 4]
def baseStart_379477 : Nat := 118140960795 + 379477 * 2 ^ 59
def prefixEnd_379477 : Nat := 4983230072969 + 3 ^ 40 * 379477 * 2
def baseEnd_379477 : Nat := 194854098326317028192323

theorem tailTrace_379477 : CollatzResearch.WordTrace tailWord_379477 prefixEnd_379477 194854098326317028192323 := by
  unfold tailWord_379477
  simp only [CollatzResearch.WordTrace]
  refine ⟨13840663246227113356960685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9227108830818075571307123 13840663246227113356960685)
  ·
    refine ⟨5190248717335167508860257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13840663246227113356960685 5190248717335167508860257)
    ·
      refine ⟨3892686538001375631645193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5190248717335167508860257 3892686538001375631645193)
      ·
        refine ⟨2919514903501031723733895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3892686538001375631645193 2919514903501031723733895)
        ·
          refine ⟨4379272355251547585600843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2919514903501031723733895 4379272355251547585600843)
          ·
            refine ⟨6568908532877321378401265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4379272355251547585600843 6568908532877321378401265)
            ·
              refine ⟨4926681399657991033800949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6568908532877321378401265 4926681399657991033800949)
              ·
                refine ⟨461876381217936659418839, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4926681399657991033800949 461876381217936659418839)
                ·
                  refine ⟨692814571826904989128259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 461876381217936659418839 692814571826904989128259)
                  ·
                    refine ⟨1039221857740357483692389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 692814571826904989128259 1039221857740357483692389)
                    ·
                      refine ⟨194854098326317028192323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1039221857740357483692389 194854098326317028192323)
                      ·
                        rfl

theorem cell23_379477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 2, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 2, 5, 1, 1, 4].length) (baseStart_379477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_379477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_379477 prefixEnd_379477 := by exact prefixLift 379477
  have htrace : WordTrace (prefixWord ++ tailWord_379477) baseStart_379477 baseEnd_379477 := by
    simpa [prefixWord, tailWord_379477, baseEnd_379477] using wordTrace_append hprefix tailTrace_379477
  have hstable : (prefixWord ++ tailWord_379477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_379477).length < 2 ^ (prefixWord ++ tailWord_379477).sum := by decide
  have hdescent : baseEnd_379477 < baseStart_379477 := by decide
  rcases family_descends (prefixWord ++ tailWord_379477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_379500 : List Nat := [2, 2, 1, 1, 3, 1, 5, 8]
def baseStart_379500 : Nat := 118140960795 + 379500 * 2 ^ 59
def prefixEnd_379500 : Nat := 4983230072969 + 3 ^ 40 * 379500 * 2
def baseEnd_379500 : Nat := 7217255865976682896471

theorem tailTrace_379500 : CollatzResearch.WordTrace tailWord_379500 prefixEnd_379500 7217255865976682896471 := by
  unfold tailWord_379500
  simp only [CollatzResearch.WordTrace]
  refine ⟨6920751062571894142523977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9227668083429192190031969 6920751062571894142523977)
  ·
    refine ⟨5190563296928920606892983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6920751062571894142523977 5190563296928920606892983)
    ·
      refine ⟨7785844945393380910339475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5190563296928920606892983 7785844945393380910339475)
      ·
        refine ⟨11678767418090071365509213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7785844945393380910339475 11678767418090071365509213)
        ·
          refine ⟨4379537781783776762065955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11678767418090071365509213 4379537781783776762065955)
          ·
            refine ⟨6569306672675665143098933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4379537781783776762065955 6569306672675665143098933)
            ·
              refine ⟨615872500563343607165525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 6569306672675665143098933 615872500563343607165525)
              ·
                refine ⟨7217255865976682896471, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 615872500563343607165525 7217255865976682896471)
                ·
                  rfl

theorem cell23_379500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 5, 8].length) (baseStart_379500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_379500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_379500 prefixEnd_379500 := by exact prefixLift 379500
  have htrace : WordTrace (prefixWord ++ tailWord_379500) baseStart_379500 baseEnd_379500 := by
    simpa [prefixWord, tailWord_379500, baseEnd_379500] using wordTrace_append hprefix tailTrace_379500
  have hstable : (prefixWord ++ tailWord_379500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_379500).length < 2 ^ (prefixWord ++ tailWord_379500).sum := by decide
  have hdescent : baseEnd_379500 < baseStart_379500 := by decide
  rcases family_descends (prefixWord ++ tailWord_379500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_379527 : List Nat := [1, 1, 4, 2, 1, 2, 1, 4, 1, 3, 3]
def baseStart_379527 : Nat := 118140960795 + 379527 * 2 ^ 59
def prefixEnd_379527 : Nat := 4983230072969 + 3 ^ 40 * 379527 * 2
def baseEnd_379527 : Nat := 194879772359041832567093

theorem tailTrace_379527 : CollatzResearch.WordTrace tailWord_379527 prefixEnd_379527 194879772359041832567093 := by
  unfold tailWord_379527
  simp only [CollatzResearch.WordTrace]
  refine ⟨13842486896045971896280835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9228324597363981264187223 13842486896045971896280835)
  ·
    refine ⟨20763730344068957844421253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13842486896045971896280835 20763730344068957844421253)
    ·
      refine ⟨3893199439512929595828985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20763730344068957844421253 3893199439512929595828985)
      ·
        refine ⟨2919899579634697196871739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3893199439512929595828985 2919899579634697196871739)
        ·
          refine ⟨4379849369452045795307609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2919899579634697196871739 4379849369452045795307609)
          ·
            refine ⟨3284887027089034346480707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4379849369452045795307609 3284887027089034346480707)
            ·
              refine ⟨4927330540633551519721061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3284887027089034346480707 4927330540633551519721061)
              ·
                refine ⟨923874476368790909947699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4927330540633551519721061 923874476368790909947699)
                ·
                  refine ⟨1385811714553186364921549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 923874476368790909947699 1385811714553186364921549)
                  ·
                    refine ⟨519679392957444886845581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1385811714553186364921549 519679392957444886845581)
                    ·
                      refine ⟨194879772359041832567093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 519679392957444886845581 194879772359041832567093)
                      ·
                        rfl

theorem cell23_379527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 1, 4, 1, 3, 3].length) (baseStart_379527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_379527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_379527 prefixEnd_379527 := by exact prefixLift 379527
  have htrace : WordTrace (prefixWord ++ tailWord_379527) baseStart_379527 baseEnd_379527 := by
    simpa [prefixWord, tailWord_379527, baseEnd_379527] using wordTrace_append hprefix tailTrace_379527
  have hstable : (prefixWord ++ tailWord_379527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_379527).length < 2 ^ (prefixWord ++ tailWord_379527).sum := by decide
  have hdescent : baseEnd_379527 < baseStart_379527 := by decide
  rcases family_descends (prefixWord ++ tailWord_379527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_379544 : List Nat := [2, 1, 2, 4, 1, 1, 3, 1, 4, 1, 3]
def baseStart_379544 : Nat := 118140960795 + 379544 * 2 ^ 59
def prefixEnd_379544 : Nat := 4983230072969 + 3 ^ 40 * 379544 * 2
def baseEnd_379544 : Nat := 194888501530168266054515

theorem tailTrace_379544 : CollatzResearch.WordTrace tailWord_379544 prefixEnd_379544 194888501530168266054515 := by
  unfold tailWord_379544
  simp only [CollatzResearch.WordTrace]
  refine ⟨6921553468492191899824843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9228737957989589199766457 6921553468492191899824843)
  ·
    refine ⟨10382330202738287849737265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6921553468492191899824843 10382330202738287849737265)
    ·
      refine ⟨7786747652053715887302949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10382330202738287849737265 7786747652053715887302949)
      ·
        refine ⟨1460015184760071728869303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7786747652053715887302949 1460015184760071728869303)
        ·
          refine ⟨2190022777140107593303955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1460015184760071728869303 2190022777140107593303955)
          ·
            refine ⟨3285034165710161389955933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2190022777140107593303955 3285034165710161389955933)
            ·
              refine ⟨1231887812141310521233475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3285034165710161389955933 1231887812141310521233475)
              ·
                refine ⟨1847831718211965781850213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1231887812141310521233475 1847831718211965781850213)
                ·
                  refine ⟨346468447164743584096915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1847831718211965781850213 346468447164743584096915)
                  ·
                    refine ⟨519702670747115376145373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 346468447164743584096915 519702670747115376145373)
                    ·
                      refine ⟨194888501530168266054515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 519702670747115376145373 194888501530168266054515)
                      ·
                        rfl

theorem cell23_379544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 3, 1, 4, 1, 3].length) (baseStart_379544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_379544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_379544 prefixEnd_379544 := by exact prefixLift 379544
  have htrace : WordTrace (prefixWord ++ tailWord_379544) baseStart_379544 baseEnd_379544 := by
    simpa [prefixWord, tailWord_379544, baseEnd_379544] using wordTrace_append hprefix tailTrace_379544
  have hstable : (prefixWord ++ tailWord_379544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_379544).length < 2 ^ (prefixWord ++ tailWord_379544).sum := by decide
  have hdescent : baseEnd_379544 < baseStart_379544 := by decide
  rcases family_descends (prefixWord ++ tailWord_379544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_379571 : List Nat := [1, 1, 1, 2, 3, 5, 2, 2, 1, 3, 2]
def baseStart_379571 : Nat := 118140960795 + 379571 * 2 ^ 59
def prefixEnd_379571 : Nat := 4983230072969 + 3 ^ 40 * 379571 * 2
def baseEnd_379571 : Nat := 194902365507839660416891

theorem tailTrace_379571 : CollatzResearch.WordTrace tailWord_379571 prefixEnd_379571 194902365507839660416891 := by
  unfold tailWord_379571
  simp only [CollatzResearch.WordTrace]
  refine ⟨13844091707886567410882567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9229394471924378273921711 13844091707886567410882567)
  ·
    refine ⟨20766137561829851116323851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13844091707886567410882567 20766137561829851116323851)
    ·
      refine ⟨31149206342744776674485777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20766137561829851116323851 31149206342744776674485777)
      ·
        refine ⟨23361904757058582505864333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31149206342744776674485777 23361904757058582505864333)
        ·
          refine ⟨8760714283896968439699125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23361904757058582505864333 8760714283896968439699125)
          ·
            refine ⟨821316964115340791221793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 8760714283896968439699125 821316964115340791221793)
            ·
              refine ⟨615987723086505593416345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 821316964115340791221793 615987723086505593416345)
              ·
                refine ⟨461990792314879195062259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 615987723086505593416345 461990792314879195062259)
                ·
                  refine ⟨692986188472318792593389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 461990792314879195062259 692986188472318792593389)
                  ·
                    refine ⟨259869820677119547222521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 692986188472318792593389 259869820677119547222521)
                    ·
                      refine ⟨194902365507839660416891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 259869820677119547222521 194902365507839660416891)
                      ·
                        rfl

theorem cell23_379571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 5, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 5, 2, 2, 1, 3, 2].length) (baseStart_379571 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_379571 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_379571 prefixEnd_379571 := by exact prefixLift 379571
  have htrace : WordTrace (prefixWord ++ tailWord_379571) baseStart_379571 baseEnd_379571 := by
    simpa [prefixWord, tailWord_379571, baseEnd_379571] using wordTrace_append hprefix tailTrace_379571
  have hstable : (prefixWord ++ tailWord_379571).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_379571).length < 2 ^ (prefixWord ++ tailWord_379571).sum := by decide
  have hdescent : baseEnd_379571 < baseStart_379571 := by decide
  rcases family_descends (prefixWord ++ tailWord_379571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_379601 : List Nat := [1, 2, 2, 1, 2, 3, 2, 4, 2, 2, 2]
def baseStart_379601 : Nat := 118140960795 + 379601 * 2 ^ 59
def prefixEnd_379601 : Nat := 4983230072969 + 3 ^ 40 * 379601 * 2
def baseEnd_379601 : Nat := 194917769927474543041753

theorem tailTrace_379601 : CollatzResearch.WordTrace tailWord_379601 prefixEnd_379601 194917769927474543041753 := by
  unfold tailWord_379601
  simp only [CollatzResearch.WordTrace]
  refine ⟨13845185897777882534474657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9230123931851921689649771 13845185897777882534474657)
  ·
    refine ⟨10383889423333411900855993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13845185897777882534474657 10383889423333411900855993)
    ·
      refine ⟨7787917067500058925641995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10383889423333411900855993 7787917067500058925641995)
      ·
        refine ⟨11681875601250088388462993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7787917067500058925641995 11681875601250088388462993)
        ·
          refine ⟨8761406700937566291347245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11681875601250088388462993 8761406700937566291347245)
          ·
            refine ⟨3285527512851587359255217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8761406700937566291347245 3285527512851587359255217)
            ·
              refine ⟨2464145634638690519441413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3285527512851587359255217 2464145634638690519441413)
              ·
                refine ⟨462027306494754472395265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2464145634638690519441413 462027306494754472395265)
                ·
                  refine ⟨346520479871065854296449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 462027306494754472395265 346520479871065854296449)
                  ·
                    refine ⟨259890359903299390722337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 346520479871065854296449 259890359903299390722337)
                    ·
                      refine ⟨194917769927474543041753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 259890359903299390722337 194917769927474543041753)
                      ·
                        rfl

theorem cell23_379601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 2, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 2, 4, 2, 2, 2].length) (baseStart_379601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_379601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_379601 prefixEnd_379601 := by exact prefixLift 379601
  have htrace : WordTrace (prefixWord ++ tailWord_379601) baseStart_379601 baseEnd_379601 := by
    simpa [prefixWord, tailWord_379601, baseEnd_379601] using wordTrace_append hprefix tailTrace_379601
  have hstable : (prefixWord ++ tailWord_379601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_379601).length < 2 ^ (prefixWord ++ tailWord_379601).sum := by decide
  have hdescent : baseEnd_379601 < baseStart_379601 := by decide
  rcases family_descends (prefixWord ++ tailWord_379601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_379607 : List Nat := [1, 1, 3, 2, 1, 4, 3, 1, 7]
def baseStart_379607 : Nat := 118140960795 + 379607 * 2 ^ 59
def prefixEnd_379607 : Nat := 4983230072969 + 3 ^ 40 * 379607 * 2
def baseEnd_379607 : Nat := 21657872312377946618525

theorem tailTrace_379607 : CollatzResearch.WordTrace tailWord_379607 prefixEnd_379607 21657872312377946618525 := by
  unfold tailWord_379607
  simp only [CollatzResearch.WordTrace]
  refine ⟨13845404735756145559193075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9230269823837430372795383 13845404735756145559193075)
  ·
    refine ⟨20768107103634218338789613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13845404735756145559193075 20768107103634218338789613)
    ·
      refine ⟨7788040163862831877046105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20768107103634218338789613 7788040163862831877046105)
      ·
        refine ⟨5841030122897123907784579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7788040163862831877046105 5841030122897123907784579)
        ·
          refine ⟨8761545184345685861676869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5841030122897123907784579 8761545184345685861676869)
          ·
            refine ⟨1642789722064816099064413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8761545184345685861676869 1642789722064816099064413)
            ·
              refine ⟨616046145774306037149155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1642789722064816099064413 616046145774306037149155)
              ·
                refine ⟨924069218661459055723733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 616046145774306037149155 924069218661459055723733)
                ·
                  refine ⟨21657872312377946618525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 924069218661459055723733 21657872312377946618525)
                  ·
                    rfl

theorem cell23_379607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 3, 1, 7].length) (baseStart_379607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_379607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_379607 prefixEnd_379607 := by exact prefixLift 379607
  have htrace : WordTrace (prefixWord ++ tailWord_379607) baseStart_379607 baseEnd_379607 := by
    simpa [prefixWord, tailWord_379607, baseEnd_379607] using wordTrace_append hprefix tailTrace_379607
  have hstable : (prefixWord ++ tailWord_379607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_379607).length < 2 ^ (prefixWord ++ tailWord_379607).sum := by decide
  have hdescent : baseEnd_379607 < baseStart_379607 := by decide
  rcases family_descends (prefixWord ++ tailWord_379607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_379697 : List Nat := [1, 2, 2, 3, 2, 1, 2, 2, 8]
def baseStart_379697 : Nat := 118140960795 + 379697 * 2 ^ 59
def prefixEnd_379697 : Nat := 4983230072969 + 3 ^ 40 * 379697 * 2
def baseEnd_379697 : Nat := 21663007118922907493479

theorem tailTrace_379697 : CollatzResearch.WordTrace tailWord_379697 prefixEnd_379697 21663007118922907493479 := by
  unfold tailWord_379697
  simp only [CollatzResearch.WordTrace]
  refine ⟨13848687305430090929969345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9232458203620060619979563 13848687305430090929969345)
  ·
    refine ⟨10386515479072568197477009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13848687305430090929969345 10386515479072568197477009)
    ·
      refine ⟨7789886609304426148107757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10386515479072568197477009 7789886609304426148107757)
      ·
        refine ⟨2921207478489159805540409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7789886609304426148107757 2921207478489159805540409)
        ·
          refine ⟨2190905608866869854155307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2921207478489159805540409 2190905608866869854155307)
          ·
            refine ⟨3286358413300304781232961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2190905608866869854155307 3286358413300304781232961)
            ·
              refine ⟨2464768809975228585924721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3286358413300304781232961 2464768809975228585924721)
              ·
                refine ⟨1848576607481421439443541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2464768809975228585924721 1848576607481421439443541)
                ·
                  refine ⟨21663007118922907493479, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 1848576607481421439443541 21663007118922907493479)
                  ·
                    rfl

theorem cell23_379697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 2, 2, 8].length) (baseStart_379697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_379697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_379697 prefixEnd_379697 := by exact prefixLift 379697
  have htrace : WordTrace (prefixWord ++ tailWord_379697) baseStart_379697 baseEnd_379697 := by
    simpa [prefixWord, tailWord_379697, baseEnd_379697] using wordTrace_append hprefix tailTrace_379697
  have hstable : (prefixWord ++ tailWord_379697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_379697).length < 2 ^ (prefixWord ++ tailWord_379697).sum := by decide
  have hdescent : baseEnd_379697 < baseStart_379697 := by decide
  rcases family_descends (prefixWord ++ tailWord_379697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_379751 : List Nat := [1, 1, 5, 1, 2, 2, 2, 1, 1, 5, 2]
def baseStart_379751 : Nat := 118140960795 + 379751 * 2 ^ 59
def prefixEnd_379751 : Nat := 4983230072969 + 3 ^ 40 * 379751 * 2
def baseEnd_379751 : Nat := 194994792025648956166063

theorem tailTrace_379751 : CollatzResearch.WordTrace tailWord_379751 prefixEnd_379751 194994792025648956166063 := by
  unfold tailWord_379751
  simp only [CollatzResearch.WordTrace]
  refine ⟨13850656847234458152435107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9233771231489638768290071 13850656847234458152435107)
  ·
    refine ⟨20775985270851687228652661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13850656847234458152435107 20775985270851687228652661)
    ·
      refine ⟨1947748619142345677686187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 20775985270851687228652661 1947748619142345677686187)
      ·
        refine ⟨2921622928713518516529281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1947748619142345677686187 2921622928713518516529281)
        ·
          refine ⟨2191217196535138887396961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2921622928713518516529281 2191217196535138887396961)
          ·
            refine ⟨1643412897401354165547721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2191217196535138887396961 1643412897401354165547721)
            ·
              refine ⟨1232559673051015624160791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1643412897401354165547721 1232559673051015624160791)
              ·
                refine ⟨1848839509576523436241187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1232559673051015624160791 1848839509576523436241187)
                ·
                  refine ⟨2773259264364785154361781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1848839509576523436241187 2773259264364785154361781)
                  ·
                    refine ⟨259993056034198608221417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2773259264364785154361781 259993056034198608221417)
                    ·
                      refine ⟨194994792025648956166063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 259993056034198608221417 194994792025648956166063)
                      ·
                        rfl

theorem cell23_379751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 2, 1, 1, 5, 2].length) (baseStart_379751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_379751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_379751 prefixEnd_379751 := by exact prefixLift 379751
  have htrace : WordTrace (prefixWord ++ tailWord_379751) baseStart_379751 baseEnd_379751 := by
    simpa [prefixWord, tailWord_379751, baseEnd_379751] using wordTrace_append hprefix tailTrace_379751
  have hstable : (prefixWord ++ tailWord_379751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_379751).length < 2 ^ (prefixWord ++ tailWord_379751).sum := by decide
  have hdescent : baseEnd_379751 < baseStart_379751 := by decide
  rcases family_descends (prefixWord ++ tailWord_379751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_379787 : List Nat := [1, 1, 1, 1, 4, 2, 3, 10]
def baseStart_379787 : Nat := 118140960795 + 379787 * 2 ^ 59
def prefixEnd_379787 : Nat := 4983230072969 + 3 ^ 40 * 379787 * 2
def baseEnd_379787 : Nat := 7222713975155956122811

theorem tailTrace_379787 : CollatzResearch.WordTrace tailWord_379787 prefixEnd_379787 7222713975155956122811 := by
  unfold tailWord_379787
  simp only [CollatzResearch.WordTrace]
  refine ⟨13851969875104036300745615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9234646583402690867163743 13851969875104036300745615)
  ·
    refine ⟨20777954812656054451118423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13851969875104036300745615 20777954812656054451118423)
    ·
      refine ⟨31166932218984081676677635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20777954812656054451118423 31166932218984081676677635)
      ·
        refine ⟨46750398328476122515016453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31166932218984081676677635 46750398328476122515016453)
        ·
          refine ⟨8765699686589272971565585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 46750398328476122515016453 8765699686589272971565585)
          ·
            refine ⟨6574274764941954728674189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8765699686589272971565585 6574274764941954728674189)
            ·
              refine ⟨2465353036853233023252821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6574274764941954728674189 2465353036853233023252821)
              ·
                refine ⟨7222713975155956122811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 2465353036853233023252821 7222713975155956122811)
                ·
                  rfl

theorem cell23_379787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 3, 10].length) (baseStart_379787 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_379787 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_379787 prefixEnd_379787 := by exact prefixLift 379787
  have htrace : WordTrace (prefixWord ++ tailWord_379787) baseStart_379787 baseEnd_379787 := by
    simpa [prefixWord, tailWord_379787, baseEnd_379787] using wordTrace_append hprefix tailTrace_379787
  have hstable : (prefixWord ++ tailWord_379787).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_379787).length < 2 ^ (prefixWord ++ tailWord_379787).sum := by decide
  have hdescent : baseEnd_379787 < baseStart_379787 := by decide
  rcases family_descends (prefixWord ++ tailWord_379787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_379815 : List Nat := [1, 1, 6, 1, 3, 1, 3, 1, 1, 1, 4]
def baseStart_379815 : Nat := 118140960795 + 379815 * 2 ^ 59
def prefixEnd_379815 : Nat := 4983230072969 + 3 ^ 40 * 379815 * 2
def baseEnd_379815 : Nat := 195027654787536705765769

theorem tailTrace_379815 : CollatzResearch.WordTrace tailWord_379815 prefixEnd_379815 195027654787536705765769 := by
  unfold tailWord_379815
  simp only [CollatzResearch.WordTrace]
  refine ⟨13852991119002597082764899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9235327412668398055176599 13852991119002597082764899)
  ·
    refine ⟨20779486678503895624147349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13852991119002597082764899 20779486678503895624147349)
    ·
      refine ⟨974038438054870107381907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 20779486678503895624147349 974038438054870107381907)
      ·
        refine ⟨1461057657082305161072861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 974038438054870107381907 1461057657082305161072861)
        ·
          refine ⟨547896621405864435402323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1461057657082305161072861 547896621405864435402323)
          ·
            refine ⟨821844932108796653103485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 547896621405864435402323 821844932108796653103485)
            ·
              refine ⟨308191849540798744913807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 821844932108796653103485 308191849540798744913807)
              ·
                refine ⟨462287774311198117370711, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 308191849540798744913807 462287774311198117370711)
                ·
                  refine ⟨693431661466797176056067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 462287774311198117370711 693431661466797176056067)
                  ·
                    refine ⟨1040147492200195764084101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 693431661466797176056067 1040147492200195764084101)
                    ·
                      refine ⟨195027654787536705765769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1040147492200195764084101 195027654787536705765769)
                      ·
                        rfl

theorem cell23_379815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 1, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 1, 3, 1, 1, 1, 4].length) (baseStart_379815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_379815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_379815 prefixEnd_379815 := by exact prefixLift 379815
  have htrace : WordTrace (prefixWord ++ tailWord_379815) baseStart_379815 baseEnd_379815 := by
    simpa [prefixWord, tailWord_379815, baseEnd_379815] using wordTrace_append hprefix tailTrace_379815
  have hstable : (prefixWord ++ tailWord_379815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_379815).length < 2 ^ (prefixWord ++ tailWord_379815).sum := by decide
  have hdescent : baseEnd_379815 < baseStart_379815 := by decide
  rcases family_descends (prefixWord ++ tailWord_379815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_379821 : List Nat := [1, 5, 2, 3, 1, 11]
def baseStart_379821 : Nat := 118140960795 + 379821 * 2 ^ 59
def prefixEnd_379821 : Nat := 4983230072969 + 3 ^ 40 * 379821 * 2
def baseEnd_379821 : Nat := 802595620047175647287

theorem tailTrace_379821 : CollatzResearch.WordTrace tailWord_379821 prefixEnd_379821 802595620047175647287 := by
  unfold tailWord_379821
  simp only [CollatzResearch.WordTrace]
  refine ⟨13853209956980860107483317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9235473304653906738322211 13853209956980860107483317)
  ·
    refine ⟨1298738433466955635076561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 13853209956980860107483317 1298738433466955635076561)
    ·
      refine ⟨974053825100216726307421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1298738433466955635076561 974053825100216726307421)
      ·
        refine ⟨365270184412581272365283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 974053825100216726307421 365270184412581272365283)
        ·
          refine ⟨547905276618871908547925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 365270184412581272365283 547905276618871908547925)
          ·
            refine ⟨802595620047175647287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 547905276618871908547925 802595620047175647287)
            ·
              rfl

theorem cell23_379821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 11].length) (baseStart_379821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_379821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_379821 prefixEnd_379821 := by exact prefixLift 379821
  have htrace : WordTrace (prefixWord ++ tailWord_379821) baseStart_379821 baseEnd_379821 := by
    simpa [prefixWord, tailWord_379821, baseEnd_379821] using wordTrace_append hprefix tailTrace_379821
  have hstable : (prefixWord ++ tailWord_379821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_379821).length < 2 ^ (prefixWord ++ tailWord_379821).sum := by decide
  have hdescent : baseEnd_379821 < baseStart_379821 := by decide
  rcases family_descends (prefixWord ++ tailWord_379821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_379831 : List Nat := [1, 1, 3, 1, 3, 1, 2, 3, 4, 1, 3]
def baseStart_379831 : Nat := 118140960795 + 379831 * 2 ^ 59
def prefixEnd_379831 : Nat := 4983230072969 + 3 ^ 40 * 379831 * 2
def baseEnd_379831 : Nat := 195035870478008643165695

theorem tailTrace_379831 : CollatzResearch.WordTrace tailWord_379831 prefixEnd_379831 195035870478008643165695 := by
  unfold tailWord_379831
  simp only [CollatzResearch.WordTrace]
  refine ⟨13853574686944631815347347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9235716457963087876898231 13853574686944631815347347)
  ·
    refine ⟨20780362030416947723021021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13853574686944631815347347 20780362030416947723021021)
    ·
      refine ⟨7792635761406355396132883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20780362030416947723021021 7792635761406355396132883)
      ·
        refine ⟨11688953642109533094199325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7792635761406355396132883 11688953642109533094199325)
        ·
          refine ⟨4383357615791074910324747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11688953642109533094199325 4383357615791074910324747)
          ·
            refine ⟨6575036423686612365487121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4383357615791074910324747 6575036423686612365487121)
            ·
              refine ⟨4931277317764959274115341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6575036423686612365487121 4931277317764959274115341)
              ·
                refine ⟨1849228994161859727793253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4931277317764959274115341 1849228994161859727793253)
                ·
                  refine ⟨346730436405348698961235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1849228994161859727793253 346730436405348698961235)
                  ·
                    refine ⟨520095654608023048441853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 346730436405348698961235 520095654608023048441853)
                    ·
                      refine ⟨195035870478008643165695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 520095654608023048441853 195035870478008643165695)
                      ·
                        rfl

theorem cell23_379831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 2, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 2, 3, 4, 1, 3].length) (baseStart_379831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_379831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_379831 prefixEnd_379831 := by exact prefixLift 379831
  have htrace : WordTrace (prefixWord ++ tailWord_379831) baseStart_379831 baseEnd_379831 := by
    simpa [prefixWord, tailWord_379831, baseEnd_379831] using wordTrace_append hprefix tailTrace_379831
  have hstable : (prefixWord ++ tailWord_379831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_379831).length < 2 ^ (prefixWord ++ tailWord_379831).sum := by decide
  have hdescent : baseEnd_379831 < baseStart_379831 := by decide
  rcases family_descends (prefixWord ++ tailWord_379831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_379832 : List Nat := [2, 1, 2, 1, 2, 4, 4, 2, 1, 2, 2]
def baseStart_379832 : Nat := 118140960795 + 379832 * 2 ^ 59
def prefixEnd_379832 : Nat := 4983230072969 + 3 ^ 40 * 379832 * 2
def baseEnd_379832 : Nat := 195036383958663139253191

theorem tailTrace_379832 : CollatzResearch.WordTrace tailWord_379832 prefixEnd_379832 195036383958663139253191 := by
  unfold tailWord_379832
  simp only [CollatzResearch.WordTrace]
  refine ⟨6926805579970504493066875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9235740773294005990755833 6926805579970504493066875)
  ·
    refine ⟨10390208369955756739600313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6926805579970504493066875 10390208369955756739600313)
    ·
      refine ⟨7792656277466817554700235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10390208369955756739600313 7792656277466817554700235)
      ·
        refine ⟨11688984416200226332050353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7792656277466817554700235 11688984416200226332050353)
        ·
          refine ⟨8766738312150169749037765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11688984416200226332050353 8766738312150169749037765)
          ·
            refine ⟨1643763433528156827944581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8766738312150169749037765 1643763433528156827944581)
            ·
              refine ⟨308205643786529405239609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1643763433528156827944581 308205643786529405239609)
              ·
                refine ⟨231154232839897053929707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 308205643786529405239609 231154232839897053929707)
                ·
                  refine ⟨346731349259845580894561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 231154232839897053929707 346731349259845580894561)
                  ·
                    refine ⟨260048511944884185670921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 346731349259845580894561 260048511944884185670921)
                    ·
                      refine ⟨195036383958663139253191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 260048511944884185670921 195036383958663139253191)
                      ·
                        rfl

theorem cell23_379832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 4, 2, 1, 2, 2].length) (baseStart_379832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_379832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_379832 prefixEnd_379832 := by exact prefixLift 379832
  have htrace : WordTrace (prefixWord ++ tailWord_379832) baseStart_379832 baseEnd_379832 := by
    simpa [prefixWord, tailWord_379832, baseEnd_379832] using wordTrace_append hprefix tailTrace_379832
  have hstable : (prefixWord ++ tailWord_379832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_379832).length < 2 ^ (prefixWord ++ tailWord_379832).sum := by decide
  have hdescent : baseEnd_379832 < baseStart_379832 := by decide
  rcases family_descends (prefixWord ++ tailWord_379832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_379848 : List Nat := [2, 1, 3, 1, 5, 1, 2, 1, 1, 3, 3]
def baseStart_379848 : Nat := 118140960795 + 379848 * 2 ^ 59
def prefixEnd_379848 : Nat := 4983230072969 + 3 ^ 40 * 379848 * 2
def baseEnd_379848 : Nat := 195044599649135076653117

theorem tailTrace_379848 : CollatzResearch.WordTrace tailWord_379848 prefixEnd_379848 195044599649135076653117 := by
  unfold tailWord_379848
  simp only [CollatzResearch.WordTrace]
  refine ⟨6927097363941521859358099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9236129818588695812477465 6927097363941521859358099)
  ·
    refine ⟨10390646045912282789037149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6927097363941521859358099 10390646045912282789037149)
    ·
      refine ⟨3896492267217106045888931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10390646045912282789037149 3896492267217106045888931)
      ·
        refine ⟨5844738400825659068833397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3896492267217106045888931 5844738400825659068833397)
        ·
          refine ⟨547944225077405537703131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 5844738400825659068833397 547944225077405537703131)
          ·
            refine ⟨821916337616108306554697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 547944225077405537703131 821916337616108306554697)
            ·
              refine ⟨616437253212081229916023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 821916337616108306554697 616437253212081229916023)
              ·
                refine ⟨924655879818121844874035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 616437253212081229916023 924655879818121844874035)
                ·
                  refine ⟨1386983819727182767311053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 924655879818121844874035 1386983819727182767311053)
                  ·
                    refine ⟨520118932397693537741645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1386983819727182767311053 520118932397693537741645)
                    ·
                      refine ⟨195044599649135076653117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 520118932397693537741645 195044599649135076653117)
                      ·
                        rfl

theorem cell23_379848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 1, 2, 1, 1, 3, 3].length) (baseStart_379848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_379848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_379848 prefixEnd_379848 := by exact prefixLift 379848
  have htrace : WordTrace (prefixWord ++ tailWord_379848) baseStart_379848 baseEnd_379848 := by
    simpa [prefixWord, tailWord_379848, baseEnd_379848] using wordTrace_append hprefix tailTrace_379848
  have hstable : (prefixWord ++ tailWord_379848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_379848).length < 2 ^ (prefixWord ++ tailWord_379848).sum := by decide
  have hdescent : baseEnd_379848 < baseStart_379848 := by decide
  rcases family_descends (prefixWord ++ tailWord_379848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_379905 : List Nat := [1, 2, 4, 1, 2, 4, 1, 1, 1, 4, 2]
def baseStart_379905 : Nat := 118140960795 + 379905 * 2 ^ 59
def prefixEnd_379905 : Nat := 4983230072969 + 3 ^ 40 * 379905 * 2
def baseEnd_379905 : Nat := 195073868046441353640355

theorem tailTrace_379905 : CollatzResearch.WordTrace tailWord_379905 prefixEnd_379905 195073868046441353640355 := by
  unfold tailWord_379905
  simp only [CollatzResearch.WordTrace]
  refine ⟨13856273688676542453541169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9237515792451028302360779 13856273688676542453541169)
  ·
    refine ⟨10392205266507406840155877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13856273688676542453541169 10392205266507406840155877)
    ·
      refine ⟨1948538487470138782529227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10392205266507406840155877 1948538487470138782529227)
      ·
        refine ⟨2922807731205208173793841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1948538487470138782529227 2922807731205208173793841)
        ·
          refine ⟨2192105798403906130345381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2922807731205208173793841 2192105798403906130345381)
          ·
            refine ⟨411019837200732399439759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2192105798403906130345381 411019837200732399439759)
            ·
              refine ⟨616529755801098599159639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 411019837200732399439759 616529755801098599159639)
              ·
                refine ⟨924794633701647898739459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 616529755801098599159639 924794633701647898739459)
                ·
                  refine ⟨1387191950552471848109189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 924794633701647898739459 1387191950552471848109189)
                  ·
                    refine ⟨260098490728588471520473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1387191950552471848109189 260098490728588471520473)
                    ·
                      refine ⟨195073868046441353640355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 260098490728588471520473 195073868046441353640355)
                      ·
                        rfl

theorem cell23_379905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 4, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 4, 1, 1, 1, 4, 2].length) (baseStart_379905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_379905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_379905 prefixEnd_379905 := by exact prefixLift 379905
  have htrace : WordTrace (prefixWord ++ tailWord_379905) baseStart_379905 baseEnd_379905 := by
    simpa [prefixWord, tailWord_379905, baseEnd_379905] using wordTrace_append hprefix tailTrace_379905
  have hstable : (prefixWord ++ tailWord_379905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_379905).length < 2 ^ (prefixWord ++ tailWord_379905).sum := by decide
  have hdescent : baseEnd_379905 < baseStart_379905 := by decide
  rcases family_descends (prefixWord ++ tailWord_379905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_379928 : List Nat := [2, 1, 2, 3, 2, 2, 3, 3, 5]
def baseStart_379928 : Nat := 118140960795 + 379928 * 2 ^ 59
def prefixEnd_379928 : Nat := 4983230072969 + 3 ^ 40 * 379928 * 2
def baseEnd_379928 : Nat := 21676186455721640405861

theorem tailTrace_379928 : CollatzResearch.WordTrace tailWord_379928 prefixEnd_379928 21676186455721640405861 := by
  unfold tailWord_379928
  simp only [CollatzResearch.WordTrace]
  refine ⟨6928556283796608690814219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9238075045062144921085625 6928556283796608690814219)
  ·
    refine ⟨10392834425694913036221329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6928556283796608690814219 10392834425694913036221329)
    ·
      refine ⟨7794625819271184777165997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10392834425694913036221329 7794625819271184777165997)
      ·
        refine ⟨2922984682226694291437249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7794625819271184777165997 2922984682226694291437249)
        ·
          refine ⟨2192238511670020718577937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2922984682226694291437249 2192238511670020718577937)
          ·
            refine ⟨1644178883752515538933453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2192238511670020718577937 1644178883752515538933453)
            ·
              refine ⟨616567081407193327100045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1644178883752515538933453 616567081407193327100045)
              ·
                refine ⟨231212655527697497662517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 616567081407193327100045 231212655527697497662517)
                ·
                  refine ⟨21676186455721640405861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 231212655527697497662517 21676186455721640405861)
                  ·
                    rfl

theorem cell23_379928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 3, 3, 5].length) (baseStart_379928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_379928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_379928 prefixEnd_379928 := by exact prefixLift 379928
  have htrace : WordTrace (prefixWord ++ tailWord_379928) baseStart_379928 baseEnd_379928 := by
    simpa [prefixWord, tailWord_379928, baseEnd_379928] using wordTrace_append hprefix tailTrace_379928
  have hstable : (prefixWord ++ tailWord_379928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_379928).length < 2 ^ (prefixWord ++ tailWord_379928).sum := by decide
  have hdescent : baseEnd_379928 < baseStart_379928 := by decide
  rcases family_descends (prefixWord ++ tailWord_379928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_379941 : List Nat := [1, 3, 1, 2, 2, 2, 3, 2, 2, 5]
def baseStart_379941 : Nat := 118140960795 + 379941 * 2 ^ 59
def prefixEnd_379941 : Nat := 4983230072969 + 3 ^ 40 * 379941 * 2
def baseEnd_379941 : Nat := 65030784450001070930063

theorem tailTrace_379941 : CollatzResearch.WordTrace tailWord_379941 prefixEnd_379941 65030784450001070930063 := by
  unfold tailWord_379941
  simp only [CollatzResearch.WordTrace]
  refine ⟨13857586716546120601851677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9238391144364080401234451 13857586716546120601851677)
  ·
    refine ⟨5196595018704795225694379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13857586716546120601851677 5196595018704795225694379)
    ·
      refine ⟨7794892528057192838541569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5196595018704795225694379 7794892528057192838541569)
      ·
        refine ⟨5846169396042894628906177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7794892528057192838541569 5846169396042894628906177)
        ·
          refine ⟨4384627047032170971679633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5846169396042894628906177 4384627047032170971679633)
          ·
            refine ⟨3288470285274128228759725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4384627047032170971679633 3288470285274128228759725)
            ·
              refine ⟨1233176356977798085784897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3288470285274128228759725 1233176356977798085784897)
              ·
                refine ⟨924882267733348564338673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1233176356977798085784897 924882267733348564338673)
                ·
                  refine ⟨693661700800011423254005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 924882267733348564338673 693661700800011423254005)
                  ·
                    refine ⟨65030784450001070930063, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 693661700800011423254005 65030784450001070930063)
                    ·
                      rfl

theorem cell23_379941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 3, 2, 2, 5].length) (baseStart_379941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_379941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_379941 prefixEnd_379941 := by exact prefixLift 379941
  have htrace : WordTrace (prefixWord ++ tailWord_379941) baseStart_379941 baseEnd_379941 := by
    simpa [prefixWord, tailWord_379941, baseEnd_379941] using wordTrace_append hprefix tailTrace_379941
  have hstable : (prefixWord ++ tailWord_379941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_379941).length < 2 ^ (prefixWord ++ tailWord_379941).sum := by decide
  have hdescent : baseEnd_379941 < baseStart_379941 := by decide
  rcases family_descends (prefixWord ++ tailWord_379941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_379956 : List Nat := [2, 5, 1, 2, 1, 3, 2, 1, 2, 2, 2]
def baseStart_379956 : Nat := 118140960795 + 379956 * 2 ^ 59
def prefixEnd_379956 : Nat := 4983230072969 + 3 ^ 40 * 379956 * 2
def baseEnd_379956 : Nat := 195100055559820654102621

theorem tailTrace_379956 : CollatzResearch.WordTrace tailWord_379956 prefixEnd_379956 195100055559820654102621 := by
  unfold tailWord_379956
  simp only [CollatzResearch.WordTrace]
  refine ⟨6929066905745889081823861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9238755874327852109098481 6929066905745889081823861)
  ·
    refine ⟨649600022413677101420987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 6929066905745889081823861 649600022413677101420987)
    ·
      refine ⟨974400033620515652131481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 649600022413677101420987 974400033620515652131481)
      ·
        refine ⟨730800025215386739098611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 974400033620515652131481 730800025215386739098611)
        ·
          refine ⟨1096200037823080108647917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 730800025215386739098611 1096200037823080108647917)
          ·
            refine ⟨411075014183655040742969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1096200037823080108647917 411075014183655040742969)
            ·
              refine ⟨308306260637741280557227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 411075014183655040742969 308306260637741280557227)
              ·
                refine ⟨462459390956611920835841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 308306260637741280557227 462459390956611920835841)
                ·
                  refine ⟨346844543217458940626881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 462459390956611920835841 346844543217458940626881)
                  ·
                    refine ⟨260133407413094205470161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 346844543217458940626881 260133407413094205470161)
                    ·
                      refine ⟨195100055559820654102621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 260133407413094205470161 195100055559820654102621)
                      ·
                        rfl

theorem cell23_379956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 3, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 3, 2, 1, 2, 2, 2].length) (baseStart_379956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_379956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_379956 prefixEnd_379956 := by exact prefixLift 379956
  have htrace : WordTrace (prefixWord ++ tailWord_379956) baseStart_379956 baseEnd_379956 := by
    simpa [prefixWord, tailWord_379956, baseEnd_379956] using wordTrace_append hprefix tailTrace_379956
  have hstable : (prefixWord ++ tailWord_379956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_379956).length < 2 ^ (prefixWord ++ tailWord_379956).sum := by decide
  have hdescent : baseEnd_379956 < baseStart_379956 := by decide
  rcases family_descends (prefixWord ++ tailWord_379956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_379971 : List Nat := [1, 1, 1, 3, 1, 2, 4, 1, 5, 4]
def baseStart_379971 : Nat := 118140960795 + 379971 * 2 ^ 59
def prefixEnd_379971 : Nat := 4983230072969 + 3 ^ 40 * 379971 * 2
def baseEnd_379971 : Nat := 65035919256546031805017

theorem tailTrace_379971 : CollatzResearch.WordTrace tailWord_379971 prefixEnd_379971 65035919256546031805017 := by
  unfold tailWord_379971
  simp only [CollatzResearch.WordTrace]
  refine ⟨13858680906437435725443767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9239120604291623816962511 13858680906437435725443767)
  ·
    refine ⟨20788021359656153588165651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13858680906437435725443767 20788021359656153588165651)
    ·
      refine ⟨31182032039484230382248477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20788021359656153588165651 31182032039484230382248477)
      ·
        refine ⟨11693262014806586393343179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31182032039484230382248477 11693262014806586393343179)
        ·
          refine ⟨17539893022209879590014769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11693262014806586393343179 17539893022209879590014769)
          ·
            refine ⟨13154919766657409692511077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17539893022209879590014769 13154919766657409692511077)
            ·
              refine ⟨2466547456248264317345827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13154919766657409692511077 2466547456248264317345827)
              ·
                refine ⟨3699821184372396476018741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2466547456248264317345827 3699821184372396476018741)
                ·
                  refine ⟨346858236034912169626757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3699821184372396476018741 346858236034912169626757)
                  ·
                    refine ⟨65035919256546031805017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 346858236034912169626757 65035919256546031805017)
                    ·
                      rfl

theorem cell23_379971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 4, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 4, 1, 5, 4].length) (baseStart_379971 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_379971 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_379971 prefixEnd_379971 := by exact prefixLift 379971
  have htrace : WordTrace (prefixWord ++ tailWord_379971) baseStart_379971 baseEnd_379971 := by
    simpa [prefixWord, tailWord_379971, baseEnd_379971] using wordTrace_append hprefix tailTrace_379971
  have hstable : (prefixWord ++ tailWord_379971).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_379971).length < 2 ^ (prefixWord ++ tailWord_379971).sum := by decide
  have hdescent : baseEnd_379971 < baseStart_379971 := by decide
  rcases family_descends (prefixWord ++ tailWord_379971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_379984 : List Nat := [2, 1, 1, 1, 1, 3, 1, 3, 10]
def baseStart_379984 : Nat := 118140960795 + 379984 * 2 ^ 59
def prefixEnd_379984 : Nat := 4983230072969 + 3 ^ 40 * 379984 * 2
def baseEnd_379984 : Nat := 21679381446460727172499

theorem tailTrace_379984 : CollatzResearch.WordTrace tailWord_379984 prefixEnd_379984 21679381446460727172499 := by
  unfold tailWord_379984
  simp only [CollatzResearch.WordTrace]
  refine ⟨6929577527695169472833503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9239436703593559297111337 6929577527695169472833503)
  ·
    refine ⟨10394366291542754209250255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6929577527695169472833503 10394366291542754209250255)
    ·
      refine ⟨15591549437314131313875383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10394366291542754209250255 15591549437314131313875383)
      ·
        refine ⟨23387324155971196970813075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15591549437314131313875383 23387324155971196970813075)
        ·
          refine ⟨35080986233956795456219613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23387324155971196970813075 35080986233956795456219613)
          ·
            refine ⟨13155369837733798296082355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35080986233956795456219613 13155369837733798296082355)
            ·
              refine ⟨19733054756600697444123533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13155369837733798296082355 19733054756600697444123533)
              ·
                refine ⟨7399895533725261541546325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19733054756600697444123533 7399895533725261541546325)
                ·
                  refine ⟨21679381446460727172499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 7399895533725261541546325 21679381446460727172499)
                  ·
                    rfl

theorem cell23_379984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 3, 10].length) (baseStart_379984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_379984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_379984 prefixEnd_379984 := by exact prefixLift 379984
  have htrace : WordTrace (prefixWord ++ tailWord_379984) baseStart_379984 baseEnd_379984 := by
    simpa [prefixWord, tailWord_379984, baseEnd_379984] using wordTrace_append hprefix tailTrace_379984
  have hstable : (prefixWord ++ tailWord_379984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_379984).length < 2 ^ (prefixWord ++ tailWord_379984).sum := by decide
  have hdescent : baseEnd_379984 < baseStart_379984 := by decide
  rcases family_descends (prefixWord ++ tailWord_379984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_380001 : List Nat := [1, 2, 3, 1, 1, 2, 3, 4, 6]
def baseStart_380001 : Nat := 118140960795 + 380001 * 2 ^ 59
def prefixEnd_380001 : Nat := 4983230072969 + 3 ^ 40 * 380001 * 2
def baseEnd_380001 : Nat := 21680351354363664226657

theorem tailTrace_380001 : CollatzResearch.WordTrace tailWord_380001 prefixEnd_380001 21680351354363664226657 := by
  unfold tailWord_380001
  simp only [CollatzResearch.WordTrace]
  refine ⟨13859775096328750849035857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9239850064219167232690571 13859775096328750849035857)
  ·
    refine ⟨10394831322246563136776893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13859775096328750849035857 10394831322246563136776893)
    ·
      refine ⟨3898061745842461176291335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10394831322246563136776893 3898061745842461176291335)
      ·
        refine ⟨5847092618763691764437003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3898061745842461176291335 5847092618763691764437003)
        ·
          refine ⟨8770638928145537646655505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5847092618763691764437003 8770638928145537646655505)
          ·
            refine ⟨6577979196109153234991629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8770638928145537646655505 6577979196109153234991629)
            ·
              refine ⟨2466742198540932463121861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6577979196109153234991629 2466742198540932463121861)
              ·
                refine ⟨462514162226424836835349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2466742198540932463121861 462514162226424836835349)
                ·
                  refine ⟨21680351354363664226657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 462514162226424836835349 21680351354363664226657)
                  ·
                    rfl

theorem cell23_380001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 3, 4, 6].length) (baseStart_380001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_380001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_380001 prefixEnd_380001 := by exact prefixLift 380001
  have htrace : WordTrace (prefixWord ++ tailWord_380001) baseStart_380001 baseEnd_380001 := by
    simpa [prefixWord, tailWord_380001, baseEnd_380001] using wordTrace_append hprefix tailTrace_380001
  have hstable : (prefixWord ++ tailWord_380001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_380001).length < 2 ^ (prefixWord ++ tailWord_380001).sum := by decide
  have hdescent : baseEnd_380001 < baseStart_380001 := by decide
  rcases family_descends (prefixWord ++ tailWord_380001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_380005 : List Nat := [1, 3, 1, 3, 2, 1, 3, 4, 1, 4]
def baseStart_380005 : Nat := 118140960795 + 380005 * 2 ^ 59
def prefixEnd_380005 : Nat := 4983230072969 + 3 ^ 40 * 380005 * 2
def baseEnd_380005 : Nat := 65041738703963654129965

theorem tailTrace_380005 : CollatzResearch.WordTrace tailWord_380005 prefixEnd_380005 65041738703963654129965 := by
  unfold tailWord_380005
  simp only [CollatzResearch.WordTrace]
  refine ⟨13859920988314259532181469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9239947325542839688120979 13859920988314259532181469)
  ·
    refine ⟨5197470370617847324568051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13859920988314259532181469 5197470370617847324568051)
    ·
      refine ⟨7796205555926770986852077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5197470370617847324568051 7796205555926770986852077)
      ·
        refine ⟨2923577083472539120069529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7796205555926770986852077 2923577083472539120069529)
        ·
          refine ⟨2192682812604404340052147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2923577083472539120069529 2192682812604404340052147)
          ·
            refine ⟨3289024218906606510078221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2192682812604404340052147 3289024218906606510078221)
            ·
              refine ⟨1233384082089977441279333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3289024218906606510078221 1233384082089977441279333)
              ·
                refine ⟨231259515391870770239875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1233384082089977441279333 231259515391870770239875)
                ·
                  refine ⟨346889273087806155359813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 231259515391870770239875 346889273087806155359813)
                  ·
                    refine ⟨65041738703963654129965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 346889273087806155359813 65041738703963654129965)
                    ·
                      rfl

theorem cell23_380005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 3, 4, 1, 4].length) (baseStart_380005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_380005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_380005 prefixEnd_380005 := by exact prefixLift 380005
  have htrace : WordTrace (prefixWord ++ tailWord_380005) baseStart_380005 baseEnd_380005 := by
    simpa [prefixWord, tailWord_380005, baseEnd_380005] using wordTrace_append hprefix tailTrace_380005
  have hstable : (prefixWord ++ tailWord_380005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_380005).length < 2 ^ (prefixWord ++ tailWord_380005).sum := by decide
  have hdescent : baseEnd_380005 < baseStart_380005 := by decide
  rcases family_descends (prefixWord ++ tailWord_380005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_380062 : List Nat := [4, 3, 1, 1, 2, 1, 1, 3, 3, 1, 3]
def baseStart_380062 : Nat := 118140960795 + 380062 * 2 ^ 59
def prefixEnd_380062 : Nat := 4983230072969 + 3 ^ 40 * 380062 * 2
def baseEnd_380062 : Nat := 195154484509197239377133

theorem tailTrace_380062 : CollatzResearch.WordTrace tailWord_380062 prefixEnd_380062 195154484509197239377133 := by
  unfold tailWord_380062
  simp only [CollatzResearch.WordTrace]
  refine ⟨1732749993638469783375805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9241333299405172178004293 1732749993638469783375805)
  ·
    refine ⟨649781247614426168765927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1732749993638469783375805 649781247614426168765927)
    ·
      refine ⟨974671871421639253148891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 649781247614426168765927 974671871421639253148891)
      ·
        refine ⟨1462007807132458879723337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 974671871421639253148891 1462007807132458879723337)
        ·
          refine ⟨1096505855349344159792503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1462007807132458879723337 1096505855349344159792503)
          ·
            refine ⟨1644758783024016239688755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1096505855349344159792503 1644758783024016239688755)
            ·
              refine ⟨2467138174536024359533133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1644758783024016239688755 2467138174536024359533133)
              ·
                refine ⟨925176815451009134824925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2467138174536024359533133 925176815451009134824925)
                ·
                  refine ⟨346941305794128425559347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 925176815451009134824925 346941305794128425559347)
                  ·
                    refine ⟨520411958691192638339021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 346941305794128425559347 520411958691192638339021)
                    ·
                      refine ⟨195154484509197239377133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 520411958691192638339021 195154484509197239377133)
                      ·
                        rfl

theorem cell23_380062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 1, 3, 3, 1, 3].length) (baseStart_380062 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_380062 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_380062 prefixEnd_380062 := by exact prefixLift 380062
  have htrace : WordTrace (prefixWord ++ tailWord_380062) baseStart_380062 baseEnd_380062 := by
    simpa [prefixWord, tailWord_380062, baseEnd_380062] using wordTrace_append hprefix tailTrace_380062
  have hstable : (prefixWord ++ tailWord_380062).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_380062).length < 2 ^ (prefixWord ++ tailWord_380062).sum := by decide
  have hdescent : baseEnd_380062 < baseStart_380062 := by decide
  rcases family_descends (prefixWord ++ tailWord_380062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_380096 : List Nat := [2, 1, 1, 2, 7, 1, 1, 3, 1, 1, 3]
def baseStart_380096 : Nat := 118140960795 + 380096 * 2 ^ 59
def prefixEnd_380096 : Nat := 4983230072969 + 3 ^ 40 * 380096 * 2
def baseEnd_380096 : Nat := 195171942851450106351977

theorem tailTrace_380096 : CollatzResearch.WordTrace tailWord_380096 prefixEnd_380096 195171942851450106351977 := by
  unfold tailWord_380096
  simp only [CollatzResearch.WordTrace]
  refine ⟨6931620015492291036872071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9242160020656388049162761 6931620015492291036872071)
  ·
    refine ⟨10397430023238436555308107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6931620015492291036872071 10397430023238436555308107)
    ·
      refine ⟨15596145034857654832962161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10397430023238436555308107 15596145034857654832962161)
      ·
        refine ⟨11697108776143241124721621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15596145034857654832962161 11697108776143241124721621)
        ·
          refine ⟨274150986940857213860663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 11697108776143241124721621 274150986940857213860663)
          ·
            refine ⟨411226480411285820790995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 274150986940857213860663 411226480411285820790995)
            ·
              refine ⟨616839720616928731186493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 411226480411285820790995 616839720616928731186493)
              ·
                refine ⟨231314895231348274194935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 616839720616928731186493 231314895231348274194935)
                ·
                  refine ⟨346972342847022411292403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 231314895231348274194935 346972342847022411292403)
                  ·
                    refine ⟨520458514270533616938605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 346972342847022411292403 520458514270533616938605)
                    ·
                      refine ⟨195171942851450106351977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 520458514270533616938605 195171942851450106351977)
                      ·
                        rfl

theorem cell23_380096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 7, 1, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 7, 1, 1, 3, 1, 1, 3].length) (baseStart_380096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_380096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_380096 prefixEnd_380096 := by exact prefixLift 380096
  have htrace : WordTrace (prefixWord ++ tailWord_380096) baseStart_380096 baseEnd_380096 := by
    simpa [prefixWord, tailWord_380096, baseEnd_380096] using wordTrace_append hprefix tailTrace_380096
  have hstable : (prefixWord ++ tailWord_380096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_380096).length < 2 ^ (prefixWord ++ tailWord_380096).sum := by decide
  have hdescent : baseEnd_380096 < baseStart_380096 := by decide
  rcases family_descends (prefixWord ++ tailWord_380096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_380121 : List Nat := [1, 2, 1, 2, 3, 1, 1, 3, 2, 7]
def baseStart_380121 : Nat := 118140960795 + 380121 * 2 ^ 59
def prefixEnd_380121 : Nat := 4983230072969 + 3 ^ 40 * 380121 * 2
def baseEnd_380121 : Nat := 65061593289270836179787

theorem tailTrace_380121 : CollatzResearch.WordTrace tailWord_380121 prefixEnd_380121 65061593289270836179787 := by
  unfold tailWord_380121
  simp only [CollatzResearch.WordTrace]
  refine ⟨13864151855894011343404217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9242767903929340895602811 13864151855894011343404217)
  ·
    refine ⟨10398113891920508507553163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13864151855894011343404217 10398113891920508507553163)
    ·
      refine ⟨15597170837880762761329745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10398113891920508507553163 15597170837880762761329745)
      ·
        refine ⟨11697878128410572070997309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15597170837880762761329745 11697878128410572070997309)
        ·
          refine ⟨4386704298153964526623991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11697878128410572070997309 4386704298153964526623991)
          ·
            refine ⟨6580056447230946789935987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4386704298153964526623991 6580056447230946789935987)
            ·
              refine ⟨9870084670846420184903981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6580056447230946789935987 9870084670846420184903981)
              ·
                refine ⟨3701281751567407569338993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9870084670846420184903981 3701281751567407569338993)
                ·
                  refine ⟨2775961313675555677004245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3701281751567407569338993 2775961313675555677004245)
                  ·
                    refine ⟨65061593289270836179787, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 2775961313675555677004245 65061593289270836179787)
                    ·
                      rfl

theorem cell23_380121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 3, 2, 7].length) (baseStart_380121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_380121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_380121 prefixEnd_380121 := by exact prefixLift 380121
  have htrace : WordTrace (prefixWord ++ tailWord_380121) baseStart_380121 baseEnd_380121 := by
    simpa [prefixWord, tailWord_380121, baseEnd_380121] using wordTrace_append hprefix tailTrace_380121
  have hstable : (prefixWord ++ tailWord_380121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_380121).length < 2 ^ (prefixWord ++ tailWord_380121).sum := by decide
  have hdescent : baseEnd_380121 < baseStart_380121 := by decide
  rcases family_descends (prefixWord ++ tailWord_380121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_380125 : List Nat := [1, 4, 3, 2, 2, 1, 2, 8]
def baseStart_380125 : Nat := 118140960795 + 380125 * 2 ^ 59
def prefixEnd_380125 : Nat := 4983230072969 + 3 ^ 40 * 380125 * 2
def baseEnd_380125 : Nat := 7229141992238166403309

theorem tailTrace_380125 : CollatzResearch.WordTrace tailWord_380125 prefixEnd_380125 7229141992238166403309 := by
  unfold tailWord_380125
  simp only [CollatzResearch.WordTrace]
  refine ⟨13864297747879520026549829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9242865165253013351033219 13864297747879520026549829)
  ·
    refine ⟨2599555827727410004978093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13864297747879520026549829 2599555827727410004978093)
    ·
      refine ⟨974833435397778751866785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2599555827727410004978093 974833435397778751866785)
      ·
        refine ⟨731125076548334063900089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 974833435397778751866785 731125076548334063900089)
        ·
          refine ⟨548343807411250547925067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 731125076548334063900089 548343807411250547925067)
          ·
            refine ⟨822515711116875821887601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 548343807411250547925067 822515711116875821887601)
            ·
              refine ⟨616886783337656866415701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 822515711116875821887601 616886783337656866415701)
              ·
                refine ⟨7229141992238166403309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 616886783337656866415701 7229141992238166403309)
                ·
                  rfl

theorem cell23_380125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 1, 2, 8].length) (baseStart_380125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_380125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_380125 prefixEnd_380125 := by exact prefixLift 380125
  have htrace : WordTrace (prefixWord ++ tailWord_380125) baseStart_380125 baseEnd_380125 := by
    simpa [prefixWord, tailWord_380125, baseEnd_380125] using wordTrace_append hprefix tailTrace_380125
  have hstable : (prefixWord ++ tailWord_380125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_380125).length < 2 ^ (prefixWord ++ tailWord_380125).sum := by decide
  have hdescent : baseEnd_380125 < baseStart_380125 := by decide
  rcases family_descends (prefixWord ++ tailWord_380125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_380151 : List Nat := [1, 1, 3, 1, 1, 1, 2, 4, 1, 8]
def baseStart_380151 : Nat := 118140960795 + 380151 * 2 ^ 59
def prefixEnd_380151 : Nat := 4983230072969 + 3 ^ 40 * 380151 * 2
def baseEnd_380151 : Nat := 65066728095815797054741

theorem tailTrace_380151 : CollatzResearch.WordTrace tailWord_380151 prefixEnd_380151 65066728095815797054741 := by
  unfold tailWord_380151
  simp only [CollatzResearch.WordTrace]
  refine ⟨13865246045785326466996307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9243497363856884311330871 13865246045785326466996307)
  ·
    refine ⟨20797869068677989700494461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13865246045785326466996307 20797869068677989700494461)
    ·
      refine ⟨7799200900754246137685423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20797869068677989700494461 7799200900754246137685423)
      ·
        refine ⟨11698801351131369206528135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7799200900754246137685423 11698801351131369206528135)
        ·
          refine ⟨17548202026697053809792203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11698801351131369206528135 17548202026697053809792203)
          ·
            refine ⟨26322303040045580714688305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17548202026697053809792203 26322303040045580714688305)
            ·
              refine ⟨19741727280034185536016229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26322303040045580714688305 19741727280034185536016229)
              ·
                refine ⟨3701573865006409788003043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19741727280034185536016229 3701573865006409788003043)
                ·
                  refine ⟨5552360797509614682004565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3701573865006409788003043 5552360797509614682004565)
                  ·
                    refine ⟨65066728095815797054741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 5552360797509614682004565 65066728095815797054741)
                    ·
                      rfl

theorem cell23_380151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 4, 1, 8].length) (baseStart_380151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_380151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_380151 prefixEnd_380151 := by exact prefixLift 380151
  have htrace : WordTrace (prefixWord ++ tailWord_380151) baseStart_380151 baseEnd_380151 := by
    simpa [prefixWord, tailWord_380151, baseEnd_380151] using wordTrace_append hprefix tailTrace_380151
  have hstable : (prefixWord ++ tailWord_380151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_380151).length < 2 ^ (prefixWord ++ tailWord_380151).sum := by decide
  have hdescent : baseEnd_380151 < baseStart_380151 := by decide
  rcases family_descends (prefixWord ++ tailWord_380151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_380188 : List Nat := [2, 2, 3, 1, 1, 1, 3, 1, 1, 4, 4]
def baseStart_380188 : Nat := 118140960795 + 380188 * 2 ^ 59
def prefixEnd_380188 : Nat := 4983230072969 + 3 ^ 40 * 380188 * 2
def baseEnd_380188 : Nat := 195219183071663746401553

theorem tailTrace_380188 : CollatzResearch.WordTrace tailWord_380188 prefixEnd_380188 195219183071663746401553 := by
  unfold tailWord_380188
  simp only [CollatzResearch.WordTrace]
  refine ⟨6933297773325640893046609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9244397031100854524062145 6933297773325640893046609)
  ·
    refine ⟨5199973329994230669784957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6933297773325640893046609 5199973329994230669784957)
    ·
      refine ⟨1949989998747836501169359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5199973329994230669784957 1949989998747836501169359)
      ·
        refine ⟨2924984998121754751754039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1949989998747836501169359 2924984998121754751754039)
        ·
          refine ⟨4387477497182632127631059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2924984998121754751754039 4387477497182632127631059)
          ·
            refine ⟨6581216245773948191446589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4387477497182632127631059 6581216245773948191446589)
            ·
              refine ⟨2467956092165230571792471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6581216245773948191446589 2467956092165230571792471)
              ·
                refine ⟨3701934138247845857688707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2467956092165230571792471 3701934138247845857688707)
                ·
                  refine ⟨5552901207371768786533061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3701934138247845857688707 5552901207371768786533061)
                  ·
                    refine ⟨1041168976382206647474949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5552901207371768786533061 1041168976382206647474949)
                    ·
                      refine ⟨195219183071663746401553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1041168976382206647474949 195219183071663746401553)
                      ·
                        rfl

theorem cell23_380188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 3, 1, 1, 4, 4].length) (baseStart_380188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_380188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_380188 prefixEnd_380188 := by exact prefixLift 380188
  have htrace : WordTrace (prefixWord ++ tailWord_380188) baseStart_380188 baseEnd_380188 := by
    simpa [prefixWord, tailWord_380188, baseEnd_380188] using wordTrace_append hprefix tailTrace_380188
  have hstable : (prefixWord ++ tailWord_380188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_380188).length < 2 ^ (prefixWord ++ tailWord_380188).sum := by decide
  have hdescent : baseEnd_380188 < baseStart_380188 := by decide
  rcases family_descends (prefixWord ++ tailWord_380188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_380208 : List Nat := [2, 1, 1, 1, 2, 2, 3, 2, 1, 5, 3]
def baseStart_380208 : Nat := 118140960795 + 380208 * 2 ^ 59
def prefixEnd_380208 : Nat := 4983230072969 + 3 ^ 40 * 380208 * 2
def baseEnd_380208 : Nat := 195229452684753668151461

theorem tailTrace_380208 : CollatzResearch.WordTrace tailWord_380208 prefixEnd_380208 195229452684753668151461 := by
  unfold tailWord_380208
  simp only [CollatzResearch.WordTrace]
  refine ⟨6933662503289412600910639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9244883337719216801214185 6933662503289412600910639)
  ·
    refine ⟨10400493754934118901365959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6933662503289412600910639 10400493754934118901365959)
    ·
      refine ⟨15600740632401178352048939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10400493754934118901365959 15600740632401178352048939)
      ·
        refine ⟨23401110948601767528073409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15600740632401178352048939 23401110948601767528073409)
        ·
          refine ⟨17550833211451325646055057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23401110948601767528073409 17550833211451325646055057)
          ·
            refine ⟨13163124908588494234541293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17550833211451325646055057 13163124908588494234541293)
            ·
              refine ⟨4936171840720685337952985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13163124908588494234541293 4936171840720685337952985)
              ·
                refine ⟨3702128880540514003464739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4936171840720685337952985 3702128880540514003464739)
                ·
                  refine ⟨5553193320810771005197109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3702128880540514003464739 5553193320810771005197109)
                  ·
                    refine ⟨520611873826009781737229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5553193320810771005197109 520611873826009781737229)
                    ·
                      refine ⟨195229452684753668151461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 520611873826009781737229 195229452684753668151461)
                      ·
                        rfl

theorem cell23_380208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 3, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 3, 2, 1, 5, 3].length) (baseStart_380208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_380208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_380208 prefixEnd_380208 := by exact prefixLift 380208
  have htrace : WordTrace (prefixWord ++ tailWord_380208) baseStart_380208 baseEnd_380208 := by
    simpa [prefixWord, tailWord_380208, baseEnd_380208] using wordTrace_append hprefix tailTrace_380208
  have hstable : (prefixWord ++ tailWord_380208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_380208).length < 2 ^ (prefixWord ++ tailWord_380208).sum := by decide
  have hdescent : baseEnd_380208 < baseStart_380208 := by decide
  rcases family_descends (prefixWord ++ tailWord_380208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_380238 : List Nat := [4, 1, 1, 1, 1, 1, 4, 1, 1, 1, 7]
def baseStart_380238 : Nat := 118140960795 + 380238 * 2 ^ 59
def prefixEnd_380238 : Nat := 4983230072969 + 3 ^ 40 * 380238 * 2
def baseEnd_380238 : Nat := 195244857104388550776323

theorem tailTrace_380238 : CollatzResearch.WordTrace tailWord_380238 prefixEnd_380238 195244857104388550776323 := by
  unfold tailWord_380238
  simp only [CollatzResearch.WordTrace]
  refine ⟨1733552399558767540676671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9245612797646760216942245 1733552399558767540676671)
  ·
    refine ⟨2600328599338151311015007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1733552399558767540676671 2600328599338151311015007)
    ·
      refine ⟨3900492899007226966522511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2600328599338151311015007 3900492899007226966522511)
      ·
        refine ⟨5850739348510840449783767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3900492899007226966522511 5850739348510840449783767)
        ·
          refine ⟨8776109022766260674675651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5850739348510840449783767 8776109022766260674675651)
          ·
            refine ⟨13164163534149391012013477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8776109022766260674675651 13164163534149391012013477)
            ·
              refine ⟨2468280662653010814752527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13164163534149391012013477 2468280662653010814752527)
              ·
                refine ⟨3702420993979516222128791, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2468280662653010814752527 3702420993979516222128791)
                ·
                  refine ⟨5553631490969274333193187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3702420993979516222128791 5553631490969274333193187)
                  ·
                    refine ⟨8330447236453911499789781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5553631490969274333193187 8330447236453911499789781)
                    ·
                      refine ⟨195244857104388550776323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 8330447236453911499789781 195244857104388550776323)
                      ·
                        rfl

theorem cell23_380238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 4, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 4, 1, 1, 1, 7].length) (baseStart_380238 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_380238 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_380238 prefixEnd_380238 := by exact prefixLift 380238
  have htrace : WordTrace (prefixWord ++ tailWord_380238) baseStart_380238 baseEnd_380238 := by
    simpa [prefixWord, tailWord_380238, baseEnd_380238] using wordTrace_append hprefix tailTrace_380238
  have hstable : (prefixWord ++ tailWord_380238).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_380238).length < 2 ^ (prefixWord ++ tailWord_380238).sum := by decide
  have hdescent : baseEnd_380238 < baseStart_380238 := by decide
  rcases family_descends (prefixWord ++ tailWord_380238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_380248 : List Nat := [2, 1, 2, 2, 1, 1, 3, 1, 3, 3, 4]
def baseStart_380248 : Nat := 118140960795 + 380248 * 2 ^ 59
def prefixEnd_380248 : Nat := 4983230072969 + 3 ^ 40 * 380248 * 2
def baseEnd_380248 : Nat := 195249991910933511651277

theorem tailTrace_380248 : CollatzResearch.WordTrace tailWord_380248 prefixEnd_380248 195249991910933511651277 := by
  unfold tailWord_380248
  simp only [CollatzResearch.WordTrace]
  refine ⟨6934391963216956016638699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9245855950955941355518265 6934391963216956016638699)
  ·
    refine ⟨10401587944825434024958049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6934391963216956016638699 10401587944825434024958049)
    ·
      refine ⟨7801190958619075518718537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10401587944825434024958049 7801190958619075518718537)
      ·
        refine ⟨5850893218964306639038903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7801190958619075518718537 5850893218964306639038903)
        ·
          refine ⟨8776339828446459958558355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5850893218964306639038903 8776339828446459958558355)
          ·
            refine ⟨13164509742669689937837533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8776339828446459958558355 13164509742669689937837533)
            ·
              refine ⟨4936691153501133726689075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13164509742669689937837533 4936691153501133726689075)
              ·
                refine ⟨7405036730251700590033613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4936691153501133726689075 7405036730251700590033613)
                ·
                  refine ⟨2776888773844387721262605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7405036730251700590033613 2776888773844387721262605)
                  ·
                    refine ⟨1041333290191645395473477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2776888773844387721262605 1041333290191645395473477)
                    ·
                      refine ⟨195249991910933511651277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1041333290191645395473477 195249991910933511651277)
                      ·
                        rfl

theorem cell23_380248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 3, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 3, 1, 3, 3, 4].length) (baseStart_380248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_380248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_380248 prefixEnd_380248 := by exact prefixLift 380248
  have htrace : WordTrace (prefixWord ++ tailWord_380248) baseStart_380248 baseEnd_380248 := by
    simpa [prefixWord, tailWord_380248, baseEnd_380248] using wordTrace_append hprefix tailTrace_380248
  have hstable : (prefixWord ++ tailWord_380248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_380248).length < 2 ^ (prefixWord ++ tailWord_380248).sum := by decide
  have hdescent : baseEnd_380248 < baseStart_380248 := by decide
  rcases family_descends (prefixWord ++ tailWord_380248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_380265 : List Nat := [1, 2, 1, 1, 1, 3, 2, 2, 4, 4, 2]
def baseStart_380265 : Nat := 118140960795 + 380265 * 2 ^ 59
def prefixEnd_380265 : Nat := 4983230072969 + 3 ^ 40 * 380265 * 2
def baseEnd_380265 : Nat := 195258721082059945138699

theorem tailTrace_380265 : CollatzResearch.WordTrace tailWord_380265 prefixEnd_380265 195258721082059945138699 := by
  unfold tailWord_380265
  simp only [CollatzResearch.WordTrace]
  refine ⟨13869403967372323936646249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9246269311581549291097499 13869403967372323936646249)
  ·
    refine ⟨10402052975529242952484687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13869403967372323936646249 10402052975529242952484687)
    ·
      refine ⟨15603079463293864428727031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10402052975529242952484687 15603079463293864428727031)
      ·
        refine ⟨23404619194940796643090547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15603079463293864428727031 23404619194940796643090547)
        ·
          refine ⟨35106928792411194964635821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23404619194940796643090547 35106928792411194964635821)
          ·
            refine ⟨13165098297154198111738433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35106928792411194964635821 13165098297154198111738433)
            ·
              refine ⟨9873823722865648583803825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13165098297154198111738433 9873823722865648583803825)
              ·
                refine ⟨7405367792149236437852869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9873823722865648583803825 7405367792149236437852869)
                ·
                  refine ⟨1388506461027981832097413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7405367792149236437852869 1388506461027981832097413)
                  ·
                    refine ⟨260344961442746593518265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1388506461027981832097413 260344961442746593518265)
                    ·
                      refine ⟨195258721082059945138699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 260344961442746593518265 195258721082059945138699)
                      ·
                        rfl

theorem cell23_380265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 2, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 2, 4, 4, 2].length) (baseStart_380265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_380265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_380265 prefixEnd_380265 := by exact prefixLift 380265
  have htrace : WordTrace (prefixWord ++ tailWord_380265) baseStart_380265 baseEnd_380265 := by
    simpa [prefixWord, tailWord_380265, baseEnd_380265] using wordTrace_append hprefix tailTrace_380265
  have hstable : (prefixWord ++ tailWord_380265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_380265).length < 2 ^ (prefixWord ++ tailWord_380265).sum := by decide
  have hdescent : baseEnd_380265 < baseStart_380265 := by decide
  rcases family_descends (prefixWord ++ tailWord_380265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_380266 : List Nat := [3, 1, 3, 3, 3, 1, 1, 3, 5]
def baseStart_380266 : Nat := 118140960795 + 380266 * 2 ^ 59
def prefixEnd_380266 : Nat := 4983230072969 + 3 ^ 40 * 380266 * 2
def baseEnd_380266 : Nat := 21695470506968271247355

theorem tailTrace_380266 : CollatzResearch.WordTrace tailWord_380266 prefixEnd_380266 21695470506968271247355 := by
  unfold tailWord_380266
  simp only [CollatzResearch.WordTrace]
  refine ⟨3467360110092175276858163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9246293626912467404955101 3467360110092175276858163)
  ·
    refine ⟨5201040165138262915287245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3467360110092175276858163 5201040165138262915287245)
    ·
      refine ⟨1950390061926848593232717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5201040165138262915287245 1950390061926848593232717)
      ·
        refine ⟨731396273222568222462269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1950390061926848593232717 731396273222568222462269)
        ·
          refine ⟨274273602458463083423351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 731396273222568222462269 274273602458463083423351)
          ·
            refine ⟨411410403687694625135027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 274273602458463083423351 411410403687694625135027)
            ·
              refine ⟨617115605531541937702541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 411410403687694625135027 617115605531541937702541)
              ·
                refine ⟨231418352074328226638453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 617115605531541937702541 231418352074328226638453)
                ·
                  refine ⟨21695470506968271247355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 231418352074328226638453 21695470506968271247355)
                  ·
                    rfl

theorem cell23_380266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 3, 1, 1, 3, 5].length) (baseStart_380266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_380266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_380266 prefixEnd_380266 := by exact prefixLift 380266
  have htrace : WordTrace (prefixWord ++ tailWord_380266) baseStart_380266 baseEnd_380266 := by
    simpa [prefixWord, tailWord_380266, baseEnd_380266] using wordTrace_append hprefix tailTrace_380266
  have hstable : (prefixWord ++ tailWord_380266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_380266).length < 2 ^ (prefixWord ++ tailWord_380266).sum := by decide
  have hdescent : baseEnd_380266 < baseStart_380266 := by decide
  rcases family_descends (prefixWord ++ tailWord_380266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_380292 : List Nat := [2, 3, 2, 1, 1, 3, 3, 1, 3, 4]
def baseStart_380292 : Nat := 118140960795 + 380292 * 2 ^ 59
def prefixEnd_380292 : Nat := 4983230072969 + 3 ^ 40 * 380292 * 2
def baseEnd_380292 : Nat := 65090861686577113167025

theorem tailTrace_380292 : CollatzResearch.WordTrace tailWord_380292 prefixEnd_380292 65090861686577113167025 := by
  unfold tailWord_380292
  simp only [CollatzResearch.WordTrace]
  refine ⟨6935194369137253773939565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9246925825516338365252753 6935194369137253773939565)
  ·
    refine ⟨2600697888426470165227337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6935194369137253773939565 2600697888426470165227337)
    ·
      refine ⟨1950523416319852623920503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2600697888426470165227337 1950523416319852623920503)
      ·
        refine ⟨2925785124479778935880755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1950523416319852623920503 2925785124479778935880755)
        ·
          refine ⟨4388677686719668403821133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2925785124479778935880755 4388677686719668403821133)
          ·
            refine ⟨1645754132519875651432925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4388677686719668403821133 1645754132519875651432925)
            ·
              refine ⟨617157799694953369287347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1645754132519875651432925 617157799694953369287347)
              ·
                refine ⟨925736699542430053931021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 617157799694953369287347 925736699542430053931021)
                ·
                  refine ⟨347151262328411270224133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 925736699542430053931021 347151262328411270224133)
                  ·
                    refine ⟨65090861686577113167025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 347151262328411270224133 65090861686577113167025)
                    ·
                      rfl

theorem cell23_380292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 3, 1, 3, 4].length) (baseStart_380292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_380292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_380292 prefixEnd_380292 := by exact prefixLift 380292
  have htrace : WordTrace (prefixWord ++ tailWord_380292) baseStart_380292 baseEnd_380292 := by
    simpa [prefixWord, tailWord_380292, baseEnd_380292] using wordTrace_append hprefix tailTrace_380292
  have hstable : (prefixWord ++ tailWord_380292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_380292).length < 2 ^ (prefixWord ++ tailWord_380292).sum := by decide
  have hdescent : baseEnd_380292 < baseStart_380292 := by decide
  rcases family_descends (prefixWord ++ tailWord_380292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_380335 : List Nat := [1, 1, 2, 1, 2, 2, 1, 7, 1, 5]
def baseStart_380335 : Nat := 118140960795 + 380335 * 2 ^ 59
def prefixEnd_380335 : Nat := 4983230072969 + 3 ^ 40 * 380335 * 2
def baseEnd_380335 : Nat := 65098221575958223754459

theorem tailTrace_380335 : CollatzResearch.WordTrace tailWord_380335 prefixEnd_380335 65098221575958223754459 := by
  unfold tailWord_380335
  simp only [CollatzResearch.WordTrace]
  refine ⟨13871957077118725891694459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9247971384745817261129639 13871957077118725891694459)
  ·
    refine ⟨20807935615678088837541689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13871957077118725891694459 20807935615678088837541689)
    ·
      refine ⟨15605951711758566628156267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20807935615678088837541689 15605951711758566628156267)
      ·
        refine ⟨23408927567637849942234401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15605951711758566628156267 23408927567637849942234401)
        ·
          refine ⟨17556695675728387456675801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23408927567637849942234401 17556695675728387456675801)
          ·
            refine ⟨13167521756796290592506851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17556695675728387456675801 13167521756796290592506851)
            ·
              refine ⟨19751282635194435888760277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13167521756796290592506851 19751282635194435888760277)
              ·
                refine ⟨462920686762369591142819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 19751282635194435888760277 462920686762369591142819)
                ·
                  refine ⟨694381030143554386714229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 462920686762369591142819 694381030143554386714229)
                  ·
                    refine ⟨65098221575958223754459, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 694381030143554386714229 65098221575958223754459)
                    ·
                      rfl

theorem cell23_380335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 7, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 7, 1, 5].length) (baseStart_380335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_380335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_380335 prefixEnd_380335 := by exact prefixLift 380335
  have htrace : WordTrace (prefixWord ++ tailWord_380335) baseStart_380335 baseEnd_380335 := by
    simpa [prefixWord, tailWord_380335, baseEnd_380335] using wordTrace_append hprefix tailTrace_380335
  have hstable : (prefixWord ++ tailWord_380335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_380335).length < 2 ^ (prefixWord ++ tailWord_380335).sum := by decide
  have hdescent : baseEnd_380335 < baseStart_380335 := by decide
  rcases family_descends (prefixWord ++ tailWord_380335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_380355 : List Nat := [1, 1, 1, 3, 1, 1, 5, 2, 3, 1, 4]
def baseStart_380355 : Nat := 118140960795 + 380355 * 2 ^ 59
def prefixEnd_380355 : Nat := 4983230072969 + 3 ^ 40 * 380355 * 2
def baseEnd_380355 : Nat := 195304934340964593013285

theorem tailTrace_380355 : CollatzResearch.WordTrace tailWord_380355 prefixEnd_380355 195304934340964593013285 := by
  unfold tailWord_380355
  simp only [CollatzResearch.WordTrace]
  refine ⟨13872686537046269307422519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9248457691364179538281679 13872686537046269307422519)
  ·
    refine ⟨20809029805569403961133779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13872686537046269307422519 20809029805569403961133779)
    ·
      refine ⟨31213544708354105941700669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20809029805569403961133779 31213544708354105941700669)
      ·
        refine ⟨11705079265632789728137751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31213544708354105941700669 11705079265632789728137751)
        ·
          refine ⟨17557618898449184592206627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11705079265632789728137751 17557618898449184592206627)
          ·
            refine ⟨26336428347673776888309941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17557618898449184592206627 26336428347673776888309941)
            ·
              refine ⟨2469040157594416583279057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 26336428347673776888309941 2469040157594416583279057)
              ·
                refine ⟨1851780118195812437459293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2469040157594416583279057 1851780118195812437459293)
                ·
                  refine ⟨694417544323429664047235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1851780118195812437459293 694417544323429664047235)
                  ·
                    refine ⟨1041626316485144496070853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 694417544323429664047235 1041626316485144496070853)
                    ·
                      refine ⟨195304934340964593013285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1041626316485144496070853 195304934340964593013285)
                      ·
                        rfl

theorem cell23_380355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 5, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 5, 2, 3, 1, 4].length) (baseStart_380355 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_380355 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_380355 prefixEnd_380355 := by exact prefixLift 380355
  have htrace : WordTrace (prefixWord ++ tailWord_380355) baseStart_380355 baseEnd_380355 := by
    simpa [prefixWord, tailWord_380355, baseEnd_380355] using wordTrace_append hprefix tailTrace_380355
  have hstable : (prefixWord ++ tailWord_380355).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_380355).length < 2 ^ (prefixWord ++ tailWord_380355).sum := by decide
  have hdescent : baseEnd_380355 < baseStart_380355 := by decide
  rcases family_descends (prefixWord ++ tailWord_380355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_380389 : List Nat := [1, 3, 1, 5, 1, 2, 1, 3, 1, 1, 4]
def baseStart_380389 : Nat := 118140960795 + 380389 * 2 ^ 59
def prefixEnd_380389 : Nat := 4983230072969 + 3 ^ 40 * 380389 * 2
def baseEnd_380389 : Nat := 195322392683217459988129

theorem tailTrace_380389 : CollatzResearch.WordTrace tailWord_380389 prefixEnd_380389 195322392683217459988129 := by
  unfold tailWord_380389
  simp only [CollatzResearch.WordTrace]
  refine ⟨13873926618923093114160221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9249284412615395409440147 13873926618923093114160221)
  ·
    refine ⟨5202722482096159917810083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13873926618923093114160221 5202722482096159917810083)
    ·
      refine ⟨7804083723144239876715125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5202722482096159917810083 7804083723144239876715125)
      ·
        refine ⟨731632849044772488442043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 7804083723144239876715125 731632849044772488442043)
        ·
          refine ⟨1097449273567158732663065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 731632849044772488442043 1097449273567158732663065)
          ·
            refine ⟨823086955175369049497299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1097449273567158732663065 823086955175369049497299)
            ·
              refine ⟨1234630432763053574245949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 823086955175369049497299 1234630432763053574245949)
              ·
                refine ⟨462986412286145090342231, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1234630432763053574245949 462986412286145090342231)
                ·
                  refine ⟨694479618429217635513347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 462986412286145090342231 694479618429217635513347)
                  ·
                    refine ⟨1041719427643826453270021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 694479618429217635513347 1041719427643826453270021)
                    ·
                      refine ⟨195322392683217459988129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1041719427643826453270021 195322392683217459988129)
                      ·
                        rfl

theorem cell23_380389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 2, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 2, 1, 3, 1, 1, 4].length) (baseStart_380389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_380389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_380389 prefixEnd_380389 := by exact prefixLift 380389
  have htrace : WordTrace (prefixWord ++ tailWord_380389) baseStart_380389 baseEnd_380389 := by
    simpa [prefixWord, tailWord_380389, baseEnd_380389] using wordTrace_append hprefix tailTrace_380389
  have hstable : (prefixWord ++ tailWord_380389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_380389).length < 2 ^ (prefixWord ++ tailWord_380389).sum := by decide
  have hdescent : baseEnd_380389 < baseStart_380389 := by decide
  rcases family_descends (prefixWord ++ tailWord_380389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_380406 : List Nat := [5, 1, 1, 1, 2, 2, 1, 3, 3, 2, 2]
def baseStart_380406 : Nat := 118140960795 + 380406 * 2 ^ 59
def prefixEnd_380406 : Nat := 4983230072969 + 3 ^ 40 * 380406 * 2
def baseEnd_380406 : Nat := 195331121854343893475551

theorem tailTrace_380406 : CollatzResearch.WordTrace tailWord_380406 prefixEnd_380406 195331121854343893475551 := by
  unfold tailWord_380406
  simp only [CollatzResearch.WordTrace]
  refine ⟨867159166241344063595567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 9249697773241003345019381 867159166241344063595567)
  ·
    refine ⟨1300738749362016095393351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 867159166241344063595567 1300738749362016095393351)
    ·
      refine ⟨1951108124043024143090027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1300738749362016095393351 1951108124043024143090027)
      ·
        refine ⟨2926662186064536214635041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1951108124043024143090027 2926662186064536214635041)
        ·
          refine ⟨2194996639548402160976281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2926662186064536214635041 2194996639548402160976281)
          ·
            refine ⟨1646247479661301620732211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2194996639548402160976281 1646247479661301620732211)
            ·
              refine ⟨2469371219491952431098317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1646247479661301620732211 2469371219491952431098317)
              ·
                refine ⟨926014207309482161661869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2469371219491952431098317 926014207309482161661869)
                ·
                  refine ⟨347255327741055810623201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 926014207309482161661869 347255327741055810623201)
                  ·
                    refine ⟨260441495805791857967401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 347255327741055810623201 260441495805791857967401)
                    ·
                      refine ⟨195331121854343893475551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 260441495805791857967401 195331121854343893475551)
                      ·
                        rfl

theorem cell23_380406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 1, 3, 3, 2, 2].length) (baseStart_380406 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_380406 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_380406 prefixEnd_380406 := by exact prefixLift 380406
  have htrace : WordTrace (prefixWord ++ tailWord_380406) baseStart_380406 baseEnd_380406 := by
    simpa [prefixWord, tailWord_380406, baseEnd_380406] using wordTrace_append hprefix tailTrace_380406
  have hstable : (prefixWord ++ tailWord_380406).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_380406).length < 2 ^ (prefixWord ++ tailWord_380406).sum := by decide
  have hdescent : baseEnd_380406 < baseStart_380406 := by decide
  rcases family_descends (prefixWord ++ tailWord_380406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_380435 : List Nat := [1, 1, 1, 2, 1, 6, 1, 1, 2, 2, 5]
def baseStart_380435 : Nat := 118140960795 + 380435 * 2 ^ 59
def prefixEnd_380435 : Nat := 4983230072969 + 3 ^ 40 * 380435 * 2
def baseEnd_380435 : Nat := 195346012793324280012917

theorem tailTrace_380435 : CollatzResearch.WordTrace tailWord_380435 prefixEnd_380435 195346012793324280012917 := by
  unfold tailWord_380435
  simp only [CollatzResearch.WordTrace]
  refine ⟨13875604376756442970334759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9250402917837628646889839 13875604376756442970334759)
  ·
    refine ⟨20813406565134664455502139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13875604376756442970334759 20813406565134664455502139)
    ·
      refine ⟨31220109847701996683253209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20813406565134664455502139 31220109847701996683253209)
      ·
        refine ⟨23415082385776497512439907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31220109847701996683253209 23415082385776497512439907)
        ·
          refine ⟨35122623578664746268659861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23415082385776497512439907 35122623578664746268659861)
          ·
            refine ⟨1646372980249909981343431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 35122623578664746268659861 1646372980249909981343431)
            ·
              refine ⟨2469559470374864972015147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1646372980249909981343431 2469559470374864972015147)
              ·
                refine ⟨3704339205562297458022721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2469559470374864972015147 3704339205562297458022721)
                ·
                  refine ⟨2778254404171723093517041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3704339205562297458022721 2778254404171723093517041)
                  ·
                    refine ⟨2083690803128792320137781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2778254404171723093517041 2083690803128792320137781)
                    ·
                      refine ⟨195346012793324280012917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2083690803128792320137781 195346012793324280012917)
                      ·
                        rfl

theorem cell23_380435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 1, 1, 2, 2, 5].length) (baseStart_380435 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_380435 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_380435 prefixEnd_380435 := by exact prefixLift 380435
  have htrace : WordTrace (prefixWord ++ tailWord_380435) baseStart_380435 baseEnd_380435 := by
    simpa [prefixWord, tailWord_380435, baseEnd_380435] using wordTrace_append hprefix tailTrace_380435
  have hstable : (prefixWord ++ tailWord_380435).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_380435).length < 2 ^ (prefixWord ++ tailWord_380435).sum := by decide
  have hdescent : baseEnd_380435 < baseStart_380435 := by decide
  rcases family_descends (prefixWord ++ tailWord_380435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_380440 : List Nat := [2, 1, 2, 3, 4, 2, 1, 3, 1, 2, 2]
def baseStart_380440 : Nat := 118140960795 + 380440 * 2 ^ 59
def prefixEnd_380440 : Nat := 4983230072969 + 3 ^ 40 * 380440 * 2
def baseEnd_380440 : Nat := 195348580196596760450395

theorem tailTrace_380440 : CollatzResearch.WordTrace tailWord_380440 prefixEnd_380440 195348580196596760450395 := by
  unfold tailWord_380440
  simp only [CollatzResearch.WordTrace]
  refine ⟨6937893370869164412133387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9250524494492219216177849 6937893370869164412133387)
  ·
    refine ⟨10406840056303746618200081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6937893370869164412133387 10406840056303746618200081)
    ·
      refine ⟨7805130042227809963650061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10406840056303746618200081 7805130042227809963650061)
      ·
        refine ⟨2926923765835428736368773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7805130042227809963650061 2926923765835428736368773)
        ·
          refine ⟨548798206094142888069145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2926923765835428736368773 548798206094142888069145)
          ·
            refine ⟨411598654570607166051859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 548798206094142888069145 411598654570607166051859)
            ·
              refine ⟨617397981855910749077789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 411598654570607166051859 617397981855910749077789)
              ·
                refine ⟨231524243195966530904171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 617397981855910749077789 231524243195966530904171)
                ·
                  refine ⟨347286364793949796356257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 231524243195966530904171 347286364793949796356257)
                  ·
                    refine ⟨260464773595462347267193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 347286364793949796356257 260464773595462347267193)
                    ·
                      refine ⟨195348580196596760450395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 260464773595462347267193 195348580196596760450395)
                      ·
                        rfl

theorem cell23_380440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 2, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 2, 1, 3, 1, 2, 2].length) (baseStart_380440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_380440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_380440 prefixEnd_380440 := by exact prefixLift 380440
  have htrace : WordTrace (prefixWord ++ tailWord_380440) baseStart_380440 baseEnd_380440 := by
    simpa [prefixWord, tailWord_380440, baseEnd_380440] using wordTrace_append hprefix tailTrace_380440
  have hstable : (prefixWord ++ tailWord_380440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_380440).length < 2 ^ (prefixWord ++ tailWord_380440).sum := by decide
  have hdescent : baseEnd_380440 < baseStart_380440 := by decide
  rcases family_descends (prefixWord ++ tailWord_380440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_380465 : List Nat := [1, 2, 2, 3, 1, 1, 1, 1, 3, 3, 5]
def baseStart_380465 : Nat := 118140960795 + 380465 * 2 ^ 59
def prefixEnd_380465 : Nat := 4983230072969 + 3 ^ 40 * 380465 * 2
def baseEnd_380465 : Nat := 195361417212959162637779

theorem tailTrace_380465 : CollatzResearch.WordTrace tailWord_380465 prefixEnd_380465 195361417212959162637779 := by
  unfold tailWord_380465
  simp only [CollatzResearch.WordTrace]
  refine ⟨13876698566647758093926849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9251132377765172062617899 13876698566647758093926849)
  ·
    refine ⟨10407523924985818570445137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13876698566647758093926849 10407523924985818570445137)
    ·
      refine ⟨7805642943739363927833853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10407523924985818570445137 7805642943739363927833853)
      ·
        refine ⟨2927116103902261472937695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7805642943739363927833853 2927116103902261472937695)
        ·
          refine ⟨4390674155853392209406543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2927116103902261472937695 4390674155853392209406543)
          ·
            refine ⟨6586011233780088314109815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4390674155853392209406543 6586011233780088314109815)
            ·
              refine ⟨9879016850670132471164723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6586011233780088314109815 9879016850670132471164723)
              ·
                refine ⟨14818525276005198706747085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9879016850670132471164723 14818525276005198706747085)
                ·
                  refine ⟨5556946978501949515030157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14818525276005198706747085 5556946978501949515030157)
                  ·
                    refine ⟨2083855116938231068136309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5556946978501949515030157 2083855116938231068136309)
                    ·
                      refine ⟨195361417212959162637779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2083855116938231068136309 195361417212959162637779)
                      ·
                        rfl

theorem cell23_380465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 1, 3, 3, 5].length) (baseStart_380465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_380465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_380465 prefixEnd_380465 := by exact prefixLift 380465
  have htrace : WordTrace (prefixWord ++ tailWord_380465) baseStart_380465 baseEnd_380465 := by
    simpa [prefixWord, tailWord_380465, baseEnd_380465] using wordTrace_append hprefix tailTrace_380465
  have hstable : (prefixWord ++ tailWord_380465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_380465).length < 2 ^ (prefixWord ++ tailWord_380465).sum := by decide
  have hdescent : baseEnd_380465 < baseStart_380465 := by decide
  rcases family_descends (prefixWord ++ tailWord_380465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_380473 : List Nat := [1, 2, 1, 5, 1, 4, 2, 1, 2, 1, 3]
def baseStart_380473 : Nat := 118140960795 + 380473 * 2 ^ 59
def prefixEnd_380473 : Nat := 4983230072969 + 3 ^ 40 * 380473 * 2
def baseEnd_380473 : Nat := 195365525058195131337743

theorem tailTrace_380473 : CollatzResearch.WordTrace tailWord_380473 prefixEnd_380473 195365525058195131337743 := by
  unfold tailWord_380473
  simp only [CollatzResearch.WordTrace]
  refine ⟨13876990350618775460218073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9251326900412516973478715 13876990350618775460218073)
  ·
    refine ⟨10407742762964081595163555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13876990350618775460218073 10407742762964081595163555)
    ·
      refine ⟨15611614144446122392745333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10407742762964081595163555 15611614144446122392745333)
      ·
        refine ⟨1463588826041823974319875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 15611614144446122392745333 1463588826041823974319875)
        ·
          refine ⟨2195383239062735961479813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1463588826041823974319875 2195383239062735961479813)
          ·
            refine ⟨411634357324262992777465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2195383239062735961479813 411634357324262992777465)
            ·
              refine ⟨308725767993197244583099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 411634357324262992777465 308725767993197244583099)
              ·
                refine ⟨463088651989795866874649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 308725767993197244583099 463088651989795866874649)
                ·
                  refine ⟨347316488992346900155987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 463088651989795866874649 347316488992346900155987)
                  ·
                    refine ⟨520974733488520350233981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 347316488992346900155987 520974733488520350233981)
                    ·
                      refine ⟨195365525058195131337743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 520974733488520350233981 195365525058195131337743)
                      ·
                        rfl

theorem cell23_380473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 4, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 4, 2, 1, 2, 1, 3].length) (baseStart_380473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_380473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_380473 prefixEnd_380473 := by exact prefixLift 380473
  have htrace : WordTrace (prefixWord ++ tailWord_380473) baseStart_380473 baseEnd_380473 := by
    simpa [prefixWord, tailWord_380473, baseEnd_380473] using wordTrace_append hprefix tailTrace_380473
  have hstable : (prefixWord ++ tailWord_380473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_380473).length < 2 ^ (prefixWord ++ tailWord_380473).sum := by decide
  have hdescent : baseEnd_380473 < baseStart_380473 := by decide
  rcases family_descends (prefixWord ++ tailWord_380473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_380485 : List Nat := [1, 3, 1, 1, 1, 4, 2, 1, 9]
def baseStart_380485 : Nat := 118140960795 + 380485 * 2 ^ 59
def prefixEnd_380485 : Nat := 4983230072969 + 3 ^ 40 * 380485 * 2
def baseEnd_380485 : Nat := 21707965202894342709743

theorem tailTrace_380485 : CollatzResearch.WordTrace tailWord_380485 prefixEnd_380485 21707965202894342709743 := by
  unfold tailWord_380485
  simp only [CollatzResearch.WordTrace]
  refine ⟨13877428026575301509654909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9251618684383534339769939 13877428026575301509654909)
  ·
    refine ⟨5204035509965738066120591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13877428026575301509654909 5204035509965738066120591)
    ·
      refine ⟨7806053264948607099180887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5204035509965738066120591 7806053264948607099180887)
      ·
        refine ⟨11709079897422910648771331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7806053264948607099180887 11709079897422910648771331)
        ·
          refine ⟨17563619846134365973156997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11709079897422910648771331 17563619846134365973156997)
          ·
            refine ⟨3293178721150193619966937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17563619846134365973156997 3293178721150193619966937)
            ·
              refine ⟨2469884040862645214975203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3293178721150193619966937 2469884040862645214975203)
              ·
                refine ⟨3704826061293967822462805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2469884040862645214975203 3704826061293967822462805)
                ·
                  refine ⟨21707965202894342709743, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 3704826061293967822462805 21707965202894342709743)
                  ·
                    rfl

theorem cell23_380485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 2, 1, 9].length) (baseStart_380485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_380485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_380485 prefixEnd_380485 := by exact prefixLift 380485
  have htrace : WordTrace (prefixWord ++ tailWord_380485) baseStart_380485 baseEnd_380485 := by
    simpa [prefixWord, tailWord_380485, baseEnd_380485] using wordTrace_append hprefix tailTrace_380485
  have hstable : (prefixWord ++ tailWord_380485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_380485).length < 2 ^ (prefixWord ++ tailWord_380485).sum := by decide
  have hdescent : baseEnd_380485 < baseStart_380485 := by decide
  rcases family_descends (prefixWord ++ tailWord_380485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_380512 : List Nat := [2, 1, 1, 3, 2, 1, 1, 4, 2, 3, 3]
def baseStart_380512 : Nat := 118140960795 + 380512 * 2 ^ 59
def prefixEnd_380512 : Nat := 4983230072969 + 3 ^ 40 * 380512 * 2
def baseEnd_380512 : Nat := 195385550803720478750063

theorem tailTrace_380512 : CollatzResearch.WordTrace tailWord_380512 prefixEnd_380512 195385550803720478750063 := by
  unfold tailWord_380512
  simp only [CollatzResearch.WordTrace]
  refine ⟨6939206398738742560443895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9252275198318323413925193 6939206398738742560443895)
  ·
    refine ⟨10408809598108113840665843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6939206398738742560443895 10408809598108113840665843)
    ·
      refine ⟨15613214397162170760998765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10408809598108113840665843 15613214397162170760998765)
      ·
        refine ⟨5854955398935814035374537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15613214397162170760998765 5854955398935814035374537)
        ·
          refine ⟨4391216549201860526530903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5854955398935814035374537 4391216549201860526530903)
          ·
            refine ⟨6586824823802790789796355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4391216549201860526530903 6586824823802790789796355)
            ·
              refine ⟨9880237235704186184694533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6586824823802790789796355 9880237235704186184694533)
              ·
                refine ⟨1852544481694534909630225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9880237235704186184694533 1852544481694534909630225)
                ·
                  refine ⟨1389408361270901182222669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1852544481694534909630225 1389408361270901182222669)
                  ·
                    refine ⟨521028135476587943333501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1389408361270901182222669 521028135476587943333501)
                    ·
                      refine ⟨195385550803720478750063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 521028135476587943333501 195385550803720478750063)
                      ·
                        rfl

theorem cell23_380512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 4, 2, 3, 3].length) (baseStart_380512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_380512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_380512 prefixEnd_380512 := by exact prefixLift 380512
  have htrace : WordTrace (prefixWord ++ tailWord_380512) baseStart_380512 baseEnd_380512 := by
    simpa [prefixWord, tailWord_380512, baseEnd_380512] using wordTrace_append hprefix tailTrace_380512
  have hstable : (prefixWord ++ tailWord_380512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_380512).length < 2 ^ (prefixWord ++ tailWord_380512).sum := by decide
  have hdescent : baseEnd_380512 < baseStart_380512 := by decide
  rcases family_descends (prefixWord ++ tailWord_380512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_380579 : List Nat := [1, 1, 1, 4, 1, 1, 6, 1, 3, 4]
def baseStart_380579 : Nat := 118140960795 + 380579 * 2 ^ 59
def prefixEnd_380579 : Nat := 4983230072969 + 3 ^ 40 * 380579 * 2
def baseEnd_380579 : Nat := 65139984669190572204085

theorem tailTrace_380579 : CollatzResearch.WordTrace tailWord_380579 prefixEnd_380579 65139984669190572204085 := by
  unfold tailWord_380579
  simp only [CollatzResearch.WordTrace]
  refine ⟨13880856488234755563576791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9253904325489837042384527 13880856488234755563576791)
  ·
    refine ⟨20821284732352133345365187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13880856488234755563576791 20821284732352133345365187)
    ·
      refine ⟨31231927098528200018047781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20821284732352133345365187 31231927098528200018047781)
      ·
        refine ⟨5855986330974037503383959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 31231927098528200018047781 5855986330974037503383959)
        ·
          refine ⟨8783979496461056255075939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5855986330974037503383959 8783979496461056255075939)
          ·
            refine ⟨13175969244691584382613909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8783979496461056255075939 13175969244691584382613909)
            ·
              refine ⟨617623558344918017935027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 13175969244691584382613909 617623558344918017935027)
              ·
                refine ⟨926435337517377026902541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 617623558344918017935027 926435337517377026902541)
                ·
                  refine ⟨347413251569016385088453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 926435337517377026902541 347413251569016385088453)
                  ·
                    refine ⟨65139984669190572204085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 347413251569016385088453 65139984669190572204085)
                    ·
                      rfl

theorem cell23_380579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 6, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 6, 1, 3, 4].length) (baseStart_380579 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_380579 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_380579 prefixEnd_380579 := by exact prefixLift 380579
  have htrace : WordTrace (prefixWord ++ tailWord_380579) baseStart_380579 baseEnd_380579 := by
    simpa [prefixWord, tailWord_380579, baseEnd_380579] using wordTrace_append hprefix tailTrace_380579
  have hstable : (prefixWord ++ tailWord_380579).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_380579).length < 2 ^ (prefixWord ++ tailWord_380579).sum := by decide
  have hdescent : baseEnd_380579 < baseStart_380579 := by decide
  rcases family_descends (prefixWord ++ tailWord_380579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_380589 : List Nat := [1, 5, 2, 1, 1, 1, 1, 1, 3, 4, 3]
def baseStart_380589 : Nat := 118140960795 + 380589 * 2 ^ 59
def prefixEnd_380589 : Nat := 4983230072969 + 3 ^ 40 * 380589 * 2
def baseEnd_380589 : Nat := 195425088814116677487209

theorem tailTrace_380589 : CollatzResearch.WordTrace tailWord_380589 prefixEnd_380589 195425088814116677487209 := by
  unfold tailWord_380589
  simp only [CollatzResearch.WordTrace]
  refine ⟨13881221218198527271440821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9254147478799018180960547 13881221218198527271440821)
  ·
    refine ⟨1301364489206111931697577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 13881221218198527271440821 1301364489206111931697577)
    ·
      refine ⟨976023366904583948773183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1301364489206111931697577 976023366904583948773183)
      ·
        refine ⟨1464035050356875923159775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 976023366904583948773183 1464035050356875923159775)
        ·
          refine ⟨2196052575535313884739663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1464035050356875923159775 2196052575535313884739663)
          ·
            refine ⟨3294078863302970827109495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2196052575535313884739663 3294078863302970827109495)
            ·
              refine ⟨4941118294954456240664243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3294078863302970827109495 4941118294954456240664243)
              ·
                refine ⟨7411677442431684360996365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4941118294954456240664243 7411677442431684360996365)
                ·
                  refine ⟨2779379040911881635373637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7411677442431684360996365 2779379040911881635373637)
                  ·
                    refine ⟨521133570170977806632557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2779379040911881635373637 521133570170977806632557)
                    ·
                      refine ⟨195425088814116677487209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 521133570170977806632557 195425088814116677487209)
                      ·
                        rfl

theorem cell23_380589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 1, 1, 3, 4, 3].length) (baseStart_380589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_380589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_380589 prefixEnd_380589 := by exact prefixLift 380589
  have htrace : WordTrace (prefixWord ++ tailWord_380589) baseStart_380589 baseEnd_380589 := by
    simpa [prefixWord, tailWord_380589, baseEnd_380589] using wordTrace_append hprefix tailTrace_380589
  have hstable : (prefixWord ++ tailWord_380589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_380589).length < 2 ^ (prefixWord ++ tailWord_380589).sum := by decide
  have hdescent : baseEnd_380589 < baseStart_380589 := by decide
  rcases family_descends (prefixWord ++ tailWord_380589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_380592 : List Nat := [2, 1, 1, 1, 2, 1, 4, 5, 6]
def baseStart_380592 : Nat := 118140960795 + 380592 * 2 ^ 59
def prefixEnd_380592 : Nat := 4983230072969 + 3 ^ 40 * 380592 * 2
def baseEnd_380592 : Nat := 21714069917342240638855

theorem tailTrace_380592 : CollatzResearch.WordTrace tailWord_380592 prefixEnd_380592 21714069917342240638855 := by
  unfold tailWord_380592
  simp only [CollatzResearch.WordTrace]
  refine ⟨6940665318593829391900015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9254220424791772522533353 6940665318593829391900015)
  ·
    refine ⟨10410997977890744087850023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6940665318593829391900015 10410997977890744087850023)
    ·
      refine ⟨15616496966836116131775035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10410997977890744087850023 15616496966836116131775035)
      ·
        refine ⟨23424745450254174197662553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15616496966836116131775035 23424745450254174197662553)
        ·
          refine ⟨17568559087690630648246915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23424745450254174197662553 17568559087690630648246915)
          ·
            refine ⟨26352838631535945972370373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17568559087690630648246915 26352838631535945972370373)
            ·
              refine ⟨4941157243412989869819445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26352838631535945972370373 4941157243412989869819445)
              ·
                refine ⟨463233491569967800295573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4941157243412989869819445 463233491569967800295573)
                ·
                  refine ⟨21714069917342240638855, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 463233491569967800295573 21714069917342240638855)
                  ·
                    rfl

theorem cell23_380592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 4, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 4, 5, 6].length) (baseStart_380592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_380592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_380592 prefixEnd_380592 := by exact prefixLift 380592
  have htrace : WordTrace (prefixWord ++ tailWord_380592) baseStart_380592 baseEnd_380592 := by
    simpa [prefixWord, tailWord_380592, baseEnd_380592] using wordTrace_append hprefix tailTrace_380592
  have hstable : (prefixWord ++ tailWord_380592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_380592).length < 2 ^ (prefixWord ++ tailWord_380592).sum := by decide
  have hdescent : baseEnd_380592 < baseStart_380592 := by decide
  rcases family_descends (prefixWord ++ tailWord_380592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_380619 : List Nat := [1, 1, 1, 1, 3, 2, 1, 4, 5, 1, 3]
def baseStart_380619 : Nat := 118140960795 + 380619 * 2 ^ 59
def prefixEnd_380619 : Nat := 4983230072969 + 3 ^ 40 * 380619 * 2
def baseEnd_380619 : Nat := 195440493233751560112071

theorem tailTrace_380619 : CollatzResearch.WordTrace tailWord_380619 prefixEnd_380619 195440493233751560112071 := by
  unfold tailWord_380619
  simp only [CollatzResearch.WordTrace]
  refine ⟨13882315408089842395032911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9254876938726561596688607 13882315408089842395032911)
  ·
    refine ⟨20823473112134763592549367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13882315408089842395032911 20823473112134763592549367)
    ·
      refine ⟨31235209668202145388824051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20823473112134763592549367 31235209668202145388824051)
      ·
        refine ⟨46852814502303218083236077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31235209668202145388824051 46852814502303218083236077)
        ·
          refine ⟨17569805438363706781213529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46852814502303218083236077 17569805438363706781213529)
          ·
            refine ⟨13177354078772780085910147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17569805438363706781213529 13177354078772780085910147)
            ·
              refine ⟨19766031118159170128865221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13177354078772780085910147 19766031118159170128865221)
              ·
                refine ⟨3706130834654844399162229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19766031118159170128865221 3706130834654844399162229)
                ·
                  refine ⟨347449765748891662421459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3706130834654844399162229 347449765748891662421459)
                  ·
                    refine ⟨521174648623337493632189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 347449765748891662421459 521174648623337493632189)
                    ·
                      refine ⟨195440493233751560112071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 521174648623337493632189 195440493233751560112071)
                      ·
                        rfl

theorem cell23_380619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 4, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 4, 5, 1, 3].length) (baseStart_380619 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_380619 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_380619 prefixEnd_380619 := by exact prefixLift 380619
  have htrace : WordTrace (prefixWord ++ tailWord_380619) baseStart_380619 baseEnd_380619 := by
    simpa [prefixWord, tailWord_380619, baseEnd_380619] using wordTrace_append hprefix tailTrace_380619
  have hstable : (prefixWord ++ tailWord_380619).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_380619).length < 2 ^ (prefixWord ++ tailWord_380619).sum := by decide
  have hdescent : baseEnd_380619 < baseStart_380619 := by decide
  rcases family_descends (prefixWord ++ tailWord_380619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_380643 : List Nat := [1, 1, 1, 7, 2, 2, 2, 1, 6]
def baseStart_380643 : Nat := 118140960795 + 380643 * 2 ^ 59
def prefixEnd_380643 : Nat := 4983230072969 + 3 ^ 40 * 380643 * 2
def baseEnd_380643 : Nat := 21716979641051051801329

theorem tailTrace_380643 : CollatzResearch.WordTrace tailWord_380643 prefixEnd_380643 21716979641051051801329 := by
  unfold tailWord_380643
  simp only [CollatzResearch.WordTrace]
  refine ⟨13883190760002894493906583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9255460506668596329271055 13883190760002894493906583)
  ·
    refine ⟨20824786140004341740859875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13883190760002894493906583 20824786140004341740859875)
    ·
      refine ⟨31237179210006512611289813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20824786140004341740859875 31237179210006512611289813)
      ·
        refine ⟨732121387734527639327105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 31237179210006512611289813 732121387734527639327105)
        ·
          refine ⟨549091040800895729495329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 732121387734527639327105 549091040800895729495329)
          ·
            refine ⟨411818280600671797121497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 549091040800895729495329 411818280600671797121497)
            ·
              refine ⟨308863710450503847841123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 411818280600671797121497 308863710450503847841123)
              ·
                refine ⟨463295565675755771761685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 308863710450503847841123 463295565675755771761685)
                ·
                  refine ⟨21716979641051051801329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 463295565675755771761685 21716979641051051801329)
                  ·
                    rfl

theorem cell23_380643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 2, 2, 1, 6].length) (baseStart_380643 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_380643 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_380643 prefixEnd_380643 := by exact prefixLift 380643
  have htrace : WordTrace (prefixWord ++ tailWord_380643) baseStart_380643 baseEnd_380643 := by
    simpa [prefixWord, tailWord_380643, baseEnd_380643] using wordTrace_append hprefix tailTrace_380643
  have hstable : (prefixWord ++ tailWord_380643).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_380643).length < 2 ^ (prefixWord ++ tailWord_380643).sum := by decide
  have hdescent : baseEnd_380643 < baseStart_380643 := by decide
  rcases family_descends (prefixWord ++ tailWord_380643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_380659 : List Nat := [1, 1, 1, 2, 2, 3, 2, 1, 2, 6, 2]
def baseStart_380659 : Nat := 118140960795 + 380659 * 2 ^ 59
def prefixEnd_380659 : Nat := 4983230072969 + 3 ^ 40 * 380659 * 2
def baseEnd_380659 : Nat := 195461032459931403611887

theorem tailTrace_380659 : CollatzResearch.WordTrace tailWord_380659 prefixEnd_380659 195461032459931403611887 := by
  unfold tailWord_380659
  simp only [CollatzResearch.WordTrace]
  refine ⟨13883774327944929226489031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9255849551963286150992687 13883774327944929226489031)
  ·
    refine ⟨20825661491917393839733547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13883774327944929226489031 20825661491917393839733547)
    ·
      refine ⟨31238492237876090759600321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20825661491917393839733547 31238492237876090759600321)
      ·
        refine ⟨23428869178407068069700241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31238492237876090759600321 23428869178407068069700241)
        ·
          refine ⟨17571651883805301052275181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23428869178407068069700241 17571651883805301052275181)
          ·
            refine ⟨6589369456426987894603193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17571651883805301052275181 6589369456426987894603193)
            ·
              refine ⟨4942027092320240920952395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6589369456426987894603193 4942027092320240920952395)
              ·
                refine ⟨7413040638480361381428593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4942027092320240920952395 7413040638480361381428593)
                ·
                  refine ⟨5559780478860271036071445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7413040638480361381428593 5559780478860271036071445)
                  ·
                    refine ⟨260614709946575204815849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5559780478860271036071445 260614709946575204815849)
                    ·
                      refine ⟨195461032459931403611887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 260614709946575204815849 195461032459931403611887)
                      ·
                        rfl

theorem cell23_380659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 2, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 2, 1, 2, 6, 2].length) (baseStart_380659 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_380659 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_380659 prefixEnd_380659 := by exact prefixLift 380659
  have htrace : WordTrace (prefixWord ++ tailWord_380659) baseStart_380659 baseEnd_380659 := by
    simpa [prefixWord, tailWord_380659, baseEnd_380659] using wordTrace_append hprefix tailTrace_380659
  have hstable : (prefixWord ++ tailWord_380659).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_380659).length < 2 ^ (prefixWord ++ tailWord_380659).sum := by decide
  have hdescent : baseEnd_380659 < baseStart_380659 := by decide
  rcases family_descends (prefixWord ++ tailWord_380659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_380669 : List Nat := [1, 4, 1, 1, 1, 1, 2, 4, 4, 4]
def baseStart_380669 : Nat := 118140960795 + 380669 * 2 ^ 59
def prefixEnd_380669 : Nat := 4983230072969 + 3 ^ 40 * 380669 * 2
def baseEnd_380669 : Nat := 65155389088825454828947

theorem tailTrace_380669 : CollatzResearch.WordTrace tailWord_380669 prefixEnd_380669 65155389088825454828947 := by
  unfold tailWord_380669
  simp only [CollatzResearch.WordTrace]
  refine ⟨13884139057908700934353061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9256092705272467289568707 13884139057908700934353061)
  ·
    refine ⟨2603276073357881425191199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13884139057908700934353061 2603276073357881425191199)
    ·
      refine ⟨3904914110036822137786799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2603276073357881425191199 3904914110036822137786799)
      ·
        refine ⟨5857371165055233206680199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3904914110036822137786799 5857371165055233206680199)
        ·
          refine ⟨8786056747582849810020299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5857371165055233206680199 8786056747582849810020299)
          ·
            refine ⟨13179085121374274715030449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8786056747582849810020299 13179085121374274715030449)
            ·
              refine ⟨9884313841030706036272837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13179085121374274715030449 9884313841030706036272837)
              ·
                refine ⟨1853308845193257381801157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9884313841030706036272837 1853308845193257381801157)
                ·
                  refine ⟨347495408473735759087717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1853308845193257381801157 347495408473735759087717)
                  ·
                    refine ⟨65155389088825454828947, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 347495408473735759087717 65155389088825454828947)
                    ·
                      rfl

theorem cell23_380669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 4, 4, 4].length) (baseStart_380669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_380669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_380669 prefixEnd_380669 := by exact prefixLift 380669
  have htrace : WordTrace (prefixWord ++ tailWord_380669) baseStart_380669 baseEnd_380669 := by
    simpa [prefixWord, tailWord_380669, baseEnd_380669] using wordTrace_append hprefix tailTrace_380669
  have hstable : (prefixWord ++ tailWord_380669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_380669).length < 2 ^ (prefixWord ++ tailWord_380669).sum := by decide
  have hdescent : baseEnd_380669 < baseStart_380669 := by decide
  rcases family_descends (prefixWord ++ tailWord_380669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_380682 : List Nat := [3, 1, 2, 2, 1, 14]
def baseStart_380682 : Nat := 118140960795 + 380682 * 2 ^ 59
def prefixEnd_380682 : Nat := 4983230072969 + 3 ^ 40 * 380682 * 2
def baseEnd_380682 : Nat := 804414989773600056067

theorem tailTrace_380682 : CollatzResearch.WordTrace tailWord_380682 prefixEnd_380682 804414989773600056067 := by
  unfold tailWord_380682
  simp only [CollatzResearch.WordTrace]
  refine ⟨3471153301715401038644075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9256408804574402769717533 3471153301715401038644075)
  ·
    refine ⟨5206729952573101557966113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3471153301715401038644075 5206729952573101557966113)
    ·
      refine ⟨3905047464429826168474585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5206729952573101557966113 3905047464429826168474585)
      ·
        refine ⟨2928785598322369626355939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3905047464429826168474585 2928785598322369626355939)
        ·
          refine ⟨4393178397483554439533909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2928785598322369626355939 4393178397483554439533909)
          ·
            refine ⟨804414989773600056067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 14 4393178397483554439533909 804414989773600056067)
            ·
              rfl

theorem cell23_380682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 14].length) (baseStart_380682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_380682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_380682 prefixEnd_380682 := by exact prefixLift 380682
  have htrace : WordTrace (prefixWord ++ tailWord_380682) baseStart_380682 baseEnd_380682 := by
    simpa [prefixWord, tailWord_380682, baseEnd_380682] using wordTrace_append hprefix tailTrace_380682
  have hstable : (prefixWord ++ tailWord_380682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_380682).length < 2 ^ (prefixWord ++ tailWord_380682).sum := by decide
  have hdescent : baseEnd_380682 < baseStart_380682 := by decide
  rcases family_descends (prefixWord ++ tailWord_380682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_380686 : List Nat := [4, 1, 1, 2, 1, 1, 3, 4, 2, 4]
def baseStart_380686 : Nat := 118140960795 + 380686 * 2 ^ 59
def prefixEnd_380686 : Nat := 4983230072969 + 3 ^ 40 * 380686 * 2
def baseEnd_380686 : Nat := 65158298812534265991421

theorem tailTrace_380686 : CollatzResearch.WordTrace tailWord_380686 prefixEnd_380686 65158298812534265991421 := by
  unfold tailWord_380686
  simp only [CollatzResearch.WordTrace]
  refine ⟨1735594887355889104715239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9256506065898075225147941 1735594887355889104715239)
  ·
    refine ⟨2603392331033833657072859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1735594887355889104715239 2603392331033833657072859)
    ·
      refine ⟨3905088496550750485609289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2603392331033833657072859 3905088496550750485609289)
      ·
        refine ⟨2928816372413062864206967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3905088496550750485609289 2928816372413062864206967)
        ·
          refine ⟨4393224558619594296310451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2928816372413062864206967 4393224558619594296310451)
          ·
            refine ⟨6589836837929391444465677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4393224558619594296310451 6589836837929391444465677)
            ·
              refine ⟨2471188814223521791674629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6589836837929391444465677 2471188814223521791674629)
              ·
                refine ⟨463347902666910335938993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2471188814223521791674629 463347902666910335938993)
                ·
                  refine ⟨347510927000182751954245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 463347902666910335938993 347510927000182751954245)
                  ·
                    refine ⟨65158298812534265991421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 347510927000182751954245 65158298812534265991421)
                    ·
                      rfl

theorem cell23_380686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 3, 4, 2, 4].length) (baseStart_380686 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_380686 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_380686 prefixEnd_380686 := by exact prefixLift 380686
  have htrace : WordTrace (prefixWord ++ tailWord_380686) baseStart_380686 baseEnd_380686 := by
    simpa [prefixWord, tailWord_380686, baseEnd_380686] using wordTrace_append hprefix tailTrace_380686
  have hstable : (prefixWord ++ tailWord_380686).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_380686).length < 2 ^ (prefixWord ++ tailWord_380686).sum := by decide
  have hdescent : baseEnd_380686 < baseStart_380686 := by decide
  rcases family_descends (prefixWord ++ tailWord_380686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_380706 : List Nat := [3, 3, 1, 1, 2, 1, 4, 1, 1, 2, 4]
def baseStart_380706 : Nat := 118140960795 + 380706 * 2 ^ 59
def prefixEnd_380706 : Nat := 4983230072969 + 3 ^ 40 * 380706 * 2
def baseEnd_380706 : Nat := 195485166050692719724171

theorem tailTrace_380706 : CollatzResearch.WordTrace tailWord_380706 prefixEnd_380706 195485166050692719724171 := by
  unfold tailWord_380706
  simp only [CollatzResearch.WordTrace]
  refine ⟨3471372139693664063362493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9256992372516437502299981 3471372139693664063362493)
  ·
    refine ⟨1301764552385124023760935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3471372139693664063362493 1301764552385124023760935)
    ·
      refine ⟨1952646828577686035641403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1301764552385124023760935 1952646828577686035641403)
      ·
        refine ⟨2928970242866529053462105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1952646828577686035641403 2928970242866529053462105)
        ·
          refine ⟨2196727682149896790096579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2928970242866529053462105 2196727682149896790096579)
          ·
            refine ⟨3295091523224845185144869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2196727682149896790096579 3295091523224845185144869)
            ·
              refine ⟨617829660604658472214663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3295091523224845185144869 617829660604658472214663)
              ·
                refine ⟨926744490906987708321995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 617829660604658472214663 926744490906987708321995)
                ·
                  refine ⟨1390116736360481562482993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 926744490906987708321995 1390116736360481562482993)
                  ·
                    refine ⟨1042587552270361171862245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1390116736360481562482993 1042587552270361171862245)
                    ·
                      refine ⟨195485166050692719724171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1042587552270361171862245 195485166050692719724171)
                      ·
                        rfl

theorem cell23_380706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 4, 1, 1, 2, 4].length) (baseStart_380706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_380706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_380706 prefixEnd_380706 := by exact prefixLift 380706
  have htrace : WordTrace (prefixWord ++ tailWord_380706) baseStart_380706 baseEnd_380706 := by
    simpa [prefixWord, tailWord_380706, baseEnd_380706] using wordTrace_append hprefix tailTrace_380706
  have hstable : (prefixWord ++ tailWord_380706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_380706).length < 2 ^ (prefixWord ++ tailWord_380706).sum := by decide
  have hdescent : baseEnd_380706 < baseStart_380706 := by decide
  rcases family_descends (prefixWord ++ tailWord_380706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_380730 : List Nat := [3, 1, 1, 1, 5, 3, 2, 1, 1, 2, 3]
def baseStart_380730 : Nat := 118140960795 + 380730 * 2 ^ 59
def prefixEnd_380730 : Nat := 4983230072969 + 3 ^ 40 * 380730 * 2
def baseEnd_380730 : Nat := 195497489586400625824061

theorem tailTrace_380730 : CollatzResearch.WordTrace tailWord_380730 prefixEnd_380730 195497489586400625824061 := by
  unfold tailWord_380730
  simp only [CollatzResearch.WordTrace]
  refine ⟨3471590977671927088080911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9257575940458472234882429 3471590977671927088080911)
  ·
    refine ⟨5207386466507890632121367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3471590977671927088080911 5207386466507890632121367)
    ·
      refine ⟨7811079699761835948182051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5207386466507890632121367 7811079699761835948182051)
      ·
        refine ⟨11716619549642753922273077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7811079699761835948182051 11716619549642753922273077)
        ·
          refine ⟨1098433082779008180213101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 11716619549642753922273077 1098433082779008180213101)
          ·
            refine ⟨411912406042128067579913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1098433082779008180213101 411912406042128067579913)
            ·
              refine ⟨308934304531596050684935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 411912406042128067579913 308934304531596050684935)
              ·
                refine ⟨463401456797394076027403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 308934304531596050684935 463401456797394076027403)
                ·
                  refine ⟨695102185196091114041105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 463401456797394076027403 695102185196091114041105)
                  ·
                    refine ⟨521326638897068335530829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 695102185196091114041105 521326638897068335530829)
                    ·
                      refine ⟨195497489586400625824061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 521326638897068335530829 195497489586400625824061)
                      ·
                        rfl

theorem cell23_380730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 3, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 3, 2, 1, 1, 2, 3].length) (baseStart_380730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_380730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_380730 prefixEnd_380730 := by exact prefixLift 380730
  have htrace : WordTrace (prefixWord ++ tailWord_380730) baseStart_380730 baseEnd_380730 := by
    simpa [prefixWord, tailWord_380730, baseEnd_380730] using wordTrace_append hprefix tailTrace_380730
  have hstable : (prefixWord ++ tailWord_380730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_380730).length < 2 ^ (prefixWord ++ tailWord_380730).sum := by decide
  have hdescent : baseEnd_380730 < baseStart_380730 := by decide
  rcases family_descends (prefixWord ++ tailWord_380730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_380743 : List Nat := [1, 1, 4, 1, 2, 1, 5, 2, 2, 1, 3]
def baseStart_380743 : Nat := 118140960795 + 380743 * 2 ^ 59
def prefixEnd_380743 : Nat := 4983230072969 + 3 ^ 40 * 380743 * 2
def baseEnd_380743 : Nat := 195504164834909074961501

theorem tailTrace_380743 : CollatzResearch.WordTrace tailWord_380743 prefixEnd_380743 195504164834909074961501 := by
  unfold tailWord_380743
  simp only [CollatzResearch.WordTrace]
  refine ⟨13886838059640611572546883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9257892039760407715031255 13886838059640611572546883)
  ·
    refine ⟨20830257089460917358820325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13886838059640611572546883 20830257089460917358820325)
    ·
      refine ⟨3905673204273922004778811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20830257089460917358820325 3905673204273922004778811)
      ·
        refine ⟨5858509806410883007168217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3905673204273922004778811 5858509806410883007168217)
        ·
          refine ⟨4393882354808162255376163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5858509806410883007168217 4393882354808162255376163)
          ·
            refine ⟨6590823532212243383064245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4393882354808162255376163 6590823532212243383064245)
            ·
              refine ⟨617889706144897817162273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 6590823532212243383064245 617889706144897817162273)
              ·
                refine ⟨463417279608673362871705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 617889706144897817162273 463417279608673362871705)
                ·
                  refine ⟨347562959706505022153779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 463417279608673362871705 347562959706505022153779)
                  ·
                    refine ⟨521344439559757533230669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 347562959706505022153779 521344439559757533230669)
                    ·
                      refine ⟨195504164834909074961501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 521344439559757533230669 195504164834909074961501)
                      ·
                        rfl

theorem cell23_380743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 5, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 5, 2, 2, 1, 3].length) (baseStart_380743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_380743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_380743 prefixEnd_380743 := by exact prefixLift 380743
  have htrace : WordTrace (prefixWord ++ tailWord_380743) baseStart_380743 baseEnd_380743 := by
    simpa [prefixWord, tailWord_380743, baseEnd_380743] using wordTrace_append hprefix tailTrace_380743
  have hstable : (prefixWord ++ tailWord_380743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_380743).length < 2 ^ (prefixWord ++ tailWord_380743).sum := by decide
  have hdescent : baseEnd_380743 < baseStart_380743 := by decide
  rcases family_descends (prefixWord ++ tailWord_380743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_380769 : List Nat := [1, 2, 3, 1, 1, 1, 4, 2, 2, 1, 5]
def baseStart_380769 : Nat := 118140960795 + 380769 * 2 ^ 59
def prefixEnd_380769 : Nat := 4983230072969 + 3 ^ 40 * 380769 * 2
def baseEnd_380769 : Nat := 195517515331925973236381

theorem tailTrace_380769 : CollatzResearch.WordTrace tailWord_380769 prefixEnd_380769 195517515331925973236381 := by
  unfold tailWord_380769
  simp only [CollatzResearch.WordTrace]
  refine ⟨13887786357546418012993361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9258524238364278675328907 13887786357546418012993361)
  ·
    refine ⟨10415839768159813509745021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13887786357546418012993361 10415839768159813509745021)
    ·
      refine ⟨3905939913059930066154383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10415839768159813509745021 3905939913059930066154383)
      ·
        refine ⟨5858909869589895099231575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3905939913059930066154383 5858909869589895099231575)
        ·
          refine ⟨8788364804384842648847363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5858909869589895099231575 8788364804384842648847363)
          ·
            refine ⟨13182547206577263973271045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8788364804384842648847363 13182547206577263973271045)
            ·
              refine ⟨2471727601233236994988321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13182547206577263973271045 2471727601233236994988321)
              ·
                refine ⟨1853795700924927746241241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2471727601233236994988321 1853795700924927746241241)
                ·
                  refine ⟨1390346775693695809680931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1853795700924927746241241 1390346775693695809680931)
                  ·
                    refine ⟨2085520163540543714521397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1390346775693695809680931 2085520163540543714521397)
                    ·
                      refine ⟨195517515331925973236381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2085520163540543714521397 195517515331925973236381)
                      ·
                        rfl

theorem cell23_380769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 4, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 4, 2, 2, 1, 5].length) (baseStart_380769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_380769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_380769 prefixEnd_380769 := by exact prefixLift 380769
  have htrace : WordTrace (prefixWord ++ tailWord_380769) baseStart_380769 baseEnd_380769 := by
    simpa [prefixWord, tailWord_380769, baseEnd_380769] using wordTrace_append hprefix tailTrace_380769
  have hstable : (prefixWord ++ tailWord_380769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_380769).length < 2 ^ (prefixWord ++ tailWord_380769).sum := by decide
  have hdescent : baseEnd_380769 < baseStart_380769 := by decide
  rcases family_descends (prefixWord ++ tailWord_380769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_380770 : List Nat := [3, 3, 2, 1, 2, 1, 1, 4, 1, 3, 2]
def baseStart_380770 : Nat := 118140960795 + 380770 * 2 ^ 59
def prefixEnd_380770 : Nat := 4983230072969 + 3 ^ 40 * 380770 * 2
def baseEnd_380770 : Nat := 195518028812580469323877

theorem tailTrace_380770 : CollatzResearch.WordTrace tailWord_380770 prefixEnd_380770 195518028812580469323877 := by
  unfold tailWord_380770
  simp only [CollatzResearch.WordTrace]
  refine ⟨3471955707635698795944941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9258548553695196789186509 3471955707635698795944941)
  ·
    refine ⟨1301983390363387048479353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3471955707635698795944941 1301983390363387048479353)
    ·
      refine ⟨976487542772540286359515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1301983390363387048479353 976487542772540286359515)
      ·
        refine ⟨1464731314158810429539273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 976487542772540286359515 1464731314158810429539273)
        ·
          refine ⟨1098548485619107822154455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1464731314158810429539273 1098548485619107822154455)
          ·
            refine ⟨1647822728428661733231683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1098548485619107822154455 1647822728428661733231683)
            ·
              refine ⟨2471734092642992599847525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1647822728428661733231683 2471734092642992599847525)
              ·
                refine ⟨463450142370561112471411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2471734092642992599847525 463450142370561112471411)
                ·
                  refine ⟨695175213555841668707117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 463450142370561112471411 695175213555841668707117)
                  ·
                    refine ⟨260690705083440625765169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 695175213555841668707117 260690705083440625765169)
                    ·
                      refine ⟨195518028812580469323877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 260690705083440625765169 195518028812580469323877)
                      ·
                        rfl

theorem cell23_380770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 1, 4, 1, 3, 2].length) (baseStart_380770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_380770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_380770 prefixEnd_380770 := by exact prefixLift 380770
  have htrace : WordTrace (prefixWord ++ tailWord_380770) baseStart_380770 baseEnd_380770 := by
    simpa [prefixWord, tailWord_380770, baseEnd_380770] using wordTrace_append hprefix tailTrace_380770
  have hstable : (prefixWord ++ tailWord_380770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_380770).length < 2 ^ (prefixWord ++ tailWord_380770).sum := by decide
  have hdescent : baseEnd_380770 < baseStart_380770 := by decide
  rcases family_descends (prefixWord ++ tailWord_380770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_380836 : List Nat := [2, 3, 1, 2, 1, 3, 1, 3, 2, 5]
def baseStart_380836 : Nat := 118140960795 + 380836 * 2 ^ 59
def prefixEnd_380836 : Nat := 4983230072969 + 3 ^ 40 * 380836 * 2
def baseEnd_380836 : Nat := 65183972845259070366191

theorem tailTrace_380836 : CollatzResearch.WordTrace tailWord_380836 prefixEnd_380836 65183972845259070366191 := by
  unfold tailWord_380836
  simp only [CollatzResearch.WordTrace]
  refine ⟨6945115024151844227841181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9260153365535792303788241 6945115024151844227841181)
  ·
    refine ⟨2604418134056941585440443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6945115024151844227841181 2604418134056941585440443)
    ·
      refine ⟨3906627201085412378160665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2604418134056941585440443 3906627201085412378160665)
      ·
        refine ⟨2929970400814059283620499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3906627201085412378160665 2929970400814059283620499)
        ·
          refine ⟨4394955601221088925430749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2929970400814059283620499 4394955601221088925430749)
          ·
            refine ⟨1648108350457908347036531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4394955601221088925430749 1648108350457908347036531)
            ·
              refine ⟨2472162525686862520554797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1648108350457908347036531 2472162525686862520554797)
              ·
                refine ⟨927060947132573445208049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2472162525686862520554797 927060947132573445208049)
                ·
                  refine ⟨695295710349430083906037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 927060947132573445208049 695295710349430083906037)
                  ·
                    refine ⟨65183972845259070366191, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 695295710349430083906037 65183972845259070366191)
                    ·
                      rfl

theorem cell23_380836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 1, 3, 2, 5].length) (baseStart_380836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_380836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_380836 prefixEnd_380836 := by exact prefixLift 380836
  have htrace : WordTrace (prefixWord ++ tailWord_380836) baseStart_380836 baseEnd_380836 := by
    simpa [prefixWord, tailWord_380836, baseEnd_380836] using wordTrace_append hprefix tailTrace_380836
  have hstable : (prefixWord ++ tailWord_380836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_380836).length < 2 ^ (prefixWord ++ tailWord_380836).sum := by decide
  have hdescent : baseEnd_380836 < baseStart_380836 := by decide
  rcases family_descends (prefixWord ++ tailWord_380836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_380856 : List Nat := [2, 1, 2, 1, 2, 3, 1, 4, 2, 1, 4]
def baseStart_380856 : Nat := 118140960795 + 380856 * 2 ^ 59
def prefixEnd_380856 : Nat := 4983230072969 + 3 ^ 40 * 380856 * 2
def baseEnd_380856 : Nat := 195562188148867132848481

theorem tailTrace_380856 : CollatzResearch.WordTrace tailWord_380856 prefixEnd_380856 195562188148867132848481 := by
  unfold tailWord_380856
  simp only [CollatzResearch.WordTrace]
  refine ⟨6945479754115615935705211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9260639672154154580940281 6945479754115615935705211)
  ·
    refine ⟨10418219631173423903557817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6945479754115615935705211 10418219631173423903557817)
    ·
      refine ⟨7813664723380067927668363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10418219631173423903557817 7813664723380067927668363)
      ·
        refine ⟨11720497085070101891502545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7813664723380067927668363 11720497085070101891502545)
        ·
          refine ⟨8790372813802576418626909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11720497085070101891502545 8790372813802576418626909)
          ·
            refine ⟨3296389805175966156985091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8790372813802576418626909 3296389805175966156985091)
            ·
              refine ⟨4944584707763949235477637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3296389805175966156985091 4944584707763949235477637)
              ·
                refine ⟨927109632705740481652057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4944584707763949235477637 927109632705740481652057)
                ·
                  refine ⟨695332224529305361239043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 927109632705740481652057 695332224529305361239043)
                  ·
                    refine ⟨1042998336793958041858565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 695332224529305361239043 1042998336793958041858565)
                    ·
                      refine ⟨195562188148867132848481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1042998336793958041858565 195562188148867132848481)
                      ·
                        rfl

theorem cell23_380856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 1, 4, 2, 1, 4].length) (baseStart_380856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_380856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_380856 prefixEnd_380856 := by exact prefixLift 380856
  have htrace : WordTrace (prefixWord ++ tailWord_380856) baseStart_380856 baseEnd_380856 := by
    simpa [prefixWord, tailWord_380856, baseEnd_380856] using wordTrace_append hprefix tailTrace_380856
  have hstable : (prefixWord ++ tailWord_380856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_380856).length < 2 ^ (prefixWord ++ tailWord_380856).sum := by decide
  have hdescent : baseEnd_380856 < baseStart_380856 := by decide
  rcases family_descends (prefixWord ++ tailWord_380856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_380869 : List Nat := [1, 3, 1, 1, 1, 1, 1, 3, 4, 1, 6]
def baseStart_380869 : Nat := 118140960795 + 380869 * 2 ^ 59
def prefixEnd_380869 : Nat := 4983230072969 + 3 ^ 40 * 380869 * 2
def baseEnd_380869 : Nat := 195568863397375581985921

theorem tailTrace_380869 : CollatzResearch.WordTrace tailWord_380869 prefixEnd_380869 195568863397375581985921 := by
  unfold tailWord_380869
  simp only [CollatzResearch.WordTrace]
  refine ⟨13891433657184135091633661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9260955771456090061089107 13891433657184135091633661)
  ·
    refine ⟨5209287621444050659362623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13891433657184135091633661 5209287621444050659362623)
    ·
      refine ⟨7813931432166075989043935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5209287621444050659362623 7813931432166075989043935)
      ·
        refine ⟨11720897148249113983565903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7813931432166075989043935 11720897148249113983565903)
        ·
          refine ⟨17581345722373670975348855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11720897148249113983565903 17581345722373670975348855)
          ·
            refine ⟨26372018583560506463023283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17581345722373670975348855 26372018583560506463023283)
            ·
              refine ⟨39558027875340759694534925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26372018583560506463023283 39558027875340759694534925)
              ·
                refine ⟨14834260453252784885450597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39558027875340759694534925 14834260453252784885450597)
                ·
                  refine ⟨2781423834984897166021987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14834260453252784885450597 2781423834984897166021987)
                  ·
                    refine ⟨4172135752477345749032981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2781423834984897166021987 4172135752477345749032981)
                    ·
                      refine ⟨195568863397375581985921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 4172135752477345749032981 195568863397375581985921)
                      ·
                        rfl

theorem cell23_380869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 3, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 3, 4, 1, 6].length) (baseStart_380869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_380869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_380869 prefixEnd_380869 := by exact prefixLift 380869
  have htrace : WordTrace (prefixWord ++ tailWord_380869) baseStart_380869 baseEnd_380869 := by
    simpa [prefixWord, tailWord_380869, baseEnd_380869] using wordTrace_append hprefix tailTrace_380869
  have hstable : (prefixWord ++ tailWord_380869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_380869).length < 2 ^ (prefixWord ++ tailWord_380869).sum := by decide
  have hdescent : baseEnd_380869 < baseStart_380869 := by decide
  rcases family_descends (prefixWord ++ tailWord_380869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_380890 : List Nat := [3, 1, 1, 2, 5, 2, 1, 1, 2, 1, 4]
def baseStart_380890 : Nat := 118140960795 + 380890 * 2 ^ 59
def prefixEnd_380890 : Nat := 4983230072969 + 3 ^ 40 * 380890 * 2
def baseEnd_380890 : Nat := 195579646491119999823325

theorem tailTrace_380890 : CollatzResearch.WordTrace tailWord_380890 prefixEnd_380890 195579646491119999823325 := by
  unfold tailWord_380890
  simp only [CollatzResearch.WordTrace]
  refine ⟨3473049897527013919537031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9261466393405370452098749 3473049897527013919537031)
  ·
    refine ⟨5209574846290520879305547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3473049897527013919537031 5209574846290520879305547)
    ·
      refine ⟨7814362269435781318958321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5209574846290520879305547 7814362269435781318958321)
      ·
        refine ⟨5860771702076835989218741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7814362269435781318958321 5860771702076835989218741)
        ·
          refine ⟨549447347069703373989257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 5860771702076835989218741 549447347069703373989257)
          ·
            refine ⟨412085510302277530491943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 549447347069703373989257 412085510302277530491943)
            ·
              refine ⟨618128265453416295737915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 412085510302277530491943 618128265453416295737915)
              ·
                refine ⟨927192398180124443606873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 618128265453416295737915 927192398180124443606873)
                ·
                  refine ⟨695394298635093332705155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 927192398180124443606873 695394298635093332705155)
                  ·
                    refine ⟨1043091447952639999057733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 695394298635093332705155 1043091447952639999057733)
                    ·
                      refine ⟨195579646491119999823325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1043091447952639999057733 195579646491119999823325)
                      ·
                        rfl

theorem cell23_380890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 2, 1, 1, 2, 1, 4].length) (baseStart_380890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_380890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_380890 prefixEnd_380890 := by exact prefixLift 380890
  have htrace : WordTrace (prefixWord ++ tailWord_380890) baseStart_380890 baseEnd_380890 := by
    simpa [prefixWord, tailWord_380890, baseEnd_380890] using wordTrace_append hprefix tailTrace_380890
  have hstable : (prefixWord ++ tailWord_380890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_380890).length < 2 ^ (prefixWord ++ tailWord_380890).sum := by decide
  have hdescent : baseEnd_380890 < baseStart_380890 := by decide
  rcases family_descends (prefixWord ++ tailWord_380890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_380900 : List Nat := [2, 3, 1, 1, 1, 1, 6, 3, 1, 4]
def baseStart_380900 : Nat := 118140960795 + 380900 * 2 ^ 59
def prefixEnd_380900 : Nat := 4983230072969 + 3 ^ 40 * 380900 * 2
def baseEnd_380900 : Nat := 65194927099221653566093

theorem tailTrace_380900 : CollatzResearch.WordTrace tailWord_380900 prefixEnd_380900 65194927099221653566093 := by
  unfold tailWord_380900
  simp only [CollatzResearch.WordTrace]
  refine ⟨6946282160035913693006077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9261709546714551590674769 6946282160035913693006077)
  ·
    refine ⟨2604855810013467634877279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6946282160035913693006077 2604855810013467634877279)
    ·
      refine ⟨3907283715020201452315919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2604855810013467634877279 3907283715020201452315919)
      ·
        refine ⟨5860925572530302178473879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3907283715020201452315919 5860925572530302178473879)
        ·
          refine ⟨8791388358795453267710819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5860925572530302178473879 8791388358795453267710819)
          ·
            refine ⟨13187082538193179901566229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8791388358795453267710819 13187082538193179901566229)
            ·
              refine ⟨618144493977805307885917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 13187082538193179901566229 618144493977805307885917)
              ·
                refine ⟨231804185241676990457219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 618144493977805307885917 231804185241676990457219)
                ·
                  refine ⟨347706277862515485685829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 231804185241676990457219 347706277862515485685829)
                  ·
                    refine ⟨65194927099221653566093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 347706277862515485685829 65194927099221653566093)
                    ·
                      rfl

theorem cell23_380900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 6, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 6, 3, 1, 4].length) (baseStart_380900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_380900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_380900 prefixEnd_380900 := by exact prefixLift 380900
  have htrace : WordTrace (prefixWord ++ tailWord_380900) baseStart_380900 baseEnd_380900 := by
    simpa [prefixWord, tailWord_380900, baseEnd_380900] using wordTrace_append hprefix tailTrace_380900
  have hstable : (prefixWord ++ tailWord_380900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_380900).length < 2 ^ (prefixWord ++ tailWord_380900).sum := by decide
  have hdescent : baseEnd_380900 < baseStart_380900 := by decide
  rcases family_descends (prefixWord ++ tailWord_380900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_380923 : List Nat := [1, 1, 1, 1, 1, 3, 5, 3, 3, 1, 3]
def baseStart_380923 : Nat := 118140960795 + 380923 * 2 ^ 59
def prefixEnd_380923 : Nat := 4983230072969 + 3 ^ 40 * 380923 * 2
def baseEnd_380923 : Nat := 195596591352718370710673

theorem tailTrace_380923 : CollatzResearch.WordTrace tailWord_380923 prefixEnd_380923 195596591352718370710673 := by
  unfold tailWord_380923
  simp only [CollatzResearch.WordTrace]
  refine ⟨13893403198988502314099423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9262268799325668209399615 13893403198988502314099423)
  ·
    refine ⟨20840104798482753471149135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13893403198988502314099423 20840104798482753471149135)
    ·
      refine ⟨31260157197724130206723703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20840104798482753471149135 31260157197724130206723703)
      ·
        refine ⟨46890235796586195310085555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31260157197724130206723703 46890235796586195310085555)
        ·
          refine ⟨70335353694879292965128333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46890235796586195310085555 70335353694879292965128333)
          ·
            refine ⟨26375757635579734861923125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 70335353694879292965128333 26375757635579734861923125)
            ·
              refine ⟨2472727278335600143305293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 26375757635579734861923125 2472727278335600143305293)
              ·
                refine ⟨927272729375850053739485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2472727278335600143305293 927272729375850053739485)
                ·
                  refine ⟨347727273515943770152307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 927272729375850053739485 347727273515943770152307)
                  ·
                    refine ⟨521590910273915655228461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 347727273515943770152307 521590910273915655228461)
                    ·
                      refine ⟨195596591352718370710673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 521590910273915655228461 195596591352718370710673)
                      ·
                        rfl

theorem cell23_380923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 5, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 5, 3, 3, 1, 3].length) (baseStart_380923 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_380923 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_380923 prefixEnd_380923 := by exact prefixLift 380923
  have htrace : WordTrace (prefixWord ++ tailWord_380923) baseStart_380923 baseEnd_380923 := by
    simpa [prefixWord, tailWord_380923, baseEnd_380923] using wordTrace_append hprefix tailTrace_380923
  have hstable : (prefixWord ++ tailWord_380923).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_380923).length < 2 ^ (prefixWord ++ tailWord_380923).sum := by decide
  have hdescent : baseEnd_380923 < baseStart_380923 := by decide
  rcases family_descends (prefixWord ++ tailWord_380923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_380933 : List Nat := [1, 3, 1, 1, 2, 4, 1, 2, 1, 5, 2]
def baseStart_380933 : Nat := 118140960795 + 380933 * 2 ^ 59
def prefixEnd_380933 : Nat := 4983230072969 + 3 ^ 40 * 380933 * 2
def baseEnd_380933 : Nat := 195601726159263331585627

theorem tailTrace_380933 : CollatzResearch.WordTrace tailWord_380933 prefixEnd_380933 195601726159263331585627 := by
  unfold tailWord_380933
  simp only [CollatzResearch.WordTrace]
  refine ⟨13893767928952274021963453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9262511952634849347975635 13893767928952274021963453)
  ·
    refine ⟨5210162973357102758236295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13893767928952274021963453 5210162973357102758236295)
    ·
      refine ⟨7815244460035654137354443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5210162973357102758236295 7815244460035654137354443)
      ·
        refine ⟨11722866690053481206031665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7815244460035654137354443 11722866690053481206031665)
        ·
          refine ⟨8792150017540110904523749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11722866690053481206031665 8792150017540110904523749)
          ·
            refine ⟨1648528128288770794598203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8792150017540110904523749 1648528128288770794598203)
            ·
              refine ⟨2472792192433156191897305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1648528128288770794598203 2472792192433156191897305)
              ·
                refine ⟨1854594144324867143922979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2472792192433156191897305 1854594144324867143922979)
                ·
                  refine ⟨2781891216487300715884469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1854594144324867143922979 2781891216487300715884469)
                  ·
                    refine ⟨260802301545684442114169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2781891216487300715884469 260802301545684442114169)
                    ·
                      refine ⟨195601726159263331585627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 260802301545684442114169 195601726159263331585627)
                      ·
                        rfl

theorem cell23_380933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 1, 2, 1, 5, 2].length) (baseStart_380933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_380933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_380933 prefixEnd_380933 := by exact prefixLift 380933
  have htrace : WordTrace (prefixWord ++ tailWord_380933) baseStart_380933 baseEnd_380933 := by
    simpa [prefixWord, tailWord_380933, baseEnd_380933] using wordTrace_append hprefix tailTrace_380933
  have hstable : (prefixWord ++ tailWord_380933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_380933).length < 2 ^ (prefixWord ++ tailWord_380933).sum := by decide
  have hdescent : baseEnd_380933 < baseStart_380933 := by decide
  rcases family_descends (prefixWord ++ tailWord_380933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_380963 : List Nat := [1, 1, 1, 4, 3, 1, 1, 5, 1, 1, 4]
def baseStart_380963 : Nat := 118140960795 + 380963 * 2 ^ 59
def prefixEnd_380963 : Nat := 4983230072969 + 3 ^ 40 * 380963 * 2
def baseEnd_380963 : Nat := 195617130578898214210489

theorem tailTrace_380963 : CollatzResearch.WordTrace tailWord_380963 prefixEnd_380963 195617130578898214210489 := by
  unfold tailWord_380963
  simp only [CollatzResearch.WordTrace]
  refine ⟨13894862118843589145555543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9263241412562392763703695 13894862118843589145555543)
  ·
    refine ⟨20842293178265383718333315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13894862118843589145555543 20842293178265383718333315)
    ·
      refine ⟨31263439767398075577499973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20842293178265383718333315 31263439767398075577499973)
      ·
        refine ⟨5861894956387139170781245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 31263439767398075577499973 5861894956387139170781245)
        ·
          refine ⟨2198210608645177189042967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5861894956387139170781245 2198210608645177189042967)
          ·
            refine ⟨3297315912967765783564451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2198210608645177189042967 3297315912967765783564451)
            ·
              refine ⟨4945973869451648675346677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3297315912967765783564451 4945973869451648675346677)
              ·
                refine ⟨463685050261092063313751, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4945973869451648675346677 463685050261092063313751)
                ·
                  refine ⟨695527575391638094970627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 463685050261092063313751 695527575391638094970627)
                  ·
                    refine ⟨1043291363087457142455941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 695527575391638094970627 1043291363087457142455941)
                    ·
                      refine ⟨195617130578898214210489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1043291363087457142455941 195617130578898214210489)
                      ·
                        rfl

theorem cell23_380963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 1, 5, 1, 1, 4].length) (baseStart_380963 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_380963 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_380963 prefixEnd_380963 := by exact prefixLift 380963
  have htrace : WordTrace (prefixWord ++ tailWord_380963) baseStart_380963 baseEnd_380963 := by
    simpa [prefixWord, tailWord_380963, baseEnd_380963] using wordTrace_append hprefix tailTrace_380963
  have hstable : (prefixWord ++ tailWord_380963).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_380963).length < 2 ^ (prefixWord ++ tailWord_380963).sum := by decide
  have hdescent : baseEnd_380963 < baseStart_380963 := by decide
  rcases family_descends (prefixWord ++ tailWord_380963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_380976 : List Nat := [2, 1, 1, 1, 2, 5, 1, 2, 1, 1, 6]
def baseStart_380976 : Nat := 118140960795 + 380976 * 2 ^ 59
def prefixEnd_380976 : Nat := 4983230072969 + 3 ^ 40 * 380976 * 2
def baseEnd_380976 : Nat := 195623805827406663347929

theorem tailTrace_380976 : CollatzResearch.WordTrace tailWord_380976 prefixEnd_380976 195623805827406663347929 := by
  unfold tailWord_380976
  simp only [CollatzResearch.WordTrace]
  refine ⟨6947668133898246182889391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9263557511864328243852521 6947668133898246182889391)
  ·
    refine ⟨10421502200847369274334087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6947668133898246182889391 10421502200847369274334087)
    ·
      refine ⟨15632253301271053911501131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10421502200847369274334087 15632253301271053911501131)
      ·
        refine ⟨23448379951906580867251697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15632253301271053911501131 23448379951906580867251697)
        ·
          refine ⟨17586284963929935650438773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23448379951906580867251697 17586284963929935650438773)
          ·
            refine ⟨1648714215368431467228635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 17586284963929935650438773 1648714215368431467228635)
            ·
              refine ⟨2473071323052647200842953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1648714215368431467228635 2473071323052647200842953)
              ·
                refine ⟨1854803492289485400632215, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2473071323052647200842953 1854803492289485400632215)
                ·
                  refine ⟨2782205238434228100948323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1854803492289485400632215 2782205238434228100948323)
                  ·
                    refine ⟨4173307857651342151422485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2782205238434228100948323 4173307857651342151422485)
                    ·
                      refine ⟨195623805827406663347929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 4173307857651342151422485 195623805827406663347929)
                      ·
                        rfl

theorem cell23_380976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 1, 2, 1, 1, 6].length) (baseStart_380976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_380976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_380976 prefixEnd_380976 := by exact prefixLift 380976
  have htrace : WordTrace (prefixWord ++ tailWord_380976) baseStart_380976 baseEnd_380976 := by
    simpa [prefixWord, tailWord_380976, baseEnd_380976] using wordTrace_append hprefix tailTrace_380976
  have hstable : (prefixWord ++ tailWord_380976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_380976).length < 2 ^ (prefixWord ++ tailWord_380976).sum := by decide
  have hdescent : baseEnd_380976 < baseStart_380976 := by decide
  rcases family_descends (prefixWord ++ tailWord_380976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_380993 : List Nat := [1, 2, 5, 1, 2, 1, 2, 1, 1, 1, 6]
def baseStart_380993 : Nat := 118140960795 + 380993 * 2 ^ 59
def prefixEnd_380993 : Nat := 4983230072969 + 3 ^ 40 * 380993 * 2
def baseEnd_380993 : Nat := 195632534998533096835351

theorem tailTrace_380993 : CollatzResearch.WordTrace tailWord_380993 prefixEnd_380993 195632534998533096835351 := by
  unfold tailWord_380993
  simp only [CollatzResearch.WordTrace]
  refine ⟨13895956308734904269147633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9263970872489936179431755 13895956308734904269147633)
  ·
    refine ⟨10421967231551178201860725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13895956308734904269147633 10421967231551178201860725)
    ·
      refine ⟨977059427957922956424443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 10421967231551178201860725 977059427957922956424443)
      ·
        refine ⟨1465589141936884434636665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 977059427957922956424443 1465589141936884434636665)
        ·
          refine ⟨1099191856452663325977499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1465589141936884434636665 1099191856452663325977499)
          ·
            refine ⟨1648787784678994988966249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1099191856452663325977499 1648787784678994988966249)
            ·
              refine ⟨1236590838509246241724687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1648787784678994988966249 1236590838509246241724687)
              ·
                refine ⟨1854886257763869362587031, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1236590838509246241724687 1854886257763869362587031)
                ·
                  refine ⟨2782329386645804043880547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1854886257763869362587031 2782329386645804043880547)
                  ·
                    refine ⟨4173494079968706065820821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2782329386645804043880547 4173494079968706065820821)
                    ·
                      refine ⟨195632534998533096835351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 4173494079968706065820821 195632534998533096835351)
                      ·
                        rfl

theorem cell23_380993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 2, 1, 1, 1, 6].length) (baseStart_380993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_380993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_380993 prefixEnd_380993 := by exact prefixLift 380993
  have htrace : WordTrace (prefixWord ++ tailWord_380993) baseStart_380993 baseEnd_380993 := by
    simpa [prefixWord, tailWord_380993, baseEnd_380993] using wordTrace_append hprefix tailTrace_380993
  have hstable : (prefixWord ++ tailWord_380993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_380993).length < 2 ^ (prefixWord ++ tailWord_380993).sum := by decide
  have hdescent : baseEnd_380993 < baseStart_380993 := by decide
  rcases family_descends (prefixWord ++ tailWord_380993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_381010 : List Nat := [3, 2, 2, 1, 4, 1, 1, 2, 1, 2, 4]
def baseStart_381010 : Nat := 118140960795 + 381010 * 2 ^ 59
def prefixEnd_381010 : Nat := 4983230072969 + 3 ^ 40 * 381010 * 2
def baseEnd_381010 : Nat := 195641264169659530322773

theorem tailTrace_381010 : CollatzResearch.WordTrace tailWord_381010 prefixEnd_381010 195641264169659530322773 := by
  unfold tailWord_381010
  simp only [CollatzResearch.WordTrace]
  refine ⟨3474144087418329043129121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9264384233115544115010989 3474144087418329043129121)
  ·
    refine ⟨2605608065563746782346841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3474144087418329043129121 2605608065563746782346841)
    ·
      refine ⟨1954206049172810086760131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2605608065563746782346841 1954206049172810086760131)
      ·
        refine ⟨2931309073759215130140197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1954206049172810086760131 2931309073759215130140197)
        ·
          refine ⟨549620451329852836901287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2931309073759215130140197 549620451329852836901287)
          ·
            refine ⟨824430676994779255351931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 549620451329852836901287 824430676994779255351931)
            ·
              refine ⟨1236646015492168883027897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 824430676994779255351931 1236646015492168883027897)
              ·
                refine ⟨927484511619126662270923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1236646015492168883027897 927484511619126662270923)
                ·
                  refine ⟨1391226767428689993406385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 927484511619126662270923 1391226767428689993406385)
                  ·
                    refine ⟨1043420075571517495054789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1391226767428689993406385 1043420075571517495054789)
                    ·
                      refine ⟨195641264169659530322773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1043420075571517495054789 195641264169659530322773)
                      ·
                        rfl

theorem cell23_381010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 1, 1, 2, 1, 2, 4].length) (baseStart_381010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_381010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_381010 prefixEnd_381010 := by exact prefixLift 381010
  have htrace : WordTrace (prefixWord ++ tailWord_381010) baseStart_381010 baseEnd_381010 := by
    simpa [prefixWord, tailWord_381010, baseEnd_381010] using wordTrace_append hprefix tailTrace_381010
  have hstable : (prefixWord ++ tailWord_381010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_381010).length < 2 ^ (prefixWord ++ tailWord_381010).sum := by decide
  have hdescent : baseEnd_381010 < baseStart_381010 := by decide
  rcases family_descends (prefixWord ++ tailWord_381010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_381013 : List Nat := [1, 3, 2, 2, 1, 3, 1, 1, 3, 3, 3]
def baseStart_381013 : Nat := 118140960795 + 381013 * 2 ^ 59
def prefixEnd_381013 : Nat := 4983230072969 + 3 ^ 40 * 381013 * 2
def baseEnd_381013 : Nat := 195642804611623018585259

theorem tailTrace_381013 : CollatzResearch.WordTrace tailWord_381013 prefixEnd_381013 195642804611623018585259 := by
  unfold tailWord_381013
  simp only [CollatzResearch.WordTrace]
  refine ⟨13896685768662447684875693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9264457179108298456583795 13896685768662447684875693)
  ·
    refine ⟨5211257163248417881828385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13896685768662447684875693 5211257163248417881828385)
    ·
      refine ⟨3908442872436313411371289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5211257163248417881828385 3908442872436313411371289)
      ·
        refine ⟨2931332154327235058528467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3908442872436313411371289 2931332154327235058528467)
        ·
          refine ⟨4396998231490852587792701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2931332154327235058528467 4396998231490852587792701)
          ·
            refine ⟨1648874336809069720422263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4396998231490852587792701 1648874336809069720422263)
            ·
              refine ⟨2473311505213604580633395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1648874336809069720422263 2473311505213604580633395)
              ·
                refine ⟨3709967257820406870950093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2473311505213604580633395 3709967257820406870950093)
                ·
                  refine ⟨1391237721682652576606285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3709967257820406870950093 1391237721682652576606285)
                  ·
                    refine ⟨521714145630994716227357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1391237721682652576606285 521714145630994716227357)
                    ·
                      refine ⟨195642804611623018585259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 521714145630994716227357 195642804611623018585259)
                      ·
                        rfl

theorem cell23_381013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 1, 1, 3, 3, 3].length) (baseStart_381013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_381013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_381013 prefixEnd_381013 := by exact prefixLift 381013
  have htrace : WordTrace (prefixWord ++ tailWord_381013) baseStart_381013 baseEnd_381013 := by
    simpa [prefixWord, tailWord_381013, baseEnd_381013] using wordTrace_append hprefix tailTrace_381013
  have hstable : (prefixWord ++ tailWord_381013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_381013).length < 2 ^ (prefixWord ++ tailWord_381013).sum := by decide
  have hdescent : baseEnd_381013 < baseStart_381013 := by decide
  rcases family_descends (prefixWord ++ tailWord_381013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_381040 : List Nat := [2, 1, 1, 1, 5, 2, 1, 2, 3, 3, 2]
def baseStart_381040 : Nat := 118140960795 + 381040 * 2 ^ 59
def prefixEnd_381040 : Nat := 4983230072969 + 3 ^ 40 * 381040 * 2
def baseEnd_381040 : Nat := 195656668589294412947635

theorem tailTrace_381040 : CollatzResearch.WordTrace tailWord_381040 prefixEnd_381040 195656668589294412947635 := by
  unfold tailWord_381040
  simp only [CollatzResearch.WordTrace]
  refine ⟨6948835269782315648054287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9265113693043087530739049 6948835269782315648054287)
  ·
    refine ⟨10423252904673473472081431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6948835269782315648054287 10423252904673473472081431)
    ·
      refine ⟨15634879357010210208122147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10423252904673473472081431 15634879357010210208122147)
      ·
        refine ⟨23452319035515315312183221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15634879357010210208122147 23452319035515315312183221)
        ·
          refine ⟨2198654909579560810517177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 23452319035515315312183221 2198654909579560810517177)
          ·
            refine ⟨1648991182184670607887883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2198654909579560810517177 1648991182184670607887883)
            ·
              refine ⟨2473486773277005911831825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1648991182184670607887883 2473486773277005911831825)
              ·
                refine ⟨1855115079957754433873869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2473486773277005911831825 1855115079957754433873869)
                ·
                  refine ⟨695668154984157912702701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1855115079957754433873869 695668154984157912702701)
                  ·
                    refine ⟨260875558119059217263513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 695668154984157912702701 260875558119059217263513)
                    ·
                      refine ⟨195656668589294412947635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 260875558119059217263513 195656668589294412947635)
                      ·
                        rfl

theorem cell23_381040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 1, 2, 3, 3, 2].length) (baseStart_381040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_381040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_381040 prefixEnd_381040 := by exact prefixLift 381040
  have htrace : WordTrace (prefixWord ++ tailWord_381040) baseStart_381040 baseEnd_381040 := by
    simpa [prefixWord, tailWord_381040, baseEnd_381040] using wordTrace_append hprefix tailTrace_381040
  have hstable : (prefixWord ++ tailWord_381040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_381040).length < 2 ^ (prefixWord ++ tailWord_381040).sum := by decide
  have hdescent : baseEnd_381040 < baseStart_381040 := by decide
  rcases family_descends (prefixWord ++ tailWord_381040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_381093 : List Nat := [1, 3, 1, 2, 1, 3, 4, 1, 7]
def baseStart_381093 : Nat := 118140960795 + 381093 * 2 ^ 59
def prefixEnd_381093 : Nat := 4983230072969 + 3 ^ 40 * 381093 * 2
def baseEnd_381093 : Nat := 21742653673775856176099

theorem tailTrace_381093 : CollatzResearch.WordTrace tailWord_381093 prefixEnd_381093 21742653673775856176099 := by
  unfold tailWord_381093
  simp only [CollatzResearch.WordTrace]
  refine ⟨13899603608372621347787933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9266402405581747565191955 13899603608372621347787933)
  ·
    refine ⟨5212351353139733005420475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13899603608372621347787933 5212351353139733005420475)
    ·
      refine ⟨7818527029709599508130713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5212351353139733005420475 7818527029709599508130713)
      ·
        refine ⟨5863895272282199631098035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7818527029709599508130713 5863895272282199631098035)
        ·
          refine ⟨8795842908423299446647053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5863895272282199631098035 8795842908423299446647053)
          ·
            refine ⟨3298441090658737292492645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8795842908423299446647053 3298441090658737292492645)
            ·
              refine ⟨618457704498513242342371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3298441090658737292492645 618457704498513242342371)
              ·
                refine ⟨927686556747769863513557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 618457704498513242342371 927686556747769863513557)
                ·
                  refine ⟨21742653673775856176099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 927686556747769863513557 21742653673775856176099)
                  ·
                    rfl

theorem cell23_381093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 4, 1, 7].length) (baseStart_381093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_381093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_381093 prefixEnd_381093 := by exact prefixLift 381093
  have htrace : WordTrace (prefixWord ++ tailWord_381093) baseStart_381093 baseEnd_381093 := by
    simpa [prefixWord, tailWord_381093, baseEnd_381093] using wordTrace_append hprefix tailTrace_381093
  have hstable : (prefixWord ++ tailWord_381093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_381093).length < 2 ^ (prefixWord ++ tailWord_381093).sum := by decide
  have hdescent : baseEnd_381093 < baseStart_381093 := by decide
  rcases family_descends (prefixWord ++ tailWord_381093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_381155 : List Nat := [1, 1, 1, 8, 2, 1, 2, 1, 2, 2, 2]
def baseStart_381155 : Nat := 118140960795 + 381155 * 2 ^ 59
def prefixEnd_381155 : Nat := 4983230072969 + 3 ^ 40 * 381155 * 2
def baseEnd_381155 : Nat := 195715718864561463009607

theorem tailTrace_381155 : CollatzResearch.WordTrace tailWord_381155 prefixEnd_381155 195715718864561463009607 := by
  unfold tailWord_381155
  simp only [CollatzResearch.WordTrace]
  refine ⟨13901864934148005936544919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9267909956098670624363279 13901864934148005936544919)
  ·
    refine ⟨20852797401222008904817379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13901864934148005936544919 20852797401222008904817379)
    ·
      refine ⟨31279196101833013357226069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20852797401222008904817379 31279196101833013357226069)
      ·
        refine ⟨366553079318355625279993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 8 31279196101833013357226069 366553079318355625279993)
        ·
          refine ⟨274914809488766718959995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 366553079318355625279993 274914809488766718959995)
          ·
            refine ⟨412372214233150078439993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 274914809488766718959995 412372214233150078439993)
            ·
              refine ⟨309279160674862558829995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 412372214233150078439993 309279160674862558829995)
              ·
                refine ⟨463918741012293838244993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 309279160674862558829995 463918741012293838244993)
                ·
                  refine ⟨347939055759220378683745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 463918741012293838244993 347939055759220378683745)
                  ·
                    refine ⟨260954291819415284012809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 347939055759220378683745 260954291819415284012809)
                    ·
                      refine ⟨195715718864561463009607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 260954291819415284012809 195715718864561463009607)
                      ·
                        rfl

theorem cell23_381155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 2, 1, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 2, 1, 2, 1, 2, 2, 2].length) (baseStart_381155 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_381155 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_381155 prefixEnd_381155 := by exact prefixLift 381155
  have htrace : WordTrace (prefixWord ++ tailWord_381155) baseStart_381155 baseEnd_381155 := by
    simpa [prefixWord, tailWord_381155, baseEnd_381155] using wordTrace_append hprefix tailTrace_381155
  have hstable : (prefixWord ++ tailWord_381155).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_381155).length < 2 ^ (prefixWord ++ tailWord_381155).sum := by decide
  have hdescent : baseEnd_381155 < baseStart_381155 := by decide
  rcases family_descends (prefixWord ++ tailWord_381155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_381187 : List Nat := [1, 1, 1, 3, 2, 3, 2, 5, 1, 4]
def baseStart_381187 : Nat := 118140960795 + 381187 * 2 ^ 59
def prefixEnd_381187 : Nat := 4983230072969 + 3 ^ 40 * 381187 * 2
def baseEnd_381187 : Nat := 65244050081835112603153

theorem tailTrace_381187 : CollatzResearch.WordTrace tailWord_381187 prefixEnd_381187 65244050081835112603153 := by
  unfold tailWord_381187
  simp only [CollatzResearch.WordTrace]
  refine ⟨13903032070032075401709815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9268688046688050267806543 13903032070032075401709815)
  ·
    refine ⟨20854548105048113102564723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13903032070032075401709815 20854548105048113102564723)
    ·
      refine ⟨31281822157572169653847085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20854548105048113102564723 31281822157572169653847085)
      ·
        refine ⟨11730683309089563620192657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31281822157572169653847085 11730683309089563620192657)
        ·
          refine ⟨8798012481817172715144493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11730683309089563620192657 8798012481817172715144493)
          ·
            refine ⟨3299254680681439768179185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8798012481817172715144493 3299254680681439768179185)
            ·
              refine ⟨2474441010511079826134389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3299254680681439768179185 2474441010511079826134389)
              ·
                refine ⟨231978844735413733700099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2474441010511079826134389 231978844735413733700099)
                ·
                  refine ⟨347968267103120600550149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 231978844735413733700099 347968267103120600550149)
                  ·
                    refine ⟨65244050081835112603153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 347968267103120600550149 65244050081835112603153)
                    ·
                      rfl

theorem cell23_381187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 2, 5, 1, 4].length) (baseStart_381187 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_381187 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_381187 prefixEnd_381187 := by exact prefixLift 381187
  have htrace : WordTrace (prefixWord ++ tailWord_381187) baseStart_381187 baseEnd_381187 := by
    simpa [prefixWord, tailWord_381187, baseEnd_381187] using wordTrace_append hprefix tailTrace_381187
  have hstable : (prefixWord ++ tailWord_381187).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_381187).length < 2 ^ (prefixWord ++ tailWord_381187).sum := by decide
  have hdescent : baseEnd_381187 < baseStart_381187 := by decide
  rcases family_descends (prefixWord ++ tailWord_381187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_381237 : List Nat := [1, 3, 3, 1, 2, 1, 3, 1, 1, 5, 2]
def baseStart_381237 : Nat := 118140960795 + 381237 * 2 ^ 59
def prefixEnd_381237 : Nat := 4983230072969 + 3 ^ 40 * 381237 * 2
def baseEnd_381237 : Nat := 195757824278230142184229

theorem tailTrace_381237 : CollatzResearch.WordTrace tailWord_381237 prefixEnd_381237 195757824278230142184229 := by
  unfold tailWord_381237
  simp only [CollatzResearch.WordTrace]
  refine ⟨13904855719850933941029965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9269903813233955960686643 13904855719850933941029965)
  ·
    refine ⟨5214320894944100227886237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13904855719850933941029965 5214320894944100227886237)
    ·
      refine ⟨1955370335604037585457339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5214320894944100227886237 1955370335604037585457339)
      ·
        refine ⟨2933055503406056378186009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1955370335604037585457339 2933055503406056378186009)
        ·
          refine ⟨2199791627554542283639507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2933055503406056378186009 2199791627554542283639507)
          ·
            refine ⟨3299687441331813425459261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2199791627554542283639507 3299687441331813425459261)
            ·
              refine ⟨1237382790499430034547223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3299687441331813425459261 1237382790499430034547223)
              ·
                refine ⟨1856074185749145051820835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1237382790499430034547223 1856074185749145051820835)
                ·
                  refine ⟨2784111278623717577731253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1856074185749145051820835 2784111278623717577731253)
                  ·
                    refine ⟨261010432370973522912305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2784111278623717577731253 261010432370973522912305)
                    ·
                      refine ⟨195757824278230142184229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 261010432370973522912305 195757824278230142184229)
                      ·
                        rfl

theorem cell23_381237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 3, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 3, 1, 1, 5, 2].length) (baseStart_381237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_381237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_381237 prefixEnd_381237 := by exact prefixLift 381237
  have htrace : WordTrace (prefixWord ++ tailWord_381237) baseStart_381237 baseEnd_381237 := by
    simpa [prefixWord, tailWord_381237, baseEnd_381237] using wordTrace_append hprefix tailTrace_381237
  have hstable : (prefixWord ++ tailWord_381237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_381237).length < 2 ^ (prefixWord ++ tailWord_381237).sum := by decide
  have hdescent : baseEnd_381237 < baseStart_381237 := by decide
  rcases family_descends (prefixWord ++ tailWord_381237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_381273 : List Nat := [1, 2, 1, 2, 2, 2, 1, 12]
def baseStart_381273 : Nat := 118140960795 + 381273 * 2 ^ 59
def prefixEnd_381273 : Nat := 4983230072969 + 3 ^ 40 * 381273 * 2
def baseEnd_381273 : Nat := 7250974428955259308669

theorem tailTrace_381273 : CollatzResearch.WordTrace tailWord_381273 prefixEnd_381273 7250974428955259308669 := by
  unfold tailWord_381273
  simp only [CollatzResearch.WordTrace]
  refine ⟨13906168747720512089340473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9270779165147008059560315 13906168747720512089340473)
  ·
    refine ⟨10429626560790384067005355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13906168747720512089340473 10429626560790384067005355)
    ·
      refine ⟨15644439841185576100508033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10429626560790384067005355 15644439841185576100508033)
      ·
        refine ⟨11733329880889182075381025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15644439841185576100508033 11733329880889182075381025)
        ·
          refine ⟨8799997410666886556535769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11733329880889182075381025 8799997410666886556535769)
          ·
            refine ⟨6599998058000164917401827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8799997410666886556535769 6599998058000164917401827)
            ·
              refine ⟨9899997087000247376102741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6599998058000164917401827 9899997087000247376102741)
              ·
                refine ⟨7250974428955259308669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 12 9899997087000247376102741 7250974428955259308669)
                ·
                  rfl

theorem cell23_381273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 12].length) (baseStart_381273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_381273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_381273 prefixEnd_381273 := by exact prefixLift 381273
  have htrace : WordTrace (prefixWord ++ tailWord_381273) baseStart_381273 baseEnd_381273 := by
    simpa [prefixWord, tailWord_381273, baseEnd_381273] using wordTrace_append hprefix tailTrace_381273
  have hstable : (prefixWord ++ tailWord_381273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_381273).length < 2 ^ (prefixWord ++ tailWord_381273).sum := by decide
  have hdescent : baseEnd_381273 < baseStart_381273 := by decide
  rcases family_descends (prefixWord ++ tailWord_381273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_381284 : List Nat := [2, 3, 1, 1, 3, 1, 1, 4, 3, 2, 2]
def baseStart_381284 : Nat := 118140960795 + 381284 * 2 ^ 59
def prefixEnd_381284 : Nat := 4983230072969 + 3 ^ 40 * 381284 * 2
def baseEnd_381284 : Nat := 195781957868991458296513

theorem tailTrace_381284 : CollatzResearch.WordTrace tailWord_381284 prefixEnd_381284 195781957868991458296513 := by
  unfold tailWord_381284
  simp only [CollatzResearch.WordTrace]
  refine ⟨6953284975340330483995453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9271046633787107311993937 6953284975340330483995453)
  ·
    refine ⟨2607481865752623931498295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6953284975340330483995453 2607481865752623931498295)
    ·
      refine ⟨3911222798628935897247443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2607481865752623931498295 3911222798628935897247443)
      ·
        refine ⟨5866834197943403845871165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3911222798628935897247443 5866834197943403845871165)
        ·
          refine ⟨2200062824228776442201687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5866834197943403845871165 2200062824228776442201687)
          ·
            refine ⟨3300094236343164663302531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2200062824228776442201687 3300094236343164663302531)
            ·
              refine ⟨4950141354514746994953797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3300094236343164663302531 4950141354514746994953797)
              ·
                refine ⟨928151503971515061553837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4950141354514746994953797 928151503971515061553837)
                ·
                  refine ⟨348056813989318148082689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 928151503971515061553837 348056813989318148082689)
                  ·
                    refine ⟨261042610491988611062017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 348056813989318148082689 261042610491988611062017)
                    ·
                      refine ⟨195781957868991458296513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 261042610491988611062017 195781957868991458296513)
                      ·
                        rfl

theorem cell23_381284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 1, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 1, 4, 3, 2, 2].length) (baseStart_381284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_381284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_381284 prefixEnd_381284 := by exact prefixLift 381284
  have htrace : WordTrace (prefixWord ++ tailWord_381284) baseStart_381284 baseEnd_381284 := by
    simpa [prefixWord, tailWord_381284, baseEnd_381284] using wordTrace_append hprefix tailTrace_381284
  have hstable : (prefixWord ++ tailWord_381284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_381284).length < 2 ^ (prefixWord ++ tailWord_381284).sum := by decide
  have hdescent : baseEnd_381284 < baseStart_381284 := by decide
  rcases family_descends (prefixWord ++ tailWord_381284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_381320 : List Nat := [2, 1, 3, 3, 1, 1, 2, 1, 2, 7]
def baseStart_381320 : Nat := 118140960795 + 381320 * 2 ^ 59
def prefixEnd_381320 : Nat := 4983230072969 + 3 ^ 40 * 381320 * 2
def baseEnd_381320 : Nat := 65266814390851105815449

theorem tailTrace_381320 : CollatzResearch.WordTrace tailWord_381320 prefixEnd_381320 65266814390851105815449 := by
  unfold tailWord_381320
  simp only [CollatzResearch.WordTrace]
  refine ⟨6953941489275119558150707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9271921985700159410867609 6953941489275119558150707)
  ·
    refine ⟨10430912233912679337226061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6953941489275119558150707 10430912233912679337226061)
    ·
      refine ⟨3911592087717254751459773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10430912233912679337226061 3911592087717254751459773)
      ·
        refine ⟨1466847032893970531797415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3911592087717254751459773 1466847032893970531797415)
        ·
          refine ⟨2200270549340955797696123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1466847032893970531797415 2200270549340955797696123)
          ·
            refine ⟨3300405824011433696544185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2200270549340955797696123 3300405824011433696544185)
            ·
              refine ⟨2475304368008575272408139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3300405824011433696544185 2475304368008575272408139)
              ·
                refine ⟨3712956552012862908612209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2475304368008575272408139 3712956552012862908612209)
                ·
                  refine ⟨2784717414009647181459157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3712956552012862908612209 2784717414009647181459157)
                  ·
                    refine ⟨65266814390851105815449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 2784717414009647181459157 65266814390851105815449)
                    ·
                      rfl

theorem cell23_381320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 2, 1, 2, 7].length) (baseStart_381320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_381320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_381320 prefixEnd_381320 := by exact prefixLift 381320
  have htrace : WordTrace (prefixWord ++ tailWord_381320) baseStart_381320 baseEnd_381320 := by
    simpa [prefixWord, tailWord_381320, baseEnd_381320] using wordTrace_append hprefix tailTrace_381320
  have hstable : (prefixWord ++ tailWord_381320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_381320).length < 2 ^ (prefixWord ++ tailWord_381320).sum := by decide
  have hdescent : baseEnd_381320 < baseStart_381320 := by decide
  rcases family_descends (prefixWord ++ tailWord_381320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_381344 : List Nat := [2, 1, 1, 4, 1, 4, 1, 1, 3, 3, 2]
def baseStart_381344 : Nat := 118140960795 + 381344 * 2 ^ 59
def prefixEnd_381344 : Nat := 4983230072969 + 3 ^ 40 * 381344 * 2
def baseEnd_381344 : Nat := 195812766708261223546237

theorem tailTrace_381344 : CollatzResearch.WordTrace tailWord_381344 prefixEnd_381344 195812766708261223546237 := by
  unfold tailWord_381344
  simp only [CollatzResearch.WordTrace]
  refine ⟨6954379165231645607587543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9272505553642194143450057 6954379165231645607587543)
  ·
    refine ⟨10431568747847468411381315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6954379165231645607587543 10431568747847468411381315)
    ·
      refine ⟨15647353121771202617071973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10431568747847468411381315 15647353121771202617071973)
      ·
        refine ⟨2933878710332100490700995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15647353121771202617071973 2933878710332100490700995)
        ·
          refine ⟨4400818065498150736051493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2933878710332100490700995 4400818065498150736051493)
          ·
            refine ⟨825153387280903263009655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4400818065498150736051493 825153387280903263009655)
            ·
              refine ⟨1237730080921354894514483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 825153387280903263009655 1237730080921354894514483)
              ·
                refine ⟨1856595121382032341771725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1237730080921354894514483 1856595121382032341771725)
                ·
                  refine ⟨696223170518262128164397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1856595121382032341771725 696223170518262128164397)
                  ·
                    refine ⟨261083688944348298061649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 696223170518262128164397 261083688944348298061649)
                    ·
                      refine ⟨195812766708261223546237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 261083688944348298061649 195812766708261223546237)
                      ·
                        rfl

theorem cell23_381344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 4, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 4, 1, 1, 3, 3, 2].length) (baseStart_381344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_381344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_381344 prefixEnd_381344 := by exact prefixLift 381344
  have htrace : WordTrace (prefixWord ++ tailWord_381344) baseStart_381344 baseEnd_381344 := by
    simpa [prefixWord, tailWord_381344, baseEnd_381344] using wordTrace_append hprefix tailTrace_381344
  have hstable : (prefixWord ++ tailWord_381344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_381344).length < 2 ^ (prefixWord ++ tailWord_381344).sum := by decide
  have hdescent : baseEnd_381344 < baseStart_381344 := by decide
  rcases family_descends (prefixWord ++ tailWord_381344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_381370 : List Nat := [3, 1, 1, 1, 2, 1, 1, 2, 3, 4, 4]
def baseStart_381370 : Nat := 118140960795 + 381370 * 2 ^ 59
def prefixEnd_381370 : Nat := 4983230072969 + 3 ^ 40 * 381370 * 2
def baseEnd_381370 : Nat := 195826117205278121821117

theorem tailTrace_381370 : CollatzResearch.WordTrace tailWord_381370 prefixEnd_381370 195826117205278121821117 := by
  unfold tailWord_381370
  simp only [CollatzResearch.WordTrace]
  refine ⟨3477426657092274413905391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9273137752246065103747709 3477426657092274413905391)
  ·
    refine ⟨5216139985638411620858087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3477426657092274413905391 5216139985638411620858087)
    ·
      refine ⟨7824209978457617431287131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5216139985638411620858087 7824209978457617431287131)
      ·
        refine ⟨11736314967686426146930697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7824209978457617431287131 11736314967686426146930697)
        ·
          refine ⟨8802236225764819610198023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11736314967686426146930697 8802236225764819610198023)
          ·
            refine ⟨13203354338647229415297035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8802236225764819610198023 13203354338647229415297035)
            ·
              refine ⟨19805031507970844122945553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13203354338647229415297035 19805031507970844122945553)
              ·
                refine ⟨14853773630978133092209165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19805031507970844122945553 14853773630978133092209165)
                ·
                  refine ⟨5570165111616799909578437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14853773630978133092209165 5570165111616799909578437)
                  ·
                    refine ⟨1044405958428149983045957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5570165111616799909578437 1044405958428149983045957)
                    ·
                      refine ⟨195826117205278121821117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1044405958428149983045957 195826117205278121821117)
                      ·
                        rfl

theorem cell23_381370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 2, 3, 4, 4].length) (baseStart_381370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_381370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_381370 prefixEnd_381370 := by exact prefixLift 381370
  have htrace : WordTrace (prefixWord ++ tailWord_381370) baseStart_381370 baseEnd_381370 := by
    simpa [prefixWord, tailWord_381370, baseEnd_381370] using wordTrace_append hprefix tailTrace_381370
  have hstable : (prefixWord ++ tailWord_381370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_381370).length < 2 ^ (prefixWord ++ tailWord_381370).sum := by decide
  have hdescent : baseEnd_381370 < baseStart_381370 := by decide
  rcases family_descends (prefixWord ++ tailWord_381370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_381397 : List Nat := [1, 3, 2, 3, 1, 3, 1, 2, 7]
def baseStart_381397 : Nat := 118140960795 + 381397 * 2 ^ 59
def prefixEnd_381397 : Nat := 4983230072969 + 3 ^ 40 * 381397 * 2
def baseEnd_381397 : Nat := 21759997909216612909277

theorem tailTrace_381397 : CollatzResearch.WordTrace tailWord_381397 prefixEnd_381397 21759997909216612909277 := by
  unfold tailWord_381397
  simp only [CollatzResearch.WordTrace]
  refine ⟨13910691399271281266854445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9273794266180854177902963 13910691399271281266854445)
  ·
    refine ⟨5216509274726730475070417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13910691399271281266854445 5216509274726730475070417)
    ·
      refine ⟨3912381956045047856302813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5216509274726730475070417 3912381956045047856302813)
      ·
        refine ⟨1467143233516892946113555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3912381956045047856302813 1467143233516892946113555)
        ·
          refine ⟨2200714850275339419170333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1467143233516892946113555 2200714850275339419170333)
          ·
            refine ⟨825268068853252282188875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2200714850275339419170333 825268068853252282188875)
            ·
              refine ⟨1237902103279878423283313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 825268068853252282188875 1237902103279878423283313)
              ·
                refine ⟨928426577459908817462485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1237902103279878423283313 928426577459908817462485)
                ·
                  refine ⟨21759997909216612909277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 928426577459908817462485 21759997909216612909277)
                  ·
                    rfl

theorem cell23_381397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 3, 1, 2, 7].length) (baseStart_381397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_381397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_381397 prefixEnd_381397 := by exact prefixLift 381397
  have htrace : WordTrace (prefixWord ++ tailWord_381397) baseStart_381397 baseEnd_381397 := by
    simpa [prefixWord, tailWord_381397, baseEnd_381397] using wordTrace_append hprefix tailTrace_381397
  have hstable : (prefixWord ++ tailWord_381397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_381397).length < 2 ^ (prefixWord ++ tailWord_381397).sum := by decide
  have hdescent : baseEnd_381397 < baseStart_381397 := by decide
  rcases family_descends (prefixWord ++ tailWord_381397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_381417 : List Nat := [1, 2, 1, 1, 1, 2, 1, 4, 1, 7, 2]
def baseStart_381417 : Nat := 118140960795 + 381417 * 2 ^ 59
def prefixEnd_381417 : Nat := 4983230072969 + 3 ^ 40 * 381417 * 2
def baseEnd_381417 : Nat := 195850250796039437933401

theorem tailTrace_381417 : CollatzResearch.WordTrace tailWord_381417 prefixEnd_381417 195850250796039437933401 := by
  unfold tailWord_381417
  simp only [CollatzResearch.WordTrace]
  refine ⟨13911420859198824682582505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9274280572799216455055003 13911420859198824682582505)
  ·
    refine ⟨10433565644399118511936879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13911420859198824682582505 10433565644399118511936879)
    ·
      refine ⟨15650348466598677767905319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10433565644399118511936879 15650348466598677767905319)
      ·
        refine ⟨23475522699898016651857979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15650348466598677767905319 23475522699898016651857979)
        ·
          refine ⟨35213284049847024977786969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23475522699898016651857979 35213284049847024977786969)
          ·
            refine ⟨26409963037385268733340227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35213284049847024977786969 26409963037385268733340227)
            ·
              refine ⟨39614944556077903100010341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26409963037385268733340227 39614944556077903100010341)
              ·
                refine ⟨7427802104264606831251939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 39614944556077903100010341 7427802104264606831251939)
                ·
                  refine ⟨11141703156396910246877909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7427802104264606831251939 11141703156396910246877909)
                  ·
                    refine ⟨261133667728052583911201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 11141703156396910246877909 261133667728052583911201)
                    ·
                      refine ⟨195850250796039437933401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 261133667728052583911201 195850250796039437933401)
                      ·
                        rfl

theorem cell23_381417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 4, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 4, 1, 7, 2].length) (baseStart_381417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_381417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_381417 prefixEnd_381417 := by exact prefixLift 381417
  have htrace : WordTrace (prefixWord ++ tailWord_381417) baseStart_381417 baseEnd_381417 := by
    simpa [prefixWord, tailWord_381417, baseEnd_381417] using wordTrace_append hprefix tailTrace_381417
  have hstable : (prefixWord ++ tailWord_381417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_381417).length < 2 ^ (prefixWord ++ tailWord_381417).sum := by decide
  have hdescent : baseEnd_381417 < baseStart_381417 := by decide
  rcases family_descends (prefixWord ++ tailWord_381417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_381442 : List Nat := [3, 4, 1, 2, 2, 1, 3, 1, 2, 2, 2]
def baseStart_381442 : Nat := 118140960795 + 381442 * 2 ^ 59
def prefixEnd_381442 : Nat := 4983230072969 + 3 ^ 40 * 381442 * 2
def baseEnd_381442 : Nat := 195863087812401840120787

theorem tailTrace_381442 : CollatzResearch.WordTrace tailWord_381442 prefixEnd_381442 195863087812401840120787 := by
  unfold tailWord_381442
  simp only [CollatzResearch.WordTrace]
  refine ⟨3478083171027063488060645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9274888456072169301495053 3478083171027063488060645)
  ·
    refine ⟨652140594567574404011371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3478083171027063488060645 652140594567574404011371)
    ·
      refine ⟨978210891851361606017057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 652140594567574404011371 978210891851361606017057)
      ·
        refine ⟨733658168888521204512793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 978210891851361606017057 733658168888521204512793)
        ·
          refine ⟨550243626666390903384595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 733658168888521204512793 550243626666390903384595)
          ·
            refine ⟨825365439999586355076893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 550243626666390903384595 825365439999586355076893)
            ·
              refine ⟨309512039999844883153835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 825365439999586355076893 309512039999844883153835)
              ·
                refine ⟨464268059999767324730753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 309512039999844883153835 464268059999767324730753)
                ·
                  refine ⟨348201044999825493548065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 464268059999767324730753 348201044999825493548065)
                  ·
                    refine ⟨261150783749869120161049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 348201044999825493548065 261150783749869120161049)
                    ·
                      refine ⟨195863087812401840120787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 261150783749869120161049 195863087812401840120787)
                      ·
                        rfl

theorem cell23_381442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 1, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 1, 3, 1, 2, 2, 2].length) (baseStart_381442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_381442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_381442 prefixEnd_381442 := by exact prefixLift 381442
  have htrace : WordTrace (prefixWord ++ tailWord_381442) baseStart_381442 baseEnd_381442 := by
    simpa [prefixWord, tailWord_381442, baseEnd_381442] using wordTrace_append hprefix tailTrace_381442
  have hstable : (prefixWord ++ tailWord_381442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_381442).length < 2 ^ (prefixWord ++ tailWord_381442).sum := by decide
  have hdescent : baseEnd_381442 < baseStart_381442 := by decide
  rcases family_descends (prefixWord ++ tailWord_381442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_381457 : List Nat := [1, 2, 2, 1, 1, 2, 2, 3, 5, 4]
def baseStart_381457 : Nat := 118140960795 + 381457 * 2 ^ 59
def prefixEnd_381457 : Nat := 4983230072969 + 3 ^ 40 * 381457 * 2
def baseEnd_381457 : Nat := 65290263340739760477739

theorem tailTrace_381457 : CollatzResearch.WordTrace tailWord_381457 prefixEnd_381457 65290263340739760477739 := by
  unfold tailWord_381457
  simp only [CollatzResearch.WordTrace]
  refine ⟨13912879779053911514038625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9275253186035941009359083 13912879779053911514038625)
  ·
    refine ⟨10434659834290433635528969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13912879779053911514038625 10434659834290433635528969)
    ·
      refine ⟨7825994875717825226646727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10434659834290433635528969 7825994875717825226646727)
      ·
        refine ⟨11738992313576737839970091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7825994875717825226646727 11738992313576737839970091)
        ·
          refine ⟨17608488470365106759955137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11738992313576737839970091 17608488470365106759955137)
          ·
            refine ⟨13206366352773830069966353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17608488470365106759955137 13206366352773830069966353)
            ·
              refine ⟨9904774764580372552474765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13206366352773830069966353 9904774764580372552474765)
              ·
                refine ⟨3714290536717639707178037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9904774764580372552474765 3714290536717639707178037)
                ·
                  refine ⟨348214737817278722547941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3714290536717639707178037 348214737817278722547941)
                  ·
                    refine ⟨65290263340739760477739, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 348214737817278722547941 65290263340739760477739)
                    ·
                      rfl

theorem cell23_381457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 3, 5, 4].length) (baseStart_381457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_381457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_381457 prefixEnd_381457 := by exact prefixLift 381457
  have htrace : WordTrace (prefixWord ++ tailWord_381457) baseStart_381457 baseEnd_381457 := by
    simpa [prefixWord, tailWord_381457, baseEnd_381457] using wordTrace_append hprefix tailTrace_381457
  have hstable : (prefixWord ++ tailWord_381457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_381457).length < 2 ^ (prefixWord ++ tailWord_381457).sum := by decide
  have hdescent : baseEnd_381457 < baseStart_381457 := by decide
  rcases family_descends (prefixWord ++ tailWord_381457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_381467 : List Nat := [1, 1, 1, 1, 1, 1, 3, 1, 8, 2, 3]
def baseStart_381467 : Nat := 118140960795 + 381467 * 2 ^ 59
def prefixEnd_381467 : Nat := 4983230072969 + 3 ^ 40 * 381467 * 2
def baseEnd_381467 : Nat := 195875924828764242308171

theorem tailTrace_381467 : CollatzResearch.WordTrace tailWord_381467 prefixEnd_381467 195875924828764242308171 := by
  unfold tailWord_381467
  simp only [CollatzResearch.WordTrace]
  refine ⟨13913244509017683221902655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9275496339345122147935103 13913244509017683221902655)
  ·
    refine ⟨20869866763526524832853983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13913244509017683221902655 20869866763526524832853983)
    ·
      refine ⟨31304800145289787249280975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20869866763526524832853983 31304800145289787249280975)
      ·
        refine ⟨46957200217934680873921463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31304800145289787249280975 46957200217934680873921463)
        ·
          refine ⟨70435800326902021310882195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46957200217934680873921463 70435800326902021310882195)
          ·
            refine ⟨105653700490353031966323293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70435800326902021310882195 105653700490353031966323293)
            ·
              refine ⟨39620137683882386987371235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 105653700490353031966323293 39620137683882386987371235)
              ·
                refine ⟨59430206525823580481056853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39620137683882386987371235 59430206525823580481056853)
                ·
                  refine ⟨696447732724495083762385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 59430206525823580481056853 696447732724495083762385)
                  ·
                    refine ⟨522335799543371312821789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 696447732724495083762385 522335799543371312821789)
                    ·
                      refine ⟨195875924828764242308171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 522335799543371312821789 195875924828764242308171)
                      ·
                        rfl

theorem cell23_381467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 8, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 8, 2, 3].length) (baseStart_381467 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_381467 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_381467 prefixEnd_381467 := by exact prefixLift 381467
  have htrace : WordTrace (prefixWord ++ tailWord_381467) baseStart_381467 baseEnd_381467 := by
    simpa [prefixWord, tailWord_381467, baseEnd_381467] using wordTrace_append hprefix tailTrace_381467
  have hstable : (prefixWord ++ tailWord_381467).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_381467).length < 2 ^ (prefixWord ++ tailWord_381467).sum := by decide
  have hdescent : baseEnd_381467 < baseStart_381467 := by decide
  rcases family_descends (prefixWord ++ tailWord_381467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_381504 : List Nat := [2, 1, 1, 2, 2, 2, 6, 1, 6]
def baseStart_381504 : Nat := 118140960795 + 381504 * 2 ^ 59
def prefixEnd_381504 : Nat := 4983230072969 + 3 ^ 40 * 381504 * 2
def baseEnd_381504 : Nat := 21766102623664510838389

theorem tailTrace_381504 : CollatzResearch.WordTrace tailWord_381504 prefixEnd_381504 21766102623664510838389 := by
  unfold tailWord_381504
  simp only [CollatzResearch.WordTrace]
  refine ⟨6957297004941819270499783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9276396006589092360666377 6957297004941819270499783)
  ·
    refine ⟨10435945507412728905749675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6957297004941819270499783 10435945507412728905749675)
    ·
      refine ⟨15653918261119093358624513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10435945507412728905749675 15653918261119093358624513)
      ·
        refine ⟨11740438695839320018968385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15653918261119093358624513 11740438695839320018968385)
        ·
          refine ⟨8805329021879490014226289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11740438695839320018968385 8805329021879490014226289)
          ·
            refine ⟨6603996766409617510669717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8805329021879490014226289 6603996766409617510669717)
            ·
              refine ⟨309562348425450820812643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 6603996766409617510669717 309562348425450820812643)
              ·
                refine ⟨464343522638176231218965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 309562348425450820812643 464343522638176231218965)
                ·
                  refine ⟨21766102623664510838389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 464343522638176231218965 21766102623664510838389)
                  ·
                    rfl

theorem cell23_381504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 6, 1, 6].length) (baseStart_381504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_381504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_381504 prefixEnd_381504 := by exact prefixLift 381504
  have htrace : WordTrace (prefixWord ++ tailWord_381504) baseStart_381504 baseEnd_381504 := by
    simpa [prefixWord, tailWord_381504, baseEnd_381504] using wordTrace_append hprefix tailTrace_381504
  have hstable : (prefixWord ++ tailWord_381504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_381504).length < 2 ^ (prefixWord ++ tailWord_381504).sum := by decide
  have hdescent : baseEnd_381504 < baseStart_381504 := by decide
  rcases family_descends (prefixWord ++ tailWord_381504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_381538 : List Nat := [3, 3, 2, 3, 1, 1, 2, 2, 6]
def baseStart_381538 : Nat := 118140960795 + 381538 * 2 ^ 59
def prefixEnd_381538 : Nat := 4983230072969 + 3 ^ 40 * 381538 * 2
def baseEnd_381538 : Nat := 21768042439470384946705

theorem tailTrace_381538 : CollatzResearch.WordTrace tailWord_381538 prefixEnd_381538 21768042439470384946705 := by
  unfold tailWord_381538
  simp only [CollatzResearch.WordTrace]
  refine ⟨3478958522940115586934317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9277222727840308231824845 3478958522940115586934317)
  ·
    refine ⟨1304609446102543345100369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3478958522940115586934317 1304609446102543345100369)
    ·
      refine ⟨978457084576907508825277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1304609446102543345100369 978457084576907508825277)
      ·
        refine ⟨366921406716340315809479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 978457084576907508825277 366921406716340315809479)
        ·
          refine ⟨550382110074510473714219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 366921406716340315809479 550382110074510473714219)
          ·
            refine ⟨825573165111765710571329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 550382110074510473714219 825573165111765710571329)
            ·
              refine ⟨619179873833824282928497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 825573165111765710571329 619179873833824282928497)
              ·
                refine ⟨464384905375368212196373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 619179873833824282928497 464384905375368212196373)
                ·
                  refine ⟨21768042439470384946705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 464384905375368212196373 21768042439470384946705)
                  ·
                    rfl

theorem cell23_381538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 1, 2, 2, 6].length) (baseStart_381538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_381538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_381538 prefixEnd_381538 := by exact prefixLift 381538
  have htrace : WordTrace (prefixWord ++ tailWord_381538) baseStart_381538 baseEnd_381538 := by
    simpa [prefixWord, tailWord_381538, baseEnd_381538] using wordTrace_append hprefix tailTrace_381538
  have hstable : (prefixWord ++ tailWord_381538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_381538).length < 2 ^ (prefixWord ++ tailWord_381538).sum := by decide
  have hdescent : baseEnd_381538 < baseStart_381538 := by decide
  rcases family_descends (prefixWord ++ tailWord_381538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_381571 : List Nat := [1, 1, 1, 3, 3, 1, 3, 1, 5, 2, 2]
def baseStart_381571 : Nat := 118140960795 + 381571 * 2 ^ 59
def prefixEnd_381571 : Nat := 4983230072969 + 3 ^ 40 * 381571 * 2
def baseEnd_381571 : Nat := 195929326816831835407693

theorem tailTrace_381571 : CollatzResearch.WordTrace tailWord_381571 prefixEnd_381571 195929326816831835407693 := by
  unfold tailWord_381571
  simp only [CollatzResearch.WordTrace]
  refine ⟨13917037700640908983688567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9278025133760605989125711 13917037700640908983688567)
  ·
    refine ⟨20875556550961363475532851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13917037700640908983688567 20875556550961363475532851)
    ·
      refine ⟨31313334826442045213299277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20875556550961363475532851 31313334826442045213299277)
      ·
        refine ⟨11742500559915766954987229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31313334826442045213299277 11742500559915766954987229)
        ·
          refine ⟨4403437709968412608120211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11742500559915766954987229 4403437709968412608120211)
          ·
            refine ⟨6605156564952618912180317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4403437709968412608120211 6605156564952618912180317)
            ·
              refine ⟨2476933711857232092067619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6605156564952618912180317 2476933711857232092067619)
              ·
                refine ⟨3715400567785848138101429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2476933711857232092067619 3715400567785848138101429)
                ·
                  refine ⟨348318803229923262947009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3715400567785848138101429 348318803229923262947009)
                  ·
                    refine ⟨261239102422442447210257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 348318803229923262947009 261239102422442447210257)
                    ·
                      refine ⟨195929326816831835407693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 261239102422442447210257 195929326816831835407693)
                      ·
                        rfl

theorem cell23_381571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 3, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 3, 1, 5, 2, 2].length) (baseStart_381571 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_381571 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_381571 prefixEnd_381571 := by exact prefixLift 381571
  have htrace : WordTrace (prefixWord ++ tailWord_381571) baseStart_381571 baseEnd_381571 := by
    simpa [prefixWord, tailWord_381571, baseEnd_381571] using wordTrace_append hprefix tailTrace_381571
  have hstable : (prefixWord ++ tailWord_381571).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_381571).length < 2 ^ (prefixWord ++ tailWord_381571).sum := by decide
  have hdescent : baseEnd_381571 < baseStart_381571 := by decide
  rcases family_descends (prefixWord ++ tailWord_381571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_381588 : List Nat := [2, 4, 2, 2, 1, 2, 1, 3, 1, 1, 4]
def baseStart_381588 : Nat := 118140960795 + 381588 * 2 ^ 59
def prefixEnd_381588 : Nat := 4983230072969 + 3 ^ 40 * 381588 * 2
def baseEnd_381588 : Nat := 195938055987958268895115

theorem tailTrace_381588 : CollatzResearch.WordTrace tailWord_381588 prefixEnd_381588 195938055987958268895115 := by
  unfold tailWord_381588
  simp only [CollatzResearch.WordTrace]
  refine ⟨6958828870789660443528709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9278438494386213924704945 6958828870789660443528709)
  ·
    refine ⟨1304780413273061333161633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6958828870789660443528709 1304780413273061333161633)
    ·
      refine ⟨978585309954795999871225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1304780413273061333161633 978585309954795999871225)
      ·
        refine ⟨733938982466096999903419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 978585309954795999871225 733938982466096999903419)
        ·
          refine ⟨1100908473699145499855129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 733938982466096999903419 1100908473699145499855129)
          ·
            refine ⟨825681355274359124891347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1100908473699145499855129 825681355274359124891347)
            ·
              refine ⟨1238522032911538687337021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 825681355274359124891347 1238522032911538687337021)
              ·
                refine ⟨464445762341827007751383, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1238522032911538687337021 464445762341827007751383)
                ·
                  refine ⟨696668643512740511627075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 464445762341827007751383 696668643512740511627075)
                  ·
                    refine ⟨1045002965269110767440613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 696668643512740511627075 1045002965269110767440613)
                    ·
                      refine ⟨195938055987958268895115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1045002965269110767440613 195938055987958268895115)
                      ·
                        rfl

theorem cell23_381588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 2, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 2, 1, 3, 1, 1, 4].length) (baseStart_381588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_381588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_381588 prefixEnd_381588 := by exact prefixLift 381588
  have htrace : WordTrace (prefixWord ++ tailWord_381588) baseStart_381588 baseEnd_381588 := by
    simpa [prefixWord, tailWord_381588, baseEnd_381588] using wordTrace_append hprefix tailTrace_381588
  have hstable : (prefixWord ++ tailWord_381588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_381588).length < 2 ^ (prefixWord ++ tailWord_381588).sum := by decide
  have hdescent : baseEnd_381588 < baseStart_381588 := by decide
  rcases family_descends (prefixWord ++ tailWord_381588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_381591 : List Nat := [1, 1, 3, 3, 2, 1, 3, 3, 1, 2, 3]
def baseStart_381591 : Nat := 118140960795 + 381591 * 2 ^ 59
def prefixEnd_381591 : Nat := 4983230072969 + 3 ^ 40 * 381591 * 2
def baseEnd_381591 : Nat := 195939596429921757157601

theorem tailTrace_381591 : CollatzResearch.WordTrace tailWord_381591 prefixEnd_381591 195939596429921757157601 := by
  unfold tailWord_381591
  simp only [CollatzResearch.WordTrace]
  refine ⟨13917767160568452399416627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9278511440378968266277751 13917767160568452399416627)
  ·
    refine ⟨20876650740852678599124941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13917767160568452399416627 20876650740852678599124941)
    ·
      refine ⟨7828744027819754474671853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20876650740852678599124941 7828744027819754474671853)
      ·
        refine ⟨2935779010432407928001945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7828744027819754474671853 2935779010432407928001945)
        ·
          refine ⟨2201834257824305946001459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2935779010432407928001945 2201834257824305946001459)
          ·
            refine ⟨3302751386736458919002189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2201834257824305946001459 3302751386736458919002189)
            ·
              refine ⟨1238531770026172094625821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3302751386736458919002189 1238531770026172094625821)
              ·
                refine ⟨464449413759814535484683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1238531770026172094625821 464449413759814535484683)
                ·
                  refine ⟨696674120639721803227025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 464449413759814535484683 696674120639721803227025)
                  ·
                    refine ⟨522505590479791352420269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 696674120639721803227025 522505590479791352420269)
                    ·
                      refine ⟨195939596429921757157601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 522505590479791352420269 195939596429921757157601)
                      ·
                        rfl

theorem cell23_381591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 3, 3, 1, 2, 3].length) (baseStart_381591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_381591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_381591 prefixEnd_381591 := by exact prefixLift 381591
  have htrace : WordTrace (prefixWord ++ tailWord_381591) baseStart_381591 baseEnd_381591 := by
    simpa [prefixWord, tailWord_381591, baseEnd_381591] using wordTrace_append hprefix tailTrace_381591
  have hstable : (prefixWord ++ tailWord_381591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_381591).length < 2 ^ (prefixWord ++ tailWord_381591).sum := by decide
  have hdescent : baseEnd_381591 < baseStart_381591 := by decide
  rcases family_descends (prefixWord ++ tailWord_381591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_381664 : List Nat := [2, 1, 1, 3, 1, 2, 1, 3, 2, 4, 3]
def baseStart_381664 : Nat := 118140960795 + 381664 * 2 ^ 59
def prefixEnd_381664 : Nat := 4983230072969 + 3 ^ 40 * 381664 * 2
def baseEnd_381664 : Nat := 195977080517699971544765

theorem tailTrace_381664 : CollatzResearch.WordTrace tailWord_381664 prefixEnd_381664 195977080517699971544765 := by
  unfold tailWord_381664
  simp only [CollatzResearch.WordTrace]
  refine ⟨6960214844651992933412023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9280286459535990577882697 6960214844651992933412023)
  ·
    refine ⟨10440322266977989400118035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6960214844651992933412023 10440322266977989400118035)
    ·
      refine ⟨15660483400466984100177053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10440322266977989400118035 15660483400466984100177053)
      ·
        refine ⟨5872681275175119037566395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15660483400466984100177053 5872681275175119037566395)
        ·
          refine ⟨8809021912762678556349593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5872681275175119037566395 8809021912762678556349593)
          ·
            refine ⟨6606766434572008917262195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8809021912762678556349593 6606766434572008917262195)
            ·
              refine ⟨9910149651858013375893293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6606766434572008917262195 9910149651858013375893293)
              ·
                refine ⟨3716306119446755015959985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9910149651858013375893293 3716306119446755015959985)
                ·
                  refine ⟨2787229589585066261969989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3716306119446755015959985 2787229589585066261969989)
                  ·
                    refine ⟨522605548047199924119373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2787229589585066261969989 522605548047199924119373)
                    ·
                      refine ⟨195977080517699971544765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 522605548047199924119373 195977080517699971544765)
                      ·
                        rfl

theorem cell23_381664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 3, 2, 4, 3].length) (baseStart_381664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_381664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_381664 prefixEnd_381664 := by exact prefixLift 381664
  have htrace : WordTrace (prefixWord ++ tailWord_381664) baseStart_381664 baseEnd_381664 := by
    simpa [prefixWord, tailWord_381664, baseEnd_381664] using wordTrace_append hprefix tailTrace_381664
  have hstable : (prefixWord ++ tailWord_381664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_381664).length < 2 ^ (prefixWord ++ tailWord_381664).sum := by decide
  have hdescent : baseEnd_381664 < baseStart_381664 := by decide
  rcases family_descends (prefixWord ++ tailWord_381664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_381672 : List Nat := [2, 1, 4, 1, 4, 2, 2, 1, 2, 1, 3]
def baseStart_381672 : Nat := 118140960795 + 381672 * 2 ^ 59
def prefixEnd_381672 : Nat := 4983230072969 + 3 ^ 40 * 381672 * 2
def baseEnd_381672 : Nat := 195981188362935940244729

theorem tailTrace_381672 : CollatzResearch.WordTrace tailWord_381672 prefixEnd_381672 195981188362935940244729 := by
  unfold tailWord_381672
  simp only [CollatzResearch.WordTrace]
  refine ⟨6960360736637501616557635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9280480982183335488743513 6960360736637501616557635)
  ·
    refine ⟨10440541104956252424836453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6960360736637501616557635 10440541104956252424836453)
    ·
      refine ⟨1957601457179297329656835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10440541104956252424836453 1957601457179297329656835)
      ·
        refine ⟨2936402185768945994485253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1957601457179297329656835 2936402185768945994485253)
        ·
          refine ⟨550575409831677373965985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2936402185768945994485253 550575409831677373965985)
          ·
            refine ⟨412931557373758030474489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 550575409831677373965985 412931557373758030474489)
            ·
              refine ⟨309698668030318522855867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 412931557373758030474489 309698668030318522855867)
              ·
                refine ⟨464548002045477784283801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 309698668030318522855867 464548002045477784283801)
                ·
                  refine ⟨348411001534108338212851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 464548002045477784283801 348411001534108338212851)
                  ·
                    refine ⟨522616502301162507319277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 348411001534108338212851 522616502301162507319277)
                    ·
                      refine ⟨195981188362935940244729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 522616502301162507319277 195981188362935940244729)
                      ·
                        rfl

theorem cell23_381672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 2, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 2, 2, 1, 2, 1, 3].length) (baseStart_381672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_381672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_381672 prefixEnd_381672 := by exact prefixLift 381672
  have htrace : WordTrace (prefixWord ++ tailWord_381672) baseStart_381672 baseEnd_381672 := by
    simpa [prefixWord, tailWord_381672, baseEnd_381672] using wordTrace_append hprefix tailTrace_381672
  have hstable : (prefixWord ++ tailWord_381672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_381672).length < 2 ^ (prefixWord ++ tailWord_381672).sum := by decide
  have hdescent : baseEnd_381672 < baseStart_381672 := by decide
  rcases family_descends (prefixWord ++ tailWord_381672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_381674 : List Nat := [3, 1, 3, 1, 1, 1, 1, 3, 1, 4, 4]
def baseStart_381674 : Nat := 118140960795 + 381674 * 2 ^ 59
def prefixEnd_381674 : Nat := 4983230072969 + 3 ^ 40 * 381674 * 2
def baseEnd_381674 : Nat := 195982215324244932419719

theorem tailTrace_381674 : CollatzResearch.WordTrace tailWord_381674 prefixEnd_381674 195982215324244932419719 := by
  unfold tailWord_381674
  simp only [CollatzResearch.WordTrace]
  refine ⟨3480198604816939393672019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9280529612845171716458717 3480198604816939393672019)
  ·
    refine ⟨5220297907225409090508029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3480198604816939393672019 5220297907225409090508029)
    ·
      refine ⟨1957611715209528408940511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5220297907225409090508029 1957611715209528408940511)
      ·
        refine ⟨2936417572814292613410767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1957611715209528408940511 2936417572814292613410767)
        ·
          refine ⟨4404626359221438920116151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2936417572814292613410767 4404626359221438920116151)
          ·
            refine ⟨6606939538832158380174227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4404626359221438920116151 6606939538832158380174227)
            ·
              refine ⟨9910409308248237570261341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6606939538832158380174227 9910409308248237570261341)
              ·
                refine ⟨3716403490593089088848003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9910409308248237570261341 3716403490593089088848003)
                ·
                  refine ⟨5574605235889633633272005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3716403490593089088848003 5574605235889633633272005)
                  ·
                    refine ⟨1045238481729306306238501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5574605235889633633272005 1045238481729306306238501)
                    ·
                      refine ⟨195982215324244932419719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1045238481729306306238501 195982215324244932419719)
                      ·
                        rfl

theorem cell23_381674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 3, 1, 4, 4].length) (baseStart_381674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_381674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_381674 prefixEnd_381674 := by exact prefixLift 381674
  have htrace : WordTrace (prefixWord ++ tailWord_381674) baseStart_381674 baseEnd_381674 := by
    simpa [prefixWord, tailWord_381674, baseEnd_381674] using wordTrace_append hprefix tailTrace_381674
  have hstable : (prefixWord ++ tailWord_381674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_381674).length < 2 ^ (prefixWord ++ tailWord_381674).sum := by decide
  have hdescent : baseEnd_381674 < baseStart_381674 := by decide
  rcases family_descends (prefixWord ++ tailWord_381674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_381748 : List Nat := [2, 5, 1, 1, 3, 1, 1, 1, 1, 7]
def baseStart_381748 : Nat := 118140960795 + 381748 * 2 ^ 59
def prefixEnd_381748 : Nat := 4983230072969 + 3 ^ 40 * 381748 * 2
def baseEnd_381748 : Nat := 65340070964225880964793

theorem tailTrace_381748 : CollatzResearch.WordTrace tailWord_381748 prefixEnd_381748 65340070964225880964793 := by
  unfold tailWord_381748
  simp only [CollatzResearch.WordTrace]
  refine ⟨6961746710499834106440949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9282328947333112141921265 6961746710499834106440949)
  ·
    refine ⟨652663754109359447478839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 6961746710499834106440949 652663754109359447478839)
    ·
      refine ⟨978995631164039171218259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 652663754109359447478839 978995631164039171218259)
      ·
        refine ⟨1468493446746058756827389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 978995631164039171218259 1468493446746058756827389)
        ·
          refine ⟨550685042529772033810271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1468493446746058756827389 550685042529772033810271)
          ·
            refine ⟨826027563794658050715407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 550685042529772033810271 826027563794658050715407)
            ·
              refine ⟨1239041345691987076073111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 826027563794658050715407 1239041345691987076073111)
              ·
                refine ⟨1858562018537980614109667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1239041345691987076073111 1858562018537980614109667)
                ·
                  refine ⟨2787843027806970921164501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1858562018537980614109667 2787843027806970921164501)
                  ·
                    refine ⟨65340070964225880964793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 2787843027806970921164501 65340070964225880964793)
                    ·
                      rfl

theorem cell23_381748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 1, 1, 1, 1, 7].length) (baseStart_381748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_381748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_381748 prefixEnd_381748 := by exact prefixLift 381748
  have htrace : WordTrace (prefixWord ++ tailWord_381748) baseStart_381748 baseEnd_381748 := by
    simpa [prefixWord, tailWord_381748, baseEnd_381748] using wordTrace_append hprefix tailTrace_381748
  have hstable : (prefixWord ++ tailWord_381748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_381748).length < 2 ^ (prefixWord ++ tailWord_381748).sum := by decide
  have hdescent : baseEnd_381748 < baseStart_381748 := by decide
  rcases family_descends (prefixWord ++ tailWord_381748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_381751 : List Nat := [1, 1, 3, 1, 2, 1, 3, 2, 1, 6, 2]
def baseStart_381751 : Nat := 118140960795 + 381751 * 2 ^ 59
def prefixEnd_381751 : Nat := 4983230072969 + 3 ^ 40 * 381751 * 2
def baseEnd_381751 : Nat := 196021753334641131156865

theorem tailTrace_381751 : CollatzResearch.WordTrace tailWord_381751 prefixEnd_381751 196021753334641131156865 := by
  unfold tailWord_381751
  simp only [CollatzResearch.WordTrace]
  refine ⟨13923602839988799725241107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9282401893325866483494071 13923602839988799725241107)
  ·
    refine ⟨20885404259983199587861661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13923602839988799725241107 20885404259983199587861661)
    ·
      refine ⟨7832026597493699845448123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20885404259983199587861661 7832026597493699845448123)
      ·
        refine ⟨11748039896240549768172185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7832026597493699845448123 11748039896240549768172185)
        ·
          refine ⟨8811029922180412326129139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11748039896240549768172185 8811029922180412326129139)
          ·
            refine ⟨13216544883270618489193709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8811029922180412326129139 13216544883270618489193709)
            ·
              refine ⟨4956204331226481933447641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13216544883270618489193709 4956204331226481933447641)
              ·
                refine ⟨3717153248419861450085731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4956204331226481933447641 3717153248419861450085731)
                ·
                  refine ⟨5575729872629792175128597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3717153248419861450085731 5575729872629792175128597)
                  ·
                    refine ⟨261362337779521508209153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5575729872629792175128597 261362337779521508209153)
                    ·
                      refine ⟨196021753334641131156865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 261362337779521508209153 196021753334641131156865)
                      ·
                        rfl

theorem cell23_381751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 3, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 3, 2, 1, 6, 2].length) (baseStart_381751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_381751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_381751 prefixEnd_381751 := by exact prefixLift 381751
  have htrace : WordTrace (prefixWord ++ tailWord_381751) baseStart_381751 baseEnd_381751 := by
    simpa [prefixWord, tailWord_381751, baseEnd_381751] using wordTrace_append hprefix tailTrace_381751
  have hstable : (prefixWord ++ tailWord_381751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_381751).length < 2 ^ (prefixWord ++ tailWord_381751).sum := by decide
  have hdescent : baseEnd_381751 < baseStart_381751 := by decide
  rcases family_descends (prefixWord ++ tailWord_381751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_381778 : List Nat := [3, 2, 2, 1, 1, 2, 4, 1, 3, 4]
def baseStart_381778 : Nat := 118140960795 + 381778 * 2 ^ 59
def prefixEnd_381778 : Nat := 4983230072969 + 3 ^ 40 * 381778 * 2
def baseEnd_381778 : Nat := 65345205770770841839747

theorem tailTrace_381778 : CollatzResearch.WordTrace tailWord_381778 prefixEnd_381778 65345205770770841839747 := by
  unfold tailWord_381778
  simp only [CollatzResearch.WordTrace]
  refine ⟨3481146902722745834118497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9283058407260655557649325 3481146902722745834118497)
  ·
    refine ⟨2610860177042059375588873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3481146902722745834118497 2610860177042059375588873)
    ·
      refine ⟨1958145132781544531691655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2610860177042059375588873 1958145132781544531691655)
      ·
        refine ⟨2937217699172316797537483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1958145132781544531691655 2937217699172316797537483)
        ·
          refine ⟨4405826548758475196306225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2937217699172316797537483 4405826548758475196306225)
          ·
            refine ⟨3304369911568856397229669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4405826548758475196306225 3304369911568856397229669)
            ·
              refine ⟨619569358419160574480563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3304369911568856397229669 619569358419160574480563)
              ·
                refine ⟨929354037628740861720845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 619569358419160574480563 929354037628740861720845)
                ·
                  refine ⟨348507764110777823145317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 929354037628740861720845 348507764110777823145317)
                  ·
                    refine ⟨65345205770770841839747, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 348507764110777823145317 65345205770770841839747)
                    ·
                      rfl

theorem cell23_381778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 4, 1, 3, 4].length) (baseStart_381778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_381778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_381778 prefixEnd_381778 := by exact prefixLift 381778
  have htrace : WordTrace (prefixWord ++ tailWord_381778) baseStart_381778 baseEnd_381778 := by
    simpa [prefixWord, tailWord_381778, baseEnd_381778] using wordTrace_append hprefix tailTrace_381778
  have hstable : (prefixWord ++ tailWord_381778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_381778).length < 2 ^ (prefixWord ++ tailWord_381778).sum := by decide
  have hdescent : baseEnd_381778 < baseStart_381778 := by decide
  rcases family_descends (prefixWord ++ tailWord_381778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_381788 : List Nat := [2, 2, 4, 2, 1, 1, 1, 2, 1, 4, 3]
def baseStart_381788 : Nat := 118140960795 + 381788 * 2 ^ 59
def prefixEnd_381788 : Nat := 4983230072969 + 3 ^ 40 * 381788 * 2
def baseEnd_381788 : Nat := 196040752118857486394195

theorem tailTrace_381788 : CollatzResearch.WordTrace tailWord_381788 prefixEnd_381788 196040752118857486394195 := by
  unfold tailWord_381788
  simp only [CollatzResearch.WordTrace]
  refine ⟨6962476170427377522169009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9283301560569836696225345 6962476170427377522169009)
  ·
    refine ⟨5221857127820533141626757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6962476170427377522169009 5221857127820533141626757)
    ·
      refine ⟨979098211466349964055017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5221857127820533141626757 979098211466349964055017)
      ·
        refine ⟨734323658599762473041263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 979098211466349964055017 734323658599762473041263)
        ·
          refine ⟨1101485487899643709561895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 734323658599762473041263 1101485487899643709561895)
          ·
            refine ⟨1652228231849465564342843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1101485487899643709561895 1652228231849465564342843)
            ·
              refine ⟨2478342347774198346514265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1652228231849465564342843 2478342347774198346514265)
              ·
                refine ⟨1858756760830648759885699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2478342347774198346514265 1858756760830648759885699)
                ·
                  refine ⟨2788135141245973139828549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1858756760830648759885699 2788135141245973139828549)
                  ·
                    refine ⟨522775338983619963717853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2788135141245973139828549 522775338983619963717853)
                    ·
                      refine ⟨196040752118857486394195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 522775338983619963717853 196040752118857486394195)
                      ·
                        rfl

theorem cell23_381788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 1, 2, 1, 4, 3].length) (baseStart_381788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_381788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_381788 prefixEnd_381788 := by exact prefixLift 381788
  have htrace : WordTrace (prefixWord ++ tailWord_381788) baseStart_381788 baseEnd_381788 := by
    simpa [prefixWord, tailWord_381788, baseEnd_381788] using wordTrace_append hprefix tailTrace_381788
  have hstable : (prefixWord ++ tailWord_381788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_381788).length < 2 ^ (prefixWord ++ tailWord_381788).sum := by decide
  have hdescent : baseEnd_381788 < baseStart_381788 := by decide
  rcases family_descends (prefixWord ++ tailWord_381788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_381822 : List Nat := [4, 2, 3, 1, 2, 1, 1, 2, 2, 2, 3]
def baseStart_381822 : Nat := 118140960795 + 381822 * 2 ^ 59
def prefixEnd_381822 : Nat := 4983230072969 + 3 ^ 40 * 381822 * 2
def baseEnd_381822 : Nat := 196058210461110353369039

theorem tailTrace_381822 : CollatzResearch.WordTrace tailWord_381822 prefixEnd_381822 196058210461110353369039 := by
  unfold tailWord_381822
  simp only [CollatzResearch.WordTrace]
  refine ⟨1740774052841447356384465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9284128281821052567383813 1740774052841447356384465)
  ·
    refine ⟨1305580539631085517288349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1740774052841447356384465 1305580539631085517288349)
    ·
      refine ⟨489592702361657068983131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1305580539631085517288349 489592702361657068983131)
      ·
        refine ⟨734389053542485603474697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 489592702361657068983131 734389053542485603474697)
        ·
          refine ⟨550791790156864202606023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 734389053542485603474697 550791790156864202606023)
          ·
            refine ⟨826187685235296303909035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 550791790156864202606023 826187685235296303909035)
            ·
              refine ⟨1239281527852944455863553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 826187685235296303909035 1239281527852944455863553)
              ·
                refine ⟨929461145889708341897665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1239281527852944455863553 929461145889708341897665)
                ·
                  refine ⟨697095859417281256423249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 929461145889708341897665 697095859417281256423249)
                  ·
                    refine ⟨522821894562960942317437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 697095859417281256423249 522821894562960942317437)
                    ·
                      refine ⟨196058210461110353369039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 522821894562960942317437 196058210461110353369039)
                      ·
                        rfl

theorem cell23_381822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 1, 1, 2, 2, 2, 3].length) (baseStart_381822 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_381822 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_381822 prefixEnd_381822 := by exact prefixLift 381822
  have htrace : WordTrace (prefixWord ++ tailWord_381822) baseStart_381822 baseEnd_381822 := by
    simpa [prefixWord, tailWord_381822, baseEnd_381822] using wordTrace_append hprefix tailTrace_381822
  have hstable : (prefixWord ++ tailWord_381822).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_381822).length < 2 ^ (prefixWord ++ tailWord_381822).sum := by decide
  have hdescent : baseEnd_381822 < baseStart_381822 := by decide
  rcases family_descends (prefixWord ++ tailWord_381822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_381835 : List Nat := [1, 1, 1, 1, 4, 2, 2, 6, 1, 1, 3]
def baseStart_381835 : Nat := 118140960795 + 381835 * 2 ^ 59
def prefixEnd_381835 : Nat := 4983230072969 + 3 ^ 40 * 381835 * 2
def baseEnd_381835 : Nat := 196064885709618802506479

theorem tailTrace_381835 : CollatzResearch.WordTrace tailWord_381835 prefixEnd_381835 196064885709618802506479 := by
  unfold tailWord_381835
  simp only [CollatzResearch.WordTrace]
  refine ⟨13926666571684482071298959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9284444381122988047532639 13926666571684482071298959)
  ·
    refine ⟨20889999857526723106948439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13926666571684482071298959 20889999857526723106948439)
    ·
      refine ⟨31334999786290084660422659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20889999857526723106948439 31334999786290084660422659)
      ·
        refine ⟨47002499679435126990633989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31334999786290084660422659 47002499679435126990633989)
        ·
          refine ⟨8812968689894086310743873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 47002499679435126990633989 8812968689894086310743873)
          ·
            refine ⟨6609726517420564733057905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8812968689894086310743873 6609726517420564733057905)
            ·
              refine ⟨4957294888065423549793429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6609726517420564733057905 4957294888065423549793429)
              ·
                refine ⟨232373197878066728896567, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 4957294888065423549793429 232373197878066728896567)
                ·
                  refine ⟨348559796817100093344851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 232373197878066728896567 348559796817100093344851)
                  ·
                    refine ⟨522839695225650140017277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 348559796817100093344851 522839695225650140017277)
                    ·
                      refine ⟨196064885709618802506479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 522839695225650140017277 196064885709618802506479)
                      ·
                        rfl

theorem cell23_381835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 2, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 2, 6, 1, 1, 3].length) (baseStart_381835 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_381835 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_381835 prefixEnd_381835 := by exact prefixLift 381835
  have htrace : WordTrace (prefixWord ++ tailWord_381835) baseStart_381835 baseEnd_381835 := by
    simpa [prefixWord, tailWord_381835, baseEnd_381835] using wordTrace_append hprefix tailTrace_381835
  have hstable : (prefixWord ++ tailWord_381835).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_381835).length < 2 ^ (prefixWord ++ tailWord_381835).sum := by decide
  have hdescent : baseEnd_381835 < baseStart_381835 := by decide
  rcases family_descends (prefixWord ++ tailWord_381835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_381841 : List Nat := [1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 4]
def baseStart_381841 : Nat := 118140960795 + 381841 * 2 ^ 59
def prefixEnd_381841 : Nat := 4983230072969 + 3 ^ 40 * 381841 * 2
def baseEnd_381841 : Nat := 196067966593545779031451

theorem tailTrace_381841 : CollatzResearch.WordTrace tailWord_381841 prefixEnd_381841 196067966593545779031451 := by
  unfold tailWord_381841
  simp only [CollatzResearch.WordTrace]
  refine ⟨13926885409662745096017377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9284590273108496730678251 13926885409662745096017377)
  ·
    refine ⟨10445164057247058822013033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13926885409662745096017377 10445164057247058822013033)
    ·
      refine ⟨7833873042935294116509775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10445164057247058822013033 7833873042935294116509775)
      ·
        refine ⟨11750809564402941174764663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7833873042935294116509775 11750809564402941174764663)
        ·
          refine ⟨17626214346604411762146995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11750809564402941174764663 17626214346604411762146995)
          ·
            refine ⟨26439321519906617643220493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17626214346604411762146995 26439321519906617643220493)
            ·
              refine ⟨9914745569964981616207685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26439321519906617643220493 9914745569964981616207685)
              ·
                refine ⟨1859014794368434053038941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9914745569964981616207685 1859014794368434053038941)
                ·
                  refine ⟨697130547888162769889603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1859014794368434053038941 697130547888162769889603)
                  ·
                    refine ⟨1045695821832244154834405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 697130547888162769889603 1045695821832244154834405)
                    ·
                      refine ⟨196067966593545779031451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1045695821832244154834405 196067966593545779031451)
                      ·
                        rfl

theorem cell23_381841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 4].length) (baseStart_381841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_381841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_381841 prefixEnd_381841 := by exact prefixLift 381841
  have htrace : WordTrace (prefixWord ++ tailWord_381841) baseStart_381841 baseEnd_381841 := by
    simpa [prefixWord, tailWord_381841, baseEnd_381841] using wordTrace_append hprefix tailTrace_381841
  have hstable : (prefixWord ++ tailWord_381841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_381841).length < 2 ^ (prefixWord ++ tailWord_381841).sum := by decide
  have hdescent : baseEnd_381841 < baseStart_381841 := by decide
  rcases family_descends (prefixWord ++ tailWord_381841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_381842 : List Nat := [3, 2, 3, 2, 2, 2, 2, 1, 6]
def baseStart_381842 : Nat := 118140960795 + 381842 * 2 ^ 59
def prefixEnd_381842 : Nat := 4983230072969 + 3 ^ 40 * 381842 * 2
def baseEnd_381842 : Nat := 21785386674911141679883

theorem tailTrace_381842 : CollatzResearch.WordTrace tailWord_381842 prefixEnd_381842 21785386674911141679883 := by
  unfold tailWord_381842
  simp only [CollatzResearch.WordTrace]
  refine ⟨3481730470664780566700945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9284614588439414844535853 3481730470664780566700945)
  ·
    refine ⟨2611297852998585425025709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3481730470664780566700945 2611297852998585425025709)
    ·
      refine ⟨979236694874469534384641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2611297852998585425025709 979236694874469534384641)
      ·
        refine ⟨734427521155852150788481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 979236694874469534384641 734427521155852150788481)
        ·
          refine ⟨550820640866889113091361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 734427521155852150788481 550820640866889113091361)
          ·
            refine ⟨413115480650166834818521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 550820640866889113091361 413115480650166834818521)
            ·
              refine ⟨309836610487625126113891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 413115480650166834818521 309836610487625126113891)
              ·
                refine ⟨464754915731437689170837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 309836610487625126113891 464754915731437689170837)
                ·
                  refine ⟨21785386674911141679883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 464754915731437689170837 21785386674911141679883)
                  ·
                    rfl

theorem cell23_381842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 2, 2, 1, 6].length) (baseStart_381842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_381842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_381842 prefixEnd_381842 := by exact prefixLift 381842
  have htrace : WordTrace (prefixWord ++ tailWord_381842) baseStart_381842 baseEnd_381842 := by
    simpa [prefixWord, tailWord_381842, baseEnd_381842] using wordTrace_append hprefix tailTrace_381842
  have hstable : (prefixWord ++ tailWord_381842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_381842).length < 2 ^ (prefixWord ++ tailWord_381842).sum := by decide
  have hdescent : baseEnd_381842 < baseStart_381842 := by decide
  rcases family_descends (prefixWord ++ tailWord_381842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_381855 : List Nat := [1, 1, 2, 5, 2, 3, 1, 2, 1, 5]
def baseStart_381855 : Nat := 118140960795 + 381855 * 2 ^ 59
def prefixEnd_381855 : Nat := 4983230072969 + 3 ^ 40 * 381855 * 2
def baseEnd_381855 : Nat := 65358385107569574752129

theorem tailTrace_381855 : CollatzResearch.WordTrace tailWord_381855 prefixEnd_381855 65358385107569574752129 := by
  unfold tailWord_381855
  simp only [CollatzResearch.WordTrace]
  refine ⟨13927396031612025487027019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9284930687741350324684679 13927396031612025487027019)
  ·
    refine ⟨20891094047418038230540529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13927396031612025487027019 20891094047418038230540529)
    ·
      refine ⟨15668320535563528672905397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20891094047418038230540529 15668320535563528672905397)
      ·
        refine ⟨1468905050209080813084881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 15668320535563528672905397 1468905050209080813084881)
        ·
          refine ⟨1101678787656810609813661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1468905050209080813084881 1101678787656810609813661)
          ·
            refine ⟨413129545371303978680123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1101678787656810609813661 413129545371303978680123)
            ·
              refine ⟨619694318056955968020185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 413129545371303978680123 619694318056955968020185)
              ·
                refine ⟨464770738542716976015139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 619694318056955968020185 464770738542716976015139)
                ·
                  refine ⟨697156107814075464022709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 464770738542716976015139 697156107814075464022709)
                  ·
                    refine ⟨65358385107569574752129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 697156107814075464022709 65358385107569574752129)
                    ·
                      rfl

theorem cell23_381855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 3, 1, 2, 1, 5].length) (baseStart_381855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_381855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_381855 prefixEnd_381855 := by exact prefixLift 381855
  have htrace : WordTrace (prefixWord ++ tailWord_381855) baseStart_381855 baseEnd_381855 := by
    simpa [prefixWord, tailWord_381855, baseEnd_381855] using wordTrace_append hprefix tailTrace_381855
  have hstable : (prefixWord ++ tailWord_381855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_381855).length < 2 ^ (prefixWord ++ tailWord_381855).sum := by decide
  have hdescent : baseEnd_381855 < baseStart_381855 := by decide
  rcases family_descends (prefixWord ++ tailWord_381855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_381921 : List Nat := [1, 2, 3, 1, 2, 1, 1, 3, 2, 2, 5]
def baseStart_381921 : Nat := 118140960795 + 381921 * 2 ^ 59
def prefixEnd_381921 : Nat := 4983230072969 + 3 ^ 40 * 381921 * 2
def baseEnd_381921 : Nat := 196109045045905466031083

theorem tailTrace_381921 : CollatzResearch.WordTrace tailWord_381921 prefixEnd_381921 196109045045905466031083 := by
  unfold tailWord_381921
  simp only [CollatzResearch.WordTrace]
  refine ⟨13929803249372918758929617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9286535499581945839286411 13929803249372918758929617)
  ·
    refine ⟨10447352437029689069197213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13929803249372918758929617 10447352437029689069197213)
    ·
      refine ⟨3917757163886133400948955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10447352437029689069197213 3917757163886133400948955)
      ·
        refine ⟨5876635745829200101423433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3917757163886133400948955 5876635745829200101423433)
        ·
          refine ⟨4407476809371900076067575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5876635745829200101423433 4407476809371900076067575)
          ·
            refine ⟨6611215214057850114101363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4407476809371900076067575 6611215214057850114101363)
            ·
              refine ⟨9916822821086775171152045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6611215214057850114101363 9916822821086775171152045)
              ·
                refine ⟨3718808557907540689182017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9916822821086775171152045 3718808557907540689182017)
                ·
                  refine ⟨2789106418430655516886513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3718808557907540689182017 2789106418430655516886513)
                  ·
                    refine ⟨2091829813822991637664885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2789106418430655516886513 2091829813822991637664885)
                    ·
                      refine ⟨196109045045905466031083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2091829813822991637664885 196109045045905466031083)
                      ·
                        rfl

theorem cell23_381921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 3, 2, 2, 5].length) (baseStart_381921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_381921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_381921 prefixEnd_381921 := by exact prefixLift 381921
  have htrace : WordTrace (prefixWord ++ tailWord_381921) baseStart_381921 baseEnd_381921 := by
    simpa [prefixWord, tailWord_381921, baseEnd_381921] using wordTrace_append hprefix tailTrace_381921
  have hstable : (prefixWord ++ tailWord_381921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_381921).length < 2 ^ (prefixWord ++ tailWord_381921).sum := by decide
  have hdescent : baseEnd_381921 < baseStart_381921 := by decide
  rcases family_descends (prefixWord ++ tailWord_381921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_381942 : List Nat := [5, 1, 1, 1, 3, 2, 1, 1, 4, 1, 3]
def baseStart_381942 : Nat := 118140960795 + 381942 * 2 ^ 59
def prefixEnd_381942 : Nat := 4983230072969 + 3 ^ 40 * 381942 * 2
def baseEnd_381942 : Nat := 196119828139649883868487

theorem tailTrace_381942 : CollatzResearch.WordTrace tailWord_381942 prefixEnd_381942 196119828139649883868487 := by
  unfold tailWord_381942
  simp only [CollatzResearch.WordTrace]
  refine ⟨870660573893552459090255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 9287046121531226230296053 870660573893552459090255)
  ·
    refine ⟨1305990860840328688635383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 870660573893552459090255 1305990860840328688635383)
    ·
      refine ⟨1958986291260493032953075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1305990860840328688635383 1958986291260493032953075)
      ·
        refine ⟨2938479436890739549429613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1958986291260493032953075 2938479436890739549429613)
        ·
          refine ⟨1101929788834027331036105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2938479436890739549429613 1101929788834027331036105)
          ·
            refine ⟨826447341625520498277079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1101929788834027331036105 826447341625520498277079)
            ·
              refine ⟨1239671012438280747415619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 826447341625520498277079 1239671012438280747415619)
              ·
                refine ⟨1859506518657421121123429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1239671012438280747415619 1859506518657421121123429)
                ·
                  refine ⟨348657472248266460210643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1859506518657421121123429 348657472248266460210643)
                  ·
                    refine ⟨522986208372399690315965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 348657472248266460210643 522986208372399690315965)
                    ·
                      refine ⟨196119828139649883868487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 522986208372399690315965 196119828139649883868487)
                      ·
                        rfl

theorem cell23_381942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 2, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 2, 1, 1, 4, 1, 3].length) (baseStart_381942 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_381942 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_381942 prefixEnd_381942 := by exact prefixLift 381942
  have htrace : WordTrace (prefixWord ++ tailWord_381942) baseStart_381942 baseEnd_381942 := by
    simpa [prefixWord, tailWord_381942, baseEnd_381942] using wordTrace_append hprefix tailTrace_381942
  have hstable : (prefixWord ++ tailWord_381942).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_381942).length < 2 ^ (prefixWord ++ tailWord_381942).sum := by decide
  have hdescent : baseEnd_381942 < baseStart_381942 := by decide
  rcases family_descends (prefixWord ++ tailWord_381942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_381951 : List Nat := [1, 1, 2, 2, 1, 2, 1, 1, 6, 1, 5]
def baseStart_381951 : Nat := 118140960795 + 381951 * 2 ^ 59
def prefixEnd_381951 : Nat := 4983230072969 + 3 ^ 40 * 381951 * 2
def baseEnd_381951 : Nat := 196124449465540348655945

theorem tailTrace_381951 : CollatzResearch.WordTrace tailWord_381951 prefixEnd_381951 196124449465540348655945 := by
  unfold tailWord_381951
  simp only [CollatzResearch.WordTrace]
  refine ⟨13930897439264233882521707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9287264959509489255014471 13930897439264233882521707)
  ·
    refine ⟨20896346158896350823782561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13930897439264233882521707 20896346158896350823782561)
    ·
      refine ⟨15672259619172263117836921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20896346158896350823782561 15672259619172263117836921)
      ·
        refine ⟨11754194714379197338377691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15672259619172263117836921 11754194714379197338377691)
        ·
          refine ⟨17631292071568796007566537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11754194714379197338377691 17631292071568796007566537)
          ·
            refine ⟨13223469053676597005674903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17631292071568796007566537 13223469053676597005674903)
            ·
              refine ⟨19835203580514895508512355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13223469053676597005674903 19835203580514895508512355)
              ·
                refine ⟨29752805370772343262768533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19835203580514895508512355 29752805370772343262768533)
                ·
                  refine ⟨1394662751754953590442275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 29752805370772343262768533 1394662751754953590442275)
                  ·
                    refine ⟨2091994127632430385663413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1394662751754953590442275 2091994127632430385663413)
                    ·
                      refine ⟨196124449465540348655945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2091994127632430385663413 196124449465540348655945)
                      ·
                        rfl

theorem cell23_381951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 6, 1, 5].length) (baseStart_381951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_381951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_381951 prefixEnd_381951 := by exact prefixLift 381951
  have htrace : WordTrace (prefixWord ++ tailWord_381951) baseStart_381951 baseEnd_381951 := by
    simpa [prefixWord, tailWord_381951, baseEnd_381951] using wordTrace_append hprefix tailTrace_381951
  have hstable : (prefixWord ++ tailWord_381951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_381951).length < 2 ^ (prefixWord ++ tailWord_381951).sum := by decide
  have hdescent : baseEnd_381951 < baseStart_381951 := by decide
  rcases family_descends (prefixWord ++ tailWord_381951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_381998 : List Nat := [4, 1, 3, 1, 1, 1, 1, 1, 1, 2, 7]
def baseStart_381998 : Nat := 118140960795 + 381998 * 2 ^ 59
def prefixEnd_381998 : Nat := 4983230072969 + 3 ^ 40 * 381998 * 2
def baseEnd_381998 : Nat := 196148583056301664768229

theorem tailTrace_381998 : CollatzResearch.WordTrace tailWord_381998 prefixEnd_381998 196148583056301664768229 := by
  unfold tailWord_381998
  simp only [CollatzResearch.WordTrace]
  refine ⟨1741576458761745113685331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9288407780062640606321765 1741576458761745113685331)
  ·
    refine ⟨2612364688142617670527997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1741576458761745113685331 2612364688142617670527997)
    ·
      refine ⟨979636758053481626447999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2612364688142617670527997 979636758053481626447999)
      ·
        refine ⟨1469455137080222439671999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 979636758053481626447999 1469455137080222439671999)
        ·
          refine ⟨2204182705620333659507999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1469455137080222439671999 2204182705620333659507999)
          ·
            refine ⟨3306274058430500489261999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2204182705620333659507999 3306274058430500489261999)
            ·
              refine ⟨4959411087645750733892999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3306274058430500489261999 4959411087645750733892999)
              ·
                refine ⟨7439116631468626100839499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4959411087645750733892999 7439116631468626100839499)
                ·
                  refine ⟨11158674947202939151259249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7439116631468626100839499 11158674947202939151259249)
                  ·
                    refine ⟨8369006210402204363444437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11158674947202939151259249 8369006210402204363444437)
                    ·
                      refine ⟨196148583056301664768229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 8369006210402204363444437 196148583056301664768229)
                      ·
                        rfl

theorem cell23_381998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 1, 1, 1, 2, 7].length) (baseStart_381998 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_381998 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_381998 prefixEnd_381998 := by exact prefixLift 381998
  have htrace : WordTrace (prefixWord ++ tailWord_381998) baseStart_381998 baseEnd_381998 := by
    simpa [prefixWord, tailWord_381998, baseEnd_381998] using wordTrace_append hprefix tailTrace_381998
  have hstable : (prefixWord ++ tailWord_381998).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_381998).length < 2 ^ (prefixWord ++ tailWord_381998).sum := by decide
  have hdescent : baseEnd_381998 < baseStart_381998 := by decide
  rcases family_descends (prefixWord ++ tailWord_381998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_382055 : List Nat := [1, 1, 5, 1, 1, 3, 2, 2, 2, 1, 4]
def baseStart_382055 : Nat := 118140960795 + 382055 * 2 ^ 59
def prefixEnd_382055 : Nat := 4983230072969 + 3 ^ 40 * 382055 * 2
def baseEnd_382055 : Nat := 196177851453607941755467

theorem tailTrace_382055 : CollatzResearch.WordTrace tailWord_382055 prefixEnd_382055 196177851453607941755467 := by
  unfold tailWord_382055
  simp only [CollatzResearch.WordTrace]
  refine ⟨13934690630887459644307619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9289793753924973096205079 13934690630887459644307619)
  ·
    refine ⟨20902035946331189466461429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13934690630887459644307619 20902035946331189466461429)
    ·
      refine ⟨1959565869968549012480759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 20902035946331189466461429 1959565869968549012480759)
      ·
        refine ⟨2939348804952823518721139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1959565869968549012480759 2939348804952823518721139)
        ·
          refine ⟨4409023207429235278081709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2939348804952823518721139 4409023207429235278081709)
          ·
            refine ⟨1653383702785963229280641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4409023207429235278081709 1653383702785963229280641)
            ·
              refine ⟨1240037777089472421960481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1653383702785963229280641 1240037777089472421960481)
              ·
                refine ⟨930028332817104316470361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1240037777089472421960481 930028332817104316470361)
                ·
                  refine ⟨697521249612828237352771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 930028332817104316470361 697521249612828237352771)
                  ·
                    refine ⟨1046281874419242356029157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 697521249612828237352771 1046281874419242356029157)
                    ·
                      refine ⟨196177851453607941755467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1046281874419242356029157 196177851453607941755467)
                      ·
                        rfl

theorem cell23_382055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 2, 2, 2, 1, 4].length) (baseStart_382055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_382055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_382055 prefixEnd_382055 := by exact prefixLift 382055
  have htrace : WordTrace (prefixWord ++ tailWord_382055) baseStart_382055 baseEnd_382055 := by
    simpa [prefixWord, tailWord_382055, baseEnd_382055] using wordTrace_append hprefix tailTrace_382055
  have hstable : (prefixWord ++ tailWord_382055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_382055).length < 2 ^ (prefixWord ++ tailWord_382055).sum := by decide
  have hdescent : baseEnd_382055 < baseStart_382055 := by decide
  rcases family_descends (prefixWord ++ tailWord_382055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_382056 : List Nat := [2, 1, 4, 4, 1, 2, 2, 2, 5]
def baseStart_382056 : Nat := 118140960795 + 382056 * 2 ^ 59
def prefixEnd_382056 : Nat := 4983230072969 + 3 ^ 40 * 382056 * 2
def baseEnd_382056 : Nat := 21797596103806937538107

theorem tailTrace_382056 : CollatzResearch.WordTrace tailWord_382056 prefixEnd_382056 21797596103806937538107 := by
  unfold tailWord_382056
  simp only [CollatzResearch.WordTrace]
  refine ⟨6967363551941918407547011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9289818069255891210062681 6967363551941918407547011)
  ·
    refine ⟨10451045327912877611320517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6967363551941918407547011 10451045327912877611320517)
    ·
      refine ⟨1959570998983664552122597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10451045327912877611320517 1959570998983664552122597)
      ·
        refine ⟨367419562309437103522987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1959570998983664552122597 367419562309437103522987)
        ·
          refine ⟨551129343464155655284481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 367419562309437103522987 551129343464155655284481)
          ·
            refine ⟨413347007598116741463361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 551129343464155655284481 413347007598116741463361)
            ·
              refine ⟨310010255698587556097521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 413347007598116741463361 310010255698587556097521)
              ·
                refine ⟨232507691773940667073141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 310010255698587556097521 232507691773940667073141)
                ·
                  refine ⟨21797596103806937538107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 232507691773940667073141 21797596103806937538107)
                  ·
                    rfl

theorem cell23_382056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 2, 2, 2, 5].length) (baseStart_382056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_382056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_382056 prefixEnd_382056 := by exact prefixLift 382056
  have htrace : WordTrace (prefixWord ++ tailWord_382056) baseStart_382056 baseEnd_382056 := by
    simpa [prefixWord, tailWord_382056, baseEnd_382056] using wordTrace_append hprefix tailTrace_382056
  have hstable : (prefixWord ++ tailWord_382056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_382056).length < 2 ^ (prefixWord ++ tailWord_382056).sum := by decide
  have hdescent : baseEnd_382056 < baseStart_382056 := by decide
  rcases family_descends (prefixWord ++ tailWord_382056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_382142 : List Nat := [4, 2, 1, 1, 3, 1, 1, 4, 1, 5]
def baseStart_382142 : Nat := 118140960795 + 382142 * 2 ^ 59
def prefixEnd_382142 : Nat := 4983230072969 + 3 ^ 40 * 382142 * 2
def baseEnd_382142 : Nat := 65407508090183033789189

theorem tailTrace_382142 : CollatzResearch.WordTrace tailWord_382142 prefixEnd_382142 65407508090183033789189 := by
  unfold tailWord_382142
  simp only [CollatzResearch.WordTrace]
  refine ⟨1742232972696534187840585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9291909187714849001816453 1742232972696534187840585)
  ·
    refine ⟨1306674729522400640880439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1742232972696534187840585 1306674729522400640880439)
    ·
      refine ⟨1960012094283600961320659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1306674729522400640880439 1960012094283600961320659)
      ·
        refine ⟨2940018141425401441980989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1960012094283600961320659 2940018141425401441980989)
        ·
          refine ⟨1102506803034525540742871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2940018141425401441980989 1102506803034525540742871)
          ·
            refine ⟨1653760204551788311114307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1102506803034525540742871 1653760204551788311114307)
            ·
              refine ⟨2480640306827682466671461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1653760204551788311114307 2480640306827682466671461)
              ·
                refine ⟨465120057530190462500899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2480640306827682466671461 465120057530190462500899)
                ·
                  refine ⟨697680086295285693751349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 465120057530190462500899 697680086295285693751349)
                  ·
                    refine ⟨65407508090183033789189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 697680086295285693751349 65407508090183033789189)
                    ·
                      rfl

theorem cell23_382142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 1, 4, 1, 5].length) (baseStart_382142 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_382142 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_382142 prefixEnd_382142 := by exact prefixLift 382142
  have htrace : WordTrace (prefixWord ++ tailWord_382142) baseStart_382142 baseEnd_382142 := by
    simpa [prefixWord, tailWord_382142, baseEnd_382142] using wordTrace_append hprefix tailTrace_382142
  have hstable : (prefixWord ++ tailWord_382142).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_382142).length < 2 ^ (prefixWord ++ tailWord_382142).sum := by decide
  have hdescent : baseEnd_382142 < baseStart_382142 := by decide
  rcases family_descends (prefixWord ++ tailWord_382142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_382162 : List Nat := [3, 2, 2, 2, 1, 1, 1, 5, 1, 1, 4]
def baseStart_382162 : Nat := 118140960795 + 382162 * 2 ^ 59
def prefixEnd_382162 : Nat := 4983230072969 + 3 ^ 40 * 382162 * 2
def baseEnd_382162 : Nat := 196232793883639023117475

theorem tailTrace_382162 : CollatzResearch.WordTrace tailWord_382162 prefixEnd_382162 196232793883639023117475 := by
  unfold tailWord_382162
  simp only [CollatzResearch.WordTrace]
  refine ⟨3484648310374954229613185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9292395494333211278968493 3484648310374954229613185)
  ·
    refine ⟨2613486232781215672209889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3484648310374954229613185 2613486232781215672209889)
    ·
      refine ⟨1960114674585911754157417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2613486232781215672209889 1960114674585911754157417)
      ·
        refine ⟨1470086005939433815618063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1960114674585911754157417 1470086005939433815618063)
        ·
          refine ⟨2205129008909150723427095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1470086005939433815618063 2205129008909150723427095)
          ·
            refine ⟨3307693513363726085140643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2205129008909150723427095 3307693513363726085140643)
            ·
              refine ⟨4961540270045589127710965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3307693513363726085140643 4961540270045589127710965)
              ·
                refine ⟨465144400316773980722903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4961540270045589127710965 465144400316773980722903)
                ·
                  refine ⟨697716600475160971084355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 465144400316773980722903 697716600475160971084355)
                  ·
                    refine ⟨1046574900712741456626533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 697716600475160971084355 1046574900712741456626533)
                    ·
                      refine ⟨196232793883639023117475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1046574900712741456626533 196232793883639023117475)
                      ·
                        rfl

theorem cell23_382162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 1, 5, 1, 1, 4].length) (baseStart_382162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_382162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_382162 prefixEnd_382162 := by exact prefixLift 382162
  have htrace : WordTrace (prefixWord ++ tailWord_382162) baseStart_382162 baseEnd_382162 := by
    simpa [prefixWord, tailWord_382162, baseEnd_382162] using wordTrace_append hprefix tailTrace_382162
  have hstable : (prefixWord ++ tailWord_382162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_382162).length < 2 ^ (prefixWord ++ tailWord_382162).sum := by decide
  have hdescent : baseEnd_382162 < baseStart_382162 := by decide
  rcases family_descends (prefixWord ++ tailWord_382162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_382173 : List Nat := [1, 4, 3, 2, 3, 1, 1, 1, 3, 1, 3]
def baseStart_382173 : Nat := 118140960795 + 382173 * 2 ^ 59
def prefixEnd_382173 : Nat := 4983230072969 + 3 ^ 40 * 382173 * 2
def baseEnd_382173 : Nat := 196238442170838480079925

theorem tailTrace_382173 : CollatzResearch.WordTrace tailWord_382173 prefixEnd_382173 196238442170838480079925 := by
  unfold tailWord_382173
  simp only [CollatzResearch.WordTrace]
  refine ⟨13938994444459965797103173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9292662962973310531402115 13938994444459965797103173)
  ·
    refine ⟨2613561458336243586956845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13938994444459965797103173 2613561458336243586956845)
    ·
      refine ⟨980085546876091345108817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2613561458336243586956845 980085546876091345108817)
      ·
        refine ⟨735064160157068508831613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 980085546876091345108817 735064160157068508831613)
        ·
          refine ⟨275649060058900690811855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 735064160157068508831613 275649060058900690811855)
          ·
            refine ⟨413473590088351036217783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 275649060058900690811855 413473590088351036217783)
            ·
              refine ⟨620210385132526554326675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 413473590088351036217783 620210385132526554326675)
              ·
                refine ⟨930315577698789831490013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 620210385132526554326675 930315577698789831490013)
                ·
                  refine ⟨348868341637046186808755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 930315577698789831490013 348868341637046186808755)
                  ·
                    refine ⟨523302512455569280213133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 348868341637046186808755 523302512455569280213133)
                    ·
                      refine ⟨196238442170838480079925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 523302512455569280213133 196238442170838480079925)
                      ·
                        rfl

theorem cell23_382173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 3, 1, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 3, 1, 1, 1, 3, 1, 3].length) (baseStart_382173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_382173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_382173 prefixEnd_382173 := by exact prefixLift 382173
  have htrace : WordTrace (prefixWord ++ tailWord_382173) baseStart_382173 baseEnd_382173 := by
    simpa [prefixWord, tailWord_382173, baseEnd_382173] using wordTrace_append hprefix tailTrace_382173
  have hstable : (prefixWord ++ tailWord_382173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_382173).length < 2 ^ (prefixWord ++ tailWord_382173).sum := by decide
  have hdescent : baseEnd_382173 < baseStart_382173 := by decide
  rcases family_descends (prefixWord ++ tailWord_382173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_382189 : List Nat := [1, 5, 1, 2, 2, 2, 1, 3, 2, 4]
def baseStart_382189 : Nat := 118140960795 + 382189 * 2 ^ 59
def prefixEnd_382189 : Nat := 4983230072969 + 3 ^ 40 * 382189 * 2
def baseEnd_382189 : Nat := 65415552620436805826617

theorem tailTrace_382189 : CollatzResearch.WordTrace tailWord_382189 prefixEnd_382189 65415552620436805826617 := by
  unfold tailWord_382189
  simp only [CollatzResearch.WordTrace]
  refine ⟨13939578012402000529685621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9293052008268000353123747 13939578012402000529685621)
  ·
    refine ⟨1306835438662687549658027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 13939578012402000529685621 1306835438662687549658027)
    ·
      refine ⟨1960253157994031324487041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1306835438662687549658027 1960253157994031324487041)
      ·
        refine ⟨1470189868495523493365281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1960253157994031324487041 1470189868495523493365281)
        ·
          refine ⟨1102642401371642620023961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1470189868495523493365281 1102642401371642620023961)
          ·
            refine ⟨826981801028731965017971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1102642401371642620023961 826981801028731965017971)
            ·
              refine ⟨1240472701543097947526957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 826981801028731965017971 1240472701543097947526957)
              ·
                refine ⟨465177263078661730322609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1240472701543097947526957 465177263078661730322609)
                ·
                  refine ⟨348882947308996297741957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 465177263078661730322609 348882947308996297741957)
                  ·
                    refine ⟨65415552620436805826617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 348882947308996297741957 65415552620436805826617)
                    ·
                      rfl

theorem cell23_382189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 2, 1, 3, 2, 4].length) (baseStart_382189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_382189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_382189 prefixEnd_382189 := by exact prefixLift 382189
  have htrace : WordTrace (prefixWord ++ tailWord_382189) baseStart_382189 baseEnd_382189 := by
    simpa [prefixWord, tailWord_382189, baseEnd_382189] using wordTrace_append hprefix tailTrace_382189
  have hstable : (prefixWord ++ tailWord_382189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_382189).length < 2 ^ (prefixWord ++ tailWord_382189).sum := by decide
  have hdescent : baseEnd_382189 < baseStart_382189 := by decide
  rcases family_descends (prefixWord ++ tailWord_382189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_382212 : List Nat := [2, 3, 2, 2, 2, 1, 1, 1, 3, 3, 3]
def baseStart_382212 : Nat := 118140960795 + 382212 * 2 ^ 59
def prefixEnd_382212 : Nat := 4983230072969 + 3 ^ 40 * 382212 * 2
def baseEnd_382212 : Nat := 196258467916363827492245

theorem tailTrace_382212 : CollatzResearch.WordTrace tailWord_382212 prefixEnd_382212 196258467916363827492245 := by
  unfold tailWord_382212
  simp only [CollatzResearch.WordTrace]
  refine ⟨6970208445659337728886445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9293611260879116971848593 6970208445659337728886445)
  ·
    refine ⟨2613828167122251648332417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6970208445659337728886445 2613828167122251648332417)
    ·
      refine ⟨1960371125341688736249313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2613828167122251648332417 1960371125341688736249313)
      ·
        refine ⟨1470278344006266552186985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1960371125341688736249313 1470278344006266552186985)
        ·
          refine ⟨1102708758004699914140239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1470278344006266552186985 1102708758004699914140239)
          ·
            refine ⟨1654063137007049871210359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1102708758004699914140239 1654063137007049871210359)
            ·
              refine ⟨2481094705510574806815539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1654063137007049871210359 2481094705510574806815539)
              ·
                refine ⟨3721642058265862210223309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2481094705510574806815539 3721642058265862210223309)
                ·
                  refine ⟨1395615771849698328833741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3721642058265862210223309 1395615771849698328833741)
                  ·
                    refine ⟨523355914443636873312653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1395615771849698328833741 523355914443636873312653)
                    ·
                      refine ⟨196258467916363827492245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 523355914443636873312653 196258467916363827492245)
                      ·
                        rfl

theorem cell23_382212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 1, 1, 3, 3, 3].length) (baseStart_382212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_382212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_382212 prefixEnd_382212 := by exact prefixLift 382212
  have htrace : WordTrace (prefixWord ++ tailWord_382212) baseStart_382212 baseEnd_382212 := by
    simpa [prefixWord, tailWord_382212, baseEnd_382212] using wordTrace_append hprefix tailTrace_382212
  have hstable : (prefixWord ++ tailWord_382212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_382212).length < 2 ^ (prefixWord ++ tailWord_382212).sum := by decide
  have hdescent : baseEnd_382212 < baseStart_382212 := by decide
  rcases family_descends (prefixWord ++ tailWord_382212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_382216 : List Nat := [2, 1, 3, 2, 4, 1, 3, 1, 1, 2, 3]
def baseStart_382216 : Nat := 118140960795 + 382216 * 2 ^ 59
def prefixEnd_382216 : Nat := 4983230072969 + 3 ^ 40 * 382216 * 2
def baseEnd_382216 : Nat := 196260521838981811842227

theorem tailTrace_382216 : CollatzResearch.WordTrace tailWord_382216 prefixEnd_382216 196260521838981811842227 := by
  unfold tailWord_382216
  simp only [CollatzResearch.WordTrace]
  refine ⟨6970281391652092070459251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9293708522202789427279001 6970281391652092070459251)
  ·
    refine ⟨10455422087478138105688877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6970281391652092070459251 10455422087478138105688877)
    ·
      refine ⟨3920783282804301789633329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10455422087478138105688877 3920783282804301789633329)
      ·
        refine ⟨2940587462103226342224997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3920783282804301789633329 2940587462103226342224997)
        ·
          refine ⟨551360149144354939167187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2940587462103226342224997 551360149144354939167187)
          ·
            refine ⟨827040223716532408750781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 551360149144354939167187 827040223716532408750781)
            ·
              refine ⟨310140083893699653281543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 827040223716532408750781 310140083893699653281543)
              ·
                refine ⟨465210125840549479922315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 310140083893699653281543 465210125840549479922315)
                ·
                  refine ⟨697815188760824219883473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 465210125840549479922315 697815188760824219883473)
                  ·
                    refine ⟨523361391570618164912605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 697815188760824219883473 523361391570618164912605)
                    ·
                      refine ⟨196260521838981811842227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 523361391570618164912605 196260521838981811842227)
                      ·
                        rfl

theorem cell23_382216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 1, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 1, 3, 1, 1, 2, 3].length) (baseStart_382216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_382216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_382216 prefixEnd_382216 := by exact prefixLift 382216
  have htrace : WordTrace (prefixWord ++ tailWord_382216) baseStart_382216 baseEnd_382216 := by
    simpa [prefixWord, tailWord_382216, baseEnd_382216] using wordTrace_append hprefix tailTrace_382216
  have hstable : (prefixWord ++ tailWord_382216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_382216).length < 2 ^ (prefixWord ++ tailWord_382216).sum := by decide
  have hdescent : baseEnd_382216 < baseStart_382216 := by decide
  rcases family_descends (prefixWord ++ tailWord_382216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_382245 : List Nat := [1, 3, 1, 2, 4, 1, 1, 1, 1, 8]
def baseStart_382245 : Nat := 118140960795 + 382245 * 2 ^ 59
def prefixEnd_382245 : Nat := 4983230072969 + 3 ^ 40 * 382245 * 2
def baseEnd_382245 : Nat := 65425137592654066126531

theorem tailTrace_382245 : CollatzResearch.WordTrace tailWord_382245 prefixEnd_382245 65425137592654066126531 := by
  unfold tailWord_382245
  simp only [CollatzResearch.WordTrace]
  refine ⟨13941620500199122093724189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9294413666799414729149459 13941620500199122093724189)
  ·
    refine ⟨5228107687574670785146571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13941620500199122093724189 5228107687574670785146571)
    ·
      refine ⟨7842161531362006177719857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5228107687574670785146571 7842161531362006177719857)
      ·
        refine ⟨5881621148521504633289893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7842161531362006177719857 5881621148521504633289893)
        ·
          refine ⟨1102803965347782118741855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5881621148521504633289893 1102803965347782118741855)
          ·
            refine ⟨1654205948021673178112783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1102803965347782118741855 1654205948021673178112783)
            ·
              refine ⟨2481308922032509767169175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1654205948021673178112783 2481308922032509767169175)
              ·
                refine ⟨3721963383048764650753763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2481308922032509767169175 3721963383048764650753763)
                ·
                  refine ⟨5582945074573146976130645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3721963383048764650753763 5582945074573146976130645)
                  ·
                    refine ⟨65425137592654066126531, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 5582945074573146976130645 65425137592654066126531)
                    ·
                      rfl

theorem cell23_382245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 1, 1, 1, 8].length) (baseStart_382245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_382245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_382245 prefixEnd_382245 := by exact prefixLift 382245
  have htrace : WordTrace (prefixWord ++ tailWord_382245) baseStart_382245 baseEnd_382245 := by
    simpa [prefixWord, tailWord_382245, baseEnd_382245] using wordTrace_append hprefix tailTrace_382245
  have hstable : (prefixWord ++ tailWord_382245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_382245).length < 2 ^ (prefixWord ++ tailWord_382245).sum := by decide
  have hdescent : baseEnd_382245 < baseStart_382245 := by decide
  rcases family_descends (prefixWord ++ tailWord_382245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_382255 : List Nat := [1, 1, 2, 1, 2, 1, 3, 1, 4, 4, 3]
def baseStart_382255 : Nat := 118140960795 + 382255 * 2 ^ 59
def prefixEnd_382255 : Nat := 4983230072969 + 3 ^ 40 * 382255 * 2
def baseEnd_382255 : Nat := 196280547584507159254547

theorem tailTrace_382255 : CollatzResearch.WordTrace tailWord_382255 prefixEnd_382255 196280547584507159254547 := by
  unfold tailWord_382255
  simp only [CollatzResearch.WordTrace]
  refine ⟨13941985230162893801588219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9294656820108595867725479 13941985230162893801588219)
  ·
    refine ⟨20912977845244340702382329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13941985230162893801588219 20912977845244340702382329)
    ·
      refine ⟨15684733383933255526786747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20912977845244340702382329 15684733383933255526786747)
      ·
        refine ⟨23527100075899883290180121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15684733383933255526786747 23527100075899883290180121)
        ·
          refine ⟨17645325056924912467635091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23527100075899883290180121 17645325056924912467635091)
          ·
            refine ⟨26467987585387368701452637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17645325056924912467635091 26467987585387368701452637)
            ·
              refine ⟨9925495344520263263044739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26467987585387368701452637 9925495344520263263044739)
              ·
                refine ⟨14888243016780394894567109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9925495344520263263044739 14888243016780394894567109)
                ·
                  refine ⟨2791545565646324042731333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14888243016780394894567109 2791545565646324042731333)
                  ·
                    refine ⟨523414793558685758012125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2791545565646324042731333 523414793558685758012125)
                    ·
                      refine ⟨196280547584507159254547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 523414793558685758012125 196280547584507159254547)
                      ·
                        rfl

theorem cell23_382255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 1, 4, 4, 3].length) (baseStart_382255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_382255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_382255 prefixEnd_382255 := by exact prefixLift 382255
  have htrace : WordTrace (prefixWord ++ tailWord_382255) baseStart_382255 baseEnd_382255 := by
    simpa [prefixWord, tailWord_382255, baseEnd_382255] using wordTrace_append hprefix tailTrace_382255
  have hstable : (prefixWord ++ tailWord_382255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_382255).length < 2 ^ (prefixWord ++ tailWord_382255).sum := by decide
  have hdescent : baseEnd_382255 < baseStart_382255 := by decide
  rcases family_descends (prefixWord ++ tailWord_382255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_382273 : List Nat := [1, 2, 5, 2, 1, 1, 4, 1, 1, 3, 2]
def baseStart_382273 : Nat := 118140960795 + 382273 * 2 ^ 59
def prefixEnd_382273 : Nat := 4983230072969 + 3 ^ 40 * 382273 * 2
def baseEnd_382273 : Nat := 196289790236288088829465

theorem tailTrace_382273 : CollatzResearch.WordTrace tailWord_382273 prefixEnd_382273 196289790236288088829465 := by
  unfold tailWord_382273
  simp only [CollatzResearch.WordTrace]
  refine ⟨13942641744097682875743473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9295094496065121917162315 13942641744097682875743473)
  ·
    refine ⟨10456981308073262156807605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13942641744097682875743473 10456981308073262156807605)
    ·
      refine ⟨980341997631868327200713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 10456981308073262156807605 980341997631868327200713)
      ·
        refine ⟨735256498223901245400535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 980341997631868327200713 735256498223901245400535)
        ·
          refine ⟨1102884747335851868100803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 735256498223901245400535 1102884747335851868100803)
          ·
            refine ⟨1654327121003777802151205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1102884747335851868100803 1654327121003777802151205)
            ·
              refine ⟨310186335188208337903351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1654327121003777802151205 310186335188208337903351)
              ·
                refine ⟨465279502782312506855027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 310186335188208337903351 465279502782312506855027)
                ·
                  refine ⟨697919254173468760282541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 465279502782312506855027 697919254173468760282541)
                  ·
                    refine ⟨261719720315050785105953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 697919254173468760282541 261719720315050785105953)
                    ·
                      refine ⟨196289790236288088829465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 261719720315050785105953 196289790236288088829465)
                      ·
                        rfl

theorem cell23_382273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 4, 1, 1, 3, 2].length) (baseStart_382273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_382273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_382273 prefixEnd_382273 := by exact prefixLift 382273
  have htrace : WordTrace (prefixWord ++ tailWord_382273) baseStart_382273 baseEnd_382273 := by
    simpa [prefixWord, tailWord_382273, baseEnd_382273] using wordTrace_append hprefix tailTrace_382273
  have hstable : (prefixWord ++ tailWord_382273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_382273).length < 2 ^ (prefixWord ++ tailWord_382273).sum := by decide
  have hdescent : baseEnd_382273 < baseStart_382273 := by decide
  rcases family_descends (prefixWord ++ tailWord_382273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_382292 : List Nat := [2, 4, 1, 1, 2, 1, 4, 1, 7]
def baseStart_382292 : Nat := 118140960795 + 382292 * 2 ^ 59
def prefixEnd_382292 : Nat := 4983230072969 + 3 ^ 40 * 382292 * 2
def baseEnd_382292 : Nat := 21811060707635946054653

theorem tailTrace_382292 : CollatzResearch.WordTrace tailWord_382292 prefixEnd_382292 21811060707635946054653 := by
  unfold tailWord_382292
  simp only [CollatzResearch.WordTrace]
  refine ⟨6971667365514424560342565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9295556487352566080456753 6971667365514424560342565)
  ·
    refine ⟨1307187631033954605064231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6971667365514424560342565 1307187631033954605064231)
    ·
      refine ⟨1960781446550931907596347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1307187631033954605064231 1960781446550931907596347)
      ·
        refine ⟨2941172169826397861394521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1960781446550931907596347 2941172169826397861394521)
        ·
          refine ⟨2205879127369798396045891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2941172169826397861394521 2205879127369798396045891)
          ·
            refine ⟨3308818691054697594068837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2205879127369798396045891 3308818691054697594068837)
            ·
              refine ⟨620403504572755798887907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3308818691054697594068837 620403504572755798887907)
              ·
                refine ⟨930605256859133698331861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 620403504572755798887907 930605256859133698331861)
                ·
                  refine ⟨21811060707635946054653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 930605256859133698331861 21811060707635946054653)
                  ·
                    rfl

theorem cell23_382292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 4, 1, 7].length) (baseStart_382292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_382292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_382292 prefixEnd_382292 := by exact prefixLift 382292
  have htrace : WordTrace (prefixWord ++ tailWord_382292) baseStart_382292 baseEnd_382292 := by
    simpa [prefixWord, tailWord_382292, baseEnd_382292] using wordTrace_append hprefix tailTrace_382292
  have hstable : (prefixWord ++ tailWord_382292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_382292).length < 2 ^ (prefixWord ++ tailWord_382292).sum := by decide
  have hdescent : baseEnd_382292 < baseStart_382292 := by decide
  rcases family_descends (prefixWord ++ tailWord_382292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_382322 : List Nat := [3, 2, 1, 2, 1, 2, 2, 3, 2, 5]
def baseStart_382322 : Nat := 118140960795 + 382322 * 2 ^ 59
def prefixEnd_382322 : Nat := 4983230072969 + 3 ^ 40 * 382322 * 2
def baseEnd_382322 : Nat := 65438316929452799038913

theorem tailTrace_382322 : CollatzResearch.WordTrace tailWord_382322 prefixEnd_382322 65438316929452799038913 := by
  unfold tailWord_382322
  simp only [CollatzResearch.WordTrace]
  refine ⟨3486107230230041061069305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9296285947280109496184813 3486107230230041061069305)
  ·
    refine ⟨2614580422672530795801979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3486107230230041061069305 2614580422672530795801979)
    ·
      refine ⟨3921870634008796193702969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2614580422672530795801979 3921870634008796193702969)
      ·
        refine ⟨2941402975506597145277227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3921870634008796193702969 2941402975506597145277227)
        ·
          refine ⟨4412104463259895717915841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2941402975506597145277227 4412104463259895717915841)
          ·
            refine ⟨3309078347444921788436881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4412104463259895717915841 3309078347444921788436881)
            ·
              refine ⟨2481808760583691341327661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3309078347444921788436881 2481808760583691341327661)
              ·
                refine ⟨930678285218884252997873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2481808760583691341327661 930678285218884252997873)
                ·
                  refine ⟨698008713914163189748405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 930678285218884252997873 698008713914163189748405)
                  ·
                    refine ⟨65438316929452799038913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 698008713914163189748405 65438316929452799038913)
                    ·
                      rfl

theorem cell23_382322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 2, 3, 2, 5].length) (baseStart_382322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_382322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_382322 prefixEnd_382322 := by exact prefixLift 382322
  have htrace : WordTrace (prefixWord ++ tailWord_382322) baseStart_382322 baseEnd_382322 := by
    simpa [prefixWord, tailWord_382322, baseEnd_382322] using wordTrace_append hprefix tailTrace_382322
  have hstable : (prefixWord ++ tailWord_382322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_382322).length < 2 ^ (prefixWord ++ tailWord_382322).sum := by decide
  have hdescent : baseEnd_382322 < baseStart_382322 := by decide
  rcases family_descends (prefixWord ++ tailWord_382322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_382354 : List Nat := [3, 2, 3, 3, 2, 1, 2, 1, 2, 2, 2]
def baseStart_382354 : Nat := 118140960795 + 382354 * 2 ^ 59
def prefixEnd_382354 : Nat := 4983230072969 + 3 ^ 40 * 382354 * 2
def baseEnd_382354 : Nat := 196331382169302271916593

theorem tailTrace_382354 : CollatzResearch.WordTrace tailWord_382354 prefixEnd_382354 196331382169302271916593 := by
  unfold tailWord_382354
  simp only [CollatzResearch.WordTrace]
  refine ⟨3486399014201058427360529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9297064037869489139628077 3486399014201058427360529)
  ·
    refine ⟨2614799260650793820520397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3486399014201058427360529 2614799260650793820520397)
    ·
      refine ⟨980549722744047682695149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2614799260650793820520397 980549722744047682695149)
      ·
        refine ⟨367706146029017881010681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 980549722744047682695149 367706146029017881010681)
        ·
          refine ⟨275779609521763410758011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 367706146029017881010681 275779609521763410758011)
          ·
            refine ⟨413669414282645116137017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 275779609521763410758011 413669414282645116137017)
            ·
              refine ⟨310252060711983837102763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 413669414282645116137017 310252060711983837102763)
              ·
                refine ⟨465378091067975755654145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 310252060711983837102763 465378091067975755654145)
                ·
                  refine ⟨349033568300981816740609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 465378091067975755654145 349033568300981816740609)
                  ·
                    refine ⟨261775176225736362555457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 349033568300981816740609 261775176225736362555457)
                    ·
                      refine ⟨196331382169302271916593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 261775176225736362555457 196331382169302271916593)
                      ·
                        rfl

theorem cell23_382354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 2, 1, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 2, 1, 2, 1, 2, 2, 2].length) (baseStart_382354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_382354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_382354 prefixEnd_382354 := by exact prefixLift 382354
  have htrace : WordTrace (prefixWord ++ tailWord_382354) baseStart_382354 baseEnd_382354 := by
    simpa [prefixWord, tailWord_382354, baseEnd_382354] using wordTrace_append hprefix tailTrace_382354
  have hstable : (prefixWord ++ tailWord_382354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_382354).length < 2 ^ (prefixWord ++ tailWord_382354).sum := by decide
  have hdescent : baseEnd_382354 < baseStart_382354 := by decide
  rcases family_descends (prefixWord ++ tailWord_382354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_382409 : List Nat := [1, 2, 1, 1, 2, 1, 3, 5, 3, 1, 3]
def baseStart_382409 : Nat := 118140960795 + 382409 * 2 ^ 59
def prefixEnd_382409 : Nat := 4983230072969 + 3 ^ 40 * 382409 * 2
def baseEnd_382409 : Nat := 196359623605299556728839

theorem tailTrace_382409 : CollatzResearch.WordTrace tailWord_382409 prefixEnd_382409 196359623605299556728839 := by
  unfold tailWord_382409
  simp only [CollatzResearch.WordTrace]
  refine ⟨13947602071604978102694281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9298401381069985401796187 13947602071604978102694281)
  ·
    refine ⟨10460701553703733577020711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13947602071604978102694281 10460701553703733577020711)
    ·
      refine ⟨15691052330555600365531067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10460701553703733577020711 15691052330555600365531067)
      ·
        refine ⟨23536578495833400548296601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15691052330555600365531067 23536578495833400548296601)
        ·
          refine ⟨17652433871875050411222451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23536578495833400548296601 17652433871875050411222451)
          ·
            refine ⟨26478650807812575616833677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17652433871875050411222451 26478650807812575616833677)
            ·
              refine ⟨9929494052929715856312629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26478650807812575616833677 9929494052929715856312629)
              ·
                refine ⟨930890067462160861529309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9929494052929715856312629 930890067462160861529309)
                ·
                  refine ⟨349083775298310323073491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 930890067462160861529309 349083775298310323073491)
                  ·
                    refine ⟨523625662947465484610237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 349083775298310323073491 523625662947465484610237)
                    ·
                      refine ⟨196359623605299556728839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 523625662947465484610237 196359623605299556728839)
                      ·
                        rfl

theorem cell23_382409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 5, 3, 1, 3].length) (baseStart_382409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_382409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_382409 prefixEnd_382409 := by exact prefixLift 382409
  have htrace : WordTrace (prefixWord ++ tailWord_382409) baseStart_382409 baseEnd_382409 := by
    simpa [prefixWord, tailWord_382409, baseEnd_382409] using wordTrace_append hprefix tailTrace_382409
  have hstable : (prefixWord ++ tailWord_382409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_382409).length < 2 ^ (prefixWord ++ tailWord_382409).sum := by decide
  have hdescent : baseEnd_382409 < baseStart_382409 := by decide
  rcases family_descends (prefixWord ++ tailWord_382409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_382426 : List Nat := [3, 1, 1, 2, 3, 3, 1, 2, 3, 1, 3]
def baseStart_382426 : Nat := 118140960795 + 382426 * 2 ^ 59
def prefixEnd_382426 : Nat := 4983230072969 + 3 ^ 40 * 382426 * 2
def baseEnd_382426 : Nat := 196368352776425990216261

theorem tailTrace_382426 : CollatzResearch.WordTrace tailWord_382426 prefixEnd_382426 196368352776425990216261 := by
  unfold tailWord_382426
  simp only [CollatzResearch.WordTrace]
  refine ⟨3487055528135847501515783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9298814741695593337375421 3487055528135847501515783)
  ·
    refine ⟨5230583292203771252273675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3487055528135847501515783 5230583292203771252273675)
    ·
      refine ⟨7845874938305656878410513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5230583292203771252273675 7845874938305656878410513)
      ·
        refine ⟨5884406203729242658807885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7845874938305656878410513 5884406203729242658807885)
        ·
          refine ⟨2206652326398465997052957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5884406203729242658807885 2206652326398465997052957)
          ·
            refine ⟨827494622399424748894859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2206652326398465997052957 827494622399424748894859)
            ·
              refine ⟨1241241933599137123342289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 827494622399424748894859 1241241933599137123342289)
              ·
                refine ⟨930931450199352842506717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1241241933599137123342289 930931450199352842506717)
                ·
                  refine ⟨349099293824757315940019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 930931450199352842506717 349099293824757315940019)
                  ·
                    refine ⟨523648940737135973910029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 349099293824757315940019 523648940737135973910029)
                    ·
                      refine ⟨196368352776425990216261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 523648940737135973910029 196368352776425990216261)
                      ·
                        rfl

theorem cell23_382426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 3, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 3, 1, 2, 3, 1, 3].length) (baseStart_382426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_382426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_382426 prefixEnd_382426 := by exact prefixLift 382426
  have htrace : WordTrace (prefixWord ++ tailWord_382426) baseStart_382426 baseEnd_382426 := by
    simpa [prefixWord, tailWord_382426, baseEnd_382426] using wordTrace_append hprefix tailTrace_382426
  have hstable : (prefixWord ++ tailWord_382426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_382426).length < 2 ^ (prefixWord ++ tailWord_382426).sum := by decide
  have hdescent : baseEnd_382426 < baseStart_382426 := by decide
  rcases family_descends (prefixWord ++ tailWord_382426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_382429 : List Nat := [1, 4, 3, 1, 1, 2, 2, 1, 3, 5]
def baseStart_382429 : Nat := 118140960795 + 382429 * 2 ^ 59
def prefixEnd_382429 : Nat := 4983230072969 + 3 ^ 40 * 382429 * 2
def baseEnd_382429 : Nat := 65456631072796492826249

theorem tailTrace_382429 : CollatzResearch.WordTrace tailWord_382429 prefixEnd_382429 65456631072796492826249 := by
  unfold tailWord_382429
  simp only [CollatzResearch.WordTrace]
  refine ⟨13948331531532521518422341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9298887687688347678948227 13948331531532521518422341)
  ·
    refine ⟨2615312162162347784704189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13948331531532521518422341 2615312162162347784704189)
    ·
      refine ⟨980742060810880419264071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2615312162162347784704189 980742060810880419264071)
      ·
        refine ⟨1471113091216320628896107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 980742060810880419264071 1471113091216320628896107)
        ·
          refine ⟨2206669636824480943344161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1471113091216320628896107 2206669636824480943344161)
          ·
            refine ⟨1655002227618360707508121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2206669636824480943344161 1655002227618360707508121)
            ·
              refine ⟨1241251670713770530631091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1655002227618360707508121 1241251670713770530631091)
              ·
                refine ⟨1861877506070655795946637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1241251670713770530631091 1861877506070655795946637)
                ·
                  refine ⟨698204064776495923479989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1861877506070655795946637 698204064776495923479989)
                  ·
                    refine ⟨65456631072796492826249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 698204064776495923479989 65456631072796492826249)
                    ·
                      rfl

theorem cell23_382429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 2, 1, 3, 5].length) (baseStart_382429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_382429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_382429 prefixEnd_382429 := by exact prefixLift 382429
  have htrace : WordTrace (prefixWord ++ tailWord_382429) baseStart_382429 baseEnd_382429 := by
    simpa [prefixWord, tailWord_382429, baseEnd_382429] using wordTrace_append hprefix tailTrace_382429
  have hstable : (prefixWord ++ tailWord_382429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_382429).length < 2 ^ (prefixWord ++ tailWord_382429).sum := by decide
  have hdescent : baseEnd_382429 < baseStart_382429 := by decide
  rcases family_descends (prefixWord ++ tailWord_382429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_382476 : List Nat := [2, 2, 1, 2, 5, 2, 1, 1, 1, 6]
def baseStart_382476 : Nat := 118140960795 + 382476 * 2 ^ 59
def prefixEnd_382476 : Nat := 4983230072969 + 3 ^ 40 * 382476 * 2
def baseEnd_382476 : Nat := 65464675603050264863677

theorem tailTrace_382476 : CollatzResearch.WordTrace tailWord_382476 prefixEnd_382476 65464675603050264863677 := by
  unfold tailWord_382476
  simp only [CollatzResearch.WordTrace]
  refine ⟨6975022881181124272691641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9300030508241499030255521 6975022881181124272691641)
  ·
    refine ⟨5231267160885843204518731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6975022881181124272691641 5231267160885843204518731)
    ·
      refine ⟨7846900741328764806778097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5231267160885843204518731 7846900741328764806778097)
      ·
        refine ⟨5885175555996573605083573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7846900741328764806778097 5885175555996573605083573)
        ·
          refine ⟨551735208374678775476585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 5885175555996573605083573 551735208374678775476585)
          ·
            refine ⟨413801406281009081607439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 551735208374678775476585 413801406281009081607439)
            ·
              refine ⟨620702109421513622411159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 413801406281009081607439 620702109421513622411159)
              ·
                refine ⟨931053164132270433616739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 620702109421513622411159 931053164132270433616739)
                ·
                  refine ⟨1396579746198405650425109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 931053164132270433616739 1396579746198405650425109)
                  ·
                    refine ⟨65464675603050264863677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1396579746198405650425109 65464675603050264863677)
                    ·
                      rfl

theorem cell23_382476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 2, 1, 1, 1, 6].length) (baseStart_382476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_382476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_382476 prefixEnd_382476 := by exact prefixLift 382476
  have htrace : WordTrace (prefixWord ++ tailWord_382476) baseStart_382476 baseEnd_382476 := by
    simpa [prefixWord, tailWord_382476, baseEnd_382476] using wordTrace_append hprefix tailTrace_382476
  have hstable : (prefixWord ++ tailWord_382476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_382476).length < 2 ^ (prefixWord ++ tailWord_382476).sum := by decide
  have hdescent : baseEnd_382476 < baseStart_382476 := by decide
  rcases family_descends (prefixWord ++ tailWord_382476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_382512 : List Nat := [2, 1, 1, 1, 2, 3, 1, 1, 4, 2, 5]
def baseStart_382512 : Nat := 118140960795 + 382512 * 2 ^ 59
def prefixEnd_382512 : Nat := 4983230072969 + 3 ^ 40 * 382512 * 2
def baseEnd_382512 : Nat := 196412512112712653740865

theorem tailTrace_382512 : CollatzResearch.WordTrace tailWord_382512 prefixEnd_382512 196412512112712653740865 := by
  unfold tailWord_382512
  simp only [CollatzResearch.WordTrace]
  refine ⟨6975679395115913346846895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9300905860154551129129193 6975679395115913346846895)
  ·
    refine ⟨10463519092673870020270343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6975679395115913346846895 10463519092673870020270343)
    ·
      refine ⟨15695278639010805030405515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10463519092673870020270343 15695278639010805030405515)
      ·
        refine ⟨23542917958516207545608273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15695278639010805030405515 23542917958516207545608273)
        ·
          refine ⟨17657188468887155659206205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23542917958516207545608273 17657188468887155659206205)
          ·
            refine ⟨6621445675832683372202327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17657188468887155659206205 6621445675832683372202327)
            ·
              refine ⟨9932168513749025058303491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6621445675832683372202327 9932168513749025058303491)
              ·
                refine ⟨14898252770623537587455237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9932168513749025058303491 14898252770623537587455237)
                ·
                  refine ⟨2793422394491913297647857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14898252770623537587455237 2793422394491913297647857)
                  ·
                    refine ⟨2095066795868934973235893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2793422394491913297647857 2095066795868934973235893)
                    ·
                      refine ⟨196412512112712653740865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2095066795868934973235893 196412512112712653740865)
                      ·
                        rfl

theorem cell23_382512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 1, 4, 2, 5].length) (baseStart_382512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_382512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_382512 prefixEnd_382512 := by exact prefixLift 382512
  have htrace : WordTrace (prefixWord ++ tailWord_382512) baseStart_382512 baseEnd_382512 := by
    simpa [prefixWord, tailWord_382512, baseEnd_382512] using wordTrace_append hprefix tailTrace_382512
  have hstable : (prefixWord ++ tailWord_382512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_382512).length < 2 ^ (prefixWord ++ tailWord_382512).sum := by decide
  have hdescent : baseEnd_382512 < baseStart_382512 := by decide
  rcases family_descends (prefixWord ++ tailWord_382512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_382517 : List Nat := [1, 3, 3, 1, 1, 4, 3, 2, 1, 2, 2]
def baseStart_382517 : Nat := 118140960795 + 382517 * 2 ^ 59
def prefixEnd_382517 : Nat := 4983230072969 + 3 ^ 40 * 382517 * 2
def baseEnd_382517 : Nat := 196415079515985134178343

theorem tailTrace_382517 : CollatzResearch.WordTrace tailWord_382517 prefixEnd_382517 196415079515985134178343 := by
  unfold tailWord_382517
  simp only [CollatzResearch.WordTrace]
  refine ⟨13951541155213712547625805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9301027436809141698417203 13951541155213712547625805)
  ·
    refine ⟨5231827933205142205359677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13951541155213712547625805 5231827933205142205359677)
    ·
      refine ⟨1961935474951928327009879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5231827933205142205359677 1961935474951928327009879)
      ·
        refine ⟨2942903212427892490514819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1961935474951928327009879 2942903212427892490514819)
        ·
          refine ⟨4414354818641838735772229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2942903212427892490514819 4414354818641838735772229)
          ·
            refine ⟨827691528495344762957293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4414354818641838735772229 827691528495344762957293)
            ·
              refine ⟨310384323185754286108985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 827691528495344762957293 310384323185754286108985)
              ·
                refine ⟨232788242389315714581739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 310384323185754286108985 232788242389315714581739)
                ·
                  refine ⟨349182363583973571872609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 232788242389315714581739 349182363583973571872609)
                  ·
                    refine ⟨261886772687980178904457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 349182363583973571872609 261886772687980178904457)
                    ·
                      refine ⟨196415079515985134178343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 261886772687980178904457 196415079515985134178343)
                      ·
                        rfl

theorem cell23_382517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 4, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 4, 3, 2, 1, 2, 2].length) (baseStart_382517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_382517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_382517 prefixEnd_382517 := by exact prefixLift 382517
  have htrace : WordTrace (prefixWord ++ tailWord_382517) baseStart_382517 baseEnd_382517 := by
    simpa [prefixWord, tailWord_382517, baseEnd_382517] using wordTrace_append hprefix tailTrace_382517
  have hstable : (prefixWord ++ tailWord_382517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_382517).length < 2 ^ (prefixWord ++ tailWord_382517).sum := by decide
  have hdescent : baseEnd_382517 < baseStart_382517 := by decide
  rcases family_descends (prefixWord ++ tailWord_382517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_382596 : List Nat := [2, 3, 2, 1, 4, 1, 1, 2, 7]
def baseStart_382596 : Nat := 118140960795 + 382596 * 2 ^ 59
def prefixEnd_382596 : Nat := 4983230072969 + 3 ^ 40 * 382596 * 2
def baseEnd_382596 : Nat := 21828404943076702787831

theorem tailTrace_382596 : CollatzResearch.WordTrace tailWord_382596 prefixEnd_382596 21828404943076702787831 := by
  unfold tailWord_382596
  simp only [CollatzResearch.WordTrace]
  refine ⟨6977211260963754519875821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9302948347951672693167761 6977211260963754519875821)
  ·
    refine ⟨2616454222861407944953433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6977211260963754519875821 2616454222861407944953433)
    ·
      refine ⟨1962340667146055958715075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2616454222861407944953433 1962340667146055958715075)
      ·
        refine ⟨2943511000719083938072613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1962340667146055958715075 2943511000719083938072613)
        ·
          refine ⟨551908312634828238388615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2943511000719083938072613 551908312634828238388615)
          ·
            refine ⟨827862468952242357582923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 551908312634828238388615 827862468952242357582923)
            ·
              refine ⟨1241793703428363536374385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 827862468952242357582923 1241793703428363536374385)
              ·
                refine ⟨931345277571272652280789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1241793703428363536374385 931345277571272652280789)
                ·
                  refine ⟨21828404943076702787831, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 931345277571272652280789 21828404943076702787831)
                  ·
                    rfl

theorem cell23_382596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 1, 1, 2, 7].length) (baseStart_382596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_382596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_382596 prefixEnd_382596 := by exact prefixLift 382596
  have htrace : WordTrace (prefixWord ++ tailWord_382596) baseStart_382596 baseEnd_382596 := by
    simpa [prefixWord, tailWord_382596, baseEnd_382596] using wordTrace_append hprefix tailTrace_382596
  have hstable : (prefixWord ++ tailWord_382596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_382596).length < 2 ^ (prefixWord ++ tailWord_382596).sum := by decide
  have hdescent : baseEnd_382596 < baseStart_382596 := by decide
  rcases family_descends (prefixWord ++ tailWord_382596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_382609 : List Nat := [1, 2, 2, 1, 1, 1, 1, 7, 2, 5]
def baseStart_382609 : Nat := 118140960795 + 382609 * 2 ^ 59
def prefixEnd_382609 : Nat := 4983230072969 + 3 ^ 40 * 382609 * 2
def baseEnd_382609 : Nat := 65487439912066258075973

theorem tailTrace_382609 : CollatzResearch.WordTrace tailWord_382609 prefixEnd_382609 65487439912066258075973 := by
  unfold tailWord_382609
  simp only [CollatzResearch.WordTrace]
  refine ⟨13954896670880412259974881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9303264447253608173316587 13954896670880412259974881)
  ·
    refine ⟨10466172503160309194981161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13954896670880412259974881 10466172503160309194981161)
    ·
      refine ⟨7849629377370231896235871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10466172503160309194981161 7849629377370231896235871)
      ·
        refine ⟨11774444066055347844353807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7849629377370231896235871 11774444066055347844353807)
        ·
          refine ⟨17661666099083021766530711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11774444066055347844353807 17661666099083021766530711)
          ·
            refine ⟨26492499148624532649796067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17661666099083021766530711 26492499148624532649796067)
            ·
              refine ⟨39738748722936798974694101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26492499148624532649796067 39738748722936798974694101)
              ·
                refine ⟨931376923193831225969393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 39738748722936798974694101 931376923193831225969393)
                ·
                  refine ⟨698532692395373419477045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 931376923193831225969393 698532692395373419477045)
                  ·
                    refine ⟨65487439912066258075973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 698532692395373419477045 65487439912066258075973)
                    ·
                      rfl

theorem cell23_382609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 5].length) (baseStart_382609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_382609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_382609 prefixEnd_382609 := by exact prefixLift 382609
  have htrace : WordTrace (prefixWord ++ tailWord_382609) baseStart_382609 baseEnd_382609 := by
    simpa [prefixWord, tailWord_382609, baseEnd_382609] using wordTrace_append hprefix tailTrace_382609
  have hstable : (prefixWord ++ tailWord_382609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_382609).length < 2 ^ (prefixWord ++ tailWord_382609).sum := by decide
  have hdescent : baseEnd_382609 < baseStart_382609 := by decide
  rcases family_descends (prefixWord ++ tailWord_382609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_382656 : List Nat := [2, 1, 1, 2, 4, 1, 1, 4, 3, 4]
def baseStart_382656 : Nat := 118140960795 + 382656 * 2 ^ 59
def prefixEnd_382656 : Nat := 4983230072969 + 3 ^ 40 * 382656 * 2
def baseEnd_382656 : Nat := 65495484442320030113401

theorem tailTrace_382656 : CollatzResearch.WordTrace tailWord_382656 prefixEnd_382656 65495484442320030113401 := by
  unfold tailWord_382656
  simp only [CollatzResearch.WordTrace]
  refine ⟨6978305450855069643467911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9304407267806759524623881 6978305450855069643467911)
  ·
    refine ⟨10467458176282604465201867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6978305450855069643467911 10467458176282604465201867)
    ·
      refine ⟨15701187264423906697802801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10467458176282604465201867 15701187264423906697802801)
      ·
        refine ⟨11775890448317930023352101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15701187264423906697802801 11775890448317930023352101)
        ·
          refine ⟨2207979459059611879378519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11775890448317930023352101 2207979459059611879378519)
          ·
            refine ⟨3311969188589417819067779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2207979459059611879378519 3311969188589417819067779)
            ·
              refine ⟨4967953782884126728601669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3311969188589417819067779 4967953782884126728601669)
              ·
                refine ⟨931491334290773761612813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4967953782884126728601669 931491334290773761612813)
                ·
                  refine ⟨349309250359040160604805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 931491334290773761612813 349309250359040160604805)
                  ·
                    refine ⟨65495484442320030113401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 349309250359040160604805 65495484442320030113401)
                    ·
                      rfl

theorem cell23_382656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 1, 4, 3, 4].length) (baseStart_382656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_382656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_382656 prefixEnd_382656 := by exact prefixLift 382656
  have htrace : WordTrace (prefixWord ++ tailWord_382656) baseStart_382656 baseEnd_382656 := by
    simpa [prefixWord, tailWord_382656, baseEnd_382656] using wordTrace_append hprefix tailTrace_382656
  have hstable : (prefixWord ++ tailWord_382656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_382656).length < 2 ^ (prefixWord ++ tailWord_382656).sum := by decide
  have hdescent : baseEnd_382656 < baseStart_382656 := by decide
  rcases family_descends (prefixWord ++ tailWord_382656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_382716 : List Nat := [2, 2, 2, 1, 3, 1, 3, 1, 3, 5]
def baseStart_382716 : Nat := 118140960795 + 382716 * 2 ^ 59
def prefixEnd_382716 : Nat := 4983230072969 + 3 ^ 40 * 382716 * 2
def baseEnd_382716 : Nat := 65505754055409951863309

theorem tailTrace_382716 : CollatzResearch.WordTrace tailWord_382716 prefixEnd_382716 65505754055409951863309 := by
  unfold tailWord_382716
  simp only [CollatzResearch.WordTrace]
  refine ⟨6979399640746384767060001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9305866187661846356080001 6979399640746384767060001)
  ·
    refine ⟨5234549730559788575295001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6979399640746384767060001 5234549730559788575295001)
    ·
      refine ⟨3925912297919841431471251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5234549730559788575295001 3925912297919841431471251)
      ·
        refine ⟨5888868446879762147206877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3925912297919841431471251 5888868446879762147206877)
        ·
          refine ⟨2208325667579910805202579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5888868446879762147206877 2208325667579910805202579)
          ·
            refine ⟨3312488501369866207803869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2208325667579910805202579 3312488501369866207803869)
            ·
              refine ⟨1242183188013699827926451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3312488501369866207803869 1242183188013699827926451)
              ·
                refine ⟨1863274782020549741889677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1242183188013699827926451 1863274782020549741889677)
                ·
                  refine ⟨698728043257706153208629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1863274782020549741889677 698728043257706153208629)
                  ·
                    refine ⟨65505754055409951863309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 698728043257706153208629 65505754055409951863309)
                    ·
                      rfl

theorem cell23_382716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 3, 1, 3, 5].length) (baseStart_382716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_382716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_382716 prefixEnd_382716 := by exact prefixLift 382716
  have htrace : WordTrace (prefixWord ++ tailWord_382716) baseStart_382716 baseEnd_382716 := by
    simpa [prefixWord, tailWord_382716, baseEnd_382716] using wordTrace_append hprefix tailTrace_382716
  have hstable : (prefixWord ++ tailWord_382716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_382716).length < 2 ^ (prefixWord ++ tailWord_382716).sum := by decide
  have hdescent : baseEnd_382716 < baseStart_382716 := by decide
  rcases family_descends (prefixWord ++ tailWord_382716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_382723 : List Nat := [1, 1, 1, 3, 2, 2, 3, 3, 2, 3, 2]
def baseStart_382723 : Nat := 118140960795 + 382723 * 2 ^ 59
def prefixEnd_382723 : Nat := 4983230072969 + 3 ^ 40 * 382723 * 2
def baseEnd_382723 : Nat := 196520856530811328202395

theorem tailTrace_382723 : CollatzResearch.WordTrace tailWord_382723 prefixEnd_382723 196520856530811328202395 := by
  unfold tailWord_382723
  simp only [CollatzResearch.WordTrace]
  refine ⟨13959054592467409729624823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9306036394978273153083215 13959054592467409729624823)
  ·
    refine ⟨20938581888701114594437235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13959054592467409729624823 20938581888701114594437235)
    ·
      refine ⟨31407872833051671891655853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20938581888701114594437235 31407872833051671891655853)
      ·
        refine ⟨11777952312394376959370945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31407872833051671891655853 11777952312394376959370945)
        ·
          refine ⟨8833464234295782719528209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11777952312394376959370945 8833464234295782719528209)
          ·
            refine ⟨6625098175721837039646157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8833464234295782719528209 6625098175721837039646157)
            ·
              refine ⟨2484411815895688889867309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6625098175721837039646157 2484411815895688889867309)
              ·
                refine ⟨931654430960883333700241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2484411815895688889867309 931654430960883333700241)
                ·
                  refine ⟨698740823220662500275181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 931654430960883333700241 698740823220662500275181)
                  ·
                    refine ⟨262027808707748437603193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 698740823220662500275181 262027808707748437603193)
                    ·
                      refine ⟨196520856530811328202395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 262027808707748437603193 196520856530811328202395)
                      ·
                        rfl

theorem cell23_382723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 3, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 3, 3, 2, 3, 2].length) (baseStart_382723 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_382723 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_382723 prefixEnd_382723 := by exact prefixLift 382723
  have htrace : WordTrace (prefixWord ++ tailWord_382723) baseStart_382723 baseEnd_382723 := by
    simpa [prefixWord, tailWord_382723, baseEnd_382723] using wordTrace_append hprefix tailTrace_382723
  have hstable : (prefixWord ++ tailWord_382723).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_382723).length < 2 ^ (prefixWord ++ tailWord_382723).sum := by decide
  have hdescent : baseEnd_382723 < baseStart_382723 := by decide
  rcases family_descends (prefixWord ++ tailWord_382723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_382770 : List Nat := [3, 2, 1, 1, 3, 2, 1, 1, 5, 2, 2]
def baseStart_382770 : Nat := 118140960795 + 382770 * 2 ^ 59
def prefixEnd_382770 : Nat := 4983230072969 + 3 ^ 40 * 382770 * 2
def baseEnd_382770 : Nat := 196544990121572644314679

theorem tailTrace_382770 : CollatzResearch.WordTrace tailWord_382770 prefixEnd_382770 196544990121572644314679 := by
  unfold tailWord_382770
  simp only [CollatzResearch.WordTrace]
  refine ⟨3490192205824284189146441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9307179215531424504390509 3490192205824284189146441)
  ·
    refine ⟨2617644154368213141859831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3490192205824284189146441 2617644154368213141859831)
    ·
      refine ⟨3926466231552319712789747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2617644154368213141859831 3926466231552319712789747)
      ·
        refine ⟨5889699347328479569184621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3926466231552319712789747 5889699347328479569184621)
        ·
          refine ⟨2208637255248179838444233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5889699347328479569184621 2208637255248179838444233)
          ·
            refine ⟨1656477941436134878833175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2208637255248179838444233 1656477941436134878833175)
            ·
              refine ⟨2484716912154202318249763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1656477941436134878833175 2484716912154202318249763)
              ·
                refine ⟨3727075368231303477374645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2484716912154202318249763 3727075368231303477374645)
                ·
                  refine ⟨349413315771684701003873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3727075368231303477374645 349413315771684701003873)
                  ·
                    refine ⟨262059986828763525752905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 349413315771684701003873 262059986828763525752905)
                    ·
                      refine ⟨196544990121572644314679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 262059986828763525752905 196544990121572644314679)
                      ·
                        rfl

theorem cell23_382770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 1, 1, 5, 2, 2].length) (baseStart_382770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_382770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_382770 prefixEnd_382770 := by exact prefixLift 382770
  have htrace : WordTrace (prefixWord ++ tailWord_382770) baseStart_382770 baseEnd_382770 := by
    simpa [prefixWord, tailWord_382770, baseEnd_382770] using wordTrace_append hprefix tailTrace_382770
  have hstable : (prefixWord ++ tailWord_382770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_382770).length < 2 ^ (prefixWord ++ tailWord_382770).sum := by decide
  have hdescent : baseEnd_382770 < baseStart_382770 := by decide
  rcases family_descends (prefixWord ++ tailWord_382770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_382774 : List Nat := [5, 1, 2, 2, 1, 3, 1, 1, 2, 3, 2]
def baseStart_382774 : Nat := 118140960795 + 382774 * 2 ^ 59
def prefixEnd_382774 : Nat := 4983230072969 + 3 ^ 40 * 382774 * 2
def baseEnd_382774 : Nat := 196547044044190628664661

theorem tailTrace_382774 : CollatzResearch.WordTrace tailWord_382774 prefixEnd_382774 196547044044190628664661 := by
  unfold tailWord_382774
  simp only [CollatzResearch.WordTrace]
  refine ⟨872557169705165339983211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 9307276476855096959820917 872557169705165339983211)
  ·
    refine ⟨1308835754557748009974817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 872557169705165339983211 1308835754557748009974817)
    ·
      refine ⟨981626815918311007481113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1308835754557748009974817 981626815918311007481113)
      ·
        refine ⟨736220111938733255610835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 981626815918311007481113 736220111938733255610835)
        ·
          refine ⟨1104330167908099883416253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 736220111938733255610835 1104330167908099883416253)
          ·
            refine ⟨414123812965537456281095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1104330167908099883416253 414123812965537456281095)
            ·
              refine ⟨621185719448306184421643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 414123812965537456281095 621185719448306184421643)
              ·
                refine ⟨931778579172459276632465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 621185719448306184421643 931778579172459276632465)
                ·
                  refine ⟨698833934379344457474349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 931778579172459276632465 698833934379344457474349)
                  ·
                    refine ⟨262062725392254171552881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 698833934379344457474349 262062725392254171552881)
                    ·
                      refine ⟨196547044044190628664661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 262062725392254171552881 196547044044190628664661)
                      ·
                        rfl

theorem cell23_382774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 3, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 3, 1, 1, 2, 3, 2].length) (baseStart_382774 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_382774 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_382774 prefixEnd_382774 := by exact prefixLift 382774
  have htrace : WordTrace (prefixWord ++ tailWord_382774) baseStart_382774 baseEnd_382774 := by
    simpa [prefixWord, tailWord_382774, baseEnd_382774] using wordTrace_append hprefix tailTrace_382774
  have hstable : (prefixWord ++ tailWord_382774).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_382774).length < 2 ^ (prefixWord ++ tailWord_382774).sum := by decide
  have hdescent : baseEnd_382774 < baseStart_382774 := by decide
  rcases family_descends (prefixWord ++ tailWord_382774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_382787 : List Nat := [1, 1, 1, 3, 1, 5, 1, 5, 1, 2, 2]
def baseStart_382787 : Nat := 118140960795 + 382787 * 2 ^ 59
def prefixEnd_382787 : Nat := 4983230072969 + 3 ^ 40 * 382787 * 2
def baseEnd_382787 : Nat := 196553719292699077802101

theorem tailTrace_382787 : CollatzResearch.WordTrace tailWord_382787 prefixEnd_382787 196553719292699077802101 := by
  unfold tailWord_382787
  simp only [CollatzResearch.WordTrace]
  refine ⟨13961388864235548659954615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9307592576157032439969743 13961388864235548659954615)
  ·
    refine ⟨20942083296353322989931923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13961388864235548659954615 20942083296353322989931923)
    ·
      refine ⟨31413124944529984484897885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20942083296353322989931923 31413124944529984484897885)
      ·
        refine ⟨11779921854198744181836707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31413124944529984484897885 11779921854198744181836707)
        ·
          refine ⟨17669882781298116272755061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11779921854198744181836707 17669882781298116272755061)
          ·
            refine ⟨1656551510746698400570787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 17669882781298116272755061 1656551510746698400570787)
            ·
              refine ⟨2484827266120047600856181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1656551510746698400570787 2484827266120047600856181)
              ·
                refine ⟨232952556198754462580267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2484827266120047600856181 232952556198754462580267)
                ·
                  refine ⟨349428834298131693870401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 232952556198754462580267 349428834298131693870401)
                  ·
                    refine ⟨262071625723598770402801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 349428834298131693870401 262071625723598770402801)
                    ·
                      refine ⟨196553719292699077802101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 262071625723598770402801 196553719292699077802101)
                      ·
                        rfl

theorem cell23_382787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 1, 5, 1, 2, 2].length) (baseStart_382787 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_382787 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_382787 prefixEnd_382787 := by exact prefixLift 382787
  have htrace : WordTrace (prefixWord ++ tailWord_382787) baseStart_382787 baseEnd_382787 := by
    simpa [prefixWord, tailWord_382787, baseEnd_382787] using wordTrace_append hprefix tailTrace_382787
  have hstable : (prefixWord ++ tailWord_382787).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_382787).length < 2 ^ (prefixWord ++ tailWord_382787).sum := by decide
  have hdescent : baseEnd_382787 < baseStart_382787 := by decide
  rcases family_descends (prefixWord ++ tailWord_382787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_382797 : List Nat := [1, 6, 1, 2, 1, 1, 3, 2, 2, 4]
def baseStart_382797 : Nat := 118140960795 + 382797 * 2 ^ 59
def prefixEnd_382797 : Nat := 4983230072969 + 3 ^ 40 * 382797 * 2
def baseEnd_382797 : Nat := 65519618033081346225685

theorem tailTrace_382797 : CollatzResearch.WordTrace tailWord_382797 prefixEnd_382797 65519618033081346225685 := by
  unfold tailWord_382797
  simp only [CollatzResearch.WordTrace]
  refine ⟨13961753594199320367818645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9307835729466213578545763 13961753594199320367818645)
  ·
    refine ⟨654457199728093142241499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 13961753594199320367818645 654457199728093142241499)
    ·
      refine ⟨981685799592139713362249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 654457199728093142241499 981685799592139713362249)
      ·
        refine ⟨736264349694104785021687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 981685799592139713362249 736264349694104785021687)
        ·
          refine ⟨1104396524541157177532531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 736264349694104785021687 1104396524541157177532531)
          ·
            refine ⟨1656594786811735766298797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1104396524541157177532531 1656594786811735766298797)
            ·
              refine ⟨621223045054400912362049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1656594786811735766298797 621223045054400912362049)
              ·
                refine ⟨465917283790800684271537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 621223045054400912362049 465917283790800684271537)
                ·
                  refine ⟨349437962843100513203653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 465917283790800684271537 349437962843100513203653)
                  ·
                    refine ⟨65519618033081346225685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 349437962843100513203653 65519618033081346225685)
                    ·
                      rfl

theorem cell23_382797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 3, 2, 2, 4].length) (baseStart_382797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_382797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_382797 prefixEnd_382797 := by exact prefixLift 382797
  have htrace : WordTrace (prefixWord ++ tailWord_382797) baseStart_382797 baseEnd_382797 := by
    simpa [prefixWord, tailWord_382797, baseEnd_382797] using wordTrace_append hprefix tailTrace_382797
  have hstable : (prefixWord ++ tailWord_382797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_382797).length < 2 ^ (prefixWord ++ tailWord_382797).sum := by decide
  have hdescent : baseEnd_382797 < baseStart_382797 := by decide
  rcases family_descends (prefixWord ++ tailWord_382797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_382804 : List Nat := [2, 4, 1, 1, 3, 1, 2, 4, 1, 2, 2]
def baseStart_382804 : Nat := 118140960795 + 382804 * 2 ^ 59
def prefixEnd_382804 : Nat := 4983230072969 + 3 ^ 40 * 382804 * 2
def baseEnd_382804 : Nat := 196562448463825511289523

theorem tailTrace_382804 : CollatzResearch.WordTrace tailWord_382804 prefixEnd_382804 196562448463825511289523 := by
  unfold tailWord_382804
  simp only [CollatzResearch.WordTrace]
  refine ⟨6981004452586980281661733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9308005936782640375548977 6981004452586980281661733)
  ·
    refine ⟨1308938334860058802811575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6981004452586980281661733 1308938334860058802811575)
    ·
      refine ⟨1963407502290088204217363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1308938334860058802811575 1963407502290088204217363)
      ·
        refine ⟨2945111253435132306326045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1963407502290088204217363 2945111253435132306326045)
        ·
          refine ⟨1104416720038174614872267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2945111253435132306326045 1104416720038174614872267)
          ·
            refine ⟨1656625080057261922308401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1104416720038174614872267 1656625080057261922308401)
            ·
              refine ⟨1242468810042946441731301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1656625080057261922308401 1242468810042946441731301)
              ·
                refine ⟨232962901883052457824619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1242468810042946441731301 232962901883052457824619)
                ·
                  refine ⟨349444352824578686736929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 232962901883052457824619 349444352824578686736929)
                  ·
                    refine ⟨262083264618434015052697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 349444352824578686736929 262083264618434015052697)
                    ·
                      refine ⟨196562448463825511289523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 262083264618434015052697 196562448463825511289523)
                      ·
                        rfl

theorem cell23_382804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 2, 4, 1, 2, 2].length) (baseStart_382804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_382804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_382804 prefixEnd_382804 := by exact prefixLift 382804
  have htrace : WordTrace (prefixWord ++ tailWord_382804) baseStart_382804 baseEnd_382804 := by
    simpa [prefixWord, tailWord_382804, baseEnd_382804] using wordTrace_append hprefix tailTrace_382804
  have hstable : (prefixWord ++ tailWord_382804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_382804).length < 2 ^ (prefixWord ++ tailWord_382804).sum := by decide
  have hdescent : baseEnd_382804 < baseStart_382804 := by decide
  rcases family_descends (prefixWord ++ tailWord_382804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_382838 : List Nat := [5, 1, 1, 3, 2, 2, 1, 3, 1, 2, 2]
def baseStart_382838 : Nat := 118140960795 + 382838 * 2 ^ 59
def prefixEnd_382838 : Nat := 4983230072969 + 3 ^ 40 * 382838 * 2
def baseEnd_382838 : Nat := 196579906806078378264367

theorem tailTrace_382838 : CollatzResearch.WordTrace tailWord_382838 prefixEnd_382838 196579906806078378264367 := by
  unfold tailWord_382838
  simp only [CollatzResearch.WordTrace]
  refine ⟨872703061690674023128823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 9308832658033856246707445 872703061690674023128823)
  ·
    refine ⟨1309054592536011034693235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 872703061690674023128823 1309054592536011034693235)
    ·
      refine ⟨1963581888804016552039853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1309054592536011034693235 1963581888804016552039853)
      ·
        refine ⟨736343208301506207014945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1963581888804016552039853 736343208301506207014945)
        ·
          refine ⟨552257406226129655261209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 736343208301506207014945 552257406226129655261209)
          ·
            refine ⟨414193054669597241445907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 552257406226129655261209 414193054669597241445907)
            ·
              refine ⟨621289582004395862168861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 414193054669597241445907 621289582004395862168861)
              ·
                refine ⟨232983593251648448313323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 621289582004395862168861 232983593251648448313323)
                ·
                  refine ⟨349475389877472672469985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 232983593251648448313323 349475389877472672469985)
                  ·
                    refine ⟨262106542408104504352489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 349475389877472672469985 262106542408104504352489)
                    ·
                      refine ⟨196579906806078378264367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 262106542408104504352489 196579906806078378264367)
                      ·
                        rfl

theorem cell23_382838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 2, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 2, 1, 3, 1, 2, 2].length) (baseStart_382838 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_382838 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_382838 prefixEnd_382838 := by exact prefixLift 382838
  have htrace : WordTrace (prefixWord ++ tailWord_382838) baseStart_382838 baseEnd_382838 := by
    simpa [prefixWord, tailWord_382838, baseEnd_382838] using wordTrace_append hprefix tailTrace_382838
  have hstable : (prefixWord ++ tailWord_382838).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_382838).length < 2 ^ (prefixWord ++ tailWord_382838).sum := by decide
  have hdescent : baseEnd_382838 < baseStart_382838 := by decide
  rcases family_descends (prefixWord ++ tailWord_382838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_382843 : List Nat := [1, 1, 1, 1, 1, 5, 1, 3, 3, 4, 2]
def baseStart_382843 : Nat := 118140960795 + 382843 * 2 ^ 59
def prefixEnd_382843 : Nat := 4983230072969 + 3 ^ 40 * 382843 * 2
def baseEnd_382843 : Nat := 196582474209350858701843

theorem tailTrace_382843 : CollatzResearch.WordTrace tailWord_382843 prefixEnd_382843 196582474209350858701843 := by
  unfold tailWord_382843
  simp only [CollatzResearch.WordTrace]
  refine ⟨13963431352032670223993183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9308954234688446815995455 13963431352032670223993183)
  ·
    refine ⟨20945147028049005335989775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13963431352032670223993183 20945147028049005335989775)
    ·
      refine ⟨31417720542073508003984663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20945147028049005335989775 31417720542073508003984663)
      ·
        refine ⟨47126580813110262005976995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31417720542073508003984663 47126580813110262005976995)
        ·
          refine ⟨70689871219665393008965493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47126580813110262005976995 70689871219665393008965493)
          ·
            refine ⟨6627175426843630594590515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 70689871219665393008965493 6627175426843630594590515)
            ·
              refine ⟨9940763140265445891885773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6627175426843630594590515 9940763140265445891885773)
              ·
                refine ⟨3727786177599542209457165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9940763140265445891885773 3727786177599542209457165)
                ·
                  refine ⟨1397919816599828328546437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3727786177599542209457165 1397919816599828328546437)
                  ·
                    refine ⟨262109965612467811602457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1397919816599828328546437 262109965612467811602457)
                    ·
                      refine ⟨196582474209350858701843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 262109965612467811602457 196582474209350858701843)
                      ·
                        rfl

theorem cell23_382843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 3, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 3, 3, 4, 2].length) (baseStart_382843 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_382843 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_382843 prefixEnd_382843 := by exact prefixLift 382843
  have htrace : WordTrace (prefixWord ++ tailWord_382843) baseStart_382843 baseEnd_382843 := by
    simpa [prefixWord, tailWord_382843, baseEnd_382843] using wordTrace_append hprefix tailTrace_382843
  have hstable : (prefixWord ++ tailWord_382843).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_382843).length < 2 ^ (prefixWord ++ tailWord_382843).sum := by decide
  have hdescent : baseEnd_382843 < baseStart_382843 := by decide
  rcases family_descends (prefixWord ++ tailWord_382843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_382881 : List Nat := [1, 2, 3, 4, 3, 1, 1, 2, 1, 3, 2]
def baseStart_382881 : Nat := 118140960795 + 382881 * 2 ^ 59
def prefixEnd_382881 : Nat := 4983230072969 + 3 ^ 40 * 382881 * 2
def baseEnd_382881 : Nat := 196601986474221710026669

theorem tailTrace_382881 : CollatzResearch.WordTrace tailWord_382881 prefixEnd_382881 196601986474221710026669 := by
  unfold tailWord_382881
  simp only [CollatzResearch.WordTrace]
  refine ⟨13964817325895002713876497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9309878217263335142584331 13964817325895002713876497)
  ·
    refine ⟨10473612994421252035407373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13964817325895002713876497 10473612994421252035407373)
    ·
      refine ⟨3927604872907969513277765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10473612994421252035407373 3927604872907969513277765)
      ·
        refine ⟨736425913670244283739581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3927604872907969513277765 736425913670244283739581)
        ·
          refine ⟨276159717626341606402343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 736425913670244283739581 276159717626341606402343)
          ·
            refine ⟨414239576439512409603515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 276159717626341606402343 414239576439512409603515)
            ·
              refine ⟨621359364659268614405273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 414239576439512409603515 621359364659268614405273)
              ·
                refine ⟨466019523494451460803955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 621359364659268614405273 466019523494451460803955)
                ·
                  refine ⟨699029285241677191205933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 466019523494451460803955 699029285241677191205933)
                  ·
                    refine ⟨262135981965628946702225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 699029285241677191205933 262135981965628946702225)
                    ·
                      refine ⟨196601986474221710026669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 262135981965628946702225 196601986474221710026669)
                      ·
                        rfl

theorem cell23_382881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 3, 1, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 3, 1, 1, 2, 1, 3, 2].length) (baseStart_382881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_382881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_382881 prefixEnd_382881 := by exact prefixLift 382881
  have htrace : WordTrace (prefixWord ++ tailWord_382881) baseStart_382881 baseEnd_382881 := by
    simpa [prefixWord, tailWord_382881, baseEnd_382881] using wordTrace_append hprefix tailTrace_382881
  have hstable : (prefixWord ++ tailWord_382881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_382881).length < 2 ^ (prefixWord ++ tailWord_382881).sum := by decide
  have hdescent : baseEnd_382881 < baseStart_382881 := by decide
  rcases family_descends (prefixWord ++ tailWord_382881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_382920 : List Nat := [2, 1, 3, 1, 4, 1, 1, 1, 2, 5, 2]
def baseStart_382920 : Nat := 118140960795 + 382920 * 2 ^ 59
def prefixEnd_382920 : Nat := 4983230072969 + 3 ^ 40 * 382920 * 2
def baseEnd_382920 : Nat := 196622012219747057438989

theorem tailTrace_382920 : CollatzResearch.WordTrace tailWord_382920 prefixEnd_382920 196622012219747057438989 := by
  unfold tailWord_382920
  simp only [CollatzResearch.WordTrace]
  refine ⟨6983119886376856187273107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9310826515169141583030809 6983119886376856187273107)
  ·
    refine ⟨10474679829565284280909661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6983119886376856187273107 10474679829565284280909661)
    ·
      refine ⟨3928004936086981605341123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10474679829565284280909661 3928004936086981605341123)
      ·
        refine ⟨5892007404130472408011685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3928004936086981605341123 5892007404130472408011685)
        ·
          refine ⟨1104751388274463576502191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5892007404130472408011685 1104751388274463576502191)
          ·
            refine ⟨1657127082411695364753287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1104751388274463576502191 1657127082411695364753287)
            ·
              refine ⟨2485690623617543047129931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1657127082411695364753287 2485690623617543047129931)
              ·
                refine ⟨3728535935426314570694897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2485690623617543047129931 3728535935426314570694897)
                ·
                  refine ⟨2796401951569735928021173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3728535935426314570694897 2796401951569735928021173)
                  ·
                    refine ⟨262162682959662743251985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2796401951569735928021173 262162682959662743251985)
                    ·
                      refine ⟨196622012219747057438989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 262162682959662743251985 196622012219747057438989)
                      ·
                        rfl

theorem cell23_382920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 1, 1, 2, 5, 2].length) (baseStart_382920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_382920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_382920 prefixEnd_382920 := by exact prefixLift 382920
  have htrace : WordTrace (prefixWord ++ tailWord_382920) baseStart_382920 baseEnd_382920 := by
    simpa [prefixWord, tailWord_382920, baseEnd_382920] using wordTrace_append hprefix tailTrace_382920
  have hstable : (prefixWord ++ tailWord_382920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_382920).length < 2 ^ (prefixWord ++ tailWord_382920).sum := by decide
  have hdescent : baseEnd_382920 < baseStart_382920 := by decide
  rcases family_descends (prefixWord ++ tailWord_382920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_382977 : List Nat := [1, 2, 4, 1, 2, 1, 1, 6, 1, 4]
def baseStart_382977 : Nat := 118140960795 + 382977 * 2 ^ 59
def prefixEnd_382977 : Nat := 4983230072969 + 3 ^ 40 * 382977 * 2
def baseEnd_382977 : Nat := 65550426872351111475409

theorem tailTrace_382977 : CollatzResearch.WordTrace tailWord_382977 prefixEnd_382977 65550426872351111475409 := by
  unfold tailWord_382977
  simp only [CollatzResearch.WordTrace]
  refine ⟨13968318733547211109371185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9312212489031474072914123 13968318733547211109371185)
  ·
    refine ⟨10476239050160408332028389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13968318733547211109371185 10476239050160408332028389)
    ·
      refine ⟨1964294821905076562255323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10476239050160408332028389 1964294821905076562255323)
      ·
        refine ⟨2946442232857614843382985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1964294821905076562255323 2946442232857614843382985)
        ·
          refine ⟨2209831674643211132537239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2946442232857614843382985 2209831674643211132537239)
          ·
            refine ⟨3314747511964816698805859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2209831674643211132537239 3314747511964816698805859)
            ·
              refine ⟨4972121267947225048208789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3314747511964816698805859 4972121267947225048208789)
              ·
                refine ⟨233068184435026174134787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 4972121267947225048208789 233068184435026174134787)
                ·
                  refine ⟨349602276652539261202181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 233068184435026174134787 349602276652539261202181)
                  ·
                    refine ⟨65550426872351111475409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 349602276652539261202181 65550426872351111475409)
                    ·
                      rfl

theorem cell23_382977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 1, 6, 1, 4].length) (baseStart_382977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_382977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_382977 prefixEnd_382977 := by exact prefixLift 382977
  have htrace : WordTrace (prefixWord ++ tailWord_382977) baseStart_382977 baseEnd_382977 := by
    simpa [prefixWord, tailWord_382977, baseEnd_382977] using wordTrace_append hprefix tailTrace_382977
  have hstable : (prefixWord ++ tailWord_382977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_382977).length < 2 ^ (prefixWord ++ tailWord_382977).sum := by decide
  have hdescent : baseEnd_382977 < baseStart_382977 := by decide
  rcases family_descends (prefixWord ++ tailWord_382977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_383028 : List Nat := [2, 5, 1, 2, 2, 1, 3, 2, 1, 4]
def baseStart_383028 : Nat := 118140960795 + 383028 * 2 ^ 59
def prefixEnd_383028 : Nat := 4983230072969 + 3 ^ 40 * 383028 * 2
def baseEnd_383028 : Nat := 65559156043477544962831

theorem tailTrace_383028 : CollatzResearch.WordTrace tailWord_383028 prefixEnd_383028 65559156043477544962831 := by
  unfold tailWord_383028
  simp only [CollatzResearch.WordTrace]
  refine ⟨6985089428181223409738869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9313452570908297879651825 6985089428181223409738869)
  ·
    refine ⟨654852133891989694663019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 6985089428181223409738869 654852133891989694663019)
    ·
      refine ⟨982278200837984541994529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 654852133891989694663019 982278200837984541994529)
      ·
        refine ⟨736708650628488406495897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 982278200837984541994529 736708650628488406495897)
        ·
          refine ⟨552531487971366304871923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 736708650628488406495897 552531487971366304871923)
          ·
            refine ⟨828797231957049457307885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 552531487971366304871923 828797231957049457307885)
            ·
              refine ⟨310798961983893546490457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 828797231957049457307885 310798961983893546490457)
              ·
                refine ⟨233099221487920159867843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 310798961983893546490457 233099221487920159867843)
                ·
                  refine ⟨349648832231880239801765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 233099221487920159867843 349648832231880239801765)
                  ·
                    refine ⟨65559156043477544962831, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 349648832231880239801765 65559156043477544962831)
                    ·
                      rfl

theorem cell23_383028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 1, 3, 2, 1, 4].length) (baseStart_383028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_383028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_383028 prefixEnd_383028 := by exact prefixLift 383028
  have htrace : WordTrace (prefixWord ++ tailWord_383028) baseStart_383028 baseEnd_383028 := by
    simpa [prefixWord, tailWord_383028, baseEnd_383028] using wordTrace_append hprefix tailTrace_383028
  have hstable : (prefixWord ++ tailWord_383028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_383028).length < 2 ^ (prefixWord ++ tailWord_383028).sum := by decide
  have hdescent : baseEnd_383028 < baseStart_383028 := by decide
  rcases family_descends (prefixWord ++ tailWord_383028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_383043 : List Nat := [1, 1, 1, 3, 1, 2, 2, 3, 3, 1, 5]
def baseStart_383043 : Nat := 118140960795 + 383043 * 2 ^ 59
def prefixEnd_383043 : Nat := 4983230072969 + 3 ^ 40 * 383043 * 2
def baseEnd_383043 : Nat := 196685170340250076200923

theorem tailTrace_383043 : CollatzResearch.WordTrace tailWord_383043 prefixEnd_383043 196685170340250076200923 := by
  unfold tailWord_383043
  simp only [CollatzResearch.WordTrace]
  refine ⟨13970725951308104381273783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9313817300872069587515855 13970725951308104381273783)
  ·
    refine ⟨20956088926962156571910675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13970725951308104381273783 20956088926962156571910675)
    ·
      refine ⟨31434133390443234857866013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20956088926962156571910675 31434133390443234857866013)
      ·
        refine ⟨11787800021416213071699755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31434133390443234857866013 11787800021416213071699755)
        ·
          refine ⟨17681700032124319607549633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11787800021416213071699755 17681700032124319607549633)
          ·
            refine ⟨13261275024093239705662225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17681700032124319607549633 13261275024093239705662225)
            ·
              refine ⟨9945956268069929779246669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13261275024093239705662225 9945956268069929779246669)
              ·
                refine ⟨3729733600526223667217501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9945956268069929779246669 3729733600526223667217501)
                ·
                  refine ⟨1398650100197333875206563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3729733600526223667217501 1398650100197333875206563)
                  ·
                    refine ⟨2097975150296000812809845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1398650100197333875206563 2097975150296000812809845)
                    ·
                      refine ⟨196685170340250076200923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2097975150296000812809845 196685170340250076200923)
                      ·
                        rfl

theorem cell23_383043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 3, 3, 1, 5].length) (baseStart_383043 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_383043 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_383043 prefixEnd_383043 := by exact prefixLift 383043
  have htrace : WordTrace (prefixWord ++ tailWord_383043) baseStart_383043 baseEnd_383043 := by
    simpa [prefixWord, tailWord_383043, baseEnd_383043] using wordTrace_append hprefix tailTrace_383043
  have hstable : (prefixWord ++ tailWord_383043).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_383043).length < 2 ^ (prefixWord ++ tailWord_383043).sum := by decide
  have hdescent : baseEnd_383043 < baseStart_383043 := by decide
  rcases family_descends (prefixWord ++ tailWord_383043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_383057 : List Nat := [1, 2, 2, 1, 3, 1, 1, 3, 5, 2, 2]
def baseStart_383057 : Nat := 118140960795 + 383057 * 2 ^ 59
def prefixEnd_383057 : Nat := 4983230072969 + 3 ^ 40 * 383057 * 2
def baseEnd_383057 : Nat := 196692359069413021425859

theorem tailTrace_383057 : CollatzResearch.WordTrace tailWord_383057 prefixEnd_383057 196692359069413021425859 := by
  unfold tailWord_383057
  simp only [CollatzResearch.WordTrace]
  refine ⟨13971236573257384772283425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9314157715504923181522283 13971236573257384772283425)
  ·
    refine ⟨10478427429943038579212569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13971236573257384772283425 10478427429943038579212569)
    ·
      refine ⟨7858820572457278934409427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10478427429943038579212569 7858820572457278934409427)
      ·
        refine ⟨11788230858685918401614141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7858820572457278934409427 11788230858685918401614141)
        ·
          refine ⟨4420586572007219400605303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11788230858685918401614141 4420586572007219400605303)
          ·
            refine ⟨6630879858010829100907955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4420586572007219400605303 6630879858010829100907955)
            ·
              refine ⟨9946319787016243651361933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6630879858010829100907955 9946319787016243651361933)
              ·
                refine ⟨3729869920131091369260725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9946319787016243651361933 3729869920131091369260725)
                ·
                  refine ⟨349675305012289815868193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3729869920131091369260725 349675305012289815868193)
                  ·
                    refine ⟨262256478759217361901145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 349675305012289815868193 262256478759217361901145)
                    ·
                      refine ⟨196692359069413021425859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 262256478759217361901145 196692359069413021425859)
                      ·
                        rfl

theorem cell23_383057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 3, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 3, 5, 2, 2].length) (baseStart_383057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_383057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_383057 prefixEnd_383057 := by exact prefixLift 383057
  have htrace : WordTrace (prefixWord ++ tailWord_383057) baseStart_383057 baseEnd_383057 := by
    simpa [prefixWord, tailWord_383057, baseEnd_383057] using wordTrace_append hprefix tailTrace_383057
  have hstable : (prefixWord ++ tailWord_383057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_383057).length < 2 ^ (prefixWord ++ tailWord_383057).sum := by decide
  have hdescent : baseEnd_383057 < baseStart_383057 := by decide
  rcases family_descends (prefixWord ++ tailWord_383057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_383063 : List Nat := [1, 1, 3, 2, 2, 1, 4, 9]
def baseStart_383063 : Nat := 118140960795 + 383063 * 2 ^ 59
def prefixEnd_383063 : Nat := 4983230072969 + 3 ^ 40 * 383063 * 2
def baseEnd_383063 : Nat := 7285016294568148072253

theorem tailTrace_383063 : CollatzResearch.WordTrace tailWord_383063 prefixEnd_383063 7285016294568148072253 := by
  unfold tailWord_383063
  simp only [CollatzResearch.WordTrace]
  refine ⟨13971455411235647797001843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9314303607490431864667895 13971455411235647797001843)
  ·
    refine ⟨20957183116853471695502765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13971455411235647797001843 20957183116853471695502765)
    ·
      refine ⟨7858943668820051885813537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20957183116853471695502765 7858943668820051885813537)
      ·
        refine ⟨5894207751615038914360153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7858943668820051885813537 5894207751615038914360153)
        ·
          refine ⟨4420655813711279185770115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5894207751615038914360153 4420655813711279185770115)
          ·
            refine ⟨6630983720566918778655173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4420655813711279185770115 6630983720566918778655173)
            ·
              refine ⟨1243309447606297270997845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6630983720566918778655173 1243309447606297270997845)
              ·
                refine ⟨7285016294568148072253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 1243309447606297270997845 7285016294568148072253)
                ·
                  rfl

theorem cell23_383063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 4, 9].length) (baseStart_383063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_383063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_383063 prefixEnd_383063 := by exact prefixLift 383063
  have htrace : WordTrace (prefixWord ++ tailWord_383063) baseStart_383063 baseEnd_383063 := by
    simpa [prefixWord, tailWord_383063, baseEnd_383063] using wordTrace_append hprefix tailTrace_383063
  have hstable : (prefixWord ++ tailWord_383063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_383063).length < 2 ^ (prefixWord ++ tailWord_383063).sum := by decide
  have hdescent : baseEnd_383063 < baseStart_383063 := by decide
  rcases family_descends (prefixWord ++ tailWord_383063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_383077 : List Nat := [1, 3, 1, 3, 2, 4, 1, 1, 1, 1, 5]
def baseStart_383077 : Nat := 118140960795 + 383077 * 2 ^ 59
def prefixEnd_383077 : Nat := 4983230072969 + 3 ^ 40 * 383077 * 2
def baseEnd_383077 : Nat := 196702628682502943175767

theorem tailTrace_383077 : CollatzResearch.WordTrace tailWord_383077 prefixEnd_383077 196702628682502943175767 := by
  unfold tailWord_383077
  simp only [CollatzResearch.WordTrace]
  refine ⟨13971966033184928188011485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9314644022123285458674323 13971966033184928188011485)
  ·
    refine ⟨5239487262444348070504307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13971966033184928188011485 5239487262444348070504307)
    ·
      refine ⟨7859230893666522105756461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5239487262444348070504307 7859230893666522105756461)
      ·
        refine ⟨2947211585124945789658673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7859230893666522105756461 2947211585124945789658673)
        ·
          refine ⟨2210408688843709342244005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2947211585124945789658673 2210408688843709342244005)
          ·
            refine ⟨414451629158195501670751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2210408688843709342244005 414451629158195501670751)
            ·
              refine ⟨621677443737293252506127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 414451629158195501670751 621677443737293252506127)
              ·
                refine ⟨932516165605939878759191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 621677443737293252506127 932516165605939878759191)
                ·
                  refine ⟨1398774248408909818138787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 932516165605939878759191 1398774248408909818138787)
                  ·
                    refine ⟨2098161372613364727208181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1398774248408909818138787 2098161372613364727208181)
                    ·
                      refine ⟨196702628682502943175767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2098161372613364727208181 196702628682502943175767)
                      ·
                        rfl

theorem cell23_383077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 4, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 4, 1, 1, 1, 1, 5].length) (baseStart_383077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_383077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_383077 prefixEnd_383077 := by exact prefixLift 383077
  have htrace : WordTrace (prefixWord ++ tailWord_383077) baseStart_383077 baseEnd_383077 := by
    simpa [prefixWord, tailWord_383077, baseEnd_383077] using wordTrace_append hprefix tailTrace_383077
  have hstable : (prefixWord ++ tailWord_383077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_383077).length < 2 ^ (prefixWord ++ tailWord_383077).sum := by decide
  have hdescent : baseEnd_383077 < baseStart_383077 := by decide
  rcases family_descends (prefixWord ++ tailWord_383077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_383107 : List Nat := [1, 1, 1, 3, 3, 4, 2, 1, 1, 3, 3]
def baseStart_383107 : Nat := 118140960795 + 383107 * 2 ^ 59
def prefixEnd_383107 : Nat := 4983230072969 + 3 ^ 40 * 383107 * 2
def baseEnd_383107 : Nat := 196718033102137825800629

theorem tailTrace_383107 : CollatzResearch.WordTrace tailWord_383107 prefixEnd_383107 196718033102137825800629 := by
  unfold tailWord_383107
  simp only [CollatzResearch.WordTrace]
  refine ⟨13973060223076243311603575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9315373482050828874402383 13973060223076243311603575)
  ·
    refine ⟨20959590334614364967405363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13973060223076243311603575 20959590334614364967405363)
    ·
      refine ⟨31439385501921547451108045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20959590334614364967405363 31439385501921547451108045)
      ·
        refine ⟨11789769563220580294165517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31439385501921547451108045 11789769563220580294165517)
        ·
          refine ⟨4421163586207717610312069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11789769563220580294165517 4421163586207717610312069)
          ·
            refine ⟨828968172413947051933513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4421163586207717610312069 828968172413947051933513)
            ·
              refine ⟨621726129310460288950135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 828968172413947051933513 621726129310460288950135)
              ·
                refine ⟨932589193965690433425203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 621726129310460288950135 932589193965690433425203)
                ·
                  refine ⟨1398883790948535650137805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 932589193965690433425203 1398883790948535650137805)
                  ·
                    refine ⟨524581421605700868801677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1398883790948535650137805 524581421605700868801677)
                    ·
                      refine ⟨196718033102137825800629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 524581421605700868801677 196718033102137825800629)
                      ·
                        rfl

theorem cell23_383107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 4, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 4, 2, 1, 1, 3, 3].length) (baseStart_383107 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_383107 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_383107 prefixEnd_383107 := by exact prefixLift 383107
  have htrace : WordTrace (prefixWord ++ tailWord_383107) baseStart_383107 baseEnd_383107 := by
    simpa [prefixWord, tailWord_383107, baseEnd_383107] using wordTrace_append hprefix tailTrace_383107
  have hstable : (prefixWord ++ tailWord_383107).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_383107).length < 2 ^ (prefixWord ++ tailWord_383107).sum := by decide
  have hdescent : baseEnd_383107 < baseStart_383107 := by decide
  rcases family_descends (prefixWord ++ tailWord_383107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_383123 : List Nat := [1, 1, 1, 2, 1, 2, 3, 1, 3, 8]
def baseStart_383123 : Nat := 118140960795 + 383123 * 2 ^ 59
def prefixEnd_383123 : Nat := 4983230072969 + 3 ^ 40 * 383123 * 2
def baseEnd_383123 : Nat := 65575416264203254400185

theorem tailTrace_383123 : CollatzResearch.WordTrace tailWord_383123 prefixEnd_383123 65575416264203254400185 := by
  unfold tailWord_383123
  simp only [CollatzResearch.WordTrace]
  refine ⟨13973643791018278044186023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9315762527345518696124015 13973643791018278044186023)
  ·
    refine ⟨20960465686527417066279035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13973643791018278044186023 20960465686527417066279035)
    ·
      refine ⟨31440698529791125599418553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20960465686527417066279035 31440698529791125599418553)
      ·
        refine ⟨23580523897343344199563915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31440698529791125599418553 23580523897343344199563915)
        ·
          refine ⟨35370785846015016299345873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23580523897343344199563915 35370785846015016299345873)
          ·
            refine ⟨26528089384511262224509405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35370785846015016299345873 26528089384511262224509405)
            ·
              refine ⟨9948033519191723334191027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26528089384511262224509405 9948033519191723334191027)
              ·
                refine ⟨14922050278787585001286541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9948033519191723334191027 14922050278787585001286541)
                ·
                  refine ⟨5595768854545344375482453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14922050278787585001286541 5595768854545344375482453)
                  ·
                    refine ⟨65575416264203254400185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 5595768854545344375482453 65575416264203254400185)
                    ·
                      rfl

theorem cell23_383123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 1, 3, 8].length) (baseStart_383123 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_383123 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_383123 prefixEnd_383123 := by exact prefixLift 383123
  have htrace : WordTrace (prefixWord ++ tailWord_383123) baseStart_383123 baseEnd_383123 := by
    simpa [prefixWord, tailWord_383123, baseEnd_383123] using wordTrace_append hprefix tailTrace_383123
  have hstable : (prefixWord ++ tailWord_383123).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_383123).length < 2 ^ (prefixWord ++ tailWord_383123).sum := by decide
  have hdescent : baseEnd_383123 < baseStart_383123 := by decide
  rcases family_descends (prefixWord ++ tailWord_383123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_383128 : List Nat := [2, 1, 2, 4, 4, 1, 2, 1, 1, 2, 3]
def baseStart_383128 : Nat := 118140960795 + 383128 * 2 ^ 59
def prefixEnd_383128 : Nat := 4983230072969 + 3 ^ 40 * 383128 * 2
def baseEnd_383128 : Nat := 196728816195882243638033

theorem tailTrace_383128 : CollatzResearch.WordTrace tailWord_383128 prefixEnd_383128 196728816195882243638033 := by
  unfold tailWord_383128
  simp only [CollatzResearch.WordTrace]
  refine ⟨6986913078000081949059019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9315884104000109265412025 6986913078000081949059019)
  ·
    refine ⟨10480369617000122923588529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6986913078000081949059019 10480369617000122923588529)
    ·
      refine ⟨7860277212750092192691397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10480369617000122923588529 7860277212750092192691397)
      ·
        refine ⟨1473801977390642286129637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7860277212750092192691397 1473801977390642286129637)
        ·
          refine ⟨276337870760745428649307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1473801977390642286129637 276337870760745428649307)
          ·
            refine ⟨414506806141118142973961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 276337870760745428649307 414506806141118142973961)
            ·
              refine ⟨310880104605838607230471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 414506806141118142973961 310880104605838607230471)
              ·
                refine ⟨466320156908757910845707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 310880104605838607230471 466320156908757910845707)
                ·
                  refine ⟨699480235363136866268561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 466320156908757910845707 699480235363136866268561)
                  ·
                    refine ⟨524610176522352649701421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 699480235363136866268561 524610176522352649701421)
                    ·
                      refine ⟨196728816195882243638033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 524610176522352649701421 196728816195882243638033)
                      ·
                        rfl

theorem cell23_383128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 4, 1, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 4, 1, 2, 1, 1, 2, 3].length) (baseStart_383128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_383128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_383128 prefixEnd_383128 := by exact prefixLift 383128
  have htrace : WordTrace (prefixWord ++ tailWord_383128) baseStart_383128 baseEnd_383128 := by
    simpa [prefixWord, tailWord_383128, baseEnd_383128] using wordTrace_append hprefix tailTrace_383128
  have hstable : (prefixWord ++ tailWord_383128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_383128).length < 2 ^ (prefixWord ++ tailWord_383128).sum := by decide
  have hdescent : baseEnd_383128 < baseStart_383128 := by decide
  rcases family_descends (prefixWord ++ tailWord_383128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_383160 : List Nat := [2, 1, 2, 1, 2, 1, 3, 3, 2, 2, 4]
def baseStart_383160 : Nat := 118140960795 + 383160 * 2 ^ 59
def prefixEnd_383160 : Nat := 4983230072969 + 3 ^ 40 * 383160 * 2
def baseEnd_383160 : Nat := 196745247576826118437885

theorem tailTrace_383160 : CollatzResearch.WordTrace tailWord_383160 prefixEnd_383160 196745247576826118437885 := by
  unfold tailWord_383160
  simp only [CollatzResearch.WordTrace]
  refine ⟨6987496645942116681641467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9316662194589488908855289 6987496645942116681641467)
  ·
    refine ⟨10481244968913175022462201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6987496645942116681641467 10481244968913175022462201)
    ·
      refine ⟨7860933726684881266846651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10481244968913175022462201 7860933726684881266846651)
      ·
        refine ⟨11791400590027321900269977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7860933726684881266846651 11791400590027321900269977)
        ·
          refine ⟨8843550442520491425202483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11791400590027321900269977 8843550442520491425202483)
          ·
            refine ⟨13265325663780737137803725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8843550442520491425202483 13265325663780737137803725)
            ·
              refine ⟨4974497123917776426676397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13265325663780737137803725 4974497123917776426676397)
              ·
                refine ⟨1865436421469166160003649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4974497123917776426676397 1865436421469166160003649)
                ·
                  refine ⟨1399077316101874620002737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1865436421469166160003649 1399077316101874620002737)
                  ·
                    refine ⟨1049307987076405965002053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1399077316101874620002737 1049307987076405965002053)
                    ·
                      refine ⟨196745247576826118437885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1049307987076405965002053 196745247576826118437885)
                      ·
                        rfl

theorem cell23_383160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 3, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 3, 3, 2, 2, 4].length) (baseStart_383160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_383160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_383160 prefixEnd_383160 := by exact prefixLift 383160
  have htrace : WordTrace (prefixWord ++ tailWord_383160) baseStart_383160 baseEnd_383160 := by
    simpa [prefixWord, tailWord_383160, baseEnd_383160] using wordTrace_append hprefix tailTrace_383160
  have hstable : (prefixWord ++ tailWord_383160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_383160).length < 2 ^ (prefixWord ++ tailWord_383160).sum := by decide
  have hdescent : baseEnd_383160 < baseStart_383160 := by decide
  rcases family_descends (prefixWord ++ tailWord_383160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_383234 : List Nat := [3, 4, 1, 1, 2, 1, 1, 3, 2, 5]
def baseStart_383234 : Nat := 118140960795 + 383234 * 2 ^ 59
def prefixEnd_383234 : Nat := 4983230072969 + 3 ^ 40 * 383234 * 2
def baseEnd_383234 : Nat := 65594415048419609637515

theorem tailTrace_383234 : CollatzResearch.WordTrace tailWord_383234 prefixEnd_383234 65594415048419609637515 := by
  unfold tailWord_383234
  simp only [CollatzResearch.WordTrace]
  refine ⟨3494423073404036000369189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9318461529077429334317837 3494423073404036000369189)
  ·
    refine ⟨655204326263256750069223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3494423073404036000369189 655204326263256750069223)
    ·
      refine ⟨982806489394885125103835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 655204326263256750069223 982806489394885125103835)
      ·
        refine ⟨1474209734092327687655753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 982806489394885125103835 1474209734092327687655753)
        ·
          refine ⟨1105657300569245765741815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1474209734092327687655753 1105657300569245765741815)
          ·
            refine ⟨1658485950853868648612723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1105657300569245765741815 1658485950853868648612723)
            ·
              refine ⟨2487728926280802972919085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1658485950853868648612723 2487728926280802972919085)
              ·
                refine ⟨932898347355301114844657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2487728926280802972919085 932898347355301114844657)
                ·
                  refine ⟨699673760516475836133493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 932898347355301114844657 699673760516475836133493)
                  ·
                    refine ⟨65594415048419609637515, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 699673760516475836133493 65594415048419609637515)
                    ·
                      rfl

theorem cell23_383234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 1, 3, 2, 5].length) (baseStart_383234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_383234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_383234 prefixEnd_383234 := by exact prefixLift 383234
  have htrace : WordTrace (prefixWord ++ tailWord_383234) baseStart_383234 baseEnd_383234 := by
    simpa [prefixWord, tailWord_383234, baseEnd_383234] using wordTrace_append hprefix tailTrace_383234
  have hstable : (prefixWord ++ tailWord_383234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_383234).length < 2 ^ (prefixWord ++ tailWord_383234).sum := by decide
  have hdescent : baseEnd_383234 < baseStart_383234 := by decide
  rcases family_descends (prefixWord ++ tailWord_383234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_383237 : List Nat := [1, 3, 1, 1, 2, 1, 2, 1, 3, 6, 2]
def baseStart_383237 : Nat := 118140960795 + 383237 * 2 ^ 59
def prefixEnd_383237 : Nat := 4983230072969 + 3 ^ 40 * 383237 * 2
def baseEnd_383237 : Nat := 196784785587222317175031

theorem tailTrace_383237 : CollatzResearch.WordTrace tailWord_383237 prefixEnd_383237 196784785587222317175031 := by
  unfold tailWord_383237
  simp only [CollatzResearch.WordTrace]
  refine ⟨13977801712605275513835965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9318534475070183675890643 13977801712605275513835965)
  ·
    refine ⟨5241675642226978317688487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13977801712605275513835965 5241675642226978317688487)
    ·
      refine ⟨7862513463340467476532731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5241675642226978317688487 7862513463340467476532731)
      ·
        refine ⟨11793770195010701214799097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7862513463340467476532731 11793770195010701214799097)
        ·
          refine ⟨8845327646258025911099323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11793770195010701214799097 8845327646258025911099323)
          ·
            refine ⟨13267991469387038866648985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8845327646258025911099323 13267991469387038866648985)
            ·
              refine ⟨9950993602040279149986739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13267991469387038866648985 9950993602040279149986739)
              ·
                refine ⟨14926490403060418724980109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9950993602040279149986739 14926490403060418724980109)
                ·
                  refine ⟨5597433901147657021867541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14926490403060418724980109 5597433901147657021867541)
                  ·
                    refine ⟨262379714116296422900041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5597433901147657021867541 262379714116296422900041)
                    ·
                      refine ⟨196784785587222317175031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 262379714116296422900041 196784785587222317175031)
                      ·
                        rfl

theorem cell23_383237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 1, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 1, 3, 6, 2].length) (baseStart_383237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_383237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_383237 prefixEnd_383237 := by exact prefixLift 383237
  have htrace : WordTrace (prefixWord ++ tailWord_383237) baseStart_383237 baseEnd_383237 := by
    simpa [prefixWord, tailWord_383237, baseEnd_383237] using wordTrace_append hprefix tailTrace_383237
  have hstable : (prefixWord ++ tailWord_383237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_383237).length < 2 ^ (prefixWord ++ tailWord_383237).sum := by decide
  have hdescent : baseEnd_383237 < baseStart_383237 := by decide
  rcases family_descends (prefixWord ++ tailWord_383237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_383280 : List Nat := [2, 1, 1, 1, 2, 2, 2, 1, 3, 2, 6]
def baseStart_383280 : Nat := 118140960795 + 383280 * 2 ^ 59
def prefixEnd_383280 : Nat := 4983230072969 + 3 ^ 40 * 383280 * 2
def baseEnd_383280 : Nat := 196806865255365648937333

theorem tailTrace_383280 : CollatzResearch.WordTrace tailWord_383280 prefixEnd_383280 196806865255365648937333 := by
  unfold tailWord_383280
  simp only [CollatzResearch.WordTrace]
  refine ⟨6989685025724746928825647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9319580034299662571767529 6989685025724746928825647)
  ·
    refine ⟨10484527538587120393238471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6989685025724746928825647 10484527538587120393238471)
    ·
      refine ⟨15726791307880680589857707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10484527538587120393238471 15726791307880680589857707)
      ·
        refine ⟨23590186961821020884786561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15726791307880680589857707 23590186961821020884786561)
        ·
          refine ⟨17692640221365765663589921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23590186961821020884786561 17692640221365765663589921)
          ·
            refine ⟨13269480166024324247692441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17692640221365765663589921 13269480166024324247692441)
            ·
              refine ⟨9952110124518243185769331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13269480166024324247692441 9952110124518243185769331)
              ·
                refine ⟨14928165186777364778653997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9952110124518243185769331 14928165186777364778653997)
                ·
                  refine ⟨5598061945041511791995249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14928165186777364778653997 5598061945041511791995249)
                  ·
                    refine ⟨4198546458781133843996437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5598061945041511791995249 4198546458781133843996437)
                    ·
                      refine ⟨196806865255365648937333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 4198546458781133843996437 196806865255365648937333)
                      ·
                        rfl

theorem cell23_383280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 1, 3, 2, 6].length) (baseStart_383280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_383280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_383280 prefixEnd_383280 := by exact prefixLift 383280
  have htrace : WordTrace (prefixWord ++ tailWord_383280) baseStart_383280 baseEnd_383280 := by
    simpa [prefixWord, tailWord_383280, baseEnd_383280] using wordTrace_append hprefix tailTrace_383280
  have hstable : (prefixWord ++ tailWord_383280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_383280).length < 2 ^ (prefixWord ++ tailWord_383280).sum := by decide
  have hdescent : baseEnd_383280 < baseStart_383280 := by decide
  rcases family_descends (prefixWord ++ tailWord_383280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_383327 : List Nat := [1, 1, 2, 3, 1, 2, 2, 1, 5, 1, 4]
def baseStart_383327 : Nat := 118140960795 + 383327 * 2 ^ 59
def prefixEnd_383327 : Nat := 4983230072969 + 3 ^ 40 * 383327 * 2
def baseEnd_383327 : Nat := 196830998846126965049617

theorem tailTrace_383327 : CollatzResearch.WordTrace tailWord_383327 prefixEnd_383327 196830998846126965049617 := by
  unfold tailWord_383327
  simp only [CollatzResearch.WordTrace]
  refine ⟨13981084282279220884612235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9320722854852813923074823 13981084282279220884612235)
  ·
    refine ⟨20971626423418831326918353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13981084282279220884612235 20971626423418831326918353)
    ·
      refine ⟨15728719817564123495188765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20971626423418831326918353 15728719817564123495188765)
      ·
        refine ⟨5898269931586546310695787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15728719817564123495188765 5898269931586546310695787)
        ·
          refine ⟨8847404897379819466043681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5898269931586546310695787 8847404897379819466043681)
          ·
            refine ⟨6635553673034864599532761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8847404897379819466043681 6635553673034864599532761)
            ·
              refine ⟨4976665254776148449649571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6635553673034864599532761 4976665254776148449649571)
              ·
                refine ⟨7464997882164222674474357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4976665254776148449649571 7464997882164222674474357)
                ·
                  refine ⟨699843551452895875731971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 7464997882164222674474357 699843551452895875731971)
                  ·
                    refine ⟨1049765327179343813597957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 699843551452895875731971 1049765327179343813597957)
                    ·
                      refine ⟨196830998846126965049617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1049765327179343813597957 196830998846126965049617)
                      ·
                        rfl

theorem cell23_383327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 2, 1, 5, 1, 4].length) (baseStart_383327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_383327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_383327 prefixEnd_383327 := by exact prefixLift 383327
  have htrace : WordTrace (prefixWord ++ tailWord_383327) baseStart_383327 baseEnd_383327 := by
    simpa [prefixWord, tailWord_383327, baseEnd_383327] using wordTrace_append hprefix tailTrace_383327
  have hstable : (prefixWord ++ tailWord_383327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_383327).length < 2 ^ (prefixWord ++ tailWord_383327).sum := by decide
  have hdescent : baseEnd_383327 < baseStart_383327 := by decide
  rcases family_descends (prefixWord ++ tailWord_383327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_383344 : List Nat := [2, 1, 1, 1, 4, 3, 1, 4, 1, 1, 4]
def baseStart_383344 : Nat := 118140960795 + 383344 * 2 ^ 59
def prefixEnd_383344 : Nat := 4983230072969 + 3 ^ 40 * 383344 * 2
def baseEnd_383344 : Nat := 196839728017253398537039

theorem tailTrace_383344 : CollatzResearch.WordTrace tailWord_383344 prefixEnd_383344 196839728017253398537039 := by
  unfold tailWord_383344
  simp only [CollatzResearch.WordTrace]
  refine ⟨6990852161608816393990543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9321136215478421858654057 6990852161608816393990543)
  ·
    refine ⟨10486278242413224590985815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6990852161608816393990543 10486278242413224590985815)
    ·
      refine ⟨15729417363619836886478723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10486278242413224590985815 15729417363619836886478723)
      ·
        refine ⟨23594126045429755329718085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15729417363619836886478723 23594126045429755329718085)
        ·
          refine ⟨4423898633518079124322141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23594126045429755329718085 4423898633518079124322141)
          ·
            refine ⟨1658961987569279671620803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4423898633518079124322141 1658961987569279671620803)
            ·
              refine ⟨2488442981353919507431205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1658961987569279671620803 2488442981353919507431205)
              ·
                refine ⟨466583059003859907643351, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2488442981353919507431205 466583059003859907643351)
                ·
                  refine ⟨699874588505789861465027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 466583059003859907643351 699874588505789861465027)
                  ·
                    refine ⟨1049811882758684792197541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 699874588505789861465027 1049811882758684792197541)
                    ·
                      refine ⟨196839728017253398537039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1049811882758684792197541 196839728017253398537039)
                      ·
                        rfl

theorem cell23_383344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 1, 4, 1, 1, 4].length) (baseStart_383344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_383344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_383344 prefixEnd_383344 := by exact prefixLift 383344
  have htrace : WordTrace (prefixWord ++ tailWord_383344) baseStart_383344 baseEnd_383344 := by
    simpa [prefixWord, tailWord_383344, baseEnd_383344] using wordTrace_append hprefix tailTrace_383344
  have hstable : (prefixWord ++ tailWord_383344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_383344).length < 2 ^ (prefixWord ++ tailWord_383344).sum := by decide
  have hdescent : baseEnd_383344 < baseStart_383344 := by decide
  rcases family_descends (prefixWord ++ tailWord_383344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_383361 : List Nat := [1, 2, 4, 3, 1, 1, 2, 3, 1, 1, 4]
def baseStart_383361 : Nat := 118140960795 + 383361 * 2 ^ 59
def prefixEnd_383361 : Nat := 4983230072969 + 3 ^ 40 * 383361 * 2
def baseEnd_383361 : Nat := 196848457188379832024461

theorem tailTrace_383361 : CollatzResearch.WordTrace tailWord_383361 prefixEnd_383361 196848457188379832024461 := by
  unfold tailWord_383361
  simp only [CollatzResearch.WordTrace]
  refine ⟨13982324364156044691349937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9321549576104029794233291 13982324364156044691349937)
  ·
    refine ⟨10486743273117033518512453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13982324364156044691349937 10486743273117033518512453)
    ·
      refine ⟨1966264363709443784721085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10486743273117033518512453 1966264363709443784721085)
      ·
        refine ⟨737349136391041419270407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1966264363709443784721085 737349136391041419270407)
        ·
          refine ⟨1106023704586562128905611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 737349136391041419270407 1106023704586562128905611)
          ·
            refine ⟨1659035556879843193358417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1106023704586562128905611 1659035556879843193358417)
            ·
              refine ⟨1244276667659882395018813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1659035556879843193358417 1244276667659882395018813)
              ·
                refine ⟨466603750372455898132055, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1244276667659882395018813 466603750372455898132055)
                ·
                  refine ⟨699905625558683847198083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 466603750372455898132055 699905625558683847198083)
                  ·
                    refine ⟨1049858438338025770797125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 699905625558683847198083 1049858438338025770797125)
                    ·
                      refine ⟨196848457188379832024461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1049858438338025770797125 196848457188379832024461)
                      ·
                        rfl

theorem cell23_383361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 2, 3, 1, 1, 4].length) (baseStart_383361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_383361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_383361 prefixEnd_383361 := by exact prefixLift 383361
  have htrace : WordTrace (prefixWord ++ tailWord_383361) baseStart_383361 baseEnd_383361 := by
    simpa [prefixWord, tailWord_383361, baseEnd_383361] using wordTrace_append hprefix tailTrace_383361
  have hstable : (prefixWord ++ tailWord_383361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_383361).length < 2 ^ (prefixWord ++ tailWord_383361).sum := by decide
  have hdescent : baseEnd_383361 < baseStart_383361 := by decide
  rcases family_descends (prefixWord ++ tailWord_383361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_383364 : List Nat := [2, 3, 2, 1, 1, 2, 4, 1, 1, 1, 5]
def baseStart_383364 : Nat := 118140960795 + 383364 * 2 ^ 59
def prefixEnd_383364 : Nat := 4983230072969 + 3 ^ 40 * 383364 * 2
def baseEnd_383364 : Nat := 196849997630343320286947

theorem tailTrace_383364 : CollatzResearch.WordTrace tailWord_383364 prefixEnd_383364 196849997630343320286947 := by
  unfold tailWord_383364
  simp only [CollatzResearch.WordTrace]
  refine ⟨6991216891572588101854573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9321622522096784135806097 6991216891572588101854573)
  ·
    refine ⟨2621706334339720538195465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6991216891572588101854573 2621706334339720538195465)
    ·
      refine ⟨1966279750754790403646599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2621706334339720538195465 1966279750754790403646599)
      ·
        refine ⟨2949419626132185605469899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1966279750754790403646599 2949419626132185605469899)
        ·
          refine ⟨4424129439198278408204849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2949419626132185605469899 4424129439198278408204849)
          ·
            refine ⟨3318097079398708806153637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4424129439198278408204849 3318097079398708806153637)
            ·
              refine ⟨622143202387257901153807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3318097079398708806153637 622143202387257901153807)
              ·
                refine ⟨933214803580886851730711, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 622143202387257901153807 933214803580886851730711)
                ·
                  refine ⟨1399822205371330277596067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 933214803580886851730711 1399822205371330277596067)
                  ·
                    refine ⟨2099733308056995416394101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1399822205371330277596067 2099733308056995416394101)
                    ·
                      refine ⟨196849997630343320286947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2099733308056995416394101 196849997630343320286947)
                      ·
                        rfl

theorem cell23_383364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 4, 1, 1, 1, 5].length) (baseStart_383364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_383364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_383364 prefixEnd_383364 := by exact prefixLift 383364
  have htrace : WordTrace (prefixWord ++ tailWord_383364) baseStart_383364 baseEnd_383364 := by
    simpa [prefixWord, tailWord_383364, baseEnd_383364] using wordTrace_append hprefix tailTrace_383364
  have hstable : (prefixWord ++ tailWord_383364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_383364).length < 2 ^ (prefixWord ++ tailWord_383364).sum := by decide
  have hdescent : baseEnd_383364 < baseStart_383364 := by decide
  rcases family_descends (prefixWord ++ tailWord_383364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_383374 : List Nat := [4, 1, 1, 4, 1, 1, 1, 2, 1, 1, 6]
def baseStart_383374 : Nat := 118140960795 + 383374 * 2 ^ 59
def prefixEnd_383374 : Nat := 4983230072969 + 3 ^ 40 * 383374 * 2
def baseEnd_383374 : Nat := 196855132436888281161901

theorem tailTrace_383374 : CollatzResearch.WordTrace tailWord_383374 prefixEnd_383374 196855132436888281161901 := by
  unfold tailWord_383374
  simp only [CollatzResearch.WordTrace]
  refine ⟨1747849814138618488946647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9321865675405965274382117 1747849814138618488946647)
  ·
    refine ⟨2621774721207927733419971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1747849814138618488946647 2621774721207927733419971)
    ·
      refine ⟨3932662081811891600129957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2621774721207927733419971 3932662081811891600129957)
      ·
        refine ⟨737374140339729675024367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3932662081811891600129957 737374140339729675024367)
        ·
          refine ⟨1106061210509594512536551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 737374140339729675024367 1106061210509594512536551)
          ·
            refine ⟨1659091815764391768804827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1106061210509594512536551 1659091815764391768804827)
            ·
              refine ⟨2488637723646587653207241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1659091815764391768804827 2488637723646587653207241)
              ·
                refine ⟨1866478292734940739905431, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2488637723646587653207241 1866478292734940739905431)
                ·
                  refine ⟨2799717439102411109858147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1866478292734940739905431 2799717439102411109858147)
                  ·
                    refine ⟨4199576158653616664787221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2799717439102411109858147 4199576158653616664787221)
                    ·
                      refine ⟨196855132436888281161901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 4199576158653616664787221 196855132436888281161901)
                      ·
                        rfl

theorem cell23_383374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 1, 2, 1, 1, 6].length) (baseStart_383374 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_383374 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_383374 prefixEnd_383374 := by exact prefixLift 383374
  have htrace : WordTrace (prefixWord ++ tailWord_383374) baseStart_383374 baseEnd_383374 := by
    simpa [prefixWord, tailWord_383374, baseEnd_383374] using wordTrace_append hprefix tailTrace_383374
  have hstable : (prefixWord ++ tailWord_383374).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_383374).length < 2 ^ (prefixWord ++ tailWord_383374).sum := by decide
  have hdescent : baseEnd_383374 < baseStart_383374 := by decide
  rcases family_descends (prefixWord ++ tailWord_383374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_383377 : List Nat := [1, 2, 2, 1, 1, 1, 2, 1, 2, 7, 3]
def baseStart_383377 : Nat := 118140960795 + 383377 * 2 ^ 59
def prefixEnd_383377 : Nat := 4983230072969 + 3 ^ 40 * 383377 * 2
def baseEnd_383377 : Nat := 196856672878851769424387

theorem tailTrace_383377 : CollatzResearch.WordTrace tailWord_383377 prefixEnd_383377 196856672878851769424387 := by
  unfold tailWord_383377
  simp only [CollatzResearch.WordTrace]
  refine ⟨13982907932098079423932385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9321938621398719615954923 13982907932098079423932385)
  ·
    refine ⟨10487180949073559567949289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13982907932098079423932385 10487180949073559567949289)
    ·
      refine ⟨7865385711805169675961967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10487180949073559567949289 7865385711805169675961967)
      ·
        refine ⟨11798078567707754513942951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7865385711805169675961967 11798078567707754513942951)
        ·
          refine ⟨17697117851561631770914427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11798078567707754513942951 17697117851561631770914427)
          ·
            refine ⟨26545676777342447656371641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17697117851561631770914427 26545676777342447656371641)
            ·
              refine ⟨19909257583006835742278731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26545676777342447656371641 19909257583006835742278731)
              ·
                refine ⟨29863886374510253613418097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19909257583006835742278731 29863886374510253613418097)
                ·
                  refine ⟨22397914780882690210063573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29863886374510253613418097 22397914780882690210063573)
                  ·
                    refine ⟨524951127676938051798365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 22397914780882690210063573 524951127676938051798365)
                    ·
                      refine ⟨196856672878851769424387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 524951127676938051798365 196856672878851769424387)
                      ·
                        rfl

theorem cell23_383377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 7, 3].length) (baseStart_383377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_383377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_383377 prefixEnd_383377 := by exact prefixLift 383377
  have htrace : WordTrace (prefixWord ++ tailWord_383377) baseStart_383377 baseEnd_383377 := by
    simpa [prefixWord, tailWord_383377, baseEnd_383377] using wordTrace_append hprefix tailTrace_383377
  have hstable : (prefixWord ++ tailWord_383377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_383377).length < 2 ^ (prefixWord ++ tailWord_383377).sum := by decide
  have hdescent : baseEnd_383377 < baseStart_383377 := by decide
  rcases family_descends (prefixWord ++ tailWord_383377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_383384 : List Nat := [2, 1, 2, 5, 1, 2, 2, 8]
def baseStart_383384 : Nat := 118140960795 + 383384 * 2 ^ 59
def prefixEnd_383384 : Nat := 4983230072969 + 3 ^ 40 * 383384 * 2
def baseEnd_383384 : Nat := 7291121009016046001365

theorem tailTrace_383384 : CollatzResearch.WordTrace tailWord_383384 prefixEnd_383384 7291121009016046001365 := by
  unfold tailWord_383384
  simp only [CollatzResearch.WordTrace]
  refine ⟨6991581621536359809718603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9322108828715146412958137 6991581621536359809718603)
  ·
    refine ⟨10487372432304539714577905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6991581621536359809718603 10487372432304539714577905)
    ·
      refine ⟨7865529324228404785933429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10487372432304539714577905 7865529324228404785933429)
      ·
        refine ⟨737393374146412948681259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 7865529324228404785933429 737393374146412948681259)
        ·
          refine ⟨1106090061219619423021889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 737393374146412948681259 1106090061219619423021889)
          ·
            refine ⟨829567545914714567266417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1106090061219619423021889 829567545914714567266417)
            ·
              refine ⟨622175659436035925449813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 829567545914714567266417 622175659436035925449813)
              ·
                refine ⟨7291121009016046001365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 622175659436035925449813 7291121009016046001365)
                ·
                  rfl

theorem cell23_383384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 2, 2, 8].length) (baseStart_383384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_383384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_383384 prefixEnd_383384 := by exact prefixLift 383384
  have htrace : WordTrace (prefixWord ++ tailWord_383384) baseStart_383384 baseEnd_383384 := by
    simpa [prefixWord, tailWord_383384, baseEnd_383384] using wordTrace_append hprefix tailTrace_383384
  have hstable : (prefixWord ++ tailWord_383384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_383384).length < 2 ^ (prefixWord ++ tailWord_383384).sum := by decide
  have hdescent : baseEnd_383384 < baseStart_383384 := by decide
  rcases family_descends (prefixWord ++ tailWord_383384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_383412 : List Nat := [2, 5, 2, 2, 1, 1, 3, 1, 1, 1, 4]
def baseStart_383412 : Nat := 118140960795 + 383412 * 2 ^ 59
def prefixEnd_383412 : Nat := 4983230072969 + 3 ^ 40 * 383412 * 2
def baseEnd_383412 : Nat := 196874644701759132486727

theorem tailTrace_383412 : CollatzResearch.WordTrace tailWord_383412 prefixEnd_383412 196874644701759132486727 := by
  unfold tailWord_383412
  simp only [CollatzResearch.WordTrace]
  refine ⟨6992092243485640200728245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9322789657980853600970993 6992092243485640200728245)
  ·
    refine ⟨655508647826778768818273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 6992092243485640200728245 655508647826778768818273)
    ·
      refine ⟨491631485870084076613705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 655508647826778768818273 491631485870084076613705)
      ·
        refine ⟨368723614402563057460279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 491631485870084076613705 368723614402563057460279)
        ·
          refine ⟨553085421603844586190419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 368723614402563057460279 553085421603844586190419)
          ·
            refine ⟨829628132405766879285629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 553085421603844586190419 829628132405766879285629)
            ·
              refine ⟨311110549652162579732111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 829628132405766879285629 311110549652162579732111)
              ·
                refine ⟨466665824478243869598167, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 311110549652162579732111 466665824478243869598167)
                ·
                  refine ⟨699998736717365804397251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 466665824478243869598167 699998736717365804397251)
                  ·
                    refine ⟨1049998105076048706595877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 699998736717365804397251 1049998105076048706595877)
                    ·
                      refine ⟨196874644701759132486727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1049998105076048706595877 196874644701759132486727)
                      ·
                        rfl

theorem cell23_383412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 1, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 1, 3, 1, 1, 1, 4].length) (baseStart_383412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_383412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_383412 prefixEnd_383412 := by exact prefixLift 383412
  have htrace : WordTrace (prefixWord ++ tailWord_383412) baseStart_383412 baseEnd_383412 := by
    simpa [prefixWord, tailWord_383412, baseEnd_383412] using wordTrace_append hprefix tailTrace_383412
  have hstable : (prefixWord ++ tailWord_383412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_383412).length < 2 ^ (prefixWord ++ tailWord_383412).sum := by decide
  have hdescent : baseEnd_383412 < baseStart_383412 := by decide
  rcases family_descends (prefixWord ++ tailWord_383412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_383427 : List Nat := [1, 1, 1, 3, 1, 1, 3, 4, 2, 6]
def baseStart_383427 : Nat := 118140960795 + 383427 * 2 ^ 59
def prefixEnd_383427 : Nat := 4983230072969 + 3 ^ 40 * 383427 * 2
def baseEnd_383427 : Nat := 65627448970525524599719

theorem tailTrace_383427 : CollatzResearch.WordTrace tailWord_383427 prefixEnd_383427 65627448970525524599719 := by
  unfold tailWord_383427
  simp only [CollatzResearch.WordTrace]
  refine ⟨13984731581916937963252535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9323154387944625308835023 13984731581916937963252535)
  ·
    refine ⟨20977097372875406944878803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13984731581916937963252535 20977097372875406944878803)
    ·
      refine ⟨31465646059313110417318205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20977097372875406944878803 31465646059313110417318205)
      ·
        refine ⟨11799617272242416406494327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31465646059313110417318205 11799617272242416406494327)
        ·
          refine ⟨17699425908363624609741491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11799617272242416406494327 17699425908363624609741491)
          ·
            refine ⟨26549138862545436914612237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17699425908363624609741491 26549138862545436914612237)
            ·
              refine ⟨9955927073454538842979589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26549138862545436914612237 9955927073454538842979589)
              ·
                refine ⟨1866736326272726033058673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9955927073454538842979589 1866736326272726033058673)
                ·
                  refine ⟨1400052244704544524794005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1866736326272726033058673 1400052244704544524794005)
                  ·
                    refine ⟨65627448970525524599719, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1400052244704544524794005 65627448970525524599719)
                    ·
                      rfl

theorem cell23_383427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 4, 2, 6].length) (baseStart_383427 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_383427 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_383427 prefixEnd_383427 := by exact prefixLift 383427
  have htrace : WordTrace (prefixWord ++ tailWord_383427) baseStart_383427 baseEnd_383427 := by
    simpa [prefixWord, tailWord_383427, baseEnd_383427] using wordTrace_append hprefix tailTrace_383427
  have hstable : (prefixWord ++ tailWord_383427).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_383427).length < 2 ^ (prefixWord ++ tailWord_383427).sum := by decide
  have hdescent : baseEnd_383427 < baseStart_383427 := by decide
  rcases family_descends (prefixWord ++ tailWord_383427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_383444 : List Nat := [2, 4, 1, 2, 2, 1, 1, 1, 1, 8]
def baseStart_383444 : Nat := 118140960795 + 383444 * 2 ^ 59
def prefixEnd_383444 : Nat := 4983230072969 + 3 ^ 40 * 383444 * 2
def baseEnd_383444 : Nat := 65630358694234335762193

theorem tailTrace_383444 : CollatzResearch.WordTrace tailWord_383444 prefixEnd_383444 65630358694234335762193 := by
  unfold tailWord_383444
  simp only [CollatzResearch.WordTrace]
  refine ⟨6992675811427674933310693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9323567748570233244414257 6992675811427674933310693)
  ·
    refine ⟨1311126714642689049995755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6992675811427674933310693 1311126714642689049995755)
    ·
      refine ⟨1966690071964033574993633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1311126714642689049995755 1966690071964033574993633)
      ·
        refine ⟨1475017553973025181245225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1966690071964033574993633 1475017553973025181245225)
        ·
          refine ⟨1106263165479768885933919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1475017553973025181245225 1106263165479768885933919)
          ·
            refine ⟨1659394748219653328900879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1106263165479768885933919 1659394748219653328900879)
            ·
              refine ⟨2489092122329479993351319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1659394748219653328900879 2489092122329479993351319)
              ·
                refine ⟨3733638183494219990026979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2489092122329479993351319 3733638183494219990026979)
                ·
                  refine ⟨5600457275241329985040469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3733638183494219990026979 5600457275241329985040469)
                  ·
                    refine ⟨65630358694234335762193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 5600457275241329985040469 65630358694234335762193)
                    ·
                      rfl

theorem cell23_383444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 1, 1, 1, 8].length) (baseStart_383444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_383444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_383444 prefixEnd_383444 := by exact prefixLift 383444
  have htrace : WordTrace (prefixWord ++ tailWord_383444) baseStart_383444 baseEnd_383444 := by
    simpa [prefixWord, tailWord_383444, baseEnd_383444] using wordTrace_append hprefix tailTrace_383444
  have hstable : (prefixWord ++ tailWord_383444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_383444).length < 2 ^ (prefixWord ++ tailWord_383444).sum := by decide
  have hdescent : baseEnd_383444 < baseStart_383444 := by decide
  rcases family_descends (prefixWord ++ tailWord_383444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_383502 : List Nat := [4, 1, 1, 2, 3, 2, 3, 1, 2, 2, 2]
def baseStart_383502 : Nat := 118140960795 + 383502 * 2 ^ 59
def prefixEnd_383502 : Nat := 4983230072969 + 3 ^ 40 * 383502 * 2
def baseEnd_383502 : Nat := 196920857960663780361313

theorem tailTrace_383502 : CollatzResearch.WordTrace tailWord_383502 prefixEnd_383502 196920857960663780361313 := by
  unfold tailWord_383502
  simp only [CollatzResearch.WordTrace]
  refine ⟨1748433382080653221529095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9324978037763483848155173 1748433382080653221529095)
  ·
    refine ⟨2622650073120979832293643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1748433382080653221529095 2622650073120979832293643)
    ·
      refine ⟨3933975109681469748440465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2622650073120979832293643 3933975109681469748440465)
      ·
        refine ⟨2950481332261102311330349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3933975109681469748440465 2950481332261102311330349)
        ·
          refine ⟨1106430499597913366748881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2950481332261102311330349 1106430499597913366748881)
          ·
            refine ⟨829822874698435025061661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1106430499597913366748881 829822874698435025061661)
            ·
              refine ⟨311183578011913134398123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 829822874698435025061661 311183578011913134398123)
              ·
                refine ⟨466775367017869701597185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 311183578011913134398123 466775367017869701597185)
                ·
                  refine ⟨350081525263402276197889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 466775367017869701597185 350081525263402276197889)
                  ·
                    refine ⟨262561143947551707148417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 350081525263402276197889 262561143947551707148417)
                    ·
                      refine ⟨196920857960663780361313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 262561143947551707148417 196920857960663780361313)
                      ·
                        rfl

theorem cell23_383502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 2, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 2, 3, 1, 2, 2, 2].length) (baseStart_383502 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_383502 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_383502 prefixEnd_383502 := by exact prefixLift 383502
  have htrace : WordTrace (prefixWord ++ tailWord_383502) baseStart_383502 baseEnd_383502 := by
    simpa [prefixWord, tailWord_383502, baseEnd_383502] using wordTrace_append hprefix tailTrace_383502
  have hstable : (prefixWord ++ tailWord_383502).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_383502).length < 2 ^ (prefixWord ++ tailWord_383502).sum := by decide
  have hdescent : baseEnd_383502 < baseStart_383502 := by decide
  rcases family_descends (prefixWord ++ tailWord_383502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_383541 : List Nat := [1, 3, 3, 1, 1, 2, 3, 2, 2, 1, 4]
def baseStart_383541 : Nat := 118140960795 + 383541 * 2 ^ 59
def prefixEnd_383541 : Nat := 4983230072969 + 3 ^ 40 * 383541 * 2
def baseEnd_383541 : Nat := 196940883706189127773633

theorem tailTrace_383541 : CollatzResearch.WordTrace tailWord_383541 prefixEnd_383541 196940883706189127773633 := by
  unfold tailWord_383541
  simp only [CollatzResearch.WordTrace]
  refine ⟨13988889503503935432902477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9325926335669290288601651 13988889503503935432902477)
  ·
    refine ⟨5245833563813975787338429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13988889503503935432902477 5245833563813975787338429)
    ·
      refine ⟨1967187586430240920251911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5245833563813975787338429 1967187586430240920251911)
      ·
        refine ⟨2950781379645361380377867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1967187586430240920251911 2950781379645361380377867)
        ·
          refine ⟨4426172069468042070566801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2950781379645361380377867 4426172069468042070566801)
          ·
            refine ⟨3319629052101031552925101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4426172069468042070566801 3319629052101031552925101)
            ·
              refine ⟨1244860894537886832346913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3319629052101031552925101 1244860894537886832346913)
              ·
                refine ⟨933645670903415124260185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1244860894537886832346913 933645670903415124260185)
                ·
                  refine ⟨700234253177561343195139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 933645670903415124260185 700234253177561343195139)
                  ·
                    refine ⟨1050351379766342014792709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 700234253177561343195139 1050351379766342014792709)
                    ·
                      refine ⟨196940883706189127773633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1050351379766342014792709 196940883706189127773633)
                      ·
                        rfl

theorem cell23_383541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 3, 2, 2, 1, 4].length) (baseStart_383541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_383541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_383541 prefixEnd_383541 := by exact prefixLift 383541
  have htrace : WordTrace (prefixWord ++ tailWord_383541) baseStart_383541 baseEnd_383541 := by
    simpa [prefixWord, tailWord_383541, baseEnd_383541] using wordTrace_append hprefix tailTrace_383541
  have hstable : (prefixWord ++ tailWord_383541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_383541).length < 2 ^ (prefixWord ++ tailWord_383541).sum := by decide
  have hdescent : baseEnd_383541 < baseStart_383541 := by decide
  rcases family_descends (prefixWord ++ tailWord_383541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_383598 : List Nat := [4, 1, 2, 2, 2, 2, 2, 2, 6]
def baseStart_383598 : Nat := 118140960795 + 383598 * 2 ^ 59
def prefixEnd_383598 : Nat := 4983230072969 + 3 ^ 40 * 383598 * 2
def baseEnd_383598 : Nat := 21885572455943933862319

theorem tailTrace_383598 : CollatzResearch.WordTrace tailWord_383598 prefixEnd_383598 21885572455943933862319 := by
  unfold tailWord_383598
  simp only [CollatzResearch.WordTrace]
  refine ⟨1748871058037179270965931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9327312309531622778484965 1748871058037179270965931)
  ·
    refine ⟨2623306587055768906448897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1748871058037179270965931 2623306587055768906448897)
    ·
      refine ⟨1967479940291826679836673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2623306587055768906448897 1967479940291826679836673)
      ·
        refine ⟨1475609955218870009877505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1967479940291826679836673 1475609955218870009877505)
        ·
          refine ⟨1106707466414152507408129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1475609955218870009877505 1106707466414152507408129)
          ·
            refine ⟨830030599810614380556097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1106707466414152507408129 830030599810614380556097)
            ·
              refine ⟨622522949857960785417073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 830030599810614380556097 622522949857960785417073)
              ·
                refine ⟨466892212393470589062805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 622522949857960785417073 466892212393470589062805)
                ·
                  refine ⟨21885572455943933862319, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 466892212393470589062805 21885572455943933862319)
                  ·
                    rfl

theorem cell23_383598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 2, 2, 2, 6].length) (baseStart_383598 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_383598 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_383598 prefixEnd_383598 := by exact prefixLift 383598
  have htrace : WordTrace (prefixWord ++ tailWord_383598) baseStart_383598 baseEnd_383598 := by
    simpa [prefixWord, tailWord_383598, baseEnd_383598] using wordTrace_append hprefix tailTrace_383598
  have hstable : (prefixWord ++ tailWord_383598).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_383598).length < 2 ^ (prefixWord ++ tailWord_383598).sum := by decide
  have hdescent : baseEnd_383598 < baseStart_383598 := by decide
  rcases family_descends (prefixWord ++ tailWord_383598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_383601 : List Nat := [1, 2, 2, 2, 1, 1, 1, 1, 5, 5, 2]
def baseStart_383601 : Nat := 118140960795 + 383601 * 2 ^ 59
def prefixEnd_383601 : Nat := 4983230072969 + 3 ^ 40 * 383601 * 2
def baseEnd_383601 : Nat := 196971692545458893023357

theorem tailTrace_383601 : CollatzResearch.WordTrace tailWord_383601 prefixEnd_383601 196971692545458893023357 := by
  unfold tailWord_383601
  simp only [CollatzResearch.WordTrace]
  refine ⟨13991077883286565680086657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9327385255524377120057771 13991077883286565680086657)
  ·
    refine ⟨10493308412464924260064993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13991077883286565680086657 10493308412464924260064993)
    ·
      refine ⟨7869981309348693195048745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10493308412464924260064993 7869981309348693195048745)
      ·
        refine ⟨5902485982011519896286559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7869981309348693195048745 5902485982011519896286559)
        ·
          refine ⟨8853728973017279844429839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5902485982011519896286559 8853728973017279844429839)
          ·
            refine ⟨13280593459525919766644759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8853728973017279844429839 13280593459525919766644759)
            ·
              refine ⟨19920890189288879649967139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13280593459525919766644759 19920890189288879649967139)
              ·
                refine ⟨29881335283933319474950709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19920890189288879649967139 29881335283933319474950709)
                ·
                  refine ⟨2801375182868748700776629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 29881335283933319474950709 2801375182868748700776629)
                  ·
                    refine ⟨262628923393945190697809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2801375182868748700776629 262628923393945190697809)
                    ·
                      refine ⟨196971692545458893023357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 262628923393945190697809 196971692545458893023357)
                      ·
                        rfl

theorem cell23_383601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 1, 5, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 1, 5, 5, 2].length) (baseStart_383601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_383601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_383601 prefixEnd_383601 := by exact prefixLift 383601
  have htrace : WordTrace (prefixWord ++ tailWord_383601) baseStart_383601 baseEnd_383601 := by
    simpa [prefixWord, tailWord_383601, baseEnd_383601] using wordTrace_append hprefix tailTrace_383601
  have hstable : (prefixWord ++ tailWord_383601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_383601).length < 2 ^ (prefixWord ++ tailWord_383601).sum := by decide
  have hdescent : baseEnd_383601 < baseStart_383601 := by decide
  rcases family_descends (prefixWord ++ tailWord_383601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_383631 : List Nat := [1, 1, 2, 1, 1, 1, 1, 5, 2, 6, 2]
def baseStart_383631 : Nat := 118140960795 + 383631 * 2 ^ 59
def prefixEnd_383631 : Nat := 4983230072969 + 3 ^ 40 * 383631 * 2
def baseEnd_383631 : Nat := 196987096965093775648219

theorem tailTrace_383631 : CollatzResearch.WordTrace tailWord_383631 prefixEnd_383631 196987096965093775648219 := by
  unfold tailWord_383631
  simp only [CollatzResearch.WordTrace]
  refine ⟨13992172073177880803678747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9328114715451920535785831 13992172073177880803678747)
  ·
    refine ⟨20988258109766821205518121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13992172073177880803678747 20988258109766821205518121)
    ·
      refine ⟨15741193582325115904138591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20988258109766821205518121 15741193582325115904138591)
      ·
        refine ⟨23611790373487673856207887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15741193582325115904138591 23611790373487673856207887)
        ·
          refine ⟨35417685560231510784311831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23611790373487673856207887 35417685560231510784311831)
          ·
            refine ⟨53126528340347266176467747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35417685560231510784311831 53126528340347266176467747)
            ·
              refine ⟨79689792510520899264701621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53126528340347266176467747 79689792510520899264701621)
              ·
                refine ⟨7470918047861334306065777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 79689792510520899264701621 7470918047861334306065777)
                ·
                  refine ⟨5603188535896000729549333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7470918047861334306065777 5603188535896000729549333)
                  ·
                    refine ⟨262649462620125034197625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5603188535896000729549333 262649462620125034197625)
                    ·
                      refine ⟨196987096965093775648219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 262649462620125034197625 196987096965093775648219)
                      ·
                        rfl

theorem cell23_383631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 5, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 5, 2, 6, 2].length) (baseStart_383631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_383631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_383631 prefixEnd_383631 := by exact prefixLift 383631
  have htrace : WordTrace (prefixWord ++ tailWord_383631) baseStart_383631 baseEnd_383631 := by
    simpa [prefixWord, tailWord_383631, baseEnd_383631] using wordTrace_append hprefix tailTrace_383631
  have hstable : (prefixWord ++ tailWord_383631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_383631).length < 2 ^ (prefixWord ++ tailWord_383631).sum := by decide
  have hdescent : baseEnd_383631 < baseStart_383631 := by decide
  rcases family_descends (prefixWord ++ tailWord_383631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_383641 : List Nat := [1, 2, 1, 2, 1, 2, 4, 2, 4, 4]
def baseStart_383641 : Nat := 118140960795 + 383641 * 2 ^ 59
def prefixEnd_383641 : Nat := 4983230072969 + 3 ^ 40 * 383641 * 2
def baseEnd_383641 : Nat := 65664077257212912174391

theorem tailTrace_383641 : CollatzResearch.WordTrace tailWord_383641 prefixEnd_383641 65664077257212912174391 := by
  unfold tailWord_383641
  simp only [CollatzResearch.WordTrace]
  refine ⟨13992536803141652511542777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9328357868761101674361851 13992536803141652511542777)
  ·
    refine ⟨10494402602356239383657083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13992536803141652511542777 10494402602356239383657083)
    ·
      refine ⟨15741603903534359075485625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10494402602356239383657083 15741603903534359075485625)
      ·
        refine ⟨11806202927650769306614219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15741603903534359075485625 11806202927650769306614219)
        ·
          refine ⟨17709304391476153959921329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11806202927650769306614219 17709304391476153959921329)
          ·
            refine ⟨13281978293607115469940997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17709304391476153959921329 13281978293607115469940997)
            ·
              refine ⟨2490370930051334150613937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13281978293607115469940997 2490370930051334150613937)
              ·
                refine ⟨1867778197538500612960453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2490370930051334150613937 1867778197538500612960453)
                ·
                  refine ⟨350208412038468864930085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1867778197538500612960453 350208412038468864930085)
                  ·
                    refine ⟨65664077257212912174391, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 350208412038468864930085 65664077257212912174391)
                    ·
                      rfl

theorem cell23_383641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 4, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 4, 2, 4, 4].length) (baseStart_383641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_383641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_383641 prefixEnd_383641 := by exact prefixLift 383641
  have htrace : WordTrace (prefixWord ++ tailWord_383641) baseStart_383641 baseEnd_383641 := by
    simpa [prefixWord, tailWord_383641, baseEnd_383641] using wordTrace_append hprefix tailTrace_383641
  have hstable : (prefixWord ++ tailWord_383641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_383641).length < 2 ^ (prefixWord ++ tailWord_383641).sum := by decide
  have hdescent : baseEnd_383641 < baseStart_383641 := by decide
  rcases family_descends (prefixWord ++ tailWord_383641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_383651 : List Nat := [1, 1, 1, 4, 1, 1, 2, 2, 5, 2, 3]
def baseStart_383651 : Nat := 118140960795 + 383651 * 2 ^ 59
def prefixEnd_383651 : Nat := 4983230072969 + 3 ^ 40 * 383651 * 2
def baseEnd_383651 : Nat := 196997366578183697398127

theorem tailTrace_383651 : CollatzResearch.WordTrace tailWord_383651 prefixEnd_383651 196997366578183697398127 := by
  unfold tailWord_383651
  simp only [CollatzResearch.WordTrace]
  refine ⟨13992901533105424219406807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9328601022070282812937871 13992901533105424219406807)
  ·
    refine ⟨20989352299658136329110211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13992901533105424219406807 20989352299658136329110211)
    ·
      refine ⟨31484028449487204493665317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20989352299658136329110211 31484028449487204493665317)
      ·
        refine ⟨5903255334278850842562247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 31484028449487204493665317 5903255334278850842562247)
        ·
          refine ⟨8854883001418276263843371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5903255334278850842562247 8854883001418276263843371)
          ·
            refine ⟨13282324502127414395765057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8854883001418276263843371 13282324502127414395765057)
            ·
              refine ⟨9961743376595560796823793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13282324502127414395765057 9961743376595560796823793)
              ·
                refine ⟨7471307532446670597617845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9961743376595560796823793 7471307532446670597617845)
                ·
                  refine ⟨700435081166875368526673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 7471307532446670597617845 700435081166875368526673)
                  ·
                    refine ⟨525326310875156526395005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 700435081166875368526673 525326310875156526395005)
                    ·
                      refine ⟨196997366578183697398127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 525326310875156526395005 196997366578183697398127)
                      ·
                        rfl

theorem cell23_383651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 2, 5, 2, 3].length) (baseStart_383651 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_383651 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_383651 prefixEnd_383651 := by exact prefixLift 383651
  have htrace : WordTrace (prefixWord ++ tailWord_383651) baseStart_383651 baseEnd_383651 := by
    simpa [prefixWord, tailWord_383651, baseEnd_383651] using wordTrace_append hprefix tailTrace_383651
  have hstable : (prefixWord ++ tailWord_383651).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_383651).length < 2 ^ (prefixWord ++ tailWord_383651).sum := by decide
  have hdescent : baseEnd_383651 < baseStart_383651 := by decide
  rcases family_descends (prefixWord ++ tailWord_383651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_383664 : List Nat := [2, 1, 1, 1, 2, 1, 3, 1, 2, 2, 7]
def baseStart_383664 : Nat := 118140960795 + 383664 * 2 ^ 59
def prefixEnd_383664 : Nat := 4983230072969 + 3 ^ 40 * 383664 * 2
def baseEnd_383664 : Nat := 197004041826692146535567

theorem tailTrace_383664 : CollatzResearch.WordTrace tailWord_383664 prefixEnd_383664 197004041826692146535567 := by
  unfold tailWord_383664
  simp only [CollatzResearch.WordTrace]
  refine ⟨6996687841029163719815023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9328917121372218293086697 6996687841029163719815023)
  ·
    refine ⟨10495031761543745579722535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6996687841029163719815023 10495031761543745579722535)
    ·
      refine ⟨15742547642315618369583803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10495031761543745579722535 15742547642315618369583803)
      ·
        refine ⟨23613821463473427554375705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15742547642315618369583803 23613821463473427554375705)
        ·
          refine ⟨17710366097605070665781779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23613821463473427554375705 17710366097605070665781779)
          ·
            refine ⟨26565549146407605998672669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17710366097605070665781779 26565549146407605998672669)
            ·
              refine ⟨9962080929902852249502251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26565549146407605998672669 9962080929902852249502251)
              ·
                refine ⟨14943121394854278374253377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9962080929902852249502251 14943121394854278374253377)
                ·
                  refine ⟨11207341046140708780690033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14943121394854278374253377 11207341046140708780690033)
                  ·
                    refine ⟨8405505784605531585517525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11207341046140708780690033 8405505784605531585517525)
                    ·
                      refine ⟨197004041826692146535567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 8405505784605531585517525 197004041826692146535567)
                      ·
                        rfl

theorem cell23_383664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 1, 2, 2, 7].length) (baseStart_383664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_383664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_383664 prefixEnd_383664 := by exact prefixLift 383664
  have htrace : WordTrace (prefixWord ++ tailWord_383664) baseStart_383664 baseEnd_383664 := by
    simpa [prefixWord, tailWord_383664, baseEnd_383664] using wordTrace_append hprefix tailTrace_383664
  have hstable : (prefixWord ++ tailWord_383664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_383664).length < 2 ^ (prefixWord ++ tailWord_383664).sum := by decide
  have hdescent : baseEnd_383664 < baseStart_383664 := by decide
  rcases family_descends (prefixWord ++ tailWord_383664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_383688 : List Nat := [2, 1, 3, 1, 2, 5, 2, 7]
def baseStart_383688 : Nat := 118140960795 + 383688 * 2 ^ 59
def prefixEnd_383688 : Nat := 4983230072969 + 3 ^ 40 * 383688 * 2
def baseEnd_383688 : Nat := 7296902420829631579091

theorem tailTrace_383688 : CollatzResearch.WordTrace tailWord_383688 prefixEnd_383688 7296902420829631579091 := by
  unfold tailWord_383688
  simp only [CollatzResearch.WordTrace]
  refine ⟨6997125516985689769251859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9329500689314253025669145 6997125516985689769251859)
  ·
    refine ⟨10495688275478534653877789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6997125516985689769251859 10495688275478534653877789)
    ·
      refine ⟨3935883103304450495204171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10495688275478534653877789 3935883103304450495204171)
      ·
        refine ⟨5903824654956675742806257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3935883103304450495204171 5903824654956675742806257)
        ·
          refine ⟨4427868491217506807104693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5903824654956675742806257 4427868491217506807104693)
          ·
            refine ⟨415112671051641263166065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 4427868491217506807104693 415112671051641263166065)
            ·
              refine ⟨311334503288730947374549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 415112671051641263166065 311334503288730947374549)
              ·
                refine ⟨7296902420829631579091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 311334503288730947374549 7296902420829631579091)
                ·
                  rfl

theorem cell23_383688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 5, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 5, 2, 7].length) (baseStart_383688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_383688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_383688 prefixEnd_383688 := by exact prefixLift 383688
  have htrace : WordTrace (prefixWord ++ tailWord_383688) baseStart_383688 baseEnd_383688 := by
    simpa [prefixWord, tailWord_383688, baseEnd_383688] using wordTrace_append hprefix tailTrace_383688
  have hstable : (prefixWord ++ tailWord_383688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_383688).length < 2 ^ (prefixWord ++ tailWord_383688).sum := by decide
  have hdescent : baseEnd_383688 < baseStart_383688 := by decide
  rcases family_descends (prefixWord ++ tailWord_383688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_383693 : List Nat := [1, 6, 2, 1, 3, 1, 1, 3, 1, 1, 3]
def baseStart_383693 : Nat := 118140960795 + 383693 * 2 ^ 59
def prefixEnd_383693 : Nat := 4983230072969 + 3 ^ 40 * 383693 * 2
def baseEnd_383693 : Nat := 197018932765672533072935

theorem tailTrace_383693 : CollatzResearch.WordTrace tailWord_383693 prefixEnd_383693 197018932765672533072935 := by
  unfold tailWord_383693
  simp only [CollatzResearch.WordTrace]
  refine ⟨13994433398953265392435733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9329622265968843594957155 13994433398953265392435733)
  ·
    refine ⟨655989065575934315270425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 13994433398953265392435733 655989065575934315270425)
    ·
      refine ⟨491991799181950736452819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 655989065575934315270425 491991799181950736452819)
      ·
        refine ⟨737987698772926104679229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 491991799181950736452819 737987698772926104679229)
        ·
          refine ⟨276745387039847289254711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 737987698772926104679229 276745387039847289254711)
          ·
            refine ⟨415118080559770933882067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 276745387039847289254711 415118080559770933882067)
            ·
              refine ⟨622677120839656400823101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 415118080559770933882067 622677120839656400823101)
              ·
                refine ⟨233503920314871150308663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 622677120839656400823101 233503920314871150308663)
                ·
                  refine ⟨350255880472306725462995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 233503920314871150308663 350255880472306725462995)
                  ·
                    refine ⟨525383820708460088194493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 350255880472306725462995 525383820708460088194493)
                    ·
                      refine ⟨197018932765672533072935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 525383820708460088194493 197018932765672533072935)
                      ·
                        rfl

theorem cell23_383693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 3, 1, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 3, 1, 1, 3, 1, 1, 3].length) (baseStart_383693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_383693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_383693 prefixEnd_383693 := by exact prefixLift 383693
  have htrace : WordTrace (prefixWord ++ tailWord_383693) baseStart_383693 baseEnd_383693 := by
    simpa [prefixWord, tailWord_383693, baseEnd_383693] using wordTrace_append hprefix tailTrace_383693
  have hstable : (prefixWord ++ tailWord_383693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_383693).length < 2 ^ (prefixWord ++ tailWord_383693).sum := by decide
  have hdescent : baseEnd_383693 < baseStart_383693 := by decide
  rcases family_descends (prefixWord ++ tailWord_383693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_383715 : List Nat := [1, 1, 1, 7, 1, 1, 2, 1, 4, 1, 3]
def baseStart_383715 : Nat := 118140960795 + 383715 * 2 ^ 59
def prefixEnd_383715 : Nat := 4983230072969 + 3 ^ 40 * 383715 * 2
def baseEnd_383715 : Nat := 197030229340071446997833

theorem tailTrace_383715 : CollatzResearch.WordTrace tailWord_383715 prefixEnd_383715 197030229340071446997833 := by
  unfold tailWord_383715
  simp only [CollatzResearch.WordTrace]
  refine ⟨13995235804873563149736599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9330157203249042099824399 13995235804873563149736599)
  ·
    refine ⟨20992853707310344724604899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13995235804873563149736599 20992853707310344724604899)
    ·
      refine ⟨31489280560965517086907349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20992853707310344724604899 31489280560965517086907349)
      ·
        refine ⟨738030013147629306724391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 31489280560965517086907349 738030013147629306724391)
        ·
          refine ⟨1107045019721443960086587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 738030013147629306724391 1107045019721443960086587)
          ·
            refine ⟨1660567529582165940129881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1107045019721443960086587 1660567529582165940129881)
            ·
              refine ⟨1245425647186624455097411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1660567529582165940129881 1245425647186624455097411)
              ·
                refine ⟨1868138470779936682646117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1245425647186624455097411 1868138470779936682646117)
                ·
                  refine ⟨350275963271238127996147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1868138470779936682646117 350275963271238127996147)
                  ·
                    refine ⟨525413944906857191994221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 350275963271238127996147 525413944906857191994221)
                    ·
                      refine ⟨197030229340071446997833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 525413944906857191994221 197030229340071446997833)
                      ·
                        rfl

theorem cell23_383715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 2, 1, 4, 1, 3].length) (baseStart_383715 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_383715 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_383715 prefixEnd_383715 := by exact prefixLift 383715
  have htrace : WordTrace (prefixWord ++ tailWord_383715) baseStart_383715 baseEnd_383715 := by
    simpa [prefixWord, tailWord_383715, baseEnd_383715] using wordTrace_append hprefix tailTrace_383715
  have hstable : (prefixWord ++ tailWord_383715).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_383715).length < 2 ^ (prefixWord ++ tailWord_383715).sum := by decide
  have hdescent : baseEnd_383715 < baseStart_383715 := by decide
  rcases family_descends (prefixWord ++ tailWord_383715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_383725 : List Nat := [1, 5, 1, 2, 1, 1, 2, 2, 3, 3, 2]
def baseStart_383725 : Nat := 118140960795 + 383725 * 2 ^ 59
def prefixEnd_383725 : Nat := 4983230072969 + 3 ^ 40 * 383725 * 2
def baseEnd_383725 : Nat := 197035364146616407872787

theorem tailTrace_383725 : CollatzResearch.WordTrace tailWord_383725 prefixEnd_383725 197035364146616407872787 := by
  unfold tailWord_383725
  simp only [CollatzResearch.WordTrace]
  refine ⟨13995600534837334857600629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9330400356558223238400419 13995600534837334857600629)
  ·
    refine ⟨1312087550141000142900059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 13995600534837334857600629 1312087550141000142900059)
    ·
      refine ⟨1968131325211500214350089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1312087550141000142900059 1968131325211500214350089)
      ·
        refine ⟨1476098493908625160762567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1968131325211500214350089 1476098493908625160762567)
        ·
          refine ⟨2214147740862937741143851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1476098493908625160762567 2214147740862937741143851)
          ·
            refine ⟨3321221611294406611715777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2214147740862937741143851 3321221611294406611715777)
            ·
              refine ⟨2490916208470804958786833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3321221611294406611715777 2490916208470804958786833)
              ·
                refine ⟨1868187156353103719090125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2490916208470804958786833 1868187156353103719090125)
                ·
                  refine ⟨700570183632413894658797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1868187156353103719090125 700570183632413894658797)
                  ·
                    refine ⟨262713818862155210497049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 700570183632413894658797 262713818862155210497049)
                    ·
                      refine ⟨197035364146616407872787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 262713818862155210497049 197035364146616407872787)
                      ·
                        rfl

theorem cell23_383725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 2, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 2, 2, 3, 3, 2].length) (baseStart_383725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_383725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_383725 prefixEnd_383725 := by exact prefixLift 383725
  have htrace : WordTrace (prefixWord ++ tailWord_383725) baseStart_383725 baseEnd_383725 := by
    simpa [prefixWord, tailWord_383725, baseEnd_383725] using wordTrace_append hprefix tailTrace_383725
  have hstable : (prefixWord ++ tailWord_383725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_383725).length < 2 ^ (prefixWord ++ tailWord_383725).sum := by decide
  have hdescent : baseEnd_383725 < baseStart_383725 := by decide
  rcases family_descends (prefixWord ++ tailWord_383725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_383741 : List Nat := [1, 4, 1, 1, 1, 1, 3, 1, 4, 1, 5]
def baseStart_383741 : Nat := 118140960795 + 383741 * 2 ^ 59
def prefixEnd_383741 : Nat := 4983230072969 + 3 ^ 40 * 383741 * 2
def baseEnd_383741 : Nat := 197043579837088345272713

theorem tailTrace_383741 : CollatzResearch.WordTrace tailWord_383741 prefixEnd_383741 197043579837088345272713 := by
  unfold tailWord_383741
  simp only [CollatzResearch.WordTrace]
  refine ⟨13996184102779369590183077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9330789401852913060122051 13996184102779369590183077)
  ·
    refine ⟨2624284519271131798159327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13996184102779369590183077 2624284519271131798159327)
    ·
      refine ⟨3936426778906697697238991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2624284519271131798159327 3936426778906697697238991)
      ·
        refine ⟨5904640168360046545858487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3936426778906697697238991 5904640168360046545858487)
        ·
          refine ⟨8856960252540069818787731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5904640168360046545858487 8856960252540069818787731)
          ·
            refine ⟨13285440378810104728181597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8856960252540069818787731 13285440378810104728181597)
            ·
              refine ⟨4982040142053789273068099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13285440378810104728181597 4982040142053789273068099)
              ·
                refine ⟨7473060213080683909602149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4982040142053789273068099 7473060213080683909602149)
                ·
                  refine ⟨1401198789952628233050403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7473060213080683909602149 1401198789952628233050403)
                  ·
                    refine ⟨2101798184928942349575605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1401198789952628233050403 2101798184928942349575605)
                    ·
                      refine ⟨197043579837088345272713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2101798184928942349575605 197043579837088345272713)
                      ·
                        rfl

theorem cell23_383741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 3, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 3, 1, 4, 1, 5].length) (baseStart_383741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_383741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_383741 prefixEnd_383741 := by exact prefixLift 383741
  have htrace : WordTrace (prefixWord ++ tailWord_383741) baseStart_383741 baseEnd_383741 := by
    simpa [prefixWord, tailWord_383741, baseEnd_383741] using wordTrace_append hprefix tailTrace_383741
  have hstable : (prefixWord ++ tailWord_383741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_383741).length < 2 ^ (prefixWord ++ tailWord_383741).sum := by decide
  have hdescent : baseEnd_383741 < baseStart_383741 := by decide
  rcases family_descends (prefixWord ++ tailWord_383741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_383742 : List Nat := [4, 2, 2, 1, 2, 2, 1, 1, 3, 3, 2]
def baseStart_383742 : Nat := 118140960795 + 383742 * 2 ^ 59
def prefixEnd_383742 : Nat := 4983230072969 + 3 ^ 40 * 383742 * 2
def baseEnd_383742 : Nat := 197044093317742841360209

theorem tailTrace_383742 : CollatzResearch.WordTrace tailWord_383742 prefixEnd_383742 197044093317742841360209 := by
  unfold tailWord_383742
  simp only [CollatzResearch.WordTrace]
  refine ⟨1749527571971968345121185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9330813717183831173979653 1749527571971968345121185)
  ·
    refine ⟨1312145678978976258840889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1749527571971968345121185 1312145678978976258840889)
    ·
      refine ⟨984109259234232194130667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1312145678978976258840889 984109259234232194130667)
      ·
        refine ⟨1476163888851348291196001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 984109259234232194130667 1476163888851348291196001)
        ·
          refine ⟨1107122916638511218397001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1476163888851348291196001 1107122916638511218397001)
          ·
            refine ⟨830342187478883413797751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1107122916638511218397001 830342187478883413797751)
            ·
              refine ⟨1245513281218325120696627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 830342187478883413797751 1245513281218325120696627)
              ·
                refine ⟨1868269921827487681044941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1245513281218325120696627 1868269921827487681044941)
                ·
                  refine ⟨700601220685307880391853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1868269921827487681044941 700601220685307880391853)
                  ·
                    refine ⟨262725457756990455146945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 700601220685307880391853 262725457756990455146945)
                    ·
                      refine ⟨197044093317742841360209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 262725457756990455146945 197044093317742841360209)
                      ·
                        rfl

theorem cell23_383742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 2, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 2, 1, 1, 3, 3, 2].length) (baseStart_383742 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_383742 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_383742 prefixEnd_383742 := by exact prefixLift 383742
  have htrace : WordTrace (prefixWord ++ tailWord_383742) baseStart_383742 baseEnd_383742 := by
    simpa [prefixWord, tailWord_383742, baseEnd_383742] using wordTrace_append hprefix tailTrace_383742
  have hstable : (prefixWord ++ tailWord_383742).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_383742).length < 2 ^ (prefixWord ++ tailWord_383742).sum := by decide
  have hdescent : baseEnd_383742 < baseStart_383742 := by decide
  rcases family_descends (prefixWord ++ tailWord_383742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_383772 : List Nat := [2, 2, 3, 1, 1, 3, 1, 4, 2, 2, 2]
def baseStart_383772 : Nat := 118140960795 + 383772 * 2 ^ 59
def prefixEnd_383772 : Nat := 4983230072969 + 3 ^ 40 * 383772 * 2
def baseEnd_383772 : Nat := 197059497737377723985071

theorem tailTrace_383772 : CollatzResearch.WordTrace tailWord_383772 prefixEnd_383772 197059497737377723985071 := by
  unfold tailWord_383772
  simp only [CollatzResearch.WordTrace]
  refine ⟨6998657382833530942280785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9331543177111374589707713 6998657382833530942280785)
  ·
    refine ⟨5248993037125148206710589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6998657382833530942280785 5248993037125148206710589)
    ·
      refine ⟨1968372388921930577516471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5248993037125148206710589 1968372388921930577516471)
      ·
        refine ⟨2952558583382895866274707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1968372388921930577516471 2952558583382895866274707)
        ·
          refine ⟨4428837875074343799412061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2952558583382895866274707 4428837875074343799412061)
          ·
            refine ⟨1660814203152878924779523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4428837875074343799412061 1660814203152878924779523)
            ·
              refine ⟨2491221304729318387169285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1660814203152878924779523 2491221304729318387169285)
              ·
                refine ⟨467103994636747197594241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2491221304729318387169285 467103994636747197594241)
                ·
                  refine ⟨350327995977560398195681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 467103994636747197594241 350327995977560398195681)
                  ·
                    refine ⟨262745996983170298646761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 350327995977560398195681 262745996983170298646761)
                    ·
                      refine ⟨197059497737377723985071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 262745996983170298646761 197059497737377723985071)
                      ·
                        rfl

theorem cell23_383772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 1, 4, 2, 2, 2].length) (baseStart_383772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_383772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_383772 prefixEnd_383772 := by exact prefixLift 383772
  have htrace : WordTrace (prefixWord ++ tailWord_383772) baseStart_383772 baseEnd_383772 := by
    simpa [prefixWord, tailWord_383772, baseEnd_383772] using wordTrace_append hprefix tailTrace_383772
  have hstable : (prefixWord ++ tailWord_383772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_383772).length < 2 ^ (prefixWord ++ tailWord_383772).sum := by decide
  have hdescent : baseEnd_383772 < baseStart_383772 := by decide
  rcases family_descends (prefixWord ++ tailWord_383772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_383788 : List Nat := [2, 2, 1, 1, 1, 4, 3, 1, 2, 3, 3]
def baseStart_383788 : Nat := 118140960795 + 383788 * 2 ^ 59
def prefixEnd_383788 : Nat := 4983230072969 + 3 ^ 40 * 383788 * 2
def baseEnd_383788 : Nat := 197067713427849661384997

theorem tailTrace_383788 : CollatzResearch.WordTrace tailWord_383788 prefixEnd_383788 197067713427849661384997 := by
  unfold tailWord_383788
  simp only [CollatzResearch.WordTrace]
  refine ⟨6998949166804548308572009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9331932222406064411429345 6998949166804548308572009)
  ·
    refine ⟨5249211875103411231429007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6998949166804548308572009 5249211875103411231429007)
    ·
      refine ⟨7873817812655116847143511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5249211875103411231429007 7873817812655116847143511)
      ·
        refine ⟨11810726718982675270715267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7873817812655116847143511 11810726718982675270715267)
        ·
          refine ⟨17716090078474012906072901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11810726718982675270715267 17716090078474012906072901)
          ·
            refine ⟨3321766889713877419888669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17716090078474012906072901 3321766889713877419888669)
            ·
              refine ⟨1245662583642704032458251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3321766889713877419888669 1245662583642704032458251)
              ·
                refine ⟨1868493875464056048687377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1245662583642704032458251 1868493875464056048687377)
                ·
                  refine ⟨1401370406598042036515533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1868493875464056048687377 1401370406598042036515533)
                  ·
                    refine ⟨525513902474265763693325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1401370406598042036515533 525513902474265763693325)
                    ·
                      refine ⟨197067713427849661384997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 525513902474265763693325 197067713427849661384997)
                      ·
                        rfl

theorem cell23_383788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 3, 3].length) (baseStart_383788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_383788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_383788 prefixEnd_383788 := by exact prefixLift 383788
  have htrace : WordTrace (prefixWord ++ tailWord_383788) baseStart_383788 baseEnd_383788 := by
    simpa [prefixWord, tailWord_383788, baseEnd_383788] using wordTrace_append hprefix tailTrace_383788
  have hstable : (prefixWord ++ tailWord_383788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_383788).length < 2 ^ (prefixWord ++ tailWord_383788).sum := by decide
  have hdescent : baseEnd_383788 < baseStart_383788 := by decide
  rcases family_descends (prefixWord ++ tailWord_383788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_383845 : List Nat := [1, 3, 1, 3, 1, 1, 4, 1, 2, 4, 2]
def baseStart_383845 : Nat := 118140960795 + 383845 * 2 ^ 59
def prefixEnd_383845 : Nat := 4983230072969 + 3 ^ 40 * 383845 * 2
def baseEnd_383845 : Nat := 197096981825155938372235

theorem tailTrace_383845 : CollatzResearch.WordTrace tailWord_383845 prefixEnd_383845 197096981825155938372235 := by
  unfold tailWord_383845
  simp only [CollatzResearch.WordTrace]
  refine ⟨13999977294402595351968989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9333318196268396901312659 13999977294402595351968989)
  ·
    refine ⟨5249991485400973256988371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13999977294402595351968989 5249991485400973256988371)
    ·
      refine ⟨7874987228101459885482557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5249991485400973256988371 7874987228101459885482557)
      ·
        refine ⟨2953120210538047457055959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7874987228101459885482557 2953120210538047457055959)
        ·
          refine ⟨4429680315807071185583939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2953120210538047457055959 4429680315807071185583939)
          ·
            refine ⟨6644520473710606778375909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4429680315807071185583939 6644520473710606778375909)
            ·
              refine ⟨1245847588820738770945483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6644520473710606778375909 1245847588820738770945483)
              ·
                refine ⟨1868771383231108156418225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1245847588820738770945483 1868771383231108156418225)
                ·
                  refine ⟨1401578537423331117313669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1868771383231108156418225 1401578537423331117313669)
                  ·
                    refine ⟨262795975766874584496313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1401578537423331117313669 262795975766874584496313)
                    ·
                      refine ⟨197096981825155938372235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 262795975766874584496313 197096981825155938372235)
                      ·
                        rfl

theorem cell23_383845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 4, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 4, 1, 2, 4, 2].length) (baseStart_383845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_383845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_383845 prefixEnd_383845 := by exact prefixLift 383845
  have htrace : WordTrace (prefixWord ++ tailWord_383845) baseStart_383845 baseEnd_383845 := by
    simpa [prefixWord, tailWord_383845, baseEnd_383845] using wordTrace_append hprefix tailTrace_383845
  have hstable : (prefixWord ++ tailWord_383845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_383845).length < 2 ^ (prefixWord ++ tailWord_383845).sum := by decide
  have hdescent : baseEnd_383845 < baseStart_383845 := by decide
  rcases family_descends (prefixWord ++ tailWord_383845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_383882 : List Nat := [3, 1, 2, 4, 1, 2, 1, 2, 2, 2, 3]
def baseStart_383882 : Nat := 118140960795 + 383882 * 2 ^ 59
def prefixEnd_383882 : Nat := 4983230072969 + 3 ^ 40 * 383882 * 2
def baseEnd_383882 : Nat := 197115980609372293609565

theorem tailTrace_383882 : CollatzResearch.WordTrace tailWord_383882 prefixEnd_383882 197115980609372293609565 := by
  unfold tailWord_383882
  simp only [CollatzResearch.WordTrace]
  refine ⟨3500331698817137667766475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9334217863512367114043933 3500331698817137667766475)
  ·
    refine ⟨5250497548225706501649713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3500331698817137667766475 5250497548225706501649713)
    ·
      refine ⟨3937873161169279876237285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5250497548225706501649713 3937873161169279876237285)
      ·
        refine ⟨738351217719239976794491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3937873161169279876237285 738351217719239976794491)
        ·
          refine ⟨1107526826578859965191737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 738351217719239976794491 1107526826578859965191737)
          ·
            refine ⟨830645119934144973893803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1107526826578859965191737 830645119934144973893803)
            ·
              refine ⟨1245967679901217460840705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 830645119934144973893803 1245967679901217460840705)
              ·
                refine ⟨934475759925913095630529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1245967679901217460840705 934475759925913095630529)
                ·
                  refine ⟨700856819944434821722897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 934475759925913095630529 700856819944434821722897)
                  ·
                    refine ⟨525642614958326116292173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 700856819944434821722897 525642614958326116292173)
                    ·
                      refine ⟨197115980609372293609565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 525642614958326116292173 197115980609372293609565)
                      ·
                        rfl

theorem cell23_383882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 2, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 2, 1, 2, 2, 2, 3].length) (baseStart_383882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_383882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_383882 prefixEnd_383882 := by exact prefixLift 383882
  have htrace : WordTrace (prefixWord ++ tailWord_383882) baseStart_383882 baseEnd_383882 := by
    simpa [prefixWord, tailWord_383882, baseEnd_383882] using wordTrace_append hprefix tailTrace_383882
  have hstable : (prefixWord ++ tailWord_383882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_383882).length < 2 ^ (prefixWord ++ tailWord_383882).sum := by decide
  have hdescent : baseEnd_383882 < baseStart_383882 := by decide
  rcases family_descends (prefixWord ++ tailWord_383882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_383928 : List Nat := [2, 1, 2, 1, 2, 4, 1, 1, 3, 6]
def baseStart_383928 : Nat := 118140960795 + 383928 * 2 ^ 59
def prefixEnd_383928 : Nat := 4983230072969 + 3 ^ 40 * 383928 * 2
def baseEnd_383928 : Nat := 65713200239826371211451

theorem tailTrace_383928 : CollatzResearch.WordTrace tailWord_383928 prefixEnd_383928 65713200239826371211451 := by
  unfold tailWord_383928
  simp only [CollatzResearch.WordTrace]
  refine ⟨7001502276550950263620219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9335336368734600351493625 7001502276550950263620219)
  ·
    refine ⟨10502253414826425395430329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7001502276550950263620219 10502253414826425395430329)
    ·
      refine ⟨7876690061119819046572747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10502253414826425395430329 7876690061119819046572747)
      ·
        refine ⟨11815035091679728569859121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7876690061119819046572747 11815035091679728569859121)
        ·
          refine ⟨8861276318759796427394341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11815035091679728569859121 8861276318759796427394341)
          ·
            refine ⟨1661489309767461830136439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8861276318759796427394341 1661489309767461830136439)
            ·
              refine ⟨2492233964651192745204659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1661489309767461830136439 2492233964651192745204659)
              ·
                refine ⟨3738350946976789117806989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2492233964651192745204659 3738350946976789117806989)
                ·
                  refine ⟨1401881605116295919177621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3738350946976789117806989 1401881605116295919177621)
                  ·
                    refine ⟨65713200239826371211451, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1401881605116295919177621 65713200239826371211451)
                    ·
                      rfl

theorem cell23_383928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 1, 1, 3, 6].length) (baseStart_383928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_383928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_383928 prefixEnd_383928 := by exact prefixLift 383928
  have htrace : WordTrace (prefixWord ++ tailWord_383928) baseStart_383928 baseEnd_383928 := by
    simpa [prefixWord, tailWord_383928, baseEnd_383928] using wordTrace_append hprefix tailTrace_383928
  have hstable : (prefixWord ++ tailWord_383928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_383928).length < 2 ^ (prefixWord ++ tailWord_383928).sum := by decide
  have hdescent : baseEnd_383928 < baseStart_383928 := by decide
  rcases family_descends (prefixWord ++ tailWord_383928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_383940 : List Nat := [2, 3, 3, 3, 2, 1, 2, 2, 1, 4]
def baseStart_383940 : Nat := 118140960795 + 383940 * 2 ^ 59
def prefixEnd_383940 : Nat := 4983230072969 + 3 ^ 40 * 383940 * 2
def baseEnd_383940 : Nat := 65715254162444355561433

theorem tailTrace_383940 : CollatzResearch.WordTrace tailWord_383940 prefixEnd_383940 65715254162444355561433 := by
  unfold tailWord_383940
  simp only [CollatzResearch.WordTrace]
  refine ⟨7001721114529213288338637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9335628152705617717784849 7001721114529213288338637)
  ·
    refine ⟨2625645417948454983126989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7001721114529213288338637 2625645417948454983126989)
    ·
      refine ⟨984617031730670618672621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2625645417948454983126989 984617031730670618672621)
      ·
        refine ⟨369231386899001482002233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 984617031730670618672621 369231386899001482002233)
        ·
          refine ⟨276923540174251111501675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 369231386899001482002233 276923540174251111501675)
          ·
            refine ⟨415385310261376667252513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 276923540174251111501675 415385310261376667252513)
            ·
              refine ⟨311538982696032500439385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 415385310261376667252513 311538982696032500439385)
              ·
                refine ⟨233654237022024375329539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 311538982696032500439385 233654237022024375329539)
                ·
                  refine ⟨350481355533036562994309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 233654237022024375329539 350481355533036562994309)
                  ·
                    refine ⟨65715254162444355561433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 350481355533036562994309 65715254162444355561433)
                    ·
                      rfl

theorem cell23_383940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 2, 1, 2, 2, 1, 4].length) (baseStart_383940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_383940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_383940 prefixEnd_383940 := by exact prefixLift 383940
  have htrace : WordTrace (prefixWord ++ tailWord_383940) baseStart_383940 baseEnd_383940 := by
    simpa [prefixWord, tailWord_383940, baseEnd_383940] using wordTrace_append hprefix tailTrace_383940
  have hstable : (prefixWord ++ tailWord_383940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_383940).length < 2 ^ (prefixWord ++ tailWord_383940).sum := by decide
  have hdescent : baseEnd_383940 < baseStart_383940 := by decide
  rcases family_descends (prefixWord ++ tailWord_383940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_383952 : List Nat := [2, 1, 1, 1, 1, 2, 3, 5, 3, 2, 2]
def baseStart_383952 : Nat := 118140960795 + 383952 * 2 ^ 59
def prefixEnd_383952 : Nat := 4983230072969 + 3 ^ 40 * 383952 * 2
def baseEnd_383952 : Nat := 197151924255187019734243

theorem tailTrace_383952 : CollatzResearch.WordTrace tailWord_383952 prefixEnd_383952 197151924255187019734243 := by
  unfold tailWord_383952
  simp only [CollatzResearch.WordTrace]
  refine ⟨7001939952507476313057055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9335919936676635084076073 7001939952507476313057055)
  ·
    refine ⟨10502909928761214469585583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7001939952507476313057055 10502909928761214469585583)
    ·
      refine ⟨15754364893141821704378375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10502909928761214469585583 15754364893141821704378375)
      ·
        refine ⟨23631547339712732556567563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15754364893141821704378375 23631547339712732556567563)
        ·
          refine ⟨35447321009569098834851345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23631547339712732556567563 35447321009569098834851345)
          ·
            refine ⟨26585490757176824126138509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35447321009569098834851345 26585490757176824126138509)
            ·
              refine ⟨9969559033941309047301941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26585490757176824126138509 9969559033941309047301941)
              ·
                refine ⟨934646159431997723184557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9969559033941309047301941 934646159431997723184557)
                ·
                  refine ⟨350492309786999146194209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 934646159431997723184557 350492309786999146194209)
                  ·
                    refine ⟨262869232340249359645657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 350492309786999146194209 262869232340249359645657)
                    ·
                      refine ⟨197151924255187019734243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 262869232340249359645657 197151924255187019734243)
                      ·
                        rfl

theorem cell23_383952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 5, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 5, 3, 2, 2].length) (baseStart_383952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_383952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_383952 prefixEnd_383952 := by exact prefixLift 383952
  have htrace : WordTrace (prefixWord ++ tailWord_383952) baseStart_383952 baseEnd_383952 := by
    simpa [prefixWord, tailWord_383952, baseEnd_383952] using wordTrace_append hprefix tailTrace_383952
  have hstable : (prefixWord ++ tailWord_383952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_383952).length < 2 ^ (prefixWord ++ tailWord_383952).sum := by decide
  have hdescent : baseEnd_383952 < baseStart_383952 := by decide
  rcases family_descends (prefixWord ++ tailWord_383952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_383962 : List Nat := [3, 1, 1, 2, 4, 1, 2, 3, 2, 4]
def baseStart_383962 : Nat := 118140960795 + 383962 * 2 ^ 59
def prefixEnd_383962 : Nat := 4983230072969 + 3 ^ 40 * 383962 * 2
def baseEnd_383962 : Nat := 65719019687243993536399

theorem tailTrace_383962 : CollatzResearch.WordTrace tailWord_383962 prefixEnd_383962 65719019687243993536399 := by
  unfold tailWord_383962
  simp only [CollatzResearch.WordTrace]
  refine ⟨3501061158744681083494535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9336163089985816222652093 3501061158744681083494535)
  ·
    refine ⟨5251591738117021625241803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3501061158744681083494535 5251591738117021625241803)
    ·
      refine ⟨7877387607175532437862705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5251591738117021625241803 7877387607175532437862705)
      ·
        refine ⟨5908040705381649328397029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7877387607175532437862705 5908040705381649328397029)
        ·
          refine ⟨1107757632259059249074443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5908040705381649328397029 1107757632259059249074443)
          ·
            refine ⟨1661636448388588873611665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1107757632259059249074443 1661636448388588873611665)
            ·
              refine ⟨1246227336291441655208749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1661636448388588873611665 1246227336291441655208749)
              ·
                refine ⟨467335251109290620703281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1246227336291441655208749 467335251109290620703281)
                ·
                  refine ⟨350501438331967965527461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 467335251109290620703281 350501438331967965527461)
                  ·
                    refine ⟨65719019687243993536399, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 350501438331967965527461 65719019687243993536399)
                    ·
                      rfl

theorem cell23_383962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 2, 3, 2, 4].length) (baseStart_383962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_383962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_383962 prefixEnd_383962 := by exact prefixLift 383962
  have htrace : WordTrace (prefixWord ++ tailWord_383962) baseStart_383962 baseEnd_383962 := by
    simpa [prefixWord, tailWord_383962, baseEnd_383962] using wordTrace_append hprefix tailTrace_383962
  have hstable : (prefixWord ++ tailWord_383962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_383962).length < 2 ^ (prefixWord ++ tailWord_383962).sum := by decide
  have hdescent : baseEnd_383962 < baseStart_383962 := by decide
  rcases family_descends (prefixWord ++ tailWord_383962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_383973 : List Nat := [1, 3, 1, 6, 2, 1, 1, 1, 2, 3, 2]
def baseStart_383973 : Nat := 118140960795 + 383973 * 2 ^ 59
def prefixEnd_383973 : Nat := 4983230072969 + 3 ^ 40 * 383973 * 2
def baseEnd_383973 : Nat := 197162707348931437571647

theorem tailTrace_383973 : CollatzResearch.WordTrace tailWord_383973 prefixEnd_383973 197162707348931437571647 := by
  unfold tailWord_383973
  simp only [CollatzResearch.WordTrace]
  refine ⟨14004645837938873212628573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9336430558625915475085715 14004645837938873212628573)
  ·
    refine ⟨5251742189227077454735715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14004645837938873212628573 5251742189227077454735715)
    ·
      refine ⟨7877613283840616182103573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5251742189227077454735715 7877613283840616182103573)
      ·
        refine ⟨369263122680028883536105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 7877613283840616182103573 369263122680028883536105)
        ·
          refine ⟨276947342010021662652079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 369263122680028883536105 276947342010021662652079)
          ·
            refine ⟨415421013015032493978119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 276947342010021662652079 415421013015032493978119)
            ·
              refine ⟨623131519522548740967179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 415421013015032493978119 623131519522548740967179)
              ·
                refine ⟨934697279283823111450769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 623131519522548740967179 934697279283823111450769)
                ·
                  refine ⟨701022959462867333588077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 934697279283823111450769 701022959462867333588077)
                  ·
                    refine ⟨262883609798575250095529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 701022959462867333588077 262883609798575250095529)
                    ·
                      refine ⟨197162707348931437571647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 262883609798575250095529 197162707348931437571647)
                      ·
                        rfl

theorem cell23_383973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 2, 1, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 2, 1, 1, 1, 2, 3, 2].length) (baseStart_383973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_383973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_383973 prefixEnd_383973 := by exact prefixLift 383973
  have htrace : WordTrace (prefixWord ++ tailWord_383973) baseStart_383973 baseEnd_383973 := by
    simpa [prefixWord, tailWord_383973, baseEnd_383973] using wordTrace_append hprefix tailTrace_383973
  have hstable : (prefixWord ++ tailWord_383973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_383973).length < 2 ^ (prefixWord ++ tailWord_383973).sum := by decide
  have hdescent : baseEnd_383973 < baseStart_383973 := by decide
  rcases family_descends (prefixWord ++ tailWord_383973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_384070 : List Nat := [6, 1, 1, 1, 1, 4, 2, 1, 2, 1, 3]
def baseStart_384070 : Nat := 118140960795 + 384070 * 2 ^ 59
def prefixEnd_384070 : Nat := 4983230072969 + 3 ^ 40 * 384070 * 2
def baseEnd_384070 : Nat := 197212514972417558058701

theorem tailTrace_384070 : CollatzResearch.WordTrace tailWord_384070 prefixEnd_384070 197212514972417558058701 := by
  unfold tailWord_384070
  simp only [CollatzResearch.WordTrace]
  refine ⟨437755741205858086840927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 9338789145724972519273109 437755741205858086840927)
  ·
    refine ⟨656633611808787130261391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 437755741205858086840927 656633611808787130261391)
    ·
      refine ⟨984950417713180695392087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 656633611808787130261391 984950417713180695392087)
      ·
        refine ⟨1477425626569771043088131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 984950417713180695392087 1477425626569771043088131)
        ·
          refine ⟨2216138439854656564632197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1477425626569771043088131 2216138439854656564632197)
          ·
            refine ⟨415525957472748105868537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2216138439854656564632197 415525957472748105868537)
            ·
              refine ⟨311644468104561079401403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 415525957472748105868537 311644468104561079401403)
              ·
                refine ⟨467466702156841619102105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 311644468104561079401403 467466702156841619102105)
                ·
                  refine ⟨350600026617631214326579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 467466702156841619102105 350600026617631214326579)
                  ·
                    refine ⟨525900039926446821489869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 350600026617631214326579 525900039926446821489869)
                    ·
                      refine ⟨197212514972417558058701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 525900039926446821489869 197212514972417558058701)
                      ·
                        rfl

theorem cell23_384070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 4, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 4, 2, 1, 2, 1, 3].length) (baseStart_384070 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_384070 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_384070 prefixEnd_384070 := by exact prefixLift 384070
  have htrace : WordTrace (prefixWord ++ tailWord_384070) baseStart_384070 baseEnd_384070 := by
    simpa [prefixWord, tailWord_384070, baseEnd_384070] using wordTrace_append hprefix tailTrace_384070
  have hstable : (prefixWord ++ tailWord_384070).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_384070).length < 2 ^ (prefixWord ++ tailWord_384070).sum := by decide
  have hdescent : baseEnd_384070 < baseStart_384070 := by decide
  rcases family_descends (prefixWord ++ tailWord_384070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_384105 : List Nat := [1, 2, 1, 1, 1, 6, 1, 2, 1, 2, 5]
def baseStart_384105 : Nat := 118140960795 + 384105 * 2 ^ 59
def prefixEnd_384105 : Nat := 4983230072969 + 3 ^ 40 * 384105 * 2
def baseEnd_384105 : Nat := 197230486795324921121039

theorem tailTrace_384105 : CollatzResearch.WordTrace tailWord_384105 prefixEnd_384105 197230486795324921121039 := by
  unfold tailWord_384105
  simp only [CollatzResearch.WordTrace]
  refine ⟨14009460273460659756433769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9339640182307106504289179 14009460273460659756433769)
  ·
    refine ⟨10507095205095494817325327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14009460273460659756433769 10507095205095494817325327)
    ·
      refine ⟨15760642807643242225987991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10507095205095494817325327 15760642807643242225987991)
      ·
        refine ⟨23640964211464863338981987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15760642807643242225987991 23640964211464863338981987)
        ·
          refine ⟨35461446317197295008472981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23640964211464863338981987 35461446317197295008472981)
          ·
            refine ⟨1662255296118623203522171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 35461446317197295008472981 1662255296118623203522171)
            ·
              refine ⟨2493382944177934805283257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1662255296118623203522171 2493382944177934805283257)
              ·
                refine ⟨1870037208133451103962443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2493382944177934805283257 1870037208133451103962443)
                ·
                  refine ⟨2805055812200176655943665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1870037208133451103962443 2805055812200176655943665)
                  ·
                    refine ⟨2103791859150132491957749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2805055812200176655943665 2103791859150132491957749)
                    ·
                      refine ⟨197230486795324921121039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2103791859150132491957749 197230486795324921121039)
                      ·
                        rfl

theorem cell23_384105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 1, 2, 1, 2, 5].length) (baseStart_384105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_384105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_384105 prefixEnd_384105 := by exact prefixLift 384105
  have htrace : WordTrace (prefixWord ++ tailWord_384105) baseStart_384105 baseEnd_384105 := by
    simpa [prefixWord, tailWord_384105, baseEnd_384105] using wordTrace_append hprefix tailTrace_384105
  have hstable : (prefixWord ++ tailWord_384105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_384105).length < 2 ^ (prefixWord ++ tailWord_384105).sum := by decide
  have hdescent : baseEnd_384105 < baseStart_384105 := by decide
  rcases family_descends (prefixWord ++ tailWord_384105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_384175 : List Nat := [1, 1, 2, 1, 2, 3, 3, 1, 1, 2, 6]
def baseStart_384175 : Nat := 118140960795 + 384175 * 2 ^ 59
def prefixEnd_384175 : Nat := 4983230072969 + 3 ^ 40 * 384175 * 2
def baseEnd_384175 : Nat := 197266430441139647245717

theorem tailTrace_384175 : CollatzResearch.WordTrace tailWord_384175 prefixEnd_384175 197266430441139647245717 := by
  unfold tailWord_384175
  simp only [CollatzResearch.WordTrace]
  refine ⟨14012013383207061711481979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9341342255471374474321319 14012013383207061711481979)
  ·
    refine ⟨21018020074810592567222969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14012013383207061711481979 21018020074810592567222969)
    ·
      refine ⟨15763515056107944425417227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21018020074810592567222969 15763515056107944425417227)
      ·
        refine ⟨23645272584161916638125841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15763515056107944425417227 23645272584161916638125841)
        ·
          refine ⟨17733954438121437478594381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23645272584161916638125841 17733954438121437478594381)
          ·
            refine ⟨6650232914295539054472893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17733954438121437478594381 6650232914295539054472893)
            ·
              refine ⟨2493837342860827145427335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6650232914295539054472893 2493837342860827145427335)
              ·
                refine ⟨3740756014291240718141003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2493837342860827145427335 3740756014291240718141003)
                ·
                  refine ⟨5611134021436861077211505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3740756014291240718141003 5611134021436861077211505)
                  ·
                    refine ⟨4208350516077645807908629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5611134021436861077211505 4208350516077645807908629)
                    ·
                      refine ⟨197266430441139647245717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 4208350516077645807908629 197266430441139647245717)
                      ·
                        rfl

theorem cell23_384175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 3, 1, 1, 2, 6].length) (baseStart_384175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_384175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_384175 prefixEnd_384175 := by exact prefixLift 384175
  have htrace : WordTrace (prefixWord ++ tailWord_384175) baseStart_384175 baseEnd_384175 := by
    simpa [prefixWord, tailWord_384175, baseEnd_384175] using wordTrace_append hprefix tailTrace_384175
  have hstable : (prefixWord ++ tailWord_384175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_384175).length < 2 ^ (prefixWord ++ tailWord_384175).sum := by decide
  have hdescent : baseEnd_384175 < baseStart_384175 := by decide
  rcases family_descends (prefixWord ++ tailWord_384175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_384209 : List Nat := [1, 2, 2, 1, 2, 2, 1, 5, 2, 3, 2]
def baseStart_384209 : Nat := 118140960795 + 384209 * 2 ^ 59
def prefixEnd_384209 : Nat := 4983230072969 + 3 ^ 40 * 384209 * 2
def baseEnd_384209 : Nat := 197283888783392514220561

theorem tailTrace_384209 : CollatzResearch.WordTrace tailWord_384209 prefixEnd_384209 197283888783392514220561 := by
  unfold tailWord_384209
  simp only [CollatzResearch.WordTrace]
  refine ⟨14013253465083885518219681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9342168976722590345479787 14013253465083885518219681)
  ·
    refine ⟨10509940098812914138664761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14013253465083885518219681 10509940098812914138664761)
    ·
      refine ⟨7882455074109685603998571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10509940098812914138664761 7882455074109685603998571)
      ·
        refine ⟨11823682611164528405997857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7882455074109685603998571 11823682611164528405997857)
        ·
          refine ⟨8867761958373396304498393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11823682611164528405997857 8867761958373396304498393)
          ·
            refine ⟨6650821468780047228373795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8867761958373396304498393 6650821468780047228373795)
            ·
              refine ⟨9976232203170070842560693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6650821468780047228373795 9976232203170070842560693)
              ·
                refine ⟨935271769047194141490065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9976232203170070842560693 935271769047194141490065)
                ·
                  refine ⟨701453826785395606117549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 935271769047194141490065 701453826785395606117549)
                  ·
                    refine ⟨263045185044523352294081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 701453826785395606117549 263045185044523352294081)
                    ·
                      refine ⟨197283888783392514220561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 263045185044523352294081 197283888783392514220561)
                      ·
                        rfl

theorem cell23_384209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 5, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 5, 2, 3, 2].length) (baseStart_384209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_384209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_384209 prefixEnd_384209 := by exact prefixLift 384209
  have htrace : WordTrace (prefixWord ++ tailWord_384209) baseStart_384209 baseEnd_384209 := by
    simpa [prefixWord, tailWord_384209, baseEnd_384209] using wordTrace_append hprefix tailTrace_384209
  have hstable : (prefixWord ++ tailWord_384209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_384209).length < 2 ^ (prefixWord ++ tailWord_384209).sum := by decide
  have hdescent : baseEnd_384209 < baseStart_384209 := by decide
  rcases family_descends (prefixWord ++ tailWord_384209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_384249 : List Nat := [1, 2, 1, 3, 1, 1, 5, 3, 2, 4]
def baseStart_384249 : Nat := 118140960795 + 384249 * 2 ^ 59
def prefixEnd_384249 : Nat := 4983230072969 + 3 ^ 40 * 384249 * 2
def baseEnd_384249 : Nat := 65768142669857452573459

theorem tailTrace_384249 : CollatzResearch.WordTrace tailWord_384249 prefixEnd_384249 65768142669857452573459 := by
  unfold tailWord_384249
  simp only [CollatzResearch.WordTrace]
  refine ⟨14014712384938972349675801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9343141589959314899783867 14014712384938972349675801)
  ·
    refine ⟨10511034288704229262256851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14014712384938972349675801 10511034288704229262256851)
    ·
      refine ⟨15766551433056343893385277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10511034288704229262256851 15766551433056343893385277)
      ·
        refine ⟨5912456787396128960019479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15766551433056343893385277 5912456787396128960019479)
        ·
          refine ⟨8868685181094193440029219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5912456787396128960019479 8868685181094193440029219)
          ·
            refine ⟨13303027771641290160043829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8868685181094193440029219 13303027771641290160043829)
            ·
              refine ⟨1247158853591370952504109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 13303027771641290160043829 1247158853591370952504109)
              ·
                refine ⟨467684570096764107189041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1247158853591370952504109 467684570096764107189041)
                ·
                  refine ⟨350763427572573080391781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 467684570096764107189041 350763427572573080391781)
                  ·
                    refine ⟨65768142669857452573459, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 350763427572573080391781 65768142669857452573459)
                    ·
                      rfl

theorem cell23_384249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 5, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 5, 3, 2, 4].length) (baseStart_384249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_384249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_384249 prefixEnd_384249 := by exact prefixLift 384249
  have htrace : WordTrace (prefixWord ++ tailWord_384249) baseStart_384249 baseEnd_384249 := by
    simpa [prefixWord, tailWord_384249, baseEnd_384249] using wordTrace_append hprefix tailTrace_384249
  have hstable : (prefixWord ++ tailWord_384249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_384249).length < 2 ^ (prefixWord ++ tailWord_384249).sum := by decide
  have hdescent : baseEnd_384249 < baseStart_384249 := by decide
  rcases family_descends (prefixWord ++ tailWord_384249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_384259 : List Nat := [1, 1, 1, 3, 2, 5, 1, 1, 3, 2, 3]
def baseStart_384259 : Nat := 118140960795 + 384259 * 2 ^ 59
def prefixEnd_384259 : Nat := 4983230072969 + 3 ^ 40 * 384259 * 2
def baseEnd_384259 : Nat := 197309562816117318595331

theorem tailTrace_384259 : CollatzResearch.WordTrace tailWord_384259 prefixEnd_384259 197309562816117318595331 := by
  unfold tailWord_384259
  simp only [CollatzResearch.WordTrace]
  refine ⟨14015077114902744057539831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9343384743268496038359887 14015077114902744057539831)
  ·
    refine ⟨21022615672354116086309747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14015077114902744057539831 21022615672354116086309747)
    ·
      refine ⟨31533923508531174129464621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21022615672354116086309747 31533923508531174129464621)
      ·
        refine ⟨11825221315699190298549233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31533923508531174129464621 11825221315699190298549233)
        ·
          refine ⟨8868915986774392723911925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11825221315699190298549233 8868915986774392723911925)
          ·
            refine ⟨831460873760099317866743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 8868915986774392723911925 831460873760099317866743)
            ·
              refine ⟨1247191310640148976800115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 831460873760099317866743 1247191310640148976800115)
              ·
                refine ⟨1870786965960223465200173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1247191310640148976800115 1870786965960223465200173)
                ·
                  refine ⟨701545112235083799450065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1870786965960223465200173 701545112235083799450065)
                  ·
                    refine ⟨526158834176312849587549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 701545112235083799450065 526158834176312849587549)
                    ·
                      refine ⟨197309562816117318595331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 526158834176312849587549 197309562816117318595331)
                      ·
                        rfl

theorem cell23_384259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 5, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 5, 1, 1, 3, 2, 3].length) (baseStart_384259 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_384259 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_384259 prefixEnd_384259 := by exact prefixLift 384259
  have htrace : WordTrace (prefixWord ++ tailWord_384259) baseStart_384259 baseEnd_384259 := by
    simpa [prefixWord, tailWord_384259, baseEnd_384259] using wordTrace_append hprefix tailTrace_384259
  have hstable : (prefixWord ++ tailWord_384259).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_384259).length < 2 ^ (prefixWord ++ tailWord_384259).sum := by decide
  have hdescent : baseEnd_384259 < baseStart_384259 := by decide
  rcases family_descends (prefixWord ++ tailWord_384259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_384273 : List Nat := [1, 2, 2, 1, 1, 4, 2, 5, 1, 2, 2]
def baseStart_384273 : Nat := 118140960795 + 384273 * 2 ^ 59
def prefixEnd_384273 : Nat := 4983230072969 + 3 ^ 40 * 384273 * 2
def baseEnd_384273 : Nat := 197316751545280263820267

theorem tailTrace_384273 : CollatzResearch.WordTrace tailWord_384273 prefixEnd_384273 197316751545280263820267 := by
  unfold tailWord_384273
  simp only [CollatzResearch.WordTrace]
  refine ⟨14015587736852024448549473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9343725157901349632366315 14015587736852024448549473)
  ·
    refine ⟨10511690802639018336412105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14015587736852024448549473 10511690802639018336412105)
    ·
      refine ⟨7883768101979263752309079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10511690802639018336412105 7883768101979263752309079)
      ·
        refine ⟨11825652152968895628463619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7883768101979263752309079 11825652152968895628463619)
        ·
          refine ⟨17738478229453343442695429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11825652152968895628463619 17738478229453343442695429)
          ·
            refine ⟨3325964668022501895505393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17738478229453343442695429 3325964668022501895505393)
            ·
              refine ⟨2494473501016876421629045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3325964668022501895505393 2494473501016876421629045)
              ·
                refine ⟨233856890720332164527723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2494473501016876421629045 233856890720332164527723)
                ·
                  refine ⟨350785336080498246791585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 233856890720332164527723 350785336080498246791585)
                  ·
                    refine ⟨263089002060373685093689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 350785336080498246791585 263089002060373685093689)
                    ·
                      refine ⟨197316751545280263820267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 263089002060373685093689 197316751545280263820267)
                      ·
                        rfl

theorem cell23_384273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 2, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 2, 5, 1, 2, 2].length) (baseStart_384273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_384273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_384273 prefixEnd_384273 := by exact prefixLift 384273
  have htrace : WordTrace (prefixWord ++ tailWord_384273) baseStart_384273 baseEnd_384273 := by
    simpa [prefixWord, tailWord_384273, baseEnd_384273] using wordTrace_append hprefix tailTrace_384273
  have hstable : (prefixWord ++ tailWord_384273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_384273).length < 2 ^ (prefixWord ++ tailWord_384273).sum := by decide
  have hdescent : baseEnd_384273 < baseStart_384273 := by decide
  rcases family_descends (prefixWord ++ tailWord_384273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_384292 : List Nat := [2, 3, 1, 3, 1, 1, 1, 1, 1, 9]
def baseStart_384292 : Nat := 118140960795 + 384292 * 2 ^ 59
def prefixEnd_384292 : Nat := 4983230072969 + 3 ^ 40 * 384292 * 2
def baseEnd_384292 : Nat := 65775502559238563160893

theorem tailTrace_384292 : CollatzResearch.WordTrace tailWord_384292 prefixEnd_384292 65775502559238563160893 := by
  unfold tailWord_384292
  simp only [CollatzResearch.WordTrace]
  refine ⟨7008140361891595346745565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9344187149188793795660753 7008140361891595346745565)
  ·
    refine ⟨2628052635709348255029587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7008140361891595346745565 2628052635709348255029587)
    ·
      refine ⟨3942078953564022382544381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2628052635709348255029587 3942078953564022382544381)
      ·
        refine ⟨1478279607586508393454143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3942078953564022382544381 1478279607586508393454143)
        ·
          refine ⟨2217419411379762590181215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1478279607586508393454143 2217419411379762590181215)
          ·
            refine ⟨3326129117069643885271823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2217419411379762590181215 3326129117069643885271823)
            ·
              refine ⟨4989193675604465827907735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3326129117069643885271823 4989193675604465827907735)
              ·
                refine ⟨7483790513406698741861603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4989193675604465827907735 7483790513406698741861603)
                ·
                  refine ⟨11225685770110048112792405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7483790513406698741861603 11225685770110048112792405)
                  ·
                    refine ⟨65775502559238563160893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 11225685770110048112792405 65775502559238563160893)
                    ·
                      rfl

theorem cell23_384292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 1, 1, 1, 9].length) (baseStart_384292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_384292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_384292 prefixEnd_384292 := by exact prefixLift 384292
  have htrace : WordTrace (prefixWord ++ tailWord_384292) baseStart_384292 baseEnd_384292 := by
    simpa [prefixWord, tailWord_384292, baseEnd_384292] using wordTrace_append hprefix tailTrace_384292
  have hstable : (prefixWord ++ tailWord_384292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_384292).length < 2 ^ (prefixWord ++ tailWord_384292).sum := by decide
  have hdescent : baseEnd_384292 < baseStart_384292 := by decide
  rcases family_descends (prefixWord ++ tailWord_384292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_384306 : List Nat := [3, 2, 1, 1, 4, 2, 2, 1, 1, 3, 3]
def baseStart_384306 : Nat := 118140960795 + 384306 * 2 ^ 59
def prefixEnd_384306 : Nat := 4983230072969 + 3 ^ 40 * 384306 * 2
def baseEnd_384306 : Nat := 197333696406878634707615

theorem tailTrace_384306 : CollatzResearch.WordTrace tailWord_384306 prefixEnd_384306 197333696406878634707615 := by
  unfold tailWord_384306
  simp only [CollatzResearch.WordTrace]
  refine ⟨3504197836433117771125193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9344527563821647389667181 3504197836433117771125193)
  ·
    refine ⟨2628148377324838328343895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3504197836433117771125193 2628148377324838328343895)
    ·
      refine ⟨3942222565987257492515843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2628148377324838328343895 3942222565987257492515843)
      ·
        refine ⟨5913333848980886238773765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3942222565987257492515843 5913333848980886238773765)
        ·
          refine ⟨1108750096683916169770081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5913333848980886238773765 1108750096683916169770081)
          ·
            refine ⟨831562572512937127327561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1108750096683916169770081 831562572512937127327561)
            ·
              refine ⟨623671929384702845495671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 831562572512937127327561 623671929384702845495671)
              ·
                refine ⟨935507894077054268243507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 623671929384702845495671 935507894077054268243507)
                ·
                  refine ⟨1403261841115581402365261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 935507894077054268243507 1403261841115581402365261)
                  ·
                    refine ⟨526223190418343025886973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1403261841115581402365261 526223190418343025886973)
                    ·
                      refine ⟨197333696406878634707615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 526223190418343025886973 197333696406878634707615)
                      ·
                        rfl

theorem cell23_384306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 2, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 2, 2, 1, 1, 3, 3].length) (baseStart_384306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_384306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_384306 prefixEnd_384306 := by exact prefixLift 384306
  have htrace : WordTrace (prefixWord ++ tailWord_384306) baseStart_384306 baseEnd_384306 := by
    simpa [prefixWord, tailWord_384306, baseEnd_384306] using wordTrace_append hprefix tailTrace_384306
  have hstable : (prefixWord ++ tailWord_384306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_384306).length < 2 ^ (prefixWord ++ tailWord_384306).sum := by decide
  have hdescent : baseEnd_384306 < baseStart_384306 := by decide
  rcases family_descends (prefixWord ++ tailWord_384306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_384312 : List Nat := [2, 1, 2, 1, 3, 1, 1, 1, 4, 3, 4]
def baseStart_384312 : Nat := 118140960795 + 384312 * 2 ^ 59
def prefixEnd_384312 : Nat := 4983230072969 + 3 ^ 40 * 384312 * 2
def baseEnd_384312 : Nat := 197336777290805611232587

theorem tailTrace_384312 : CollatzResearch.WordTrace tailWord_384312 prefixEnd_384312 197336777290805611232587 := by
  unfold tailWord_384312
  simp only [CollatzResearch.WordTrace]
  refine ⟨7008505091855367054609595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9344673455807156072812793 7008505091855367054609595)
  ·
    refine ⟨10512757637783050581914393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7008505091855367054609595 10512757637783050581914393)
    ·
      refine ⟨7884568228337287936435795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10512757637783050581914393 7884568228337287936435795)
      ·
        refine ⟨11826852342505931904653693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7884568228337287936435795 11826852342505931904653693)
        ·
          refine ⟨4435069628439724464245135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11826852342505931904653693 4435069628439724464245135)
          ·
            refine ⟨6652604442659586696367703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4435069628439724464245135 6652604442659586696367703)
            ·
              refine ⟨9978906663989380044551555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6652604442659586696367703 9978906663989380044551555)
              ·
                refine ⟨14968359995984070066827333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9978906663989380044551555 14968359995984070066827333)
                ·
                  refine ⟨2806567499247013137530125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14968359995984070066827333 2806567499247013137530125)
                  ·
                    refine ⟨1052462812217629926573797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2806567499247013137530125 1052462812217629926573797)
                    ·
                      refine ⟨197336777290805611232587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1052462812217629926573797 197336777290805611232587)
                      ·
                        rfl

theorem cell23_384312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 1, 4, 3, 4].length) (baseStart_384312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_384312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_384312 prefixEnd_384312 := by exact prefixLift 384312
  have htrace : WordTrace (prefixWord ++ tailWord_384312) baseStart_384312 baseEnd_384312 := by
    simpa [prefixWord, tailWord_384312, baseEnd_384312] using wordTrace_append hprefix tailTrace_384312
  have hstable : (prefixWord ++ tailWord_384312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_384312).length < 2 ^ (prefixWord ++ tailWord_384312).sum := by decide
  have hdescent : baseEnd_384312 < baseStart_384312 := by decide
  rcases family_descends (prefixWord ++ tailWord_384312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_384316 : List Nat := [2, 2, 2, 2, 1, 3, 2, 1, 3, 3, 2]
def baseStart_384316 : Nat := 118140960795 + 384316 * 2 ^ 59
def prefixEnd_384316 : Nat := 4983230072969 + 3 ^ 40 * 384316 * 2
def baseEnd_384316 : Nat := 197338831213423595582569

theorem tailTrace_384316 : CollatzResearch.WordTrace tailWord_384316 prefixEnd_384316 197338831213423595582569 := by
  unfold tailWord_384316
  simp only [CollatzResearch.WordTrace]
  refine ⟨7008578037848121396182401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9344770717130828528243201 7008578037848121396182401)
  ·
    refine ⟨5256433528386091047136801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7008578037848121396182401 5256433528386091047136801)
    ·
      refine ⟨3942325146289568285352601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5256433528386091047136801 3942325146289568285352601)
      ·
        refine ⟨2956743859717176214014451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3942325146289568285352601 2956743859717176214014451)
        ·
          refine ⟨4435115789575764321021677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2956743859717176214014451 4435115789575764321021677)
          ·
            refine ⟨1663168421090911620383129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4435115789575764321021677 1663168421090911620383129)
            ·
              refine ⟨1247376315818183715287347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1663168421090911620383129 1247376315818183715287347)
              ·
                refine ⟨1871064473727275572931021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1247376315818183715287347 1871064473727275572931021)
                ·
                  refine ⟨701649177647728339849133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1871064473727275572931021 701649177647728339849133)
                  ·
                    refine ⟨263118441617898127443425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 701649177647728339849133 263118441617898127443425)
                    ·
                      refine ⟨197338831213423595582569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 263118441617898127443425 197338831213423595582569)
                      ·
                        rfl

theorem cell23_384316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 2, 1, 3, 3, 2].length) (baseStart_384316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_384316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_384316 prefixEnd_384316 := by exact prefixLift 384316
  have htrace : WordTrace (prefixWord ++ tailWord_384316) baseStart_384316 baseEnd_384316 := by
    simpa [prefixWord, tailWord_384316, baseEnd_384316] using wordTrace_append hprefix tailTrace_384316
  have hstable : (prefixWord ++ tailWord_384316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_384316).length < 2 ^ (prefixWord ++ tailWord_384316).sum := by decide
  have hdescent : baseEnd_384316 < baseStart_384316 := by decide
  rcases family_descends (prefixWord ++ tailWord_384316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_384409 : List Nat := [1, 2, 1, 2, 1, 6, 1, 1, 1, 2, 5]
def baseStart_384409 : Nat := 118140960795 + 384409 * 2 ^ 59
def prefixEnd_384409 : Nat := 4983230072969 + 3 ^ 40 * 384409 * 2
def baseEnd_384409 : Nat := 197386584914291731719641

theorem tailTrace_384409 : CollatzResearch.WordTrace tailWord_384409 prefixEnd_384409 197386584914291731719641 := by
  unfold tailWord_384409
  simp only [CollatzResearch.WordTrace]
  refine ⟨14020548064359319675500281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9347032042906213117000187 14020548064359319675500281)
  ·
    refine ⟨10515411048269489756625211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14020548064359319675500281 10515411048269489756625211)
    ·
      refine ⟨15773116572404234634937817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10515411048269489756625211 15773116572404234634937817)
      ·
        refine ⟨11829837429303175976203363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15773116572404234634937817 11829837429303175976203363)
        ·
          refine ⟨17744756143954763964305045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11829837429303175976203363 17744756143954763964305045)
          ·
            refine ⟨831785444247879560826799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 17744756143954763964305045 831785444247879560826799)
            ·
              refine ⟨1247678166371819341240199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 831785444247879560826799 1247678166371819341240199)
              ·
                refine ⟨1871517249557729011860299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1247678166371819341240199 1871517249557729011860299)
                ·
                  refine ⟨2807275874336593517790449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1871517249557729011860299 2807275874336593517790449)
                  ·
                    refine ⟨2105456905752445138342837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2807275874336593517790449 2105456905752445138342837)
                    ·
                      refine ⟨197386584914291731719641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2105456905752445138342837 197386584914291731719641)
                      ·
                        rfl

theorem cell23_384409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 6, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 6, 1, 1, 1, 2, 5].length) (baseStart_384409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_384409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_384409 prefixEnd_384409 := by exact prefixLift 384409
  have htrace : WordTrace (prefixWord ++ tailWord_384409) baseStart_384409 baseEnd_384409 := by
    simpa [prefixWord, tailWord_384409, baseEnd_384409] using wordTrace_append hprefix tailTrace_384409
  have hstable : (prefixWord ++ tailWord_384409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_384409).length < 2 ^ (prefixWord ++ tailWord_384409).sum := by decide
  have hdescent : baseEnd_384409 < baseStart_384409 := by decide
  rcases family_descends (prefixWord ++ tailWord_384409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_384419 : List Nat := [1, 1, 1, 4, 1, 3, 1, 2, 4, 1, 4]
def baseStart_384419 : Nat := 118140960795 + 384419 * 2 ^ 59
def prefixEnd_384419 : Nat := 4983230072969 + 3 ^ 40 * 384419 * 2
def baseEnd_384419 : Nat := 197391719720836692594595

theorem tailTrace_384419 : CollatzResearch.WordTrace tailWord_384419 prefixEnd_384419 197391719720836692594595 := by
  unfold tailWord_384419
  simp only [CollatzResearch.WordTrace]
  refine ⟨14020912794323091383364311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9347275196215394255576207 14020912794323091383364311)
  ·
    refine ⟨21031369191484637075046467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14020912794323091383364311 21031369191484637075046467)
    ·
      refine ⟨31547053787226955612569701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21031369191484637075046467 31547053787226955612569701)
      ·
        refine ⟨5915072585105054177356819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 31547053787226955612569701 5915072585105054177356819)
        ·
          refine ⟨8872608877657581266035229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5915072585105054177356819 8872608877657581266035229)
          ·
            refine ⟨3327228329121592974763211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8872608877657581266035229 3327228329121592974763211)
            ·
              refine ⟨4990842493682389462144817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3327228329121592974763211 4990842493682389462144817)
              ·
                refine ⟨3743131870261792096608613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4990842493682389462144817 3743131870261792096608613)
                ·
                  refine ⟨701837225674086018114115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3743131870261792096608613 701837225674086018114115)
                  ·
                    refine ⟨1052755838511129027171173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 701837225674086018114115 1052755838511129027171173)
                    ·
                      refine ⟨197391719720836692594595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1052755838511129027171173 197391719720836692594595)
                      ·
                        rfl

theorem cell23_384419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 1, 2, 4, 1, 4].length) (baseStart_384419 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_384419 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_384419 prefixEnd_384419 := by exact prefixLift 384419
  have htrace : WordTrace (prefixWord ++ tailWord_384419) baseStart_384419 baseEnd_384419 := by
    simpa [prefixWord, tailWord_384419, baseEnd_384419] using wordTrace_append hprefix tailTrace_384419
  have hstable : (prefixWord ++ tailWord_384419).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_384419).length < 2 ^ (prefixWord ++ tailWord_384419).sum := by decide
  have hdescent : baseEnd_384419 < baseStart_384419 := by decide
  rcases family_descends (prefixWord ++ tailWord_384419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_384456 : List Nat := [2, 1, 3, 1, 3, 1, 1, 4, 2, 2, 3]
def baseStart_384456 : Nat := 118140960795 + 384456 * 2 ^ 59
def prefixEnd_384456 : Nat := 4983230072969 + 3 ^ 40 * 384456 * 2
def baseEnd_384456 : Nat := 197410718505053047831925

theorem tailTrace_384456 : CollatzResearch.WordTrace tailWord_384456 prefixEnd_384456 197410718505053047831925 := by
  unfold tailWord_384456
  simp only [CollatzResearch.WordTrace]
  refine ⟨7011131147594523351230611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9348174863459364468307481 7011131147594523351230611)
  ·
    refine ⟨10516696721391785026845917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7011131147594523351230611 10516696721391785026845917)
    ·
      refine ⟨3943761270521919385067219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10516696721391785026845917 3943761270521919385067219)
      ·
        refine ⟨5915641905782879077600829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3943761270521919385067219 5915641905782879077600829)
        ·
          refine ⟨2218365714668579654100311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5915641905782879077600829 2218365714668579654100311)
          ·
            refine ⟨3327548572002869481150467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2218365714668579654100311 3327548572002869481150467)
            ·
              refine ⟨4991322858004304221725701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3327548572002869481150467 4991322858004304221725701)
              ·
                refine ⟨935873035875807041573569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4991322858004304221725701 935873035875807041573569)
                ·
                  refine ⟨701904776906855281180177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 935873035875807041573569 701904776906855281180177)
                  ·
                    refine ⟨526428582680141460885133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 701904776906855281180177 526428582680141460885133)
                    ·
                      refine ⟨197410718505053047831925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 526428582680141460885133 197410718505053047831925)
                      ·
                        rfl

theorem cell23_384456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 1, 4, 2, 2, 3].length) (baseStart_384456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_384456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_384456 prefixEnd_384456 := by exact prefixLift 384456
  have htrace : WordTrace (prefixWord ++ tailWord_384456) baseStart_384456 baseEnd_384456 := by
    simpa [prefixWord, tailWord_384456, baseEnd_384456] using wordTrace_append hprefix tailTrace_384456
  have hstable : (prefixWord ++ tailWord_384456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_384456).length < 2 ^ (prefixWord ++ tailWord_384456).sum := by decide
  have hdescent : baseEnd_384456 < baseStart_384456 := by decide
  rcases family_descends (prefixWord ++ tailWord_384456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_384459 : List Nat := [1, 1, 1, 1, 3, 3, 3, 4, 6]
def baseStart_384459 : Nat := 118140960795 + 384459 * 2 ^ 59
def prefixEnd_384459 : Nat := 4983230072969 + 3 ^ 40 * 384459 * 2
def baseEnd_384459 : Nat := 21934695438557392899379

theorem tailTrace_384459 : CollatzResearch.WordTrace tailWord_384459 prefixEnd_384459 21934695438557392899379 := by
  unfold tailWord_384459
  simp only [CollatzResearch.WordTrace]
  refine ⟨14022371714178178214820431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9348247809452118809880287 14022371714178178214820431)
  ·
    refine ⟨21033557571267267322230647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14022371714178178214820431 21033557571267267322230647)
    ·
      refine ⟨31550336356900900983345971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21033557571267267322230647 31550336356900900983345971)
      ·
        refine ⟨47325504535351351475018957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31550336356900900983345971 47325504535351351475018957)
        ·
          refine ⟨17747064200756756803132109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47325504535351351475018957 17747064200756756803132109)
          ·
            refine ⟨6655149075283783801174541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17747064200756756803132109 6655149075283783801174541)
            ·
              refine ⟨2495680903231418925440453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6655149075283783801174541 2495680903231418925440453)
              ·
                refine ⟨467940169355891048520085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2495680903231418925440453 467940169355891048520085)
                ·
                  refine ⟨21934695438557392899379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 467940169355891048520085 21934695438557392899379)
                  ·
                    rfl

theorem cell23_384459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 3, 4, 6].length) (baseStart_384459 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_384459 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_384459 prefixEnd_384459 := by exact prefixLift 384459
  have htrace : WordTrace (prefixWord ++ tailWord_384459) baseStart_384459 baseEnd_384459 := by
    simpa [prefixWord, tailWord_384459, baseEnd_384459] using wordTrace_append hprefix tailTrace_384459
  have hstable : (prefixWord ++ tailWord_384459).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_384459).length < 2 ^ (prefixWord ++ tailWord_384459).sum := by decide
  have hdescent : baseEnd_384459 < baseStart_384459 := by decide
  rcases family_descends (prefixWord ++ tailWord_384459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_384470 : List Nat := [5, 2, 1, 1, 1, 3, 1, 1, 2, 4, 2]
def baseStart_384470 : Nat := 118140960795 + 384470 * 2 ^ 59
def prefixEnd_384470 : Nat := 4983230072969 + 3 ^ 40 * 384470 * 2
def baseEnd_384470 : Nat := 197417907234215993056861

theorem tailTrace_384470 : CollatzResearch.WordTrace tailWord_384470 prefixEnd_384470 197417907234215993056861 := by
  unfold tailWord_384470
  simp only [CollatzResearch.WordTrace]
  refine ⟨876423307321145443341929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 9348515278092218062313909 876423307321145443341929)
  ·
    refine ⟨657317480490859082506447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 876423307321145443341929 657317480490859082506447)
    ·
      refine ⟨985976220736288623759671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 657317480490859082506447 985976220736288623759671)
      ·
        refine ⟨1478964331104432935639507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 985976220736288623759671 1478964331104432935639507)
        ·
          refine ⟨2218446496656649403459261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1478964331104432935639507 2218446496656649403459261)
          ·
            refine ⟨831917436246243526297223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2218446496656649403459261 831917436246243526297223)
            ·
              refine ⟨1247876154369365289445835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 831917436246243526297223 1247876154369365289445835)
              ·
                refine ⟨1871814231554047934168753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1247876154369365289445835 1871814231554047934168753)
                ·
                  refine ⟨1403860673665535950626565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1871814231554047934168753 1403860673665535950626565)
                  ·
                    refine ⟨263223876312287990742481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1403860673665535950626565 263223876312287990742481)
                    ·
                      refine ⟨197417907234215993056861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 263223876312287990742481 197417907234215993056861)
                      ·
                        rfl

theorem cell23_384470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 3, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 3, 1, 1, 2, 4, 2].length) (baseStart_384470 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_384470 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_384470 prefixEnd_384470 := by exact prefixLift 384470
  have htrace : WordTrace (prefixWord ++ tailWord_384470) baseStart_384470 baseEnd_384470 := by
    simpa [prefixWord, tailWord_384470, baseEnd_384470] using wordTrace_append hprefix tailTrace_384470
  have hstable : (prefixWord ++ tailWord_384470).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_384470).length < 2 ^ (prefixWord ++ tailWord_384470).sum := by decide
  have hdescent : baseEnd_384470 < baseStart_384470 := by decide
  rcases family_descends (prefixWord ++ tailWord_384470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_384490 : List Nat := [3, 1, 3, 1, 4, 2, 1, 1, 2, 2, 3]
def baseStart_384490 : Nat := 118140960795 + 384490 * 2 ^ 59
def prefixEnd_384490 : Nat := 4983230072969 + 3 ^ 40 * 384490 * 2
def baseEnd_384490 : Nat := 197428176847305914806769

theorem tailTrace_384490 : CollatzResearch.WordTrace tailWord_384490 prefixEnd_384490 197428176847305914806769 := by
  unfold tailWord_384490
  simp only [CollatzResearch.WordTrace]
  refine ⟨3505875594266467627299731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9349001584710580339465949 3505875594266467627299731)
  ·
    refine ⟨5258813391399701440949597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3505875594266467627299731 5258813391399701440949597)
    ·
      refine ⟨1972055021774888040356099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5258813391399701440949597 1972055021774888040356099)
      ·
        refine ⟨2958082532662332060534149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1972055021774888040356099 2958082532662332060534149)
        ·
          refine ⟨554640474874187261350153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2958082532662332060534149 554640474874187261350153)
          ·
            refine ⟨415980356155640446012615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 554640474874187261350153 415980356155640446012615)
            ·
              refine ⟨623970534233460669018923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 415980356155640446012615 623970534233460669018923)
              ·
                refine ⟨935955801350191003528385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 623970534233460669018923 935955801350191003528385)
                ·
                  refine ⟨701966851012643252646289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 935955801350191003528385 701966851012643252646289)
                  ·
                    refine ⟨526475138259482439484717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 701966851012643252646289 526475138259482439484717)
                    ·
                      refine ⟨197428176847305914806769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 526475138259482439484717 197428176847305914806769)
                      ·
                        rfl

theorem cell23_384490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 2, 1, 1, 2, 2, 3].length) (baseStart_384490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_384490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_384490 prefixEnd_384490 := by exact prefixLift 384490
  have htrace : WordTrace (prefixWord ++ tailWord_384490) baseStart_384490 baseEnd_384490 := by
    simpa [prefixWord, tailWord_384490, baseEnd_384490] using wordTrace_append hprefix tailTrace_384490
  have hstable : (prefixWord ++ tailWord_384490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_384490).length < 2 ^ (prefixWord ++ tailWord_384490).sum := by decide
  have hdescent : baseEnd_384490 < baseStart_384490 := by decide
  rcases family_descends (prefixWord ++ tailWord_384490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_384506 : List Nat := [3, 1, 1, 1, 1, 2, 5, 3, 1, 5]
def baseStart_384506 : Nat := 118140960795 + 384506 * 2 ^ 59
def prefixEnd_384506 : Nat := 4983230072969 + 3 ^ 40 * 384506 * 2
def baseEnd_384506 : Nat := 65812130845925950735565

theorem tailTrace_384506 : CollatzResearch.WordTrace tailWord_384506 prefixEnd_384506 65812130845925950735565 := by
  unfold tailWord_384506
  simp only [CollatzResearch.WordTrace]
  refine ⟨3506021486251976310445343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9349390630005270161187581 3506021486251976310445343)
  ·
    refine ⟨5259032229377964465668015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3506021486251976310445343 5259032229377964465668015)
    ·
      refine ⟨7888548344066946698502023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5259032229377964465668015 7888548344066946698502023)
      ·
        refine ⟨11832822516100420047753035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7888548344066946698502023 11832822516100420047753035)
        ·
          refine ⟨17749233774150630071629553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11832822516100420047753035 17749233774150630071629553)
          ·
            refine ⟨13311925330612972553722165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17749233774150630071629553 13311925330612972553722165)
            ·
              refine ⟨1247992999744966176911453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 13311925330612972553722165 1247992999744966176911453)
              ·
                refine ⟨467997374904362316341795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1247992999744966176911453 467997374904362316341795)
                ·
                  refine ⟨701996062356543474512693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 467997374904362316341795 701996062356543474512693)
                  ·
                    refine ⟨65812130845925950735565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 701996062356543474512693 65812130845925950735565)
                    ·
                      rfl

theorem cell23_384506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 5, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 5, 3, 1, 5].length) (baseStart_384506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_384506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_384506 prefixEnd_384506 := by exact prefixLift 384506
  have htrace : WordTrace (prefixWord ++ tailWord_384506) baseStart_384506 baseEnd_384506 := by
    simpa [prefixWord, tailWord_384506, baseEnd_384506] using wordTrace_append hprefix tailTrace_384506
  have hstable : (prefixWord ++ tailWord_384506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_384506).length < 2 ^ (prefixWord ++ tailWord_384506).sum := by decide
  have hdescent : baseEnd_384506 < baseStart_384506 := by decide
  rcases family_descends (prefixWord ++ tailWord_384506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_384520 : List Nat := [2, 1, 3, 2, 1, 1, 4, 4, 1, 1, 3]
def baseStart_384520 : Nat := 118140960795 + 384520 * 2 ^ 59
def prefixEnd_384520 : Nat := 4983230072969 + 3 ^ 40 * 384520 * 2
def baseEnd_384520 : Nat := 197443581266940797431631

theorem tailTrace_384520 : CollatzResearch.WordTrace tailWord_384520 prefixEnd_384520 197443581266940797431631 := by
  unfold tailWord_384520
  simp only [CollatzResearch.WordTrace]
  refine ⟨7012298283478592816395507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9349731044638123755194009 7012298283478592816395507)
  ·
    refine ⟨10518447425217889224593261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7012298283478592816395507 10518447425217889224593261)
    ·
      refine ⟨3944417784456708459222473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10518447425217889224593261 3944417784456708459222473)
      ·
        refine ⟨2958313338342531344416855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3944417784456708459222473 2958313338342531344416855)
        ·
          refine ⟨4437470007513797016625283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2958313338342531344416855 4437470007513797016625283)
          ·
            refine ⟨6656205011270695524937925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4437470007513797016625283 6656205011270695524937925)
            ·
              refine ⟨1248038439613255410925861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6656205011270695524937925 1248038439613255410925861)
              ·
                refine ⟨234007207427485389548599, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1248038439613255410925861 234007207427485389548599)
                ·
                  refine ⟨351010811141228084322899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 234007207427485389548599 351010811141228084322899)
                  ·
                    refine ⟨526516216711842126484349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 351010811141228084322899 526516216711842126484349)
                    ·
                      refine ⟨197443581266940797431631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 526516216711842126484349 197443581266940797431631)
                      ·
                        rfl

theorem cell23_384520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 4, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 4, 4, 1, 1, 3].length) (baseStart_384520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_384520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_384520 prefixEnd_384520 := by exact prefixLift 384520
  have htrace : WordTrace (prefixWord ++ tailWord_384520) baseStart_384520 baseEnd_384520 := by
    simpa [prefixWord, tailWord_384520, baseEnd_384520] using wordTrace_append hprefix tailTrace_384520
  have hstable : (prefixWord ++ tailWord_384520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_384520).length < 2 ^ (prefixWord ++ tailWord_384520).sum := by decide
  have hdescent : baseEnd_384520 < baseStart_384520 := by decide
  rcases family_descends (prefixWord ++ tailWord_384520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_384563 : List Nat := [1, 1, 1, 2, 4, 3, 2, 3, 1, 2, 3]
def baseStart_384563 : Nat := 118140960795 + 384563 * 2 ^ 59
def prefixEnd_384563 : Nat := 4983230072969 + 3 ^ 40 * 384563 * 2
def baseEnd_384563 : Nat := 197465660935084129193933

theorem tailTrace_384563 : CollatzResearch.WordTrace tailWord_384563 prefixEnd_384563 197465660935084129193933 := by
  unfold tailWord_384563
  simp only [CollatzResearch.WordTrace]
  refine ⟨14026164905801403976606343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9350776603867602651070895 14026164905801403976606343)
  ·
    refine ⟨21039247358702105964909515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14026164905801403976606343 21039247358702105964909515)
    ·
      refine ⟨31558871038053158947364273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21039247358702105964909515 31558871038053158947364273)
      ·
        refine ⟨23669153278539869210523205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31558871038053158947364273 23669153278539869210523205)
        ·
          refine ⟨4437966239726225476973101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23669153278539869210523205 4437966239726225476973101)
          ·
            refine ⟨1664237339897334553864913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4437966239726225476973101 1664237339897334553864913)
            ·
              refine ⟨1248178004923000915398685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1664237339897334553864913 1248178004923000915398685)
              ·
                refine ⟨468066751846125343274507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1248178004923000915398685 468066751846125343274507)
                ·
                  refine ⟨702100127769188014911761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 468066751846125343274507 702100127769188014911761)
                  ·
                    refine ⟨526575095826891011183821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 702100127769188014911761 526575095826891011183821)
                    ·
                      refine ⟨197465660935084129193933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 526575095826891011183821 197465660935084129193933)
                      ·
                        rfl

theorem cell23_384563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 2, 3, 1, 2, 3].length) (baseStart_384563 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_384563 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_384563 prefixEnd_384563 := by exact prefixLift 384563
  have htrace : WordTrace (prefixWord ++ tailWord_384563) baseStart_384563 baseEnd_384563 := by
    simpa [prefixWord, tailWord_384563, baseEnd_384563] using wordTrace_append hprefix tailTrace_384563
  have hstable : (prefixWord ++ tailWord_384563).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_384563).length < 2 ^ (prefixWord ++ tailWord_384563).sum := by decide
  have hdescent : baseEnd_384563 < baseStart_384563 := by decide
  rcases family_descends (prefixWord ++ tailWord_384563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_384633 : List Nat := [1, 2, 1, 3, 3, 1, 1, 2, 3, 4, 2]
def baseStart_384633 : Nat := 118140960795 + 384633 * 2 ^ 59
def prefixEnd_384633 : Nat := 4983230072969 + 3 ^ 40 * 384633 * 2
def baseEnd_384633 : Nat := 197501604580898855318611

theorem tailTrace_384633 : CollatzResearch.WordTrace tailWord_384633 prefixEnd_384633 197501604580898855318611 := by
  unfold tailWord_384633
  simp only [CollatzResearch.WordTrace]
  refine ⟨14028718015547805931654553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9352478677031870621103035 14028718015547805931654553)
  ·
    refine ⟨10521538511660854448740915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14028718015547805931654553 10521538511660854448740915)
    ·
      refine ⟨15782307767491281673111373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10521538511660854448740915 15782307767491281673111373)
      ·
        refine ⟨5918365412809230627416765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15782307767491281673111373 5918365412809230627416765)
        ·
          refine ⟨2219387029803461485281287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5918365412809230627416765 2219387029803461485281287)
          ·
            refine ⟨3329080544705192227921931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2219387029803461485281287 3329080544705192227921931)
            ·
              refine ⟨4993620817057788341882897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3329080544705192227921931 4993620817057788341882897)
              ·
                refine ⟨3745215612793341256412173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4993620817057788341882897 3745215612793341256412173)
                ·
                  refine ⟨1404455854797502971154565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3745215612793341256412173 1404455854797502971154565)
                  ·
                    refine ⟨263335472774531807091481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1404455854797502971154565 263335472774531807091481)
                    ·
                      refine ⟨197501604580898855318611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 263335472774531807091481 197501604580898855318611)
                      ·
                        rfl

theorem cell23_384633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 1, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 1, 2, 3, 4, 2].length) (baseStart_384633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_384633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_384633 prefixEnd_384633 := by exact prefixLift 384633
  have htrace : WordTrace (prefixWord ++ tailWord_384633) baseStart_384633 baseEnd_384633 := by
    simpa [prefixWord, tailWord_384633, baseEnd_384633] using wordTrace_append hprefix tailTrace_384633
  have hstable : (prefixWord ++ tailWord_384633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_384633).length < 2 ^ (prefixWord ++ tailWord_384633).sum := by decide
  have hdescent : baseEnd_384633 < baseStart_384633 := by decide
  rcases family_descends (prefixWord ++ tailWord_384633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_384650 : List Nat := [3, 1, 2, 3, 2, 1, 1, 3, 1, 4, 2]
def baseStart_384650 : Nat := 118140960795 + 384650 * 2 ^ 59
def prefixEnd_384650 : Nat := 4983230072969 + 3 ^ 40 * 384650 * 2
def baseEnd_384650 : Nat := 197510333752025288806033

theorem tailTrace_384650 : CollatzResearch.WordTrace tailWord_384650 prefixEnd_384650 197510333752025288806033 := by
  unfold tailWord_384650
  simp only [CollatzResearch.WordTrace]
  refine ⟨3507334514121554458755851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9352892037657478556682269 3507334514121554458755851)
  ·
    refine ⟨5261001771182331688133777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3507334514121554458755851 5261001771182331688133777)
    ·
      refine ⟨3945751328386748766100333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5261001771182331688133777 3945751328386748766100333)
      ·
        refine ⟨1479656748145030787287625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3945751328386748766100333 1479656748145030787287625)
        ·
          refine ⟨1109742561108773090465719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1479656748145030787287625 1109742561108773090465719)
          ·
            refine ⟨1664613841663159635698579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1109742561108773090465719 1664613841663159635698579)
            ·
              refine ⟨2496920762494739453547869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1664613841663159635698579 2496920762494739453547869)
              ·
                refine ⟨936345285935527295080451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2496920762494739453547869 936345285935527295080451)
                ·
                  refine ⟨1404517928903290942620677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 936345285935527295080451 1404517928903290942620677)
                  ·
                    refine ⟨263347111669367051741377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1404517928903290942620677 263347111669367051741377)
                    ·
                      refine ⟨197510333752025288806033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 263347111669367051741377 197510333752025288806033)
                      ·
                        rfl

theorem cell23_384650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 1, 3, 1, 4, 2].length) (baseStart_384650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_384650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_384650 prefixEnd_384650 := by exact prefixLift 384650
  have htrace : WordTrace (prefixWord ++ tailWord_384650) baseStart_384650 baseEnd_384650 := by
    simpa [prefixWord, tailWord_384650, baseEnd_384650] using wordTrace_append hprefix tailTrace_384650
  have hstable : (prefixWord ++ tailWord_384650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_384650).length < 2 ^ (prefixWord ++ tailWord_384650).sum := by decide
  have hdescent : baseEnd_384650 < baseStart_384650 := by decide
  rcases family_descends (prefixWord ++ tailWord_384650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_384671 : List Nat := [1, 1, 2, 7, 1, 2, 2, 1, 1, 3, 2]
def baseStart_384671 : Nat := 118140960795 + 384671 * 2 ^ 59
def prefixEnd_384671 : Nat := 4983230072969 + 3 ^ 40 * 384671 * 2
def baseEnd_384671 : Nat := 197521116845769706643437

theorem tailTrace_384671 : CollatzResearch.WordTrace tailWord_384671 prefixEnd_384671 197521116845769706643437 := by
  unfold tailWord_384671
  simp only [CollatzResearch.WordTrace]
  refine ⟨14030103989410138421537867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9353402659606758947691911 14030103989410138421537867)
  ·
    refine ⟨21045155984115207632306801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14030103989410138421537867 21045155984115207632306801)
    ·
      refine ⟨15783866988086405724230101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21045155984115207632306801 15783866988086405724230101)
      ·
        refine ⟨369934382533275134161643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 15783866988086405724230101 369934382533275134161643)
        ·
          refine ⟨554901573799912701242465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 369934382533275134161643 554901573799912701242465)
          ·
            refine ⟨416176180349934525931849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 554901573799912701242465 416176180349934525931849)
            ·
              refine ⟨312132135262450894448887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 416176180349934525931849 312132135262450894448887)
              ·
                refine ⟨468198202893676341673331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 312132135262450894448887 468198202893676341673331)
                ·
                  refine ⟨702297304340514512509997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 468198202893676341673331 702297304340514512509997)
                  ·
                    refine ⟨263361489127692942191249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 702297304340514512509997 263361489127692942191249)
                    ·
                      refine ⟨197521116845769706643437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 263361489127692942191249 197521116845769706643437)
                      ·
                        rfl

theorem cell23_384671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 2, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 2, 2, 1, 1, 3, 2].length) (baseStart_384671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_384671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_384671 prefixEnd_384671 := by exact prefixLift 384671
  have htrace : WordTrace (prefixWord ++ tailWord_384671) baseStart_384671 baseEnd_384671 := by
    simpa [prefixWord, tailWord_384671, baseEnd_384671] using wordTrace_append hprefix tailTrace_384671
  have hstable : (prefixWord ++ tailWord_384671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_384671).length < 2 ^ (prefixWord ++ tailWord_384671).sum := by decide
  have hdescent : baseEnd_384671 < baseStart_384671 := by decide
  rcases family_descends (prefixWord ++ tailWord_384671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_384696 : List Nat := [2, 1, 2, 1, 2, 1, 1, 5, 1, 2, 5]
def baseStart_384696 : Nat := 118140960795 + 384696 * 2 ^ 59
def prefixEnd_384696 : Nat := 4983230072969 + 3 ^ 40 * 384696 * 2
def baseEnd_384696 : Nat := 197533953862132108830821

theorem tailTrace_384696 : CollatzResearch.WordTrace tailWord_384696 prefixEnd_384696 197533953862132108830821 := by
  unfold tailWord_384696
  simp only [CollatzResearch.WordTrace]
  refine ⟨7015507907159783845598971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9354010542879711794131961 7015507907159783845598971)
  ·
    refine ⟨10523261860739675768398457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7015507907159783845598971 10523261860739675768398457)
    ·
      refine ⟨7892446395554756826298843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10523261860739675768398457 7892446395554756826298843)
      ·
        refine ⟨11838669593332135239448265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7892446395554756826298843 11838669593332135239448265)
        ·
          refine ⟨8879002194999101429586199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11838669593332135239448265 8879002194999101429586199)
          ·
            refine ⟨13318503292498652144379299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8879002194999101429586199 13318503292498652144379299)
            ·
              refine ⟨19977754938747978216568949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13318503292498652144379299 19977754938747978216568949)
              ·
                refine ⟨1872914525507622957803339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 19977754938747978216568949 1872914525507622957803339)
                ·
                  refine ⟨2809371788261434436705009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1872914525507622957803339 2809371788261434436705009)
                  ·
                    refine ⟨2107028841196075827528757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2809371788261434436705009 2107028841196075827528757)
                    ·
                      refine ⟨197533953862132108830821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 2107028841196075827528757 197533953862132108830821)
                      ·
                        rfl

theorem cell23_384696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 5, 1, 2, 5].length) (baseStart_384696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_384696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_384696 prefixEnd_384696 := by exact prefixLift 384696
  have htrace : WordTrace (prefixWord ++ tailWord_384696) baseStart_384696 baseEnd_384696 := by
    simpa [prefixWord, tailWord_384696, baseEnd_384696] using wordTrace_append hprefix tailTrace_384696
  have hstable : (prefixWord ++ tailWord_384696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_384696).length < 2 ^ (prefixWord ++ tailWord_384696).sum := by decide
  have hdescent : baseEnd_384696 < baseStart_384696 := by decide
  rcases family_descends (prefixWord ++ tailWord_384696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
