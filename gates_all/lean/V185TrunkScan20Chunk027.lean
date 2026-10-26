import V185TrunkScan20Chunk026

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental

namespace V185TrunkScan20Incremental

def tailWord_164860 : List Nat := [2, 2, 2, 1, 2, 3, 1, 1, 6]
def baseStart_164860 : Nat := 118140960795 + 164860 * 2 ^ 59
def prefixEnd_164860 : Nat := 4983230072969 + 3 ^ 40 * 164860 * 2
def baseEnd_164860 : Nat := 75246596178071305059403

theorem tailTrace_164860 : CollatzResearch.WordTrace tailWord_164860 prefixEnd_164860 75246596178071305059403 := by
  unfold tailWord_164860
  simp only [CollatzResearch.WordTrace]
  refine ⟨3006469091373925345754017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4008625455165233794338689 3006469091373925345754017)
  ·
    refine ⟨2254851818530444009315513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3006469091373925345754017 2254851818530444009315513)
    ·
      refine ⟨1691138863897833006986635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2254851818530444009315513 1691138863897833006986635)
      ·
        refine ⟨2536708295846749510479953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1691138863897833006986635 2536708295846749510479953)
        ·
          refine ⟨1902531221885062132859965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2536708295846749510479953 1902531221885062132859965)
          ·
            refine ⟨713449208206898299822487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1902531221885062132859965 713449208206898299822487)
            ·
              refine ⟨1070173812310347449733731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 713449208206898299822487 1070173812310347449733731)
              ·
                refine ⟨1605260718465521174600597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1070173812310347449733731 1605260718465521174600597)
                ·
                  refine ⟨75246596178071305059403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1605260718465521174600597 75246596178071305059403)
                  ·
                    rfl

theorem cell20_164860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 1, 1, 6].length) (baseStart_164860 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_164860 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_164860 prefixEnd_164860 := by exact prefixLift 164860
  have htrace : WordTrace (prefixWord ++ tailWord_164860) baseStart_164860 baseEnd_164860 := by
    simpa [prefixWord, tailWord_164860, baseEnd_164860] using wordTrace_append hprefix tailTrace_164860
  have hstable : (prefixWord ++ tailWord_164860).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_164860).length < 2 ^ (prefixWord ++ tailWord_164860).sum := by decide
  have hdescent : baseEnd_164860 < baseStart_164860 := by decide
  rcases family_descends (prefixWord ++ tailWord_164860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_164887 : List Nat := [1, 1, 3, 5, 1, 3, 1, 2, 3]
def baseStart_164887 : Nat := 118140960795 + 164887 * 2 ^ 59
def prefixEnd_164887 : Nat := 4983230072969 + 3 ^ 40 * 164887 * 2
def baseEnd_164887 : Nat := 75258919713779211159293

theorem tailTrace_164887 : CollatzResearch.WordTrace tailWord_164887 prefixEnd_164887 75258919713779211159293 := by
  unfold tailWord_164887
  simp only [CollatzResearch.WordTrace]
  refine ⟨6013922953650034302740915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4009281969100022868493943 6013922953650034302740915)
  ·
    refine ⟨9020884430475051454111373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6013922953650034302740915 9020884430475051454111373)
    ·
      refine ⟨3382831661428144295291765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9020884430475051454111373 3382831661428144295291765)
      ·
        refine ⟨317140468258888527683603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 3382831661428144295291765 317140468258888527683603)
        ·
          refine ⟨475710702388332791525405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 317140468258888527683603 475710702388332791525405)
          ·
            refine ⟨178391513395624796822027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 475710702388332791525405 178391513395624796822027)
            ·
              refine ⟨267587270093437195233041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 178391513395624796822027 267587270093437195233041)
              ·
                refine ⟨200690452570077896424781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 267587270093437195233041 200690452570077896424781)
                ·
                  refine ⟨75258919713779211159293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 200690452570077896424781 75258919713779211159293)
                  ·
                    rfl

theorem cell20_164887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 3, 1, 2, 3].length) (baseStart_164887 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_164887 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_164887 prefixEnd_164887 := by exact prefixLift 164887
  have htrace : WordTrace (prefixWord ++ tailWord_164887) baseStart_164887 baseEnd_164887 := by
    simpa [prefixWord, tailWord_164887, baseEnd_164887] using wordTrace_append hprefix tailTrace_164887
  have hstable : (prefixWord ++ tailWord_164887).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_164887).length < 2 ^ (prefixWord ++ tailWord_164887).sum := by decide
  have hdescent : baseEnd_164887 < baseStart_164887 := by decide
  rcases family_descends (prefixWord ++ tailWord_164887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_164908 : List Nat := [2, 2, 1, 1, 1, 2, 7, 1, 3]
def baseStart_164908 : Nat := 118140960795 + 164908 * 2 ^ 59
def prefixEnd_164908 : Nat := 4983230072969 + 3 ^ 40 * 164908 * 2
def baseEnd_164908 : Nat := 75268504685996471459207

theorem tailTrace_164908 : CollatzResearch.WordTrace tailWord_164908 prefixEnd_164908 75268504685996471459207 := by
  unfold tailWord_164908
  simp only [CollatzResearch.WordTrace]
  refine ⟨3007344443286977444627689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4009792591049303259503585 3007344443286977444627689)
  ·
    refine ⟨2255508332465233083470767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3007344443286977444627689 2255508332465233083470767)
    ·
      refine ⟨3383262498697849625206151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2255508332465233083470767 3383262498697849625206151)
      ·
        refine ⟨5074893748046774437809227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3383262498697849625206151 5074893748046774437809227)
        ·
          refine ⟨7612340622070161656713841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5074893748046774437809227 7612340622070161656713841)
          ·
            refine ⟨5709255466552621242535381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7612340622070161656713841 5709255466552621242535381)
            ·
              refine ⟨133810674997327060371923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 5709255466552621242535381 133810674997327060371923)
              ·
                refine ⟨200716012495990590557885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 133810674997327060371923 200716012495990590557885)
                ·
                  refine ⟨75268504685996471459207, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 200716012495990590557885 75268504685996471459207)
                  ·
                    rfl

theorem cell20_164908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 3].length) (baseStart_164908 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_164908 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_164908 prefixEnd_164908 := by exact prefixLift 164908
  have htrace : WordTrace (prefixWord ++ tailWord_164908) baseStart_164908 baseEnd_164908 := by
    simpa [prefixWord, tailWord_164908, baseEnd_164908] using wordTrace_append hprefix tailTrace_164908
  have hstable : (prefixWord ++ tailWord_164908).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_164908).length < 2 ^ (prefixWord ++ tailWord_164908).sum := by decide
  have hdescent : baseEnd_164908 < baseStart_164908 := by decide
  rcases family_descends (prefixWord ++ tailWord_164908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_164918 : List Nat := [5, 1, 2, 1, 1, 4, 2, 4]
def baseStart_164918 : Nat := 118140960795 + 164918 * 2 ^ 59
def prefixEnd_164918 : Nat := 4983230072969 + 3 ^ 40 * 164918 * 2
def baseEnd_164918 : Nat := 25091022986160293708611

theorem tailTrace_164918 : CollatzResearch.WordTrace tailWord_164918 prefixEnd_164918 25091022986160293708611 := by
  unfold tailWord_164918
  simp only [CollatzResearch.WordTrace]
  refine ⟨375940851033607912319963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 4010035744358484398079605 375940851033607912319963)
  ·
    refine ⟨563911276550411868479945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 375940851033607912319963 563911276550411868479945)
    ·
      refine ⟨422933457412808901359959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 563911276550411868479945 422933457412808901359959)
      ·
        refine ⟨634400186119213352039939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 422933457412808901359959 634400186119213352039939)
        ·
          refine ⟨951600279178820028059909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 634400186119213352039939 951600279178820028059909)
          ·
            refine ⟨178425052346028755261233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 951600279178820028059909 178425052346028755261233)
            ·
              refine ⟨133818789259521566445925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 178425052346028755261233 133818789259521566445925)
              ·
                refine ⟨25091022986160293708611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 133818789259521566445925 25091022986160293708611)
                ·
                  rfl

theorem cell20_164918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 4, 2, 4].length) (baseStart_164918 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_164918 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_164918 prefixEnd_164918 := by exact prefixLift 164918
  have htrace : WordTrace (prefixWord ++ tailWord_164918) baseStart_164918 baseEnd_164918 := by
    simpa [prefixWord, tailWord_164918, baseEnd_164918] using wordTrace_append hprefix tailTrace_164918
  have hstable : (prefixWord ++ tailWord_164918).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_164918).length < 2 ^ (prefixWord ++ tailWord_164918).sum := by decide
  have hdescent : baseEnd_164918 < baseStart_164918 := by decide
  rcases family_descends (prefixWord ++ tailWord_164918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_164922 : List Nat := [3, 1, 1, 1, 3, 1, 6, 4]
def baseStart_164922 : Nat := 118140960795 + 164922 * 2 ^ 59
def prefixEnd_164922 : Nat := 4983230072969 + 3 ^ 40 * 164922 * 2
def baseEnd_164922 : Nat := 25091631555824881664161

theorem tailTrace_164922 : CollatzResearch.WordTrace tailWord_164922 prefixEnd_164922 25091631555824881664161 := by
  unfold tailWord_164922
  simp only [CollatzResearch.WordTrace]
  refine ⟨1503799877130808820066255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4010133005682156853510013 1503799877130808820066255)
  ·
    refine ⟨2255699815696213230099383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1503799877130808820066255 2255699815696213230099383)
    ·
      refine ⟨3383549723544319845149075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2255699815696213230099383 3383549723544319845149075)
      ·
        refine ⟨5075324585316479767723613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3383549723544319845149075 5075324585316479767723613)
        ·
          refine ⟨1903246719493679912896355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5075324585316479767723613 1903246719493679912896355)
          ·
            refine ⟨2854870079240519869344533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1903246719493679912896355 2854870079240519869344533)
            ·
              refine ⟨133822034964399368875525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 2854870079240519869344533 133822034964399368875525)
              ·
                refine ⟨25091631555824881664161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 133822034964399368875525 25091631555824881664161)
                ·
                  rfl

theorem cell20_164922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 6, 4].length) (baseStart_164922 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_164922 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_164922 prefixEnd_164922 := by exact prefixLift 164922
  have htrace : WordTrace (prefixWord ++ tailWord_164922) baseStart_164922 baseEnd_164922 := by
    simpa [prefixWord, tailWord_164922, baseEnd_164922] using wordTrace_append hprefix tailTrace_164922
  have hstable : (prefixWord ++ tailWord_164922).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_164922).length < 2 ^ (prefixWord ++ tailWord_164922).sum := by decide
  have hdescent : baseEnd_164922 < baseStart_164922 := by decide
  rcases family_descends (prefixWord ++ tailWord_164922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_165060 : List Nat := [2, 3, 3, 1, 3, 1, 1, 1, 5]
def baseStart_165060 : Nat := 118140960795 + 165060 * 2 ^ 59
def prefixEnd_165060 : Nat := 4983230072969 + 3 ^ 40 * 165060 * 2
def baseEnd_165060 : Nat := 75337881627759498391919

theorem tailTrace_165060 : CollatzResearch.WordTrace tailWord_165060 prefixEnd_165060 75337881627759498391919 := by
  unfold tailWord_165060
  simp only [CollatzResearch.WordTrace]
  refine ⟨3010116391011642424394317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4013488521348856565859089 3010116391011642424394317)
  ·
    refine ⟨1128793646629365909147869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3010116391011642424394317 1128793646629365909147869)
    ·
      refine ⟨423297617486012215930451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1128793646629365909147869 423297617486012215930451)
      ·
        refine ⟨634946426229018323895677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 423297617486012215930451 634946426229018323895677)
        ·
          refine ⟨238104909835881871460879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 634946426229018323895677 238104909835881871460879)
          ·
            refine ⟨357157364753822807191319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 238104909835881871460879 357157364753822807191319)
            ·
              refine ⟨535736047130734210786979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 357157364753822807191319 535736047130734210786979)
              ·
                refine ⟨803604070696101316180469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 535736047130734210786979 803604070696101316180469)
                ·
                  refine ⟨75337881627759498391919, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 803604070696101316180469 75337881627759498391919)
                  ·
                    rfl

theorem cell20_165060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 1, 1, 1, 5].length) (baseStart_165060 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_165060 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_165060 prefixEnd_165060 := by exact prefixLift 165060
  have htrace : WordTrace (prefixWord ++ tailWord_165060) baseStart_165060 baseEnd_165060 := by
    simpa [prefixWord, tailWord_165060, baseEnd_165060] using wordTrace_append hprefix tailTrace_165060
  have hstable : (prefixWord ++ tailWord_165060).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_165060).length < 2 ^ (prefixWord ++ tailWord_165060).sum := by decide
  have hdescent : baseEnd_165060 < baseStart_165060 := by decide
  rcases family_descends (prefixWord ++ tailWord_165060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_165077 : List Nat := [1, 3, 2, 4, 1, 2, 3, 1, 3]
def baseStart_165077 : Nat := 118140960795 + 165077 * 2 ^ 59
def prefixEnd_165077 : Nat := 4983230072969 + 3 ^ 40 * 165077 * 2
def baseEnd_165077 : Nat := 75345640890982994825183

theorem tailTrace_165077 : CollatzResearch.WordTrace tailWord_165077 prefixEnd_165077 75345640890982994825183 := by
  unfold tailWord_165077
  simp only [CollatzResearch.WordTrace]
  refine ⟨6020852822961696752157485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4013901881974464501438323 6020852822961696752157485)
  ·
    refine ⟨2257819808610636282059057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6020852822961696752157485 2257819808610636282059057)
    ·
      refine ⟨1693364856457977211544293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2257819808610636282059057 1693364856457977211544293)
      ·
        refine ⟨317505910585870727164555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1693364856457977211544293 317505910585870727164555)
        ·
          refine ⟨476258865878806090746833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 317505910585870727164555 476258865878806090746833)
          ·
            refine ⟨357194149409104568060125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 476258865878806090746833 357194149409104568060125)
            ·
              refine ⟨133947806028414213022547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 357194149409104568060125 133947806028414213022547)
              ·
                refine ⟨200921709042621319533821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 133947806028414213022547 200921709042621319533821)
                ·
                  refine ⟨75345640890982994825183, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 200921709042621319533821 75345640890982994825183)
                  ·
                    rfl

theorem cell20_165077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 2, 3, 1, 3].length) (baseStart_165077 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_165077 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_165077 prefixEnd_165077 := by exact prefixLift 165077
  have htrace : WordTrace (prefixWord ++ tailWord_165077) baseStart_165077 baseEnd_165077 := by
    simpa [prefixWord, tailWord_165077, baseEnd_165077] using wordTrace_append hprefix tailTrace_165077
  have hstable : (prefixWord ++ tailWord_165077).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_165077).length < 2 ^ (prefixWord ++ tailWord_165077).sum := by decide
  have hdescent : baseEnd_165077 < baseStart_165077 := by decide
  rcases family_descends (prefixWord ++ tailWord_165077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_165088 : List Nat := [2, 1, 1, 3, 1, 4, 2, 2, 4]
def baseStart_165088 : Nat := 118140960795 + 165088 * 2 ^ 59
def prefixEnd_165088 : Nat := 4983230072969 + 3 ^ 40 * 165088 * 2
def baseEnd_165088 : Nat := 75350661590715845458471

theorem tailTrace_165088 : CollatzResearch.WordTrace tailWord_165088 prefixEnd_165088 75350661590715845458471 := by
  unfold tailWord_165088
  simp only [CollatzResearch.WordTrace]
  refine ⟨3010627012960922815403959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4014169350614563753871945 3010627012960922815403959)
  ·
    refine ⟨4515940519441384223105939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3010627012960922815403959 4515940519441384223105939)
    ·
      refine ⟨6773910779162076334658909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4515940519441384223105939 6773910779162076334658909)
      ·
        refine ⟨2540216542185778625497091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6773910779162076334658909 2540216542185778625497091)
        ·
          refine ⟨3810324813278667938245637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2540216542185778625497091 3810324813278667938245637)
          ·
            refine ⟨714435902489750238421057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3810324813278667938245637 714435902489750238421057)
            ·
              refine ⟨535826926867312678815793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 714435902489750238421057 535826926867312678815793)
              ·
                refine ⟨401870195150484509111845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 535826926867312678815793 401870195150484509111845)
                ·
                  refine ⟨75350661590715845458471, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 401870195150484509111845 75350661590715845458471)
                  ·
                    rfl

theorem cell20_165088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 2, 2, 4].length) (baseStart_165088 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_165088 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_165088 prefixEnd_165088 := by exact prefixLift 165088
  have htrace : WordTrace (prefixWord ++ tailWord_165088) baseStart_165088 baseEnd_165088 := by
    simpa [prefixWord, tailWord_165088, baseEnd_165088] using wordTrace_append hprefix tailTrace_165088
  have hstable : (prefixWord ++ tailWord_165088).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_165088).length < 2 ^ (prefixWord ++ tailWord_165088).sum := by decide
  have hdescent : baseEnd_165088 < baseStart_165088 := by decide
  rcases family_descends (prefixWord ++ tailWord_165088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_165101 : List Nat := [1, 5, 1, 2, 2, 3, 1, 3, 2]
def baseStart_165101 : Nat := 118140960795 + 165101 * 2 ^ 59
def prefixEnd_165101 : Nat := 4983230072969 + 3 ^ 40 * 165101 * 2
def baseEnd_165101 : Nat := 75356595144945578025085

theorem tailTrace_165101 : CollatzResearch.WordTrace tailWord_165101 prefixEnd_165101 75356595144945578025085 := by
  unfold tailWord_165101
  simp only [CollatzResearch.WordTrace]
  refine ⟨6021728174874748851031157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4014485449916499234020771 6021728174874748851031157)
  ·
    refine ⟨564537016394507704784171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 6021728174874748851031157 564537016394507704784171)
    ·
      refine ⟨846805524591761557176257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 564537016394507704784171 846805524591761557176257)
      ·
        refine ⟨635104143443821167882193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 846805524591761557176257 635104143443821167882193)
        ·
          refine ⟨476328107582865875911645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 635104143443821167882193 476328107582865875911645)
          ·
            refine ⟨178623040343574703466867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 476328107582865875911645 178623040343574703466867)
            ·
              refine ⟨267934560515362055200301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 178623040343574703466867 267934560515362055200301)
              ·
                refine ⟨100475460193260770700113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 267934560515362055200301 100475460193260770700113)
                ·
                  refine ⟨75356595144945578025085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 100475460193260770700113 75356595144945578025085)
                  ·
                    rfl

theorem cell20_165101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 3, 1, 3, 2].length) (baseStart_165101 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_165101 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_165101 prefixEnd_165101 := by exact prefixLift 165101
  have htrace : WordTrace (prefixWord ++ tailWord_165101) baseStart_165101 baseEnd_165101 := by
    simpa [prefixWord, tailWord_165101, baseEnd_165101] using wordTrace_append hprefix tailTrace_165101
  have hstable : (prefixWord ++ tailWord_165101).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_165101).length < 2 ^ (prefixWord ++ tailWord_165101).sum := by decide
  have hdescent : baseEnd_165101 < baseStart_165101 := by decide
  rcases family_descends (prefixWord ++ tailWord_165101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_165147 : List Nat := [1, 1, 1, 1, 1, 1, 5, 3, 6]
def baseStart_165147 : Nat := 118140960795 + 165147 * 2 ^ 59
def prefixEnd_165147 : Nat := 4983230072969 + 3 ^ 40 * 165147 * 2
def baseEnd_165147 : Nat := 75377590798373862491563

theorem tailTrace_165147 : CollatzResearch.WordTrace tailWord_165147 prefixEnd_165147 75377590798373862491563 := by
  unfold tailWord_165147
  simp only [CollatzResearch.WordTrace]
  refine ⟨6023405932708098707205695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4015603955138732471470463 6023405932708098707205695)
  ·
    refine ⟨9035108899062148060808543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6023405932708098707205695 9035108899062148060808543)
    ·
      refine ⟨13552663348593222091212815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9035108899062148060808543 13552663348593222091212815)
      ·
        refine ⟨20328995022889833136819223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13552663348593222091212815 20328995022889833136819223)
        ·
          refine ⟨30493492534334749705228835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20328995022889833136819223 30493492534334749705228835)
          ·
            refine ⟨45740238801502124557843253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30493492534334749705228835 45740238801502124557843253)
            ·
              refine ⟨4288147387640824177297805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 45740238801502124557843253 4288147387640824177297805)
              ·
                refine ⟨1608055270365309066486677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4288147387640824177297805 1608055270365309066486677)
                ·
                  refine ⟨75377590798373862491563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1608055270365309066486677 75377590798373862491563)
                  ·
                    rfl

theorem cell20_165147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 3, 6].length) (baseStart_165147 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_165147 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_165147 prefixEnd_165147 := by exact prefixLift 165147
  have htrace : WordTrace (prefixWord ++ tailWord_165147) baseStart_165147 baseEnd_165147 := by
    simpa [prefixWord, tailWord_165147, baseEnd_165147] using wordTrace_append hprefix tailTrace_165147
  have hstable : (prefixWord ++ tailWord_165147).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_165147).length < 2 ^ (prefixWord ++ tailWord_165147).sum := by decide
  have hdescent : baseEnd_165147 < baseStart_165147 := by decide
  rcases family_descends (prefixWord ++ tailWord_165147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_165219 : List Nat := [1, 1, 1, 5, 2, 2, 1, 5, 2]
def baseStart_165219 : Nat := 118140960795 + 165219 * 2 ^ 59
def prefixEnd_165219 : Nat := 4983230072969 + 3 ^ 40 * 165219 * 2
def baseEnd_165219 : Nat := 75410453560261612091269

theorem tailTrace_165219 : CollatzResearch.WordTrace tailWord_165219 prefixEnd_165219 75410453560261612091269 := by
  unfold tailWord_165219
  simp only [CollatzResearch.WordTrace]
  refine ⟨6026031988447255003826711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4017354658964836669217807 6026031988447255003826711)
  ·
    refine ⟨9039047982670882505740067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6026031988447255003826711 9039047982670882505740067)
    ·
      refine ⟨13558571974006323758610101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9039047982670882505740067 13558571974006323758610101)
      ·
        refine ⟨1271116122563092852369697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 13558571974006323758610101 1271116122563092852369697)
        ·
          refine ⟨953337091922319639277273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1271116122563092852369697 953337091922319639277273)
          ·
            refine ⟨715002818941739729457955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 953337091922319639277273 715002818941739729457955)
            ·
              refine ⟨1072504228412609594186933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 715002818941739729457955 1072504228412609594186933)
              ·
                refine ⟨100547271413682149455025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1072504228412609594186933 100547271413682149455025)
                ·
                  refine ⟨75410453560261612091269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 100547271413682149455025 75410453560261612091269)
                  ·
                    rfl

theorem cell20_165219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 1, 5, 2].length) (baseStart_165219 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_165219 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_165219 prefixEnd_165219 := by exact prefixLift 165219
  have htrace : WordTrace (prefixWord ++ tailWord_165219) baseStart_165219 baseEnd_165219 := by
    simpa [prefixWord, tailWord_165219, baseEnd_165219] using wordTrace_append hprefix tailTrace_165219
  have hstable : (prefixWord ++ tailWord_165219).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_165219).length < 2 ^ (prefixWord ++ tailWord_165219).sum := by decide
  have hdescent : baseEnd_165219 < baseStart_165219 := by decide
  rcases family_descends (prefixWord ++ tailWord_165219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_165226 : List Nat := [3, 1, 3, 3, 2, 1, 7]
def baseStart_165226 : Nat := 118140960795 + 165226 * 2 ^ 59
def prefixEnd_165226 : Nat := 4983230072969 + 3 ^ 40 * 165226 * 2
def baseEnd_165226 : Nat := 8379294283444522095323

theorem tailTrace_165226 : CollatzResearch.WordTrace tailWord_165226 prefixEnd_165226 8379294283444522095323 := by
  unfold tailWord_165226
  simp only [CollatzResearch.WordTrace]
  refine ⟨1506571824855473799832883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4017524866281263466221021 1506571824855473799832883)
  ·
    refine ⟨2259857737283210699749325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1506571824855473799832883 2259857737283210699749325)
    ·
      refine ⟨847446651481204012405997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2259857737283210699749325 847446651481204012405997)
      ·
        refine ⟨317792494305451504652249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 847446651481204012405997 317792494305451504652249)
        ·
          refine ⟨238344370729088628489187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 317792494305451504652249 238344370729088628489187)
          ·
            refine ⟨357516556093632942733781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 238344370729088628489187 357516556093632942733781)
            ·
              refine ⟨8379294283444522095323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 357516556093632942733781 8379294283444522095323)
              ·
                rfl

theorem cell20_165226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 1, 7].length) (baseStart_165226 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_165226 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_165226 prefixEnd_165226 := by exact prefixLift 165226
  have htrace : WordTrace (prefixWord ++ tailWord_165226) baseStart_165226 baseEnd_165226 := by
    simpa [prefixWord, tailWord_165226, baseEnd_165226] using wordTrace_append hprefix tailTrace_165226
  have hstable : (prefixWord ++ tailWord_165226).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_165226).length < 2 ^ (prefixWord ++ tailWord_165226).sum := by decide
  have hdescent : baseEnd_165226 < baseStart_165226 := by decide
  rcases family_descends (prefixWord ++ tailWord_165226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_165233 : List Nat := [1, 2, 2, 2, 1, 2, 5, 2, 3]
def baseStart_165233 : Nat := 118140960795 + 165233 * 2 ^ 59
def prefixEnd_165233 : Nat := 4983230072969 + 3 ^ 40 * 165233 * 2
def baseEnd_165233 : Nat := 75416843541739785624545

theorem tailTrace_165233 : CollatzResearch.WordTrace tailWord_165233 prefixEnd_165233 75416843541739785624545 := by
  unfold tailWord_165233
  simp only [CollatzResearch.WordTrace]
  refine ⟨6026542610396535394836353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4017695073597690263224235 6026542610396535394836353)
  ·
    refine ⟨4519906957797401546127265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6026542610396535394836353 4519906957797401546127265)
    ·
      refine ⟨3389930218348051159595449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4519906957797401546127265 3389930218348051159595449)
      ·
        refine ⟨2542447663761038369696587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3389930218348051159595449 2542447663761038369696587)
        ·
          refine ⟨3813671495641557554544881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2542447663761038369696587 3813671495641557554544881)
          ·
            refine ⟨2860253621731168165908661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3813671495641557554544881 2860253621731168165908661)
            ·
              refine ⟨268148777037297015553937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2860253621731168165908661 268148777037297015553937)
              ·
                refine ⟨201111582777972761665453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 268148777037297015553937 201111582777972761665453)
                ·
                  refine ⟨75416843541739785624545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 201111582777972761665453 75416843541739785624545)
                  ·
                    rfl

theorem cell20_165233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 5, 2, 3].length) (baseStart_165233 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_165233 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_165233 prefixEnd_165233 := by exact prefixLift 165233
  have htrace : WordTrace (prefixWord ++ tailWord_165233) baseStart_165233 baseEnd_165233 := by
    simpa [prefixWord, tailWord_165233, baseEnd_165233] using wordTrace_append hprefix tailTrace_165233
  have hstable : (prefixWord ++ tailWord_165233).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_165233).length < 2 ^ (prefixWord ++ tailWord_165233).sum := by decide
  have hdescent : baseEnd_165233 < baseStart_165233 := by decide
  rcases family_descends (prefixWord ++ tailWord_165233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_165292 : List Nat := [2, 2, 1, 1, 1, 1, 6, 1, 5]
def baseStart_165292 : Nat := 118140960795 + 165292 * 2 ^ 59
def prefixEnd_165292 : Nat := 4983230072969 + 3 ^ 40 * 165292 * 2
def baseEnd_165292 : Nat := 75443772749397802657637

theorem tailTrace_165292 : CollatzResearch.WordTrace tailWord_165292 prefixEnd_165292 75443772749397802657637 := by
  unfold tailWord_165292
  simp only [CollatzResearch.WordTrace]
  refine ⟨3014347258591394235617065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4019129678121858980822753 3014347258591394235617065)
  ·
    refine ⟨2260760443943545676712799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3014347258591394235617065 2260760443943545676712799)
    ·
      refine ⟨3391140665915318515069199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2260760443943545676712799 3391140665915318515069199)
      ·
        refine ⟨5086710998872977772603799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3391140665915318515069199 5086710998872977772603799)
        ·
          refine ⟨7630066498309466658905699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5086710998872977772603799 7630066498309466658905699)
          ·
            refine ⟨11445099747464199988358549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7630066498309466658905699 11445099747464199988358549)
            ·
              refine ⟨536489050662384374454307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 11445099747464199988358549 536489050662384374454307)
              ·
                refine ⟨804733575993576561681461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 536489050662384374454307 804733575993576561681461)
                ·
                  refine ⟨75443772749397802657637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 804733575993576561681461 75443772749397802657637)
                  ·
                    rfl

theorem cell20_165292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 5].length) (baseStart_165292 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_165292 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_165292 prefixEnd_165292 := by exact prefixLift 165292
  have htrace : WordTrace (prefixWord ++ tailWord_165292) baseStart_165292 baseEnd_165292 := by
    simpa [prefixWord, tailWord_165292, baseEnd_165292] using wordTrace_append hprefix tailTrace_165292
  have hstable : (prefixWord ++ tailWord_165292).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_165292).length < 2 ^ (prefixWord ++ tailWord_165292).sum := by decide
  have hdescent : baseEnd_165292 < baseStart_165292 := by decide
  rcases family_descends (prefixWord ++ tailWord_165292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_165305 : List Nat := [1, 2, 1, 4, 4, 2, 2, 1, 3]
def baseStart_165305 : Nat := 118140960795 + 165305 * 2 ^ 59
def prefixEnd_165305 : Nat := 4983230072969 + 3 ^ 40 * 165305 * 2
def baseEnd_165305 : Nat := 75449706303627535224251

theorem tailTrace_165305 : CollatzResearch.WordTrace tailWord_165305 prefixEnd_165305 75449706303627535224251 := by
  unfold tailWord_165305
  simp only [CollatzResearch.WordTrace]
  refine ⟨6029168666135691691457369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4019445777423794460971579 6029168666135691691457369)
  ·
    refine ⟨4521876499601768768593027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6029168666135691691457369 4521876499601768768593027)
    ·
      refine ⟨6782814749402653152889541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4521876499601768768593027 6782814749402653152889541)
      ·
        refine ⟨1271777765512997466166789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6782814749402653152889541 1271777765512997466166789)
        ·
          refine ⟨238458331033687024906273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1271777765512997466166789 238458331033687024906273)
          ·
            refine ⟨178843748275265268679705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 238458331033687024906273 178843748275265268679705)
            ·
              refine ⟨134132811206448951509779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 178843748275265268679705 134132811206448951509779)
              ·
                refine ⟨201199216809673427264669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 134132811206448951509779 201199216809673427264669)
                ·
                  refine ⟨75449706303627535224251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 201199216809673427264669 75449706303627535224251)
                  ·
                    rfl

theorem cell20_165305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 2, 2, 1, 3].length) (baseStart_165305 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_165305 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_165305 prefixEnd_165305 := by exact prefixLift 165305
  have htrace : WordTrace (prefixWord ++ tailWord_165305) baseStart_165305 baseEnd_165305 := by
    simpa [prefixWord, tailWord_165305, baseEnd_165305] using wordTrace_append hprefix tailTrace_165305
  have hstable : (prefixWord ++ tailWord_165305).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_165305).length < 2 ^ (prefixWord ++ tailWord_165305).sum := by decide
  have hdescent : baseEnd_165305 < baseStart_165305 := by decide
  rcases family_descends (prefixWord ++ tailWord_165305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_165309 : List Nat := [1, 4, 1, 2, 2, 1, 3, 3, 3]
def baseStart_165309 : Nat := 118140960795 + 165309 * 2 ^ 59
def prefixEnd_165309 : Nat := 4983230072969 + 3 ^ 40 * 165309 * 2
def baseEnd_165309 : Nat := 75451532012621299090901

theorem tailTrace_165309 : CollatzResearch.WordTrace tailWord_165309 prefixEnd_165309 75451532012621299090901 := by
  unfold tailWord_165309
  simp only [CollatzResearch.WordTrace]
  refine ⟨6029314558121200374602981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4019543038747466916401987 6029314558121200374602981)
  ·
    refine ⟨1130496479647725070238059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6029314558121200374602981 1130496479647725070238059)
    ·
      refine ⟨1695744719471587605357089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1130496479647725070238059 1695744719471587605357089)
      ·
        refine ⟨1271808539603690704017817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1695744719471587605357089 1271808539603690704017817)
        ·
          refine ⟨953856404702768028013363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1271808539603690704017817 953856404702768028013363)
          ·
            refine ⟨1430784607054152042020045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 953856404702768028013363 1430784607054152042020045)
            ·
              refine ⟨536544227645307015757517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1430784607054152042020045 536544227645307015757517)
              ·
                refine ⟨201204085366990130909069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 536544227645307015757517 201204085366990130909069)
                ·
                  refine ⟨75451532012621299090901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 201204085366990130909069 75451532012621299090901)
                  ·
                    rfl

theorem cell20_165309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 3, 3, 3].length) (baseStart_165309 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_165309 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_165309 prefixEnd_165309 := by exact prefixLift 165309
  have htrace : WordTrace (prefixWord ++ tailWord_165309) baseStart_165309 baseEnd_165309 := by
    simpa [prefixWord, tailWord_165309, baseEnd_165309] using wordTrace_append hprefix tailTrace_165309
  have hstable : (prefixWord ++ tailWord_165309).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_165309).length < 2 ^ (prefixWord ++ tailWord_165309).sum := by decide
  have hdescent : baseEnd_165309 < baseStart_165309 := by decide
  rcases family_descends (prefixWord ++ tailWord_165309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_165333 : List Nat := [1, 3, 2, 3, 1, 1, 2, 5, 2]
def baseStart_165333 : Nat := 118140960795 + 165333 * 2 ^ 59
def prefixEnd_165333 : Nat := 4983230072969 + 3 ^ 40 * 165333 * 2
def baseEnd_165333 : Nat := 75462486266583882290803

theorem tailTrace_165333 : CollatzResearch.WordTrace tailWord_165333 prefixEnd_165333 75462486266583882290803 := by
  unfold tailWord_165333
  simp only [CollatzResearch.WordTrace]
  refine ⟨6030189910034252473476653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4020126606689501648984435 6030189910034252473476653)
  ·
    refine ⟨2261321216262844677553745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6030189910034252473476653 2261321216262844677553745)
    ·
      refine ⟨1695990912197133508165309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2261321216262844677553745 1695990912197133508165309)
      ·
        refine ⟨635996592073925065561991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1695990912197133508165309 635996592073925065561991)
        ·
          refine ⟨953994888110887598342987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 635996592073925065561991 953994888110887598342987)
          ·
            refine ⟨1430992332166331397514481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 953994888110887598342987 1430992332166331397514481)
            ·
              refine ⟨1073244249124748548135861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1430992332166331397514481 1073244249124748548135861)
              ·
                refine ⟨100616648355445176387737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1073244249124748548135861 100616648355445176387737)
                ·
                  refine ⟨75462486266583882290803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 100616648355445176387737 75462486266583882290803)
                  ·
                    rfl

theorem cell20_165333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 2, 5, 2].length) (baseStart_165333 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_165333 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_165333 prefixEnd_165333 := by exact prefixLift 165333
  have htrace : WordTrace (prefixWord ++ tailWord_165333) baseStart_165333 baseEnd_165333 := by
    simpa [prefixWord, tailWord_165333, baseEnd_165333] using wordTrace_append hprefix tailTrace_165333
  have hstable : (prefixWord ++ tailWord_165333).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_165333).length < 2 ^ (prefixWord ++ tailWord_165333).sum := by decide
  have hdescent : baseEnd_165333 < baseStart_165333 := by decide
  rcases family_descends (prefixWord ++ tailWord_165333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_165347 : List Nat := [1, 1, 1, 6, 2, 1, 1, 4, 3]
def baseStart_165347 : Nat := 118140960795 + 165347 * 2 ^ 59
def prefixEnd_165347 : Nat := 4983230072969 + 3 ^ 40 * 165347 * 2
def baseEnd_165347 : Nat := 75468876248062055824079

theorem tailTrace_165347 : CollatzResearch.WordTrace tailWord_165347 prefixEnd_165347 75468876248062055824079 := by
  unfold tailWord_165347
  simp only [CollatzResearch.WordTrace]
  refine ⟨6030700531983532864486295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4020467021322355242990863 6030700531983532864486295)
  ·
    refine ⟨9046050797975299296729443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6030700531983532864486295 9046050797975299296729443)
    ·
      refine ⟨13569076196962948945094165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9046050797975299296729443 13569076196962948945094165)
      ·
        refine ⟨636050446732638231801289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 13569076196962948945094165 636050446732638231801289)
        ·
          refine ⟨477037835049478673850967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 636050446732638231801289 477037835049478673850967)
          ·
            refine ⟨715556752574218010776451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 477037835049478673850967 715556752574218010776451)
            ·
              refine ⟨1073335128861327016164677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 715556752574218010776451 1073335128861327016164677)
              ·
                refine ⟨201250336661498815530877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1073335128861327016164677 201250336661498815530877)
                ·
                  refine ⟨75468876248062055824079, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 201250336661498815530877 75468876248062055824079)
                  ·
                    rfl

theorem cell20_165347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 1, 4, 3].length) (baseStart_165347 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_165347 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_165347 prefixEnd_165347 := by exact prefixLift 165347
  have htrace : WordTrace (prefixWord ++ tailWord_165347) baseStart_165347 baseEnd_165347 := by
    simpa [prefixWord, tailWord_165347, baseEnd_165347] using wordTrace_append hprefix tailTrace_165347
  have hstable : (prefixWord ++ tailWord_165347).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_165347).length < 2 ^ (prefixWord ++ tailWord_165347).sum := by decide
  have hdescent : baseEnd_165347 < baseStart_165347 := by decide
  rcases family_descends (prefixWord ++ tailWord_165347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_165357 : List Nat := [1, 5, 1, 3, 2, 2, 1, 5]
def baseStart_165357 : Nat := 118140960795 + 165357 * 2 ^ 59
def prefixEnd_165357 : Nat := 4983230072969 + 3 ^ 40 * 165357 * 2
def baseEnd_165357 : Nat := 25157813506848821830235

theorem tailTrace_165357 : CollatzResearch.WordTrace tailWord_165357 prefixEnd_165357 25157813506848821830235 := by
  unfold tailWord_165357
  simp only [CollatzResearch.WordTrace]
  refine ⟨6031065261947304572350325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4020710174631536381566883 6031065261947304572350325)
  ·
    refine ⟨565412368307559803657843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 6031065261947304572350325 565412368307559803657843)
    ·
      refine ⟨848118552461339705486765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 565412368307559803657843 848118552461339705486765)
      ·
        refine ⟨318044457173002389557537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 848118552461339705486765 318044457173002389557537)
        ·
          refine ⟨238533342879751792168153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 318044457173002389557537 238533342879751792168153)
          ·
            refine ⟨178900007159813844126115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 238533342879751792168153 178900007159813844126115)
            ·
              refine ⟨268350010739720766189173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 178900007159813844126115 268350010739720766189173)
              ·
                refine ⟨25157813506848821830235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 268350010739720766189173 25157813506848821830235)
                ·
                  rfl

theorem cell20_165357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 2, 1, 5].length) (baseStart_165357 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_165357 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_165357 prefixEnd_165357 := by exact prefixLift 165357
  have htrace : WordTrace (prefixWord ++ tailWord_165357) baseStart_165357 baseEnd_165357 := by
    simpa [prefixWord, tailWord_165357, baseEnd_165357] using wordTrace_append hprefix tailTrace_165357
  have hstable : (prefixWord ++ tailWord_165357).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_165357).length < 2 ^ (prefixWord ++ tailWord_165357).sum := by decide
  have hdescent : baseEnd_165357 < baseStart_165357 := by decide
  rcases family_descends (prefixWord ++ tailWord_165357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_165361 : List Nat := [1, 2, 2, 2, 3, 2, 3, 5]
def baseStart_165361 : Nat := 118140960795 + 165361 * 2 ^ 59
def prefixEnd_165361 : Nat := 4983230072969 + 3 ^ 40 * 165361 * 2
def baseEnd_165361 : Nat := 25158422076513409785785

theorem tailTrace_165361 : CollatzResearch.WordTrace tailWord_165361 prefixEnd_165361 25158422076513409785785 := by
  unfold tailWord_165361
  simp only [CollatzResearch.WordTrace]
  refine ⟨6031211153932813255495937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4020807435955208836997291 6031211153932813255495937)
  ·
    refine ⟨4523408365449609941621953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6031211153932813255495937 4523408365449609941621953)
    ·
      refine ⟨3392556274087207456216465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4523408365449609941621953 3392556274087207456216465)
      ·
        refine ⟨2544417205565405592162349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3392556274087207456216465 2544417205565405592162349)
        ·
          refine ⟨954156452087027097060881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2544417205565405592162349 954156452087027097060881)
          ·
            refine ⟨715617339065270322795661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 954156452087027097060881 715617339065270322795661)
            ·
              refine ⟨268356502149476371048373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 715617339065270322795661 268356502149476371048373)
              ·
                refine ⟨25158422076513409785785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 268356502149476371048373 25158422076513409785785)
                ·
                  rfl

theorem cell20_165361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 3, 5].length) (baseStart_165361 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_165361 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_165361 prefixEnd_165361 := by exact prefixLift 165361
  have htrace : WordTrace (prefixWord ++ tailWord_165361) baseStart_165361 baseEnd_165361 := by
    simpa [prefixWord, tailWord_165361, baseEnd_165361] using wordTrace_append hprefix tailTrace_165361
  have hstable : (prefixWord ++ tailWord_165361).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_165361).length < 2 ^ (prefixWord ++ tailWord_165361).sum := by decide
  have hdescent : baseEnd_165361 < baseStart_165361 := by decide
  rcases family_descends (prefixWord ++ tailWord_165361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_165374 : List Nat := [4, 2, 2, 3, 1, 1, 3, 4]
def baseStart_165374 : Nat := 118140960795 + 165374 * 2 ^ 59
def prefixEnd_165374 : Nat := 4983230072969 + 3 ^ 40 * 165374 * 2
def baseEnd_165374 : Nat := 25160399927923320641323

theorem tailTrace_165374 : CollatzResearch.WordTrace tailWord_165374 prefixEnd_165374 25160399927923320641323 := by
  unfold tailWord_165374
  simp only [CollatzResearch.WordTrace]
  refine ⟨753960662860714559464897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4021123535257144317146117 753960662860714559464897)
  ·
    refine ⟨565470497145535919598673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 753960662860714559464897 565470497145535919598673)
    ·
      refine ⟨424102872859151939699005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 565470497145535919598673 424102872859151939699005)
      ·
        refine ⟨159038577322181977387127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 424102872859151939699005 159038577322181977387127)
        ·
          refine ⟨238557865983272966080691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 159038577322181977387127 238557865983272966080691)
          ·
            refine ⟨357836798974909449121037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 238557865983272966080691 357836798974909449121037)
            ·
              refine ⟨134188799615591043420389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 357836798974909449121037 134188799615591043420389)
              ·
                refine ⟨25160399927923320641323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 134188799615591043420389 25160399927923320641323)
                ·
                  rfl

theorem cell20_165374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 1, 3, 4].length) (baseStart_165374 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_165374 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_165374 prefixEnd_165374 := by exact prefixLift 165374
  have htrace : WordTrace (prefixWord ++ tailWord_165374) baseStart_165374 baseEnd_165374 := by
    simpa [prefixWord, tailWord_165374, baseEnd_165374] using wordTrace_append hprefix tailTrace_165374
  have hstable : (prefixWord ++ tailWord_165374).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_165374).length < 2 ^ (prefixWord ++ tailWord_165374).sum := by decide
  have hdescent : baseEnd_165374 < baseStart_165374 := by decide
  rcases family_descends (prefixWord ++ tailWord_165374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_165388 : List Nat := [2, 2, 1, 2, 5, 1, 2, 3, 2]
def baseStart_165388 : Nat := 118140960795 + 165388 * 2 ^ 59
def prefixEnd_165388 : Nat := 4983230072969 + 3 ^ 40 * 165388 * 2
def baseEnd_165388 : Nat := 75487589765248135457245

theorem tailTrace_165388 : CollatzResearch.WordTrace tailWord_165388 prefixEnd_165388 75487589765248135457245 := by
  unfold tailWord_165388
  simp only [CollatzResearch.WordTrace]
  refine ⟨3016097962417498433364409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4021463949889997911152545 3016097962417498433364409)
  ·
    refine ⟨2262073471813123825023307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3016097962417498433364409 2262073471813123825023307)
    ·
      refine ⟨3393110207719685737534961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2262073471813123825023307 3393110207719685737534961)
      ·
        refine ⟨2544832655789764303151221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3393110207719685737534961 2544832655789764303151221)
        ·
          refine ⟨238578061480290403420427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 2544832655789764303151221 238578061480290403420427)
          ·
            refine ⟨357867092220435605130641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 238578061480290403420427 357867092220435605130641)
            ·
              refine ⟨268400319165326703847981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 357867092220435605130641 268400319165326703847981)
              ·
                refine ⟨100650119686997513942993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 268400319165326703847981 100650119686997513942993)
                ·
                  refine ⟨75487589765248135457245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 100650119686997513942993 75487589765248135457245)
                  ·
                    rfl

theorem cell20_165388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 1, 2, 3, 2].length) (baseStart_165388 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_165388 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_165388 prefixEnd_165388 := by exact prefixLift 165388
  have htrace : WordTrace (prefixWord ++ tailWord_165388) baseStart_165388 baseEnd_165388 := by
    simpa [prefixWord, tailWord_165388, baseEnd_165388] using wordTrace_append hprefix tailTrace_165388
  have hstable : (prefixWord ++ tailWord_165388).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_165388).length < 2 ^ (prefixWord ++ tailWord_165388).sum := by decide
  have hdescent : baseEnd_165388 < baseStart_165388 := by decide
  rcases family_descends (prefixWord ++ tailWord_165388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_165409 : List Nat := [1, 2, 3, 2, 2, 2, 2, 4, 2]
def baseStart_165409 : Nat := 118140960795 + 165409 * 2 ^ 59
def prefixEnd_165409 : Nat := 4983230072969 + 3 ^ 40 * 165409 * 2
def baseEnd_165409 : Nat := 75497174737465395757159

theorem tailTrace_165409 : CollatzResearch.WordTrace tailWord_165409 prefixEnd_165409 75497174737465395757159 := by
  unfold tailWord_165409
  simp only [CollatzResearch.WordTrace]
  refine ⟨6032961857758917453243281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4021974571839278302162187 6032961857758917453243281)
  ·
    refine ⟨4524721393319188089932461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6032961857758917453243281 4524721393319188089932461)
    ·
      refine ⟨1696770522494695533724673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4524721393319188089932461 1696770522494695533724673)
      ·
        refine ⟨1272577891871021650293505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1696770522494695533724673 1272577891871021650293505)
        ·
          refine ⟨954433418903266237720129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1272577891871021650293505 954433418903266237720129)
          ·
            refine ⟨715825064177449678290097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 954433418903266237720129 715825064177449678290097)
            ·
              refine ⟨536868798133087258717573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 715825064177449678290097 536868798133087258717573)
              ·
                refine ⟨100662899649953861009545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 536868798133087258717573 100662899649953861009545)
                ·
                  refine ⟨75497174737465395757159, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 100662899649953861009545 75497174737465395757159)
                  ·
                    rfl

theorem cell20_165409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 2, 4, 2].length) (baseStart_165409 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_165409 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_165409 prefixEnd_165409 := by exact prefixLift 165409
  have htrace : WordTrace (prefixWord ++ tailWord_165409) baseStart_165409 baseEnd_165409 := by
    simpa [prefixWord, tailWord_165409, baseEnd_165409] using wordTrace_append hprefix tailTrace_165409
  have hstable : (prefixWord ++ tailWord_165409).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_165409).length < 2 ^ (prefixWord ++ tailWord_165409).sum := by decide
  have hdescent : baseEnd_165409 < baseStart_165409 := by decide
  rcases family_descends (prefixWord ++ tailWord_165409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_165475 : List Nat := [1, 1, 1, 5, 1, 4, 2, 5]
def baseStart_165475 : Nat := 118140960795 + 165475 * 2 ^ 59
def prefixEnd_165475 : Nat := 4983230072969 + 3 ^ 40 * 165475 * 2
def baseEnd_165475 : Nat := 25175766311954166518963

theorem tailTrace_165475 : CollatzResearch.WordTrace tailWord_165475 prefixEnd_165475 25175766311954166518963 := by
  unfold tailWord_165475
  simp only [CollatzResearch.WordTrace]
  refine ⟨6035369075519810725145879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4023579383679873816763919 6035369075519810725145879)
  ·
    refine ⟨9053053613279716087718819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6035369075519810725145879 9053053613279716087718819)
    ·
      refine ⟨13579580419919574131578229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9053053613279716087718819 13579580419919574131578229)
      ·
        refine ⟨1273085664367460074835459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 13579580419919574131578229 1273085664367460074835459)
        ·
          refine ⟨1909628496551190112253189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1273085664367460074835459 1909628496551190112253189)
          ·
            refine ⟨358055343103348146047473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1909628496551190112253189 358055343103348146047473)
            ·
              refine ⟨268541507327511109535605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 358055343103348146047473 268541507327511109535605)
              ·
                refine ⟨25175766311954166518963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 268541507327511109535605 25175766311954166518963)
                ·
                  rfl

theorem cell20_165475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 4, 2, 5].length) (baseStart_165475 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_165475 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_165475 prefixEnd_165475 := by exact prefixLift 165475
  have htrace : WordTrace (prefixWord ++ tailWord_165475) baseStart_165475 baseEnd_165475 := by
    simpa [prefixWord, tailWord_165475, baseEnd_165475] using wordTrace_append hprefix tailTrace_165475
  have hstable : (prefixWord ++ tailWord_165475).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_165475).length < 2 ^ (prefixWord ++ tailWord_165475).sum := by decide
  have hdescent : baseEnd_165475 < baseStart_165475 := by decide
  rcases family_descends (prefixWord ++ tailWord_165475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_165489 : List Nat := [1, 2, 2, 2, 1, 1, 1, 6, 4]
def baseStart_165489 : Nat := 118140960795 + 165489 * 2 ^ 59
def prefixEnd_165489 : Nat := 4983230072969 + 3 ^ 40 * 165489 * 2
def baseEnd_165489 : Nat := 75533688917340673090165

theorem tailTrace_165489 : CollatzResearch.WordTrace tailWord_165489 prefixEnd_165489 75533688917340673090165 := by
  unfold tailWord_165489
  simp only [CollatzResearch.WordTrace]
  refine ⟨6035879697469091116155521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4023919798312727410770347 6035879697469091116155521)
  ·
    refine ⟨4526909773101818337116641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6035879697469091116155521 4526909773101818337116641)
    ·
      refine ⟨3395182329826363752837481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4526909773101818337116641 3395182329826363752837481)
      ·
        refine ⟨2546386747369772814628111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3395182329826363752837481 2546386747369772814628111)
        ·
          refine ⟨3819580121054659221942167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2546386747369772814628111 3819580121054659221942167)
          ·
            refine ⟨5729370181581988832913251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3819580121054659221942167 5729370181581988832913251)
            ·
              refine ⟨8594055272372983249369877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5729370181581988832913251 8594055272372983249369877)
              ·
                refine ⟨402846340892483589814213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 8594055272372983249369877 402846340892483589814213)
                ·
                  refine ⟨75533688917340673090165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 402846340892483589814213 75533688917340673090165)
                  ·
                    rfl

theorem cell20_165489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 6, 4].length) (baseStart_165489 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_165489 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_165489 prefixEnd_165489 := by exact prefixLift 165489
  have htrace : WordTrace (prefixWord ++ tailWord_165489) baseStart_165489 baseEnd_165489 := by
    simpa [prefixWord, tailWord_165489, baseEnd_165489] using wordTrace_append hprefix tailTrace_165489
  have hstable : (prefixWord ++ tailWord_165489).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_165489).length < 2 ^ (prefixWord ++ tailWord_165489).sum := by decide
  have hdescent : baseEnd_165489 < baseStart_165489 := by decide
  rcases family_descends (prefixWord ++ tailWord_165489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_165537 : List Nat := [1, 2, 3, 3, 2, 1, 2, 3, 3]
def baseStart_165537 : Nat := 118140960795 + 165537 * 2 ^ 59
def prefixEnd_165537 : Nat := 4983230072969 + 3 ^ 40 * 165537 * 2
def baseEnd_165537 : Nat := 75555597425265839489969

theorem tailTrace_165537 : CollatzResearch.WordTrace tailWord_165537 prefixEnd_165537 75555597425265839489969 := by
  unfold tailWord_165537
  simp only [CollatzResearch.WordTrace]
  refine ⟨6037630401295195313902865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4025086934196796875935243 6037630401295195313902865)
  ·
    refine ⟨4528222800971396485427149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6037630401295195313902865 4528222800971396485427149)
    ·
      refine ⟨1698083550364273682035181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4528222800971396485427149 1698083550364273682035181)
      ·
        refine ⟨636781331386602630763193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1698083550364273682035181 636781331386602630763193)
        ·
          refine ⟨477585998539951973072395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 636781331386602630763193 477585998539951973072395)
          ·
            refine ⟨716378997809927959608593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 477585998539951973072395 716378997809927959608593)
            ·
              refine ⟨537284248357445969706445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 716378997809927959608593 537284248357445969706445)
              ·
                refine ⟨201481593134042238639917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 537284248357445969706445 201481593134042238639917)
                ·
                  refine ⟨75555597425265839489969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 201481593134042238639917 75555597425265839489969)
                  ·
                    rfl

theorem cell20_165537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 2, 3, 3].length) (baseStart_165537 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_165537 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_165537 prefixEnd_165537 := by exact prefixLift 165537
  have htrace : WordTrace (prefixWord ++ tailWord_165537) baseStart_165537 baseEnd_165537 := by
    simpa [prefixWord, tailWord_165537, baseEnd_165537] using wordTrace_append hprefix tailTrace_165537
  have hstable : (prefixWord ++ tailWord_165537).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_165537).length < 2 ^ (prefixWord ++ tailWord_165537).sum := by decide
  have hdescent : baseEnd_165537 < baseStart_165537 := by decide
  rcases family_descends (prefixWord ++ tailWord_165537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_165551 : List Nat := [1, 1, 2, 1, 2, 4, 5, 4]
def baseStart_165551 : Nat := 118140960795 + 165551 * 2 ^ 59
def prefixEnd_165551 : Nat := 4983230072969 + 3 ^ 40 * 165551 * 2
def baseEnd_165551 : Nat := 25187329135581337674415

theorem tailTrace_165551 : CollatzResearch.WordTrace tailWord_165551 prefixEnd_165551 25187329135581337674415 := by
  unfold tailWord_165551
  simp only [CollatzResearch.WordTrace]
  refine ⟨6038141023244475704912507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4025427348829650469941671 6038141023244475704912507)
  ·
    refine ⟨9057211534866713557368761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6038141023244475704912507 9057211534866713557368761)
    ·
      refine ⟨6792908651150035168026571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9057211534866713557368761 6792908651150035168026571)
      ·
        refine ⟨10189362976725052752039857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6792908651150035168026571 10189362976725052752039857)
        ·
          refine ⟨7642022232543789564029893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10189362976725052752039857 7642022232543789564029893)
          ·
            refine ⟨1432879168601960543255605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7642022232543789564029893 1432879168601960543255605)
            ·
              refine ⟨134332422056433800930213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1432879168601960543255605 134332422056433800930213)
              ·
                refine ⟨25187329135581337674415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 134332422056433800930213 25187329135581337674415)
                ·
                  rfl

theorem cell20_165551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 5, 4].length) (baseStart_165551 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_165551 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_165551 prefixEnd_165551 := by exact prefixLift 165551
  have htrace : WordTrace (prefixWord ++ tailWord_165551) baseStart_165551 baseEnd_165551 := by
    simpa [prefixWord, tailWord_165551, baseEnd_165551] using wordTrace_append hprefix tailTrace_165551
  have hstable : (prefixWord ++ tailWord_165551).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_165551).length < 2 ^ (prefixWord ++ tailWord_165551).sum := by decide
  have hdescent : baseEnd_165551 < baseStart_165551 := by decide
  rcases family_descends (prefixWord ++ tailWord_165551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_165565 : List Nat := [1, 4, 1, 2, 1, 2, 1, 2, 6]
def baseStart_165565 : Nat := 118140960795 + 165565 * 2 ^ 59
def prefixEnd_165565 : Nat := 4983230072969 + 3 ^ 40 * 165565 * 2
def baseEnd_165565 : Nat := 75568377388222186556521

theorem tailTrace_165565 : CollatzResearch.WordTrace tailWord_165565 prefixEnd_165565 75568377388222186556521 := by
  unfold tailWord_165565
  simp only [CollatzResearch.WordTrace]
  refine ⟨6038651645193756095922149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4025767763462504063948099 6038651645193756095922149)
  ·
    refine ⟨1132247183473829267985403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6038651645193756095922149 1132247183473829267985403)
    ·
      refine ⟨1698370775210743901978105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1132247183473829267985403 1698370775210743901978105)
      ·
        refine ⟨1273778081408057926483579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1698370775210743901978105 1273778081408057926483579)
        ·
          refine ⟨1910667122112086889725369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1273778081408057926483579 1910667122112086889725369)
          ·
            refine ⟨1433000341584065167294027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1910667122112086889725369 1433000341584065167294027)
            ·
              refine ⟨2149500512376097750941041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1433000341584065167294027 2149500512376097750941041)
              ·
                refine ⟨1612125384282073313205781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2149500512376097750941041 1612125384282073313205781)
                ·
                  refine ⟨75568377388222186556521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1612125384282073313205781 75568377388222186556521)
                  ·
                    rfl

theorem cell20_165565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 1, 2, 6].length) (baseStart_165565 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_165565 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_165565 prefixEnd_165565 := by exact prefixLift 165565
  have htrace : WordTrace (prefixWord ++ tailWord_165565) baseStart_165565 baseEnd_165565 := by
    simpa [prefixWord, tailWord_165565, baseEnd_165565] using wordTrace_append hprefix tailTrace_165565
  have hstable : (prefixWord ++ tailWord_165565).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_165565).length < 2 ^ (prefixWord ++ tailWord_165565).sum := by decide
  have hdescent : baseEnd_165565 < baseStart_165565 := by decide
  rcases family_descends (prefixWord ++ tailWord_165565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_165582 : List Nat := [4, 1, 1, 1, 3, 1, 4, 1, 4]
def baseStart_165582 : Nat := 118140960795 + 165582 * 2 ^ 59
def prefixEnd_165582 : Nat := 4983230072969 + 3 ^ 40 * 165582 * 2
def baseEnd_165582 : Nat := 75576136651445682989785

theorem tailTrace_165582 : CollatzResearch.WordTrace tailWord_165582 prefixEnd_165582 75576136651445682989785 := by
  unfold tailWord_165582
  simp only [CollatzResearch.WordTrace]
  refine ⟨754908960766520999911375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4026181124088111999527333 754908960766520999911375)
  ·
    refine ⟨1132363441149781499867063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 754908960766520999911375 1132363441149781499867063)
    ·
      refine ⟨1698545161724672249800595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1132363441149781499867063 1698545161724672249800595)
      ·
        refine ⟨2547817742587008374700893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1698545161724672249800595 2547817742587008374700893)
        ·
          refine ⟨955431653470128140512835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2547817742587008374700893 955431653470128140512835)
          ·
            refine ⟨1433147480205192210769253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 955431653470128140512835 1433147480205192210769253)
            ·
              refine ⟨268715152538473539519235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1433147480205192210769253 268715152538473539519235)
              ·
                refine ⟨403072728807710309278853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 268715152538473539519235 403072728807710309278853)
                ·
                  refine ⟨75576136651445682989785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 403072728807710309278853 75576136651445682989785)
                  ·
                    rfl

theorem cell20_165582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 4, 1, 4].length) (baseStart_165582 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_165582 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_165582 prefixEnd_165582 := by exact prefixLift 165582
  have htrace : WordTrace (prefixWord ++ tailWord_165582) baseStart_165582 baseEnd_165582 := by
    simpa [prefixWord, tailWord_165582, baseEnd_165582] using wordTrace_append hprefix tailTrace_165582
  have hstable : (prefixWord ++ tailWord_165582).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_165582).length < 2 ^ (prefixWord ++ tailWord_165582).sum := by decide
  have hdescent : baseEnd_165582 < baseStart_165582 := by decide
  rcases family_descends (prefixWord ++ tailWord_165582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_165717 : List Nat := [1, 3, 2, 2, 2, 2, 1, 1, 6]
def baseStart_165717 : Nat := 118140960795 + 165717 * 2 ^ 59
def prefixEnd_165717 : Nat := 4983230072969 + 3 ^ 40 * 165717 * 2
def baseEnd_165717 : Nat := 75637754329985213489233

theorem tailTrace_165717 : CollatzResearch.WordTrace tailWord_165717 prefixEnd_165717 75637754329985213489233 := by
  unfold tailWord_165717
  simp only [CollatzResearch.WordTrace]
  refine ⟨6044195540643086055455405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4029463693762057370303603 6044195540643086055455405)
  ·
    refine ⟨2266573327741157270795777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6044195540643086055455405 2266573327741157270795777)
    ·
      refine ⟨1699929995805867953096833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2266573327741157270795777 1699929995805867953096833)
      ·
        refine ⟨1274947496854400964822625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1699929995805867953096833 1274947496854400964822625)
        ·
          refine ⟨956210622640800723616969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1274947496854400964822625 956210622640800723616969)
          ·
            refine ⟨717157966980600542712727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 956210622640800723616969 717157966980600542712727)
            ·
              refine ⟨1075736950470900814069091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 717157966980600542712727 1075736950470900814069091)
              ·
                refine ⟨1613605425706351221103637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1075736950470900814069091 1613605425706351221103637)
                ·
                  refine ⟨75637754329985213489233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1613605425706351221103637 75637754329985213489233)
                  ·
                    rfl

theorem cell20_165717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 1, 1, 6].length) (baseStart_165717 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_165717 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_165717 prefixEnd_165717 := by exact prefixLift 165717
  have htrace : WordTrace (prefixWord ++ tailWord_165717) baseStart_165717 baseEnd_165717 := by
    simpa [prefixWord, tailWord_165717, baseEnd_165717] using wordTrace_append hprefix tailTrace_165717
  have hstable : (prefixWord ++ tailWord_165717).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_165717).length < 2 ^ (prefixWord ++ tailWord_165717).sum := by decide
  have hdescent : baseEnd_165717 < baseStart_165717 := by decide
  rcases family_descends (prefixWord ++ tailWord_165717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_165730 : List Nat := [3, 3, 2, 1, 2, 2, 2, 3, 2]
def baseStart_165730 : Nat := 118140960795 + 165730 * 2 ^ 59
def prefixEnd_165730 : Nat := 4983230072969 + 3 ^ 40 * 165730 * 2
def baseEnd_165730 : Nat := 75643687884214946055847

theorem tailTrace_165730 : CollatzResearch.WordTrace tailWord_165730 prefixEnd_165730 75643687884214946055847 := by
  unfold tailWord_165730
  simp only [CollatzResearch.WordTrace]
  refine ⟨1511167422398997318919661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4029779793063992850452429 1511167422398997318919661)
  ·
    refine ⟨566687783399623994594873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1511167422398997318919661 566687783399623994594873)
    ·
      refine ⟨425015837549717995946155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 566687783399623994594873 425015837549717995946155)
      ·
        refine ⟨637523756324576993919233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 425015837549717995946155 637523756324576993919233)
        ·
          refine ⟨478142817243432745439425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 637523756324576993919233 478142817243432745439425)
          ·
            refine ⟨358607112932574559079569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 478142817243432745439425 358607112932574559079569)
            ·
              refine ⟨268955334699430919309677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 358607112932574559079569 268955334699430919309677)
              ·
                refine ⟨100858250512286594741129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 268955334699430919309677 100858250512286594741129)
                ·
                  refine ⟨75643687884214946055847, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 100858250512286594741129 75643687884214946055847)
                  ·
                    rfl

theorem cell20_165730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 2, 2, 3, 2].length) (baseStart_165730 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_165730 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_165730 prefixEnd_165730 := by exact prefixLift 165730
  have htrace : WordTrace (prefixWord ++ tailWord_165730) baseStart_165730 baseEnd_165730 := by
    simpa [prefixWord, tailWord_165730, baseEnd_165730] using wordTrace_append hprefix tailTrace_165730
  have hstable : (prefixWord ++ tailWord_165730).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_165730).length < 2 ^ (prefixWord ++ tailWord_165730).sum := by decide
  have hdescent : baseEnd_165730 < baseStart_165730 := by decide
  rcases family_descends (prefixWord ++ tailWord_165730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_165761 : List Nat := [1, 2, 4, 4, 1, 1, 3, 1, 3]
def baseStart_165761 : Nat := 118140960795 + 165761 * 2 ^ 59
def prefixEnd_165761 : Nat := 4983230072969 + 3 ^ 40 * 165761 * 2
def baseEnd_165761 : Nat := 75657837128916616022387

theorem tailTrace_165761 : CollatzResearch.WordTrace tailWord_165761 prefixEnd_165761 75657837128916616022387 := by
  unfold tailWord_165761
  simp only [CollatzResearch.WordTrace]
  refine ⟨6045800352483681570057137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4030533568322454380038091 6045800352483681570057137)
  ·
    refine ⟨4534350264362761177542853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6045800352483681570057137 4534350264362761177542853)
    ·
      refine ⟨850190674568017720789285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4534350264362761177542853 850190674568017720789285)
      ·
        refine ⟨159410751481503322647991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 850190674568017720789285 159410751481503322647991)
        ·
          refine ⟨239116127222254983971987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 159410751481503322647991 239116127222254983971987)
          ·
            refine ⟨358674190833382475957981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 239116127222254983971987 358674190833382475957981)
            ·
              refine ⟨134502821562518428484243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 358674190833382475957981 134502821562518428484243)
              ·
                refine ⟨201754232343777642726365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 134502821562518428484243 201754232343777642726365)
                ·
                  refine ⟨75657837128916616022387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 201754232343777642726365 75657837128916616022387)
                  ·
                    rfl

theorem cell20_165761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 1, 3, 1, 3].length) (baseStart_165761 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_165761 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_165761 prefixEnd_165761 := by exact prefixLift 165761
  have htrace : WordTrace (prefixWord ++ tailWord_165761) baseStart_165761 baseEnd_165761 := by
    simpa [prefixWord, tailWord_165761, baseEnd_165761] using wordTrace_append hprefix tailTrace_165761
  have hstable : (prefixWord ++ tailWord_165761).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_165761).length < 2 ^ (prefixWord ++ tailWord_165761).sum := by decide
  have hdescent : baseEnd_165761 < baseStart_165761 := by decide
  rcases family_descends (prefixWord ++ tailWord_165761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_165765 : List Nat := [1, 3, 1, 1, 3, 2, 5, 1, 3]
def baseStart_165765 : Nat := 118140960795 + 165765 * 2 ^ 59
def prefixEnd_165765 : Nat := 4983230072969 + 3 ^ 40 * 165765 * 2
def baseEnd_165765 : Nat := 75659662837910379889037

theorem tailTrace_165765 : CollatzResearch.WordTrace tailWord_165765 prefixEnd_165765 75659662837910379889037 := by
  unfold tailWord_165765
  simp only [CollatzResearch.WordTrace]
  refine ⟨6045946244469190253202749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4030630829646126835468499 6045946244469190253202749)
  ·
    refine ⟨2267229841675946344951031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6045946244469190253202749 2267229841675946344951031)
    ·
      refine ⟨3400844762513919517426547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2267229841675946344951031 3400844762513919517426547)
      ·
        refine ⟨5101267143770879276139821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3400844762513919517426547 5101267143770879276139821)
        ·
          refine ⟨1912975178914079728552433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5101267143770879276139821 1912975178914079728552433)
          ·
            refine ⟨1434731384185559796414325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1912975178914079728552433 1434731384185559796414325)
            ·
              refine ⟨134506067267396230913843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1434731384185559796414325 134506067267396230913843)
              ·
                refine ⟨201759100901094346370765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 134506067267396230913843 201759100901094346370765)
                ·
                  refine ⟨75659662837910379889037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 201759100901094346370765 75659662837910379889037)
                  ·
                    rfl

theorem cell20_165765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 5, 1, 3].length) (baseStart_165765 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_165765 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_165765 prefixEnd_165765 := by exact prefixLift 165765
  have htrace : WordTrace (prefixWord ++ tailWord_165765) baseStart_165765 baseEnd_165765 := by
    simpa [prefixWord, tailWord_165765, baseEnd_165765] using wordTrace_append hprefix tailTrace_165765
  have hstable : (prefixWord ++ tailWord_165765).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_165765).length < 2 ^ (prefixWord ++ tailWord_165765).sum := by decide
  have hdescent : baseEnd_165765 < baseStart_165765 := by decide
  rcases family_descends (prefixWord ++ tailWord_165765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_165786 : List Nat := [3, 1, 1, 4, 2, 1, 1, 2, 5]
def baseStart_165786 : Nat := 118140960795 + 165786 * 2 ^ 59
def prefixEnd_165786 : Nat := 4983230072969 + 3 ^ 40 * 165786 * 2
def baseEnd_165786 : Nat := 75669247810127640188951

theorem tailTrace_165786 : CollatzResearch.WordTrace tailWord_165786 prefixEnd_165786 75669247810127640188951 := by
  unfold tailWord_165786
  simp only [CollatzResearch.WordTrace]
  refine ⟨1511678044348277709929303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4031141451595407226478141 1511678044348277709929303)
  ·
    refine ⟨2267517066522416564893955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1511678044348277709929303 2267517066522416564893955)
    ·
      refine ⟨3401275599783624847340933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2267517066522416564893955 3401275599783624847340933)
      ·
        refine ⟨637739174959429658876425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3401275599783624847340933 637739174959429658876425)
        ·
          refine ⟨478304381219572244157319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 637739174959429658876425 478304381219572244157319)
          ·
            refine ⟨717456571829358366235979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 478304381219572244157319 717456571829358366235979)
            ·
              refine ⟨1076184857744037549353969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 717456571829358366235979 1076184857744037549353969)
              ·
                refine ⟨807138643308028162015477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1076184857744037549353969 807138643308028162015477)
                ·
                  refine ⟨75669247810127640188951, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 807138643308028162015477 75669247810127640188951)
                  ·
                    rfl

theorem cell20_165786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 1, 2, 5].length) (baseStart_165786 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_165786 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_165786 prefixEnd_165786 := by exact prefixLift 165786
  have htrace : WordTrace (prefixWord ++ tailWord_165786) baseStart_165786 baseEnd_165786 := by
    simpa [prefixWord, tailWord_165786, baseEnd_165786] using wordTrace_append hprefix tailTrace_165786
  have hstable : (prefixWord ++ tailWord_165786).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_165786).length < 2 ^ (prefixWord ++ tailWord_165786).sum := by decide
  have hdescent : baseEnd_165786 < baseStart_165786 := by decide
  rcases family_descends (prefixWord ++ tailWord_165786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_165789 : List Nat := [1, 4, 2, 1, 2, 2, 3, 3, 2]
def baseStart_165789 : Nat := 118140960795 + 165789 * 2 ^ 59
def prefixEnd_165789 : Nat := 4983230072969 + 3 ^ 40 * 165789 * 2
def baseEnd_165789 : Nat := 75670617091872963088939

theorem tailTrace_165789 : CollatzResearch.WordTrace tailWord_165789 prefixEnd_165789 75670617091872963088939 := by
  unfold tailWord_165789
  simp only [CollatzResearch.WordTrace]
  refine ⟨6046821596382242352076421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4031214397588161568050947 6046821596382242352076421)
  ·
    refine ⟨1133779049321670441014329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6046821596382242352076421 1133779049321670441014329)
    ·
      refine ⟨850334286991252830760747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1133779049321670441014329 850334286991252830760747)
      ·
        refine ⟨1275501430486879246141121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 850334286991252830760747 1275501430486879246141121)
        ·
          refine ⟨956626072865159434605841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1275501430486879246141121 956626072865159434605841)
          ·
            refine ⟨717469554648869575954381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 956626072865159434605841 717469554648869575954381)
            ·
              refine ⟨269051082993326090982893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 717469554648869575954381 269051082993326090982893)
              ·
                refine ⟨100894156122497284118585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 269051082993326090982893 100894156122497284118585)
                ·
                  refine ⟨75670617091872963088939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 100894156122497284118585 75670617091872963088939)
                  ·
                    rfl

theorem cell20_165789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 3, 3, 2].length) (baseStart_165789 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_165789 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_165789 prefixEnd_165789 := by exact prefixLift 165789
  have htrace : WordTrace (prefixWord ++ tailWord_165789) baseStart_165789 baseEnd_165789 := by
    simpa [prefixWord, tailWord_165789, baseEnd_165789] using wordTrace_append hprefix tailTrace_165789
  have hstable : (prefixWord ++ tailWord_165789).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_165789).length < 2 ^ (prefixWord ++ tailWord_165789).sum := by decide
  have hdescent : baseEnd_165789 < baseStart_165789 := by decide
  rcases family_descends (prefixWord ++ tailWord_165789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_165807 : List Nat := [1, 1, 2, 1, 2, 2, 3, 3, 5]
def baseStart_165807 : Nat := 118140960795 + 165807 * 2 ^ 59
def prefixEnd_165807 : Nat := 4983230072969 + 3 ^ 40 * 165807 * 2
def baseEnd_165807 : Nat := 75678832782344900488865

theorem tailTrace_165807 : CollatzResearch.WordTrace tailWord_165807 prefixEnd_165807 75678832782344900488865 := by
  unfold tailWord_165807
  simp only [CollatzResearch.WordTrace]
  refine ⟨6047478110317031426231675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4031652073544687617487783 6047478110317031426231675)
  ·
    refine ⟨9071217165475547139347513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6047478110317031426231675 9071217165475547139347513)
    ·
      refine ⟨6803412874106660354510635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9071217165475547139347513 6803412874106660354510635)
      ·
        refine ⟨10205119311159990531765953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6803412874106660354510635 10205119311159990531765953)
        ·
          refine ⟨7653839483369992898824465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10205119311159990531765953 7653839483369992898824465)
          ·
            refine ⟨5740379612527494674118349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7653839483369992898824465 5740379612527494674118349)
            ·
              refine ⟨2152642354697810502794381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5740379612527494674118349 2152642354697810502794381)
              ·
                refine ⟨807240883011678938547893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2152642354697810502794381 807240883011678938547893)
                ·
                  refine ⟨75678832782344900488865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 807240883011678938547893 75678832782344900488865)
                  ·
                    rfl

theorem cell20_165807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 3, 3, 5].length) (baseStart_165807 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_165807 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_165807 prefixEnd_165807 := by exact prefixLift 165807
  have htrace : WordTrace (prefixWord ++ tailWord_165807) baseStart_165807 baseEnd_165807 := by
    simpa [prefixWord, tailWord_165807, baseEnd_165807] using wordTrace_append hprefix tailTrace_165807
  have hstable : (prefixWord ++ tailWord_165807).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_165807).length < 2 ^ (prefixWord ++ tailWord_165807).sum := by decide
  have hdescent : baseEnd_165807 < baseStart_165807 := by decide
  rcases family_descends (prefixWord ++ tailWord_165807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_165810 : List Nat := [3, 2, 1, 1, 1, 1, 1, 8, 2]
def baseStart_165810 : Nat := 118140960795 + 165810 * 2 ^ 59
def prefixEnd_165810 : Nat := 4983230072969 + 3 ^ 40 * 165810 * 2
def baseEnd_165810 : Nat := 75680202064090223388853

theorem tailTrace_165810 : CollatzResearch.WordTrace tailWord_165810 prefixEnd_165810 75680202064090223388853 := by
  unfold tailWord_165810
  simp only [CollatzResearch.WordTrace]
  refine ⟨1511896882326540734647721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4031725019537441959060589 1511896882326540734647721)
  ·
    refine ⟨1133922661744905550985791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1511896882326540734647721 1133922661744905550985791)
    ·
      refine ⟨1700883992617358326478687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1133922661744905550985791 1700883992617358326478687)
      ·
        refine ⟨2551325988926037489718031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1700883992617358326478687 2551325988926037489718031)
        ·
          refine ⟨3826988983389056234577047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2551325988926037489718031 3826988983389056234577047)
          ·
            refine ⟨5740483475083584351865571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3826988983389056234577047 5740483475083584351865571)
            ·
              refine ⟨8610725212625376527798357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5740483475083584351865571 8610725212625376527798357)
              ·
                refine ⟨100906936085453631185137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8610725212625376527798357 100906936085453631185137)
                ·
                  refine ⟨75680202064090223388853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 100906936085453631185137 75680202064090223388853)
                  ·
                    rfl

theorem cell20_165810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 8, 2].length) (baseStart_165810 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_165810 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_165810 prefixEnd_165810 := by exact prefixLift 165810
  have htrace : WordTrace (prefixWord ++ tailWord_165810) baseStart_165810 baseEnd_165810 := by
    simpa [prefixWord, tailWord_165810, baseEnd_165810] using wordTrace_append hprefix tailTrace_165810
  have hstable : (prefixWord ++ tailWord_165810).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_165810).length < 2 ^ (prefixWord ++ tailWord_165810).sum := by decide
  have hdescent : baseEnd_165810 < baseStart_165810 := by decide
  rcases family_descends (prefixWord ++ tailWord_165810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_165820 : List Nat := [2, 2, 2, 5, 1, 1, 1, 3, 3]
def baseStart_165820 : Nat := 118140960795 + 165820 * 2 ^ 59
def prefixEnd_165820 : Nat := 4983230072969 + 3 ^ 40 * 165820 * 2
def baseEnd_165820 : Nat := 75684766336574633055479

theorem tailTrace_165820 : CollatzResearch.WordTrace tailWord_165820 prefixEnd_165820 75684766336574633055479 := by
  unfold tailWord_165820
  simp only [CollatzResearch.WordTrace]
  refine ⟨3023976129634967323227457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4031968172846623097636609 3023976129634967323227457)
  ·
    refine ⟨2267982097226225492420593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3023976129634967323227457 2267982097226225492420593)
    ·
      refine ⟨1700986572919669119315445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2267982097226225492420593 1700986572919669119315445)
      ·
        refine ⟨159467491211218979935823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 1700986572919669119315445 159467491211218979935823)
        ·
          refine ⟨239201236816828469903735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 159467491211218979935823 239201236816828469903735)
          ·
            refine ⟨358801855225242704855603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 239201236816828469903735 358801855225242704855603)
            ·
              refine ⟨538202782837864057283405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 358801855225242704855603 538202782837864057283405)
              ·
                refine ⟨201826043564199021481277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 538202782837864057283405 201826043564199021481277)
                ·
                  refine ⟨75684766336574633055479, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 201826043564199021481277 75684766336574633055479)
                  ·
                    rfl

theorem cell20_165820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 1, 1, 3, 3].length) (baseStart_165820 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_165820 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_165820 prefixEnd_165820 := by exact prefixLift 165820
  have htrace : WordTrace (prefixWord ++ tailWord_165820) baseStart_165820 baseEnd_165820 := by
    simpa [prefixWord, tailWord_165820, baseEnd_165820] using wordTrace_append hprefix tailTrace_165820
  have hstable : (prefixWord ++ tailWord_165820).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_165820).length < 2 ^ (prefixWord ++ tailWord_165820).sum := by decide
  have hdescent : baseEnd_165820 < baseStart_165820 := by decide
  rcases family_descends (prefixWord ++ tailWord_165820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_165824 : List Nat := [2, 1, 1, 2, 3, 2, 3, 3, 3]
def baseStart_165824 : Nat := 118140960795 + 165824 * 2 ^ 59
def prefixEnd_165824 : Nat := 4983230072969 + 3 ^ 40 * 165824 * 2
def baseEnd_165824 : Nat := 75686592045568396922129

theorem tailTrace_165824 : CollatzResearch.WordTrace tailWord_165824 prefixEnd_165824 75686592045568396922129 := by
  unfold tailWord_165824
  simp only [CollatzResearch.WordTrace]
  refine ⟨3024049075627721664800263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4032065434170295553067017 3024049075627721664800263)
  ·
    refine ⟨4536073613441582497200395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3024049075627721664800263 4536073613441582497200395)
    ·
      refine ⟨6804110420162373745800593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4536073613441582497200395 6804110420162373745800593)
      ·
        refine ⟨5103082815121780309350445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6804110420162373745800593 5103082815121780309350445)
        ·
          refine ⟨1913656055670667616006417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5103082815121780309350445 1913656055670667616006417)
          ·
            refine ⟨1435242041753000712004813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1913656055670667616006417 1435242041753000712004813)
            ·
              refine ⟨538215765657375267001805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1435242041753000712004813 538215765657375267001805)
              ·
                refine ⟨201830912121515725125677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 538215765657375267001805 201830912121515725125677)
                ·
                  refine ⟨75686592045568396922129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 201830912121515725125677 75686592045568396922129)
                  ·
                    rfl

theorem cell20_165824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 3, 3, 3].length) (baseStart_165824 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_165824 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_165824 prefixEnd_165824 := by exact prefixLift 165824
  have htrace : WordTrace (prefixWord ++ tailWord_165824) baseStart_165824 baseEnd_165824 := by
    simpa [prefixWord, tailWord_165824, baseEnd_165824] using wordTrace_append hprefix tailTrace_165824
  have hstable : (prefixWord ++ tailWord_165824).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_165824).length < 2 ^ (prefixWord ++ tailWord_165824).sum := by decide
  have hdescent : baseEnd_165824 < baseStart_165824 := by decide
  rcases family_descends (prefixWord ++ tailWord_165824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_165838 : List Nat := [4, 1, 1, 1, 2, 2, 1, 8]
def baseStart_165838 : Nat := 118140960795 + 165838 * 2 ^ 59
def prefixEnd_165838 : Nat := 4983230072969 + 3 ^ 40 * 165838 * 2
def baseEnd_165838 : Nat := 25230994009015523485135

theorem tailTrace_165838 : CollatzResearch.WordTrace tailWord_165838 prefixEnd_165838 25230994009015523485135 := by
  unfold tailWord_165838
  simp only [CollatzResearch.WordTrace]
  refine ⟨756076096650590465076271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4032405848803149147073445 756076096650590465076271)
  ·
    refine ⟨1134114144975885697614407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 756076096650590465076271 1134114144975885697614407)
    ·
      refine ⟨1701171217463828546421611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1134114144975885697614407 1701171217463828546421611)
      ·
        refine ⟨2551756826195742819632417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1701171217463828546421611 2551756826195742819632417)
        ·
          refine ⟨1913817619646807114724313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2551756826195742819632417 1913817619646807114724313)
          ·
            refine ⟨1435363214735105336043235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1913817619646807114724313 1435363214735105336043235)
            ·
              refine ⟨2153044822102658004064853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1435363214735105336043235 2153044822102658004064853)
              ·
                refine ⟨25230994009015523485135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2153044822102658004064853 25230994009015523485135)
                ·
                  rfl

theorem cell20_165838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 1, 8].length) (baseStart_165838 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_165838 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_165838 prefixEnd_165838 := by exact prefixLift 165838
  have htrace : WordTrace (prefixWord ++ tailWord_165838) baseStart_165838 baseEnd_165838 := by
    simpa [prefixWord, tailWord_165838, baseEnd_165838] using wordTrace_append hprefix tailTrace_165838
  have hstable : (prefixWord ++ tailWord_165838).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_165838).length < 2 ^ (prefixWord ++ tailWord_165838).sum := by decide
  have hdescent : baseEnd_165838 < baseStart_165838 := by decide
  rcases family_descends (prefixWord ++ tailWord_165838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_165848 : List Nat := [2, 1, 2, 2, 2, 2, 2, 5, 2]
def baseStart_165848 : Nat := 118140960795 + 165848 * 2 ^ 59
def prefixEnd_165848 : Nat := 4983230072969 + 3 ^ 40 * 165848 * 2
def baseEnd_165848 : Nat := 75697546299530980122031

theorem tailTrace_165848 : CollatzResearch.WordTrace tailWord_165848 prefixEnd_165848 75697546299530980122031 := by
  unfold tailWord_165848
  simp only [CollatzResearch.WordTrace]
  refine ⟨3024486751584247714237099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4032649002112330285649465 3024486751584247714237099)
  ·
    refine ⟨4536730127376371571355649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3024486751584247714237099 4536730127376371571355649)
    ·
      refine ⟨3402547595532278678516737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4536730127376371571355649 3402547595532278678516737)
      ·
        refine ⟨2551910696649209008887553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3402547595532278678516737 2551910696649209008887553)
        ·
          refine ⟨1913933022486906756665665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2551910696649209008887553 1913933022486906756665665)
          ·
            refine ⟨1435449766865180067499249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1913933022486906756665665 1435449766865180067499249)
            ·
              refine ⟨1076587325148885050624437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1435449766865180067499249 1076587325148885050624437)
              ·
                refine ⟨100930061732707973496041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1076587325148885050624437 100930061732707973496041)
                ·
                  refine ⟨75697546299530980122031, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 100930061732707973496041 75697546299530980122031)
                  ·
                    rfl

theorem cell20_165848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 2, 5, 2].length) (baseStart_165848 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_165848 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_165848 prefixEnd_165848 := by exact prefixLift 165848
  have htrace : WordTrace (prefixWord ++ tailWord_165848) baseStart_165848 baseEnd_165848 := by
    simpa [prefixWord, tailWord_165848, baseEnd_165848] using wordTrace_append hprefix tailTrace_165848
  have hstable : (prefixWord ++ tailWord_165848).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_165848).length < 2 ^ (prefixWord ++ tailWord_165848).sum := by decide
  have hdescent : baseEnd_165848 < baseStart_165848 := by decide
  rcases family_descends (prefixWord ++ tailWord_165848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_165886 : List Nat := [4, 2, 2, 2, 1, 1, 1, 1, 6]
def baseStart_165886 : Nat := 118140960795 + 165886 * 2 ^ 59
def prefixEnd_165886 : Nat := 4983230072969 + 3 ^ 40 * 165886 * 2
def baseEnd_165886 : Nat := 75714890534971736855209

theorem tailTrace_165886 : CollatzResearch.WordTrace tailWord_165886 prefixEnd_165886 75714890534971736855209 := by
  unfold tailWord_165886
  simp only [CollatzResearch.WordTrace]
  refine ⟨756294934628853489794689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4033572984687218612238341 756294934628853489794689)
  ·
    refine ⟨567221200971640117346017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 756294934628853489794689 567221200971640117346017)
    ·
      refine ⟨425415900728730088009513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 567221200971640117346017 425415900728730088009513)
      ·
        refine ⟨319061925546547566007135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 425415900728730088009513 319061925546547566007135)
        ·
          refine ⟨478592888319821349010703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 319061925546547566007135 478592888319821349010703)
          ·
            refine ⟨717889332479732023516055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 478592888319821349010703 717889332479732023516055)
            ·
              refine ⟨1076833998719598035274083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 717889332479732023516055 1076833998719598035274083)
              ·
                refine ⟨1615250998079397052911125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1076833998719598035274083 1615250998079397052911125)
                ·
                  refine ⟨75714890534971736855209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1615250998079397052911125 75714890534971736855209)
                  ·
                    rfl

theorem cell20_165886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 1, 1, 6].length) (baseStart_165886 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_165886 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_165886 prefixEnd_165886 := by exact prefixLift 165886
  have htrace : WordTrace (prefixWord ++ tailWord_165886) baseStart_165886 baseEnd_165886 := by
    simpa [prefixWord, tailWord_165886, baseEnd_165886] using wordTrace_append hprefix tailTrace_165886
  have hstable : (prefixWord ++ tailWord_165886).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_165886).length < 2 ^ (prefixWord ++ tailWord_165886).sum := by decide
  have hdescent : baseEnd_165886 < baseStart_165886 := by decide
  rcases family_descends (prefixWord ++ tailWord_165886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_165893 : List Nat := [1, 3, 1, 1, 2, 5, 3, 4]
def baseStart_165893 : Nat := 118140960795 + 165893 * 2 ^ 59
def prefixEnd_165893 : Nat := 4983230072969 + 3 ^ 40 * 165893 * 2
def baseEnd_165893 : Nat := 25239361841903607873949

theorem tailTrace_165893 : CollatzResearch.WordTrace tailWord_165893 prefixEnd_165893 25239361841903607873949 := by
  unfold tailWord_165893
  simp only [CollatzResearch.WordTrace]
  refine ⟨6050614788005468113862333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4033743192003645409241555 6050614788005468113862333)
  ·
    refine ⟨2268980545502050542698375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6050614788005468113862333 2268980545502050542698375)
    ·
      refine ⟨3403470818253075814047563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2268980545502050542698375 3403470818253075814047563)
      ·
        refine ⟨5105206227379613721071345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3403470818253075814047563 5105206227379613721071345)
        ·
          refine ⟨3828904670534710290803509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5105206227379613721071345 3828904670534710290803509)
          ·
            refine ⟨358959812862629089762829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 3828904670534710290803509 358959812862629089762829)
            ·
              refine ⟨134609929823485908661061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 358959812862629089762829 134609929823485908661061)
              ·
                refine ⟨25239361841903607873949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 134609929823485908661061 25239361841903607873949)
                ·
                  rfl

theorem cell20_165893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 5, 3, 4].length) (baseStart_165893 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_165893 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_165893 prefixEnd_165893 := by exact prefixLift 165893
  have htrace : WordTrace (prefixWord ++ tailWord_165893) baseStart_165893 baseEnd_165893 := by
    simpa [prefixWord, tailWord_165893, baseEnd_165893] using wordTrace_append hprefix tailTrace_165893
  have hstable : (prefixWord ++ tailWord_165893).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_165893).length < 2 ^ (prefixWord ++ tailWord_165893).sum := by decide
  have hdescent : baseEnd_165893 < baseStart_165893 := by decide
  rcases family_descends (prefixWord ++ tailWord_165893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_165914 : List Nat := [3, 1, 1, 3, 1, 4, 7]
def baseStart_165914 : Nat := 118140960795 + 165914 * 2 ^ 59
def prefixEnd_165914 : Nat := 4983230072969 + 3 ^ 40 * 165914 * 2
def baseEnd_165914 : Nat := 8414185610880898213529

theorem tailTrace_165914 : CollatzResearch.WordTrace tailWord_165914 prefixEnd_165914 8414185610880898213529 := by
  unfold tailWord_165914
  simp only [CollatzResearch.WordTrace]
  refine ⟨1512845180232347175094199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4034253813952925800251197 1512845180232347175094199)
  ·
    refine ⟨2269267770348520762641299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1512845180232347175094199 2269267770348520762641299)
    ·
      refine ⟨3403901655522781143961949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2269267770348520762641299 3403901655522781143961949)
      ·
        refine ⟨1276463120821042928985731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3403901655522781143961949 1276463120821042928985731)
        ·
          refine ⟨1914694681231564393478597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1276463120821042928985731 1914694681231564393478597)
          ·
            refine ⟨359005252730918323777237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1914694681231564393478597 359005252730918323777237)
            ·
              refine ⟨8414185610880898213529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 359005252730918323777237 8414185610880898213529)
              ·
                rfl

theorem cell20_165914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 4, 7].length) (baseStart_165914 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_165914 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_165914 prefixEnd_165914 := by exact prefixLift 165914
  have htrace : WordTrace (prefixWord ++ tailWord_165914) baseStart_165914 baseEnd_165914 := by
    simpa [prefixWord, tailWord_165914, baseEnd_165914] using wordTrace_append hprefix tailTrace_165914
  have hstable : (prefixWord ++ tailWord_165914).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_165914).length < 2 ^ (prefixWord ++ tailWord_165914).sum := by decide
  have hdescent : baseEnd_165914 < baseStart_165914 := by decide
  rcases family_descends (prefixWord ++ tailWord_165914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_165917 : List Nat := [1, 4, 2, 2, 2, 1, 3, 2, 3]
def baseStart_165917 : Nat := 118140960795 + 165917 * 2 ^ 59
def prefixEnd_165917 : Nat := 4983230072969 + 3 ^ 40 * 165917 * 2
def baseEnd_165917 : Nat := 75729039779673406821749

theorem tailTrace_165917 : CollatzResearch.WordTrace tailWord_165917 prefixEnd_165917 75729039779673406821749 := by
  unfold tailWord_165917
  simp only [CollatzResearch.WordTrace]
  refine ⟨6051490139918520212736005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4034326759945680141824003 6051490139918520212736005)
  ·
    refine ⟨1134654401234722539888001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6051490139918520212736005 1134654401234722539888001)
    ·
      refine ⟨850990800926041904916001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1134654401234722539888001 850990800926041904916001)
      ·
        refine ⟨638243100694531428687001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 850990800926041904916001 638243100694531428687001)
        ·
          refine ⟨478682325520898571515251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 638243100694531428687001 478682325520898571515251)
          ·
            refine ⟨718023488281347857272877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 478682325520898571515251 718023488281347857272877)
            ·
              refine ⟨269258808105505446477329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 718023488281347857272877 269258808105505446477329)
              ·
                refine ⟨201944106079129084857997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 269258808105505446477329 201944106079129084857997)
                ·
                  refine ⟨75729039779673406821749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 201944106079129084857997 75729039779673406821749)
                  ·
                    rfl

theorem cell20_165917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 3, 2, 3].length) (baseStart_165917 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_165917 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_165917 prefixEnd_165917 := by exact prefixLift 165917
  have htrace : WordTrace (prefixWord ++ tailWord_165917) baseStart_165917 baseEnd_165917 := by
    simpa [prefixWord, tailWord_165917, baseEnd_165917] using wordTrace_append hprefix tailTrace_165917
  have hstable : (prefixWord ++ tailWord_165917).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_165917).length < 2 ^ (prefixWord ++ tailWord_165917).sum := by decide
  have hdescent : baseEnd_165917 < baseStart_165917 := by decide
  rcases family_descends (prefixWord ++ tailWord_165917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_165934 : List Nat := [4, 1, 3, 1, 1, 3, 3, 1, 3]
def baseStart_165934 : Nat := 118140960795 + 165934 * 2 ^ 59
def prefixEnd_165934 : Nat := 4983230072969 + 3 ^ 40 * 165934 * 2
def baseEnd_165934 : Nat := 75736799042896903255013

theorem tailTrace_165934 : CollatzResearch.WordTrace tailWord_165934 prefixEnd_165934 75736799042896903255013 := by
  unfold tailWord_165934
  simp only [CollatzResearch.WordTrace]
  refine ⟨756513772607116514513107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4034740120571288077403237 756513772607116514513107)
  ·
    refine ⟨1134770658910674771769661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 756513772607116514513107 1134770658910674771769661)
    ·
      refine ⟨425538997091503039413623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1134770658910674771769661 425538997091503039413623)
      ·
        refine ⟨638308495637254559120435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 425538997091503039413623 638308495637254559120435)
        ·
          refine ⟨957462743455881838680653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 638308495637254559120435 957462743455881838680653)
          ·
            refine ⟨359048528795955689505245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 957462743455881838680653 359048528795955689505245)
            ·
              refine ⟨134643198298483383564467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 359048528795955689505245 134643198298483383564467)
              ·
                refine ⟨201964797447725075346701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 134643198298483383564467 201964797447725075346701)
                ·
                  refine ⟨75736799042896903255013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 201964797447725075346701 75736799042896903255013)
                  ·
                    rfl

theorem cell20_165934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 3, 3, 1, 3].length) (baseStart_165934 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_165934 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_165934 prefixEnd_165934 := by exact prefixLift 165934
  have htrace : WordTrace (prefixWord ++ tailWord_165934) baseStart_165934 baseEnd_165934 := by
    simpa [prefixWord, tailWord_165934, baseEnd_165934] using wordTrace_append hprefix tailTrace_165934
  have hstable : (prefixWord ++ tailWord_165934).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_165934).length < 2 ^ (prefixWord ++ tailWord_165934).sum := by decide
  have hdescent : baseEnd_165934 < baseStart_165934 := by decide
  rcases family_descends (prefixWord ++ tailWord_165934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_165952 : List Nat := [2, 1, 1, 2, 2, 5, 1, 6]
def baseStart_165952 : Nat := 118140960795 + 165952 * 2 ^ 59
def prefixEnd_165952 : Nat := 4983230072969 + 3 ^ 40 * 165952 * 2
def baseEnd_165952 : Nat := 25248338244456280218313

theorem tailTrace_165952 : CollatzResearch.WordTrace tailWord_165952 prefixEnd_165952 25248338244456280218313 := by
  unfold tailWord_165952
  simp only [CollatzResearch.WordTrace]
  refine ⟨3026383347395860595130055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4035177796527814126840073 3026383347395860595130055)
  ·
    refine ⟨4539575021093790892695083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3026383347395860595130055 4539575021093790892695083)
    ·
      refine ⟨6809362531640686339042625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4539575021093790892695083 6809362531640686339042625)
      ·
        refine ⟨5107021898730514754281969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6809362531640686339042625 5107021898730514754281969)
        ·
          refine ⟨3830266424047886065711477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5107021898730514754281969 3830266424047886065711477)
          ·
            refine ⟨359087477254489318660451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 3830266424047886065711477 359087477254489318660451)
            ·
              refine ⟨538631215881733977990677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 359087477254489318660451 538631215881733977990677)
              ·
                refine ⟨25248338244456280218313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 538631215881733977990677 25248338244456280218313)
                ·
                  rfl

theorem cell20_165952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 5, 1, 6].length) (baseStart_165952 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_165952 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_165952 prefixEnd_165952 := by exact prefixLift 165952
  have htrace : WordTrace (prefixWord ++ tailWord_165952) baseStart_165952 baseEnd_165952 := by
    simpa [prefixWord, tailWord_165952, baseEnd_165952] using wordTrace_append hprefix tailTrace_165952
  have hstable : (prefixWord ++ tailWord_165952).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_165952).length < 2 ^ (prefixWord ++ tailWord_165952).sum := by decide
  have hdescent : baseEnd_165952 < baseStart_165952 := by decide
  rcases family_descends (prefixWord ++ tailWord_165952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_165959 : List Nat := [1, 1, 4, 1, 3, 1, 1, 1, 7]
def baseStart_165959 : Nat := 118140960795 + 165959 * 2 ^ 59
def prefixEnd_165959 : Nat := 4983230072969 + 3 ^ 40 * 165959 * 2
def baseEnd_165959 : Nat := 75748209724107927421577

theorem tailTrace_165959 : CollatzResearch.WordTrace tailWord_165959 prefixEnd_165959 75748209724107927421577 := by
  unfold tailWord_165959
  simp only [CollatzResearch.WordTrace]
  refine ⟨6053022005766361385764931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4035348003844240923843287 6053022005766361385764931)
  ·
    refine ⟨9079533008649542078647397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6053022005766361385764931 9079533008649542078647397)
    ·
      refine ⟨1702412439121789139746387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9079533008649542078647397 1702412439121789139746387)
      ·
        refine ⟨2553618658682683709619581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1702412439121789139746387 2553618658682683709619581)
        ·
          refine ⟨957606997006006391107343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2553618658682683709619581 957606997006006391107343)
          ·
            refine ⟨1436410495509009586661015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 957606997006006391107343 1436410495509009586661015)
            ·
              refine ⟨2154615743263514379991523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1436410495509009586661015 2154615743263514379991523)
              ·
                refine ⟨3231923614895271569987285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2154615743263514379991523 3231923614895271569987285)
                ·
                  refine ⟨75748209724107927421577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3231923614895271569987285 75748209724107927421577)
                  ·
                    rfl

theorem cell20_165959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 1, 1, 7].length) (baseStart_165959 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_165959 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_165959 prefixEnd_165959 := by exact prefixLift 165959
  have htrace : WordTrace (prefixWord ++ tailWord_165959) baseStart_165959 baseEnd_165959 := by
    simpa [prefixWord, tailWord_165959, baseEnd_165959] using wordTrace_append hprefix tailTrace_165959
  have hstable : (prefixWord ++ tailWord_165959).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_165959).length < 2 ^ (prefixWord ++ tailWord_165959).sum := by decide
  have hdescent : baseEnd_165959 < baseStart_165959 := by decide
  rcases family_descends (prefixWord ++ tailWord_165959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_165986 : List Nat := [3, 3, 2, 2, 2, 1, 2, 5]
def baseStart_165986 : Nat := 118140960795 + 165986 * 2 ^ 59
def prefixEnd_165986 : Nat := 4983230072969 + 3 ^ 40 * 165986 * 2
def baseEnd_165986 : Nat := 25253511086605277840489

theorem tailTrace_165986 : CollatzResearch.WordTrace tailWord_165986 prefixEnd_165986 25253511086605277840489 := by
  unfold tailWord_165986
  simp only [CollatzResearch.WordTrace]
  refine ⟨1513501694167136249249453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4036004517779029997998541 1513501694167136249249453)
  ·
    refine ⟨567563135312676093468545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1513501694167136249249453 567563135312676093468545)
    ·
      refine ⟨425672351484507070101409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 567563135312676093468545 425672351484507070101409)
      ·
        refine ⟨319254263613380302576057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 425672351484507070101409 319254263613380302576057)
        ·
          refine ⟨239440697710035226932043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 319254263613380302576057 239440697710035226932043)
          ·
            refine ⟨359161046565052840398065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 239440697710035226932043 359161046565052840398065)
            ·
              refine ⟨269370784923789630298549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 359161046565052840398065 269370784923789630298549)
              ·
                refine ⟨25253511086605277840489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 269370784923789630298549 25253511086605277840489)
                ·
                  rfl

theorem cell20_165986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 1, 2, 5].length) (baseStart_165986 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_165986 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_165986 prefixEnd_165986 := by exact prefixLift 165986
  have htrace : WordTrace (prefixWord ++ tailWord_165986) baseStart_165986 baseEnd_165986 := by
    simpa [prefixWord, tailWord_165986, baseEnd_165986] using wordTrace_append hprefix tailTrace_165986
  have hstable : (prefixWord ++ tailWord_165986).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_165986).length < 2 ^ (prefixWord ++ tailWord_165986).sum := by decide
  have hdescent : baseEnd_165986 < baseStart_165986 := by decide
  rcases family_descends (prefixWord ++ tailWord_165986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_166045 : List Nat := [1, 4, 2, 1, 1, 5, 1, 5]
def baseStart_166045 : Nat := 118140960795 + 166045 * 2 ^ 59
def prefixEnd_166045 : Nat := 4983230072969 + 3 ^ 40 * 166045 * 2
def baseEnd_166045 : Nat := 25262487489157950184853

theorem tailTrace_166045 : CollatzResearch.WordTrace tailWord_166045 prefixEnd_166045 25262487489157950184853 := by
  unfold tailWord_166045
  simp only [CollatzResearch.WordTrace]
  refine ⟨6056158683454798073395589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4037439122303198715597059 6056158683454798073395589)
  ·
    refine ⟨1135529753147774638761673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6056158683454798073395589 1135529753147774638761673)
    ·
      refine ⟨851647314860830979071255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1135529753147774638761673 851647314860830979071255)
      ·
        refine ⟨1277470972291246468606883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 851647314860830979071255 1277470972291246468606883)
        ·
          refine ⟨1916206458436869702910325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1277470972291246468606883 1916206458436869702910325)
          ·
            refine ⟨179644355478456534647843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1916206458436869702910325 179644355478456534647843)
            ·
              refine ⟨269466533217684801971765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 179644355478456534647843 269466533217684801971765)
              ·
                refine ⟨25262487489157950184853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 269466533217684801971765 25262487489157950184853)
                ·
                  rfl

theorem cell20_166045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 5, 1, 5].length) (baseStart_166045 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_166045 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_166045 prefixEnd_166045 := by exact prefixLift 166045
  have htrace : WordTrace (prefixWord ++ tailWord_166045) baseStart_166045 baseEnd_166045 := by
    simpa [prefixWord, tailWord_166045, baseEnd_166045] using wordTrace_append hprefix tailTrace_166045
  have hstable : (prefixWord ++ tailWord_166045).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_166045).length < 2 ^ (prefixWord ++ tailWord_166045).sum := by decide
  have hdescent : baseEnd_166045 < baseStart_166045 := by decide
  rcases family_descends (prefixWord ++ tailWord_166045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_166068 : List Nat := [2, 5, 3, 1, 1, 1, 2, 3, 2]
def baseStart_166068 : Nat := 118140960795 + 166068 * 2 ^ 59
def prefixEnd_166068 : Nat := 4983230072969 + 3 ^ 40 * 166068 * 2
def baseEnd_166068 : Nat := 75797960294187992787799

theorem tailTrace_166068 : CollatzResearch.WordTrace tailWord_166068 prefixEnd_166068 75797960294187992787799 := by
  unfold tailWord_166068
  simp only [CollatzResearch.WordTrace]
  refine ⟨3028498781185736500741429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4037998374914315334321905 3028498781185736500741429)
  ·
    refine ⟨283921760736162796944509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 3028498781185736500741429 283921760736162796944509)
    ·
      refine ⟨106470660276061048854191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 283921760736162796944509 106470660276061048854191)
      ·
        refine ⟨159705990414091573281287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106470660276061048854191 159705990414091573281287)
        ·
          refine ⟨239558985621137359921931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 159705990414091573281287 239558985621137359921931)
          ·
            refine ⟨359338478431706039882897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 239558985621137359921931 359338478431706039882897)
            ·
              refine ⟨269503858823779529912173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 359338478431706039882897 269503858823779529912173)
              ·
                refine ⟨101063947058917323717065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 269503858823779529912173 101063947058917323717065)
                ·
                  refine ⟨75797960294187992787799, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 101063947058917323717065 75797960294187992787799)
                  ·
                    rfl

theorem cell20_166068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 1, 2, 3, 2].length) (baseStart_166068 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_166068 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_166068 prefixEnd_166068 := by exact prefixLift 166068
  have htrace : WordTrace (prefixWord ++ tailWord_166068) baseStart_166068 baseEnd_166068 := by
    simpa [prefixWord, tailWord_166068, baseEnd_166068] using wordTrace_append hprefix tailTrace_166068
  have hstable : (prefixWord ++ tailWord_166068).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_166068).length < 2 ^ (prefixWord ++ tailWord_166068).sum := by decide
  have hdescent : baseEnd_166068 < baseStart_166068 := by decide
  rcases family_descends (prefixWord ++ tailWord_166068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_166073 : List Nat := [1, 2, 1, 4, 1, 2, 2, 2, 5]
def baseStart_166073 : Nat := 118140960795 + 166073 * 2 ^ 59
def prefixEnd_166073 : Nat := 4983230072969 + 3 ^ 40 * 166073 * 2
def baseEnd_166073 : Nat := 75800242430430197621111

theorem tailTrace_166073 : CollatzResearch.WordTrace tailWord_166073 prefixEnd_166073 75800242430430197621111 := by
  unfold tailWord_166073
  simp only [CollatzResearch.WordTrace]
  refine ⟨6057179927353358855414873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4038119951568905903609915 6057179927353358855414873)
  ·
    refine ⟨4542884945515019141561155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6057179927353358855414873 4542884945515019141561155)
    ·
      refine ⟨6814327418272528712341733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4542884945515019141561155 6814327418272528712341733)
      ·
        refine ⟨1277686390926099133564075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6814327418272528712341733 1277686390926099133564075)
        ·
          refine ⟨1916529586389148700346113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1277686390926099133564075 1916529586389148700346113)
          ·
            refine ⟨1437397189791861525259585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1916529586389148700346113 1437397189791861525259585)
            ·
              refine ⟨1078047892343896143944689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1437397189791861525259585 1078047892343896143944689)
              ·
                refine ⟨808535919257922107958517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1078047892343896143944689 808535919257922107958517)
                ·
                  refine ⟨75800242430430197621111, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 808535919257922107958517 75800242430430197621111)
                  ·
                    rfl

theorem cell20_166073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 2, 2, 5].length) (baseStart_166073 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_166073 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_166073 prefixEnd_166073 := by exact prefixLift 166073
  have htrace : WordTrace (prefixWord ++ tailWord_166073) baseStart_166073 baseEnd_166073 := by
    simpa [prefixWord, tailWord_166073, baseEnd_166073] using wordTrace_append hprefix tailTrace_166073
  have hstable : (prefixWord ++ tailWord_166073).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_166073).length < 2 ^ (prefixWord ++ tailWord_166073).sum := by decide
  have hdescent : baseEnd_166073 < baseStart_166073 := by decide
  rcases family_descends (prefixWord ++ tailWord_166073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_166148 : List Nat := [2, 3, 2, 2, 3, 1, 3, 2, 2]
def baseStart_166148 : Nat := 118140960795 + 166148 * 2 ^ 59
def prefixEnd_166148 : Nat := 4983230072969 + 3 ^ 40 * 166148 * 2
def baseEnd_166148 : Nat := 75834474474063270120805

theorem tailTrace_166148 : CollatzResearch.WordTrace tailWord_166148 prefixEnd_166148 75834474474063270120805 := by
  unfold tailWord_166148
  simp only [CollatzResearch.WordTrace]
  refine ⟨3029957701040823332197549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4039943601387764442930065 3029957701040823332197549)
  ·
    refine ⟨1136234137890308749574081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3029957701040823332197549 1136234137890308749574081)
    ·
      refine ⟨852175603417731562180561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1136234137890308749574081 852175603417731562180561)
      ·
        refine ⟨639131702563298671635421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 852175603417731562180561 639131702563298671635421)
        ·
          refine ⟨239674388461237001863283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 639131702563298671635421 239674388461237001863283)
          ·
            refine ⟨359511582691855502794925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 239674388461237001863283 359511582691855502794925)
            ·
              refine ⟨134816843509445813548097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 359511582691855502794925 134816843509445813548097)
              ·
                refine ⟨101112632632084360161073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 134816843509445813548097 101112632632084360161073)
                ·
                  refine ⟨75834474474063270120805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 101112632632084360161073 75834474474063270120805)
                  ·
                    rfl

theorem cell20_166148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 1, 3, 2, 2].length) (baseStart_166148 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_166148 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_166148 prefixEnd_166148 := by exact prefixLift 166148
  have htrace : WordTrace (prefixWord ++ tailWord_166148) baseStart_166148 baseEnd_166148 := by
    simpa [prefixWord, tailWord_166148, baseEnd_166148] using wordTrace_append hprefix tailTrace_166148
  have hstable : (prefixWord ++ tailWord_166148).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_166148).length < 2 ^ (prefixWord ++ tailWord_166148).sum := by decide
  have hdescent : baseEnd_166148 < baseStart_166148 := by decide
  rcases family_descends (prefixWord ++ tailWord_166148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_166152 : List Nat := [2, 1, 3, 2, 3, 3, 1, 1, 4]
def baseStart_166152 : Nat := 118140960795 + 166152 * 2 ^ 59
def prefixEnd_166152 : Nat := 4983230072969 + 3 ^ 40 * 166152 * 2
def baseEnd_166152 : Nat := 75836300183057033987455

theorem tailTrace_166152 : CollatzResearch.WordTrace tailWord_166152 prefixEnd_166152 75836300183057033987455 := by
  unfold tailWord_166152
  simp only [CollatzResearch.WordTrace]
  refine ⟨3030030647033577673770355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4040040862711436898360473 3030030647033577673770355)
  ·
    refine ⟨4545045970550366510655533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3030030647033577673770355 4545045970550366510655533)
    ·
      refine ⟨1704392238956387441495825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4545045970550366510655533 1704392238956387441495825)
      ·
        refine ⟨1278294179217290581121869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1704392238956387441495825 1278294179217290581121869)
        ·
          refine ⟨479360317206483967920701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1278294179217290581121869 479360317206483967920701)
          ·
            refine ⟨179760118952431487970263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 479360317206483967920701 179760118952431487970263)
            ·
              refine ⟨269640178428647231955395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 179760118952431487970263 269640178428647231955395)
              ·
                refine ⟨404460267642970847933093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 269640178428647231955395 404460267642970847933093)
                ·
                  refine ⟨75836300183057033987455, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 404460267642970847933093 75836300183057033987455)
                  ·
                    rfl

theorem cell20_166152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 3, 1, 1, 4].length) (baseStart_166152 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_166152 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_166152 prefixEnd_166152 := by exact prefixLift 166152
  have htrace : WordTrace (prefixWord ++ tailWord_166152) baseStart_166152 baseEnd_166152 := by
    simpa [prefixWord, tailWord_166152, baseEnd_166152] using wordTrace_append hprefix tailTrace_166152
  have hstable : (prefixWord ++ tailWord_166152).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_166152).length < 2 ^ (prefixWord ++ tailWord_166152).sum := by decide
  have hdescent : baseEnd_166152 < baseStart_166152 := by decide
  rcases family_descends (prefixWord ++ tailWord_166152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_166180 : List Nat := [2, 3, 1, 3, 1, 2, 2, 6]
def baseStart_166180 : Nat := 118140960795 + 166180 * 2 ^ 59
def prefixEnd_166180 : Nat := 4983230072969 + 3 ^ 40 * 166180 * 2
def baseEnd_166180 : Nat := 25283026715337793684669

theorem tailTrace_166180 : CollatzResearch.WordTrace tailWord_166180 prefixEnd_166180 25283026715337793684669 := by
  unfold tailWord_166180
  simp only [CollatzResearch.WordTrace]
  refine ⟨3030541268982858064779997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4040721691977144086373329 3030541268982858064779997)
  ·
    refine ⟨1136452975868571774292499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3030541268982858064779997 1136452975868571774292499)
    ·
      refine ⟨1704679463802857661438749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1136452975868571774292499 1704679463802857661438749)
      ·
        refine ⟨639254798926071623039531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1704679463802857661438749 639254798926071623039531)
        ·
          refine ⟨958882198389107434559297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 639254798926071623039531 958882198389107434559297)
          ·
            refine ⟨719161648791830575919473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 958882198389107434559297 719161648791830575919473)
            ·
              refine ⟨539371236593872931939605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 719161648791830575919473 539371236593872931939605)
              ·
                refine ⟨25283026715337793684669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 539371236593872931939605 25283026715337793684669)
                ·
                  rfl

theorem cell20_166180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 2, 6].length) (baseStart_166180 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_166180 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_166180 prefixEnd_166180 := by exact prefixLift 166180
  have htrace : WordTrace (prefixWord ++ tailWord_166180) baseStart_166180 baseEnd_166180 := by
    simpa [prefixWord, tailWord_166180, baseEnd_166180] using wordTrace_append hprefix tailTrace_166180
  have hstable : (prefixWord ++ tailWord_166180).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_166180).length < 2 ^ (prefixWord ++ tailWord_166180).sum := by decide
  have hdescent : baseEnd_166180 < baseStart_166180 := by decide
  rcases family_descends (prefixWord ++ tailWord_166180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_166204 : List Nat := [2, 2, 2, 2, 1, 2, 4, 2, 3]
def baseStart_166204 : Nat := 118140960795 + 166204 * 2 ^ 59
def prefixEnd_166204 : Nat := 4983230072969 + 3 ^ 40 * 166204 * 2
def baseEnd_166204 : Nat := 75860034399975964253909

theorem tailTrace_166204 : CollatzResearch.WordTrace tailWord_166204 prefixEnd_166204 75860034399975964253909 := by
  unfold tailWord_166204
  simp only [CollatzResearch.WordTrace]
  refine ⟨3030978944939384114216833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4041305259919178818955777 3030978944939384114216833)
  ·
    refine ⟨2273234208704538085662625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3030978944939384114216833 2273234208704538085662625)
    ·
      refine ⟨1704925656528403564246969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2273234208704538085662625 1704925656528403564246969)
      ·
        refine ⟨1278694242396302673185227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1704925656528403564246969 1278694242396302673185227)
        ·
          refine ⟨1918041363594454009777841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1278694242396302673185227 1918041363594454009777841)
          ·
            refine ⟨1438531022695840507333381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1918041363594454009777841 1438531022695840507333381)
            ·
              refine ⟨269724566755470095125009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1438531022695840507333381 269724566755470095125009)
              ·
                refine ⟨202293425066602571343757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 269724566755470095125009 202293425066602571343757)
                ·
                  refine ⟨75860034399975964253909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 202293425066602571343757 75860034399975964253909)
                  ·
                    rfl

theorem cell20_166204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 4, 2, 3].length) (baseStart_166204 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_166204 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_166204 prefixEnd_166204 := by exact prefixLift 166204
  have htrace : WordTrace (prefixWord ++ tailWord_166204) baseStart_166204 baseEnd_166204 := by
    simpa [prefixWord, tailWord_166204, baseEnd_166204] using wordTrace_append hprefix tailTrace_166204
  have hstable : (prefixWord ++ tailWord_166204).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_166204).length < 2 ^ (prefixWord ++ tailWord_166204).sum := by decide
  have hdescent : baseEnd_166204 < baseStart_166204 := by decide
  rcases family_descends (prefixWord ++ tailWord_166204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_166239 : List Nat := [1, 1, 2, 3, 1, 2, 2, 8]
def baseStart_166239 : Nat := 118140960795 + 166239 * 2 ^ 59
def prefixEnd_166239 : Nat := 4983230072969 + 3 ^ 40 * 166239 * 2
def baseEnd_166239 : Nat := 25292003117890466029033

theorem tailTrace_166239 : CollatzResearch.WordTrace tailWord_166239 prefixEnd_166239 25292003117890466029033 := by
  unfold tailWord_166239
  simp only [CollatzResearch.WordTrace]
  refine ⟨6063234444751969205957771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4042156296501312803971847 6063234444751969205957771)
  ·
    refine ⟨9094851667127953808936657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6063234444751969205957771 9094851667127953808936657)
    ·
      refine ⟨6821138750345965356702493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9094851667127953808936657 6821138750345965356702493)
      ·
        refine ⟨2557927031379737008763435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6821138750345965356702493 2557927031379737008763435)
        ·
          refine ⟨3836890547069605513145153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2557927031379737008763435 3836890547069605513145153)
          ·
            refine ⟨2877667910302204134858865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3836890547069605513145153 2877667910302204134858865)
            ·
              refine ⟨2158250932726653101144149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2877667910302204134858865 2158250932726653101144149)
              ·
                refine ⟨25292003117890466029033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2158250932726653101144149 25292003117890466029033)
                ·
                  rfl

theorem cell20_166239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 2, 8].length) (baseStart_166239 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_166239 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_166239 prefixEnd_166239 := by exact prefixLift 166239
  have htrace : WordTrace (prefixWord ++ tailWord_166239) baseStart_166239 baseEnd_166239 := by
    simpa [prefixWord, tailWord_166239, baseEnd_166239] using wordTrace_append hprefix tailTrace_166239
  have hstable : (prefixWord ++ tailWord_166239).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_166239).length < 2 ^ (prefixWord ++ tailWord_166239).sum := by decide
  have hdescent : baseEnd_166239 < baseStart_166239 := by decide
  rcases family_descends (prefixWord ++ tailWord_166239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_166263 : List Nat := [1, 1, 3, 1, 1, 2, 2, 6, 3]
def baseStart_166263 : Nat := 118140960795 + 166263 * 2 ^ 59
def prefixEnd_166263 : Nat := 4983230072969 + 3 ^ 40 * 166263 * 2
def baseEnd_166263 : Nat := 75886963607633981287001

theorem tailTrace_166263 : CollatzResearch.WordTrace tailWord_166263 prefixEnd_166263 75886963607633981287001 := by
  unfold tailWord_166263
  simp only [CollatzResearch.WordTrace]
  refine ⟨6064109796665021304831443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4042739864443347536554295 6064109796665021304831443)
  ·
    refine ⟨9096164694997531957247165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6064109796665021304831443 9096164694997531957247165)
    ·
      refine ⟨3411061760624074483967687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9096164694997531957247165 3411061760624074483967687)
      ·
        refine ⟨5116592640936111725951531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3411061760624074483967687 5116592640936111725951531)
        ·
          refine ⟨7674888961404167588927297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5116592640936111725951531 7674888961404167588927297)
          ·
            refine ⟨5756166721053125691695473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7674888961404167588927297 5756166721053125691695473)
            ·
              refine ⟨4317125040789844268771605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5756166721053125691695473 4317125040789844268771605)
              ·
                refine ⟨202365236287023950098669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 4317125040789844268771605 202365236287023950098669)
                ·
                  refine ⟨75886963607633981287001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 202365236287023950098669 75886963607633981287001)
                  ·
                    rfl

theorem cell20_166263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 6, 3].length) (baseStart_166263 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_166263 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_166263 prefixEnd_166263 := by exact prefixLift 166263
  have htrace : WordTrace (prefixWord ++ tailWord_166263) baseStart_166263 baseEnd_166263 := by
    simpa [prefixWord, tailWord_166263, baseEnd_166263] using wordTrace_append hprefix tailTrace_166263
  have hstable : (prefixWord ++ tailWord_166263).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_166263).length < 2 ^ (prefixWord ++ tailWord_166263).sum := by decide
  have hdescent : baseEnd_166263 < baseStart_166263 := by decide
  rcases family_descends (prefixWord ++ tailWord_166263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_166277 : List Nat := [1, 3, 1, 1, 3, 1, 1, 9]
def baseStart_166277 : Nat := 118140960795 + 166277 * 2 ^ 59
def prefixEnd_166277 : Nat := 4983230072969 + 3 ^ 40 * 166277 * 2
def baseEnd_166277 : Nat := 25297784529704051606759

theorem tailTrace_166277 : CollatzResearch.WordTrace tailWord_166277 prefixEnd_166277 25297784529704051606759 := by
  unfold tailWord_166277
  simp only [CollatzResearch.WordTrace]
  refine ⟨6064620418614301695841085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4043080279076201130560723 6064620418614301695841085)
  ·
    refine ⟨2274232656980363135940407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6064620418614301695841085 2274232656980363135940407)
    ·
      refine ⟨3411348985470544703910611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2274232656980363135940407 3411348985470544703910611)
      ·
        refine ⟨5117023478205817055865917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3411348985470544703910611 5117023478205817055865917)
        ·
          refine ⟨1918883804327181395949719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5117023478205817055865917 1918883804327181395949719)
          ·
            refine ⟨2878325706490772093924579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1918883804327181395949719 2878325706490772093924579)
            ·
              refine ⟨4317488559736158140886869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2878325706490772093924579 4317488559736158140886869)
              ·
                refine ⟨25297784529704051606759, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 4317488559736158140886869 25297784529704051606759)
                ·
                  rfl

theorem cell20_166277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 9].length) (baseStart_166277 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_166277 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_166277 prefixEnd_166277 := by exact prefixLift 166277
  have htrace : WordTrace (prefixWord ++ tailWord_166277) baseStart_166277 baseEnd_166277 := by
    simpa [prefixWord, tailWord_166277, baseEnd_166277] using wordTrace_append hprefix tailTrace_166277
  have hstable : (prefixWord ++ tailWord_166277).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_166277).length < 2 ^ (prefixWord ++ tailWord_166277).sum := by decide
  have hdescent : baseEnd_166277 < baseStart_166277 := by decide
  rcases family_descends (prefixWord ++ tailWord_166277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_166304 : List Nat := [2, 1, 1, 4, 1, 3, 3, 3, 2]
def baseStart_166304 : Nat := 118140960795 + 166304 * 2 ^ 59
def prefixEnd_166304 : Nat := 4983230072969 + 3 ^ 40 * 166304 * 2
def baseEnd_166304 : Nat := 75905677124820060920167

theorem tailTrace_166304 : CollatzResearch.WordTrace tailWord_166304 prefixEnd_166304 75905677124820060920167 := by
  unfold tailWord_166304
  simp only [CollatzResearch.WordTrace]
  refine ⟨3032802594758242653536983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4043736793010990204715977 3032802594758242653536983)
  ·
    refine ⟨4549203892137363980305475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3032802594758242653536983 4549203892137363980305475)
    ·
      refine ⟨6823805838206045970458213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4549203892137363980305475 6823805838206045970458213)
      ·
        refine ⟨1279463594663633619460915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6823805838206045970458213 1279463594663633619460915)
        ·
          refine ⟨1919195391995450429191373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1279463594663633619460915 1919195391995450429191373)
          ·
            refine ⟨719698271998293910946765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1919195391995450429191373 719698271998293910946765)
            ·
              refine ⟨269886851999360216605037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 719698271998293910946765 269886851999360216605037)
              ·
                refine ⟨101207569499760081226889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 269886851999360216605037 101207569499760081226889)
                ·
                  refine ⟨75905677124820060920167, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 101207569499760081226889 75905677124820060920167)
                  ·
                    rfl

theorem cell20_166304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 3, 3, 2].length) (baseStart_166304 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_166304 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_166304 prefixEnd_166304 := by exact prefixLift 166304
  have htrace : WordTrace (prefixWord ++ tailWord_166304) baseStart_166304 baseEnd_166304 := by
    simpa [prefixWord, tailWord_166304, baseEnd_166304] using wordTrace_append hprefix tailTrace_166304
  have hstable : (prefixWord ++ tailWord_166304).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_166304).length < 2 ^ (prefixWord ++ tailWord_166304).sum := by decide
  have hdescent : baseEnd_166304 < baseStart_166304 := by decide
  rcases family_descends (prefixWord ++ tailWord_166304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_166308 : List Nat := [2, 3, 1, 2, 1, 1, 2, 2, 6]
def baseStart_166308 : Nat := 118140960795 + 166308 * 2 ^ 59
def prefixEnd_166308 : Nat := 4983230072969 + 3 ^ 40 * 166308 * 2
def baseEnd_166308 : Nat := 75907502833813824786817

theorem tailTrace_166308 : CollatzResearch.WordTrace tailWord_166308 prefixEnd_166308 75907502833813824786817 := by
  unfold tailWord_166308
  simp only [CollatzResearch.WordTrace]
  refine ⟨3032875540750996995109789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4043834054334662660146385 3032875540750996995109789)
  ·
    refine ⟨1137328327781623873166171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3032875540750996995109789 1137328327781623873166171)
    ·
      refine ⟨1705992491672435809749257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1137328327781623873166171 1705992491672435809749257)
      ·
        refine ⟨1279494368754326857311943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1705992491672435809749257 1279494368754326857311943)
        ·
          refine ⟨1919241553131490285967915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1279494368754326857311943 1919241553131490285967915)
          ·
            refine ⟨2878862329697235428951873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1919241553131490285967915 2878862329697235428951873)
            ·
              refine ⟨2159146747272926571713905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2878862329697235428951873 2159146747272926571713905)
              ·
                refine ⟨1619360060454694928785429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2159146747272926571713905 1619360060454694928785429)
                ·
                  refine ⟨75907502833813824786817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1619360060454694928785429 75907502833813824786817)
                  ·
                    rfl

theorem cell20_166308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 2, 2, 6].length) (baseStart_166308 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_166308 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_166308 prefixEnd_166308 := by exact prefixLift 166308
  have htrace : WordTrace (prefixWord ++ tailWord_166308) baseStart_166308 baseEnd_166308 := by
    simpa [prefixWord, tailWord_166308, baseEnd_166308] using wordTrace_append hprefix tailTrace_166308
  have hstable : (prefixWord ++ tailWord_166308).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_166308).length < 2 ^ (prefixWord ++ tailWord_166308).sum := by decide
  have hdescent : baseEnd_166308 < baseStart_166308 := by decide
  rcases family_descends (prefixWord ++ tailWord_166308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_166321 : List Nat := [1, 2, 2, 4, 1, 3, 3, 2, 2]
def baseStart_166321 : Nat := 118140960795 + 166321 * 2 ^ 59
def prefixEnd_166321 : Nat := 4983230072969 + 3 ^ 40 * 166321 * 2
def baseEnd_166321 : Nat := 75913436388043557353431

theorem tailTrace_166321 : CollatzResearch.WordTrace tailWord_166321 prefixEnd_166321 75913436388043557353431 := by
  unfold tailWord_166321
  simp only [CollatzResearch.WordTrace]
  refine ⟨6066225230454897210442817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4044150153636598140295211 6066225230454897210442817)
  ·
    refine ⟨4549668922841172907832113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6066225230454897210442817 4549668922841172907832113)
    ·
      refine ⟨3412251692130879680874085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4549668922841172907832113 3412251692130879680874085)
      ·
        refine ⟨639797192274539940163891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3412251692130879680874085 639797192274539940163891)
        ·
          refine ⟨959695788411809910245837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 639797192274539940163891 959695788411809910245837)
          ·
            refine ⟨359885920654428716342189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 959695788411809910245837 359885920654428716342189)
            ·
              refine ⟨134957220245410768628321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 359885920654428716342189 134957220245410768628321)
              ·
                refine ⟨101217915184058076471241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 134957220245410768628321 101217915184058076471241)
                ·
                  refine ⟨75913436388043557353431, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 101217915184058076471241 75913436388043557353431)
                  ·
                    rfl

theorem cell20_166321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 3, 3, 2, 2].length) (baseStart_166321 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_166321 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_166321 prefixEnd_166321 := by exact prefixLift 166321
  have htrace : WordTrace (prefixWord ++ tailWord_166321) baseStart_166321 baseEnd_166321 := by
    simpa [prefixWord, tailWord_166321, baseEnd_166321] using wordTrace_append hprefix tailTrace_166321
  have hstable : (prefixWord ++ tailWord_166321).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_166321).length < 2 ^ (prefixWord ++ tailWord_166321).sum := by decide
  have hdescent : baseEnd_166321 < baseStart_166321 := by decide
  rcases family_descends (prefixWord ++ tailWord_166321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_166332 : List Nat := [2, 2, 2, 4, 1, 1, 1, 7]
def baseStart_166332 : Nat := 118140960795 + 166332 * 2 ^ 59
def prefixEnd_166332 : Nat := 4983230072969 + 3 ^ 40 * 166332 * 2
def baseEnd_166332 : Nat := 25306152362592135995573

theorem tailTrace_166332 : CollatzResearch.WordTrace tailWord_166332 prefixEnd_166332 25306152362592135995573 := by
  unfold tailWord_166332
  simp only [CollatzResearch.WordTrace]
  refine ⟨3033313216707523044546625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4044417622276697392728833 3033313216707523044546625)
  ·
    refine ⟨2274984912530642283409969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3033313216707523044546625 2274984912530642283409969)
    ·
      refine ⟨1706238684397981712557477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2274984912530642283409969 1706238684397981712557477)
      ·
        refine ⟨319919753324621571104527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1706238684397981712557477 319919753324621571104527)
        ·
          refine ⟨479879629986932356656791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 319919753324621571104527 479879629986932356656791)
          ·
            refine ⟨719819444980398534985187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 479879629986932356656791 719819444980398534985187)
            ·
              refine ⟨1079729167470597802477781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 719819444980398534985187 1079729167470597802477781)
              ·
                refine ⟨25306152362592135995573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1079729167470597802477781 25306152362592135995573)
                ·
                  rfl

theorem cell20_166332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 1, 7].length) (baseStart_166332 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_166332 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_166332 prefixEnd_166332 := by exact prefixLift 166332
  have htrace : WordTrace (prefixWord ++ tailWord_166332) baseStart_166332 baseEnd_166332 := by
    simpa [prefixWord, tailWord_166332, baseEnd_166332] using wordTrace_append hprefix tailTrace_166332
  have hstable : (prefixWord ++ tailWord_166332).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_166332).length < 2 ^ (prefixWord ++ tailWord_166332).sum := by decide
  have hdescent : baseEnd_166332 < baseStart_166332 := by decide
  rcases family_descends (prefixWord ++ tailWord_166332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_166346 : List Nat := [3, 1, 2, 1, 2, 2, 2, 1, 6]
def baseStart_166346 : Nat := 118140960795 + 166346 * 2 ^ 59
def prefixEnd_166346 : Nat := 4983230072969 + 3 ^ 40 * 166346 * 2
def baseEnd_166346 : Nat := 75924847069254581519995

theorem tailTrace_166346 : CollatzResearch.WordTrace tailWord_166346 prefixEnd_166346 75924847069254581519995 := by
  unfold tailWord_166346
  simp only [CollatzResearch.WordTrace]
  refine ⟨1516784263841081620025723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4044758036909550986735261 1516784263841081620025723)
  ·
    refine ⟨2275176395761622430038585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1516784263841081620025723 2275176395761622430038585)
    ·
      refine ⟨1706382296821216822528939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2275176395761622430038585 1706382296821216822528939)
      ·
        refine ⟨2559573445231825233793409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1706382296821216822528939 2559573445231825233793409)
        ·
          refine ⟨1919680083923868925345057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2559573445231825233793409 1919680083923868925345057)
          ·
            refine ⟨1439760062942901694008793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1919680083923868925345057 1439760062942901694008793)
            ·
              refine ⟨1079820047207176270506595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1439760062942901694008793 1079820047207176270506595)
              ·
                refine ⟨1619730070810764405759893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1079820047207176270506595 1619730070810764405759893)
                ·
                  refine ⟨75924847069254581519995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1619730070810764405759893 75924847069254581519995)
                  ·
                    rfl

theorem cell20_166346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 2, 1, 6].length) (baseStart_166346 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_166346 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_166346 prefixEnd_166346 := by exact prefixLift 166346
  have htrace : WordTrace (prefixWord ++ tailWord_166346) baseStart_166346 baseEnd_166346 := by
    simpa [prefixWord, tailWord_166346, baseEnd_166346] using wordTrace_append hprefix tailTrace_166346
  have hstable : (prefixWord ++ tailWord_166346).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_166346).length < 2 ^ (prefixWord ++ tailWord_166346).sum := by decide
  have hdescent : baseEnd_166346 < baseStart_166346 := by decide
  rcases family_descends (prefixWord ++ tailWord_166346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_166373 : List Nat := [1, 3, 1, 5, 2, 1, 2, 2, 3]
def baseStart_166373 : Nat := 118140960795 + 166373 * 2 ^ 59
def prefixEnd_166373 : Nat := 4983230072969 + 3 ^ 40 * 166373 * 2
def baseEnd_166373 : Nat := 75937170604962487619885

theorem tailTrace_166373 : CollatzResearch.WordTrace tailWord_166373 prefixEnd_166373 75937170604962487619885 := by
  unfold tailWord_166373
  simp only [CollatzResearch.WordTrace]
  refine ⟨6068121826266510091335773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4045414550844340060890515 6068121826266510091335773)
  ·
    refine ⟨2275545684849941284250915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6068121826266510091335773 2275545684849941284250915)
    ·
      refine ⟨3413318527274911926376373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2275545684849941284250915 3413318527274911926376373)
      ·
        refine ⟨319998611932022993097785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 3413318527274911926376373 319998611932022993097785)
        ·
          refine ⟨239998958949017244823339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 319998611932022993097785 239998958949017244823339)
          ·
            refine ⟨359998438423525867235009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 239998958949017244823339 359998438423525867235009)
            ·
              refine ⟨269998828817644400426257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 359998438423525867235009 269998828817644400426257)
              ·
                refine ⟨202499121613233300319693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 269998828817644400426257 202499121613233300319693)
                ·
                  refine ⟨75937170604962487619885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 202499121613233300319693 75937170604962487619885)
                  ·
                    rfl

theorem cell20_166373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 1, 2, 2, 3].length) (baseStart_166373 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_166373 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_166373 prefixEnd_166373 := by exact prefixLift 166373
  have htrace : WordTrace (prefixWord ++ tailWord_166373) baseStart_166373 baseEnd_166373 := by
    simpa [prefixWord, tailWord_166373, baseEnd_166373] using wordTrace_append hprefix tailTrace_166373
  have hstable : (prefixWord ++ tailWord_166373).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_166373).length < 2 ^ (prefixWord ++ tailWord_166373).sum := by decide
  have hdescent : baseEnd_166373 < baseStart_166373 := by decide
  rcases family_descends (prefixWord ++ tailWord_166373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_166384 : List Nat := [2, 1, 1, 1, 3, 3, 2, 3, 4]
def baseStart_166384 : Nat := 118140960795 + 166384 * 2 ^ 59
def prefixEnd_166384 : Nat := 4983230072969 + 3 ^ 40 * 166384 * 2
def baseEnd_166384 : Nat := 75942191304695338253173

theorem tailTrace_166384 : CollatzResearch.WordTrace tailWord_166384 prefixEnd_166384 75942191304695338253173 := by
  unfold tailWord_166384
  simp only [CollatzResearch.WordTrace]
  refine ⟨3034261514613329484993103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4045682019484439313324137 3034261514613329484993103)
  ·
    refine ⟨4551392271919994227489655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3034261514613329484993103 4551392271919994227489655)
    ·
      refine ⟨6827088407879991341234483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4551392271919994227489655 6827088407879991341234483)
      ·
        refine ⟨10240632611819987011851725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6827088407879991341234483 10240632611819987011851725)
        ·
          refine ⟨3840237229432495129444397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10240632611819987011851725 3840237229432495129444397)
          ·
            refine ⟨1440088961037185673541649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3840237229432495129444397 1440088961037185673541649)
            ·
              refine ⟨1080066720777889255156237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1440088961037185673541649 1080066720777889255156237)
              ·
                refine ⟨405025020291708470683589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1080066720777889255156237 405025020291708470683589)
                ·
                  refine ⟨75942191304695338253173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 405025020291708470683589 75942191304695338253173)
                  ·
                    rfl

theorem cell20_166384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 2, 3, 4].length) (baseStart_166384 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_166384 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_166384 prefixEnd_166384 := by exact prefixLift 166384
  have htrace : WordTrace (prefixWord ++ tailWord_166384) baseStart_166384 baseEnd_166384 := by
    simpa [prefixWord, tailWord_166384, baseEnd_166384] using wordTrace_append hprefix tailTrace_166384
  have hstable : (prefixWord ++ tailWord_166384).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_166384).length < 2 ^ (prefixWord ++ tailWord_166384).sum := by decide
  have hdescent : baseEnd_166384 < baseStart_166384 := by decide
  rcases family_descends (prefixWord ++ tailWord_166384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_166401 : List Nat := [1, 2, 4, 1, 3, 2, 1, 2, 4]
def baseStart_166401 : Nat := 118140960795 + 166401 * 2 ^ 59
def prefixEnd_166401 : Nat := 4983230072969 + 3 ^ 40 * 166401 * 2
def baseEnd_166401 : Nat := 75949950567918834686437

theorem tailTrace_166401 : CollatzResearch.WordTrace tailWord_166401 prefixEnd_166401 75949950567918834686437 := by
  unfold tailWord_166401
  simp only [CollatzResearch.WordTrace]
  refine ⟨6069143070165070873355057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4046095380110047248903371 6069143070165070873355057)
  ·
    refine ⟨4551857302623803155016293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6069143070165070873355057 4551857302623803155016293)
    ·
      refine ⟨853473244241963091565555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4551857302623803155016293 853473244241963091565555)
      ·
        refine ⟨1280209866362944637348333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 853473244241963091565555 1280209866362944637348333)
        ·
          refine ⟨480078699886104239005625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1280209866362944637348333 480078699886104239005625)
          ·
            refine ⟨360059024914578179254219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 480078699886104239005625 360059024914578179254219)
            ·
              refine ⟨540088537371867268881329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 360059024914578179254219 540088537371867268881329)
              ·
                refine ⟨405066403028900451660997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 540088537371867268881329 405066403028900451660997)
                ·
                  refine ⟨75949950567918834686437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 405066403028900451660997 75949950567918834686437)
                  ·
                    rfl

theorem cell20_166401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 2, 1, 2, 4].length) (baseStart_166401 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_166401 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_166401 prefixEnd_166401 := by exact prefixLift 166401
  have htrace : WordTrace (prefixWord ++ tailWord_166401) baseStart_166401 baseEnd_166401 := by
    simpa [prefixWord, tailWord_166401, baseEnd_166401] using wordTrace_append hprefix tailTrace_166401
  have hstable : (prefixWord ++ tailWord_166401).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_166401).length < 2 ^ (prefixWord ++ tailWord_166401).sum := by decide
  have hdescent : baseEnd_166401 < baseStart_166401 := by decide
  rcases family_descends (prefixWord ++ tailWord_166401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_166432 : List Nat := [2, 1, 1, 6, 2, 1, 1, 1, 5]
def baseStart_166432 : Nat := 118140960795 + 166432 * 2 ^ 59
def prefixEnd_166432 : Nat := 4983230072969 + 3 ^ 40 * 166432 * 2
def baseEnd_166432 : Nat := 75964099812620504652977

theorem tailTrace_166432 : CollatzResearch.WordTrace tailWord_166432 prefixEnd_166432 75964099812620504652977 := by
  unfold tailWord_166432
  simp only [CollatzResearch.WordTrace]
  refine ⟨3035136866526381583866775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4046849155368508778489033 3035136866526381583866775)
  ·
    refine ⟨4552705299789572375800163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3035136866526381583866775 4552705299789572375800163)
    ·
      refine ⟨6829057949684358563700245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4552705299789572375800163 6829057949684358563700245)
      ·
        refine ⟨320112091391454307673449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 6829057949684358563700245 320112091391454307673449)
        ·
          refine ⟨240084068543590730755087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 320112091391454307673449 240084068543590730755087)
          ·
            refine ⟨360126102815386096132631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 240084068543590730755087 360126102815386096132631)
            ·
              refine ⟨540189154223079144198947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 360126102815386096132631 540189154223079144198947)
              ·
                refine ⟨810283731334618716298421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 540189154223079144198947 810283731334618716298421)
                ·
                  refine ⟨75964099812620504652977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 810283731334618716298421 75964099812620504652977)
                  ·
                    rfl

theorem cell20_166432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 1, 1, 1, 5].length) (baseStart_166432 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_166432 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_166432 prefixEnd_166432 := by exact prefixLift 166432
  have htrace : WordTrace (prefixWord ++ tailWord_166432) baseStart_166432 baseEnd_166432 := by
    simpa [prefixWord, tailWord_166432, baseEnd_166432] using wordTrace_append hprefix tailTrace_166432
  have hstable : (prefixWord ++ tailWord_166432).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_166432).length < 2 ^ (prefixWord ++ tailWord_166432).sum := by decide
  have hdescent : baseEnd_166432 < baseStart_166432 := by decide
  rcases family_descends (prefixWord ++ tailWord_166432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_166484 : List Nat := [2, 4, 1, 1, 1, 5, 6]
def baseStart_166484 : Nat := 118140960795 + 166484 * 2 ^ 59
def prefixEnd_166484 : Nat := 4983230072969 + 3 ^ 40 * 166484 * 2
def baseEnd_166484 : Nat := 8443092669948826102159

theorem tailTrace_166484 : CollatzResearch.WordTrace tailWord_166484 prefixEnd_166484 8443092669948826102159 := by
  unfold tailWord_166484
  simp only [CollatzResearch.WordTrace]
  refine ⟨3036085164432188024313253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4048113552576250699084337 3036085164432188024313253)
  ·
    refine ⟨569265968331035254558735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3036085164432188024313253 569265968331035254558735)
    ·
      refine ⟨853898952496552881838103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 569265968331035254558735 853898952496552881838103)
      ·
        refine ⟨1280848428744829322757155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 853898952496552881838103 1280848428744829322757155)
        ·
          refine ⟨1921272643117243984135733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1280848428744829322757155 1921272643117243984135733)
          ·
            refine ⟨180119310292241623512725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1921272643117243984135733 180119310292241623512725)
            ·
              refine ⟨8443092669948826102159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 180119310292241623512725 8443092669948826102159)
              ·
                rfl

theorem cell20_166484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 5, 6].length) (baseStart_166484 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_166484 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_166484 prefixEnd_166484 := by exact prefixLift 166484
  have htrace : WordTrace (prefixWord ++ tailWord_166484) baseStart_166484 baseEnd_166484 := by
    simpa [prefixWord, tailWord_166484, baseEnd_166484] using wordTrace_append hprefix tailTrace_166484
  have hstable : (prefixWord ++ tailWord_166484).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_166484).length < 2 ^ (prefixWord ++ tailWord_166484).sum := by decide
  have hdescent : baseEnd_166484 < baseStart_166484 := by decide
  rcases family_descends (prefixWord ++ tailWord_166484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_166504 : List Nat := [2, 1, 4, 3, 2, 2, 2, 1, 3]
def baseStart_166504 : Nat := 118140960795 + 166504 * 2 ^ 59
def prefixEnd_166504 : Nat := 4983230072969 + 3 ^ 40 * 166504 * 2
def baseEnd_166504 : Nat := 75996962574508254252683

theorem tailTrace_166504 : CollatzResearch.WordTrace tailWord_166504 prefixEnd_166504 75996962574508254252683 := by
  unfold tailWord_166504
  simp only [CollatzResearch.WordTrace]
  refine ⟨3036449894395959732177283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4048599859194612976236377 3036449894395959732177283)
  ·
    refine ⟨4554674841593939598265925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3036449894395959732177283 4554674841593939598265925)
    ·
      refine ⟨854001532798863674674861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4554674841593939598265925 854001532798863674674861)
      ·
        refine ⟨320250574799573878003073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 854001532798863674674861 320250574799573878003073)
        ·
          refine ⟨240187931099680408502305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 320250574799573878003073 240187931099680408502305)
          ·
            refine ⟨180140948324760306376729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 240187931099680408502305 180140948324760306376729)
            ·
              refine ⟨135105711243570229782547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 180140948324760306376729 135105711243570229782547)
              ·
                refine ⟨202658566865355344673821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 135105711243570229782547 202658566865355344673821)
                ·
                  refine ⟨75996962574508254252683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 202658566865355344673821 75996962574508254252683)
                  ·
                    rfl

theorem cell20_166504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 2, 2, 1, 3].length) (baseStart_166504 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_166504 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_166504 prefixEnd_166504 := by exact prefixLift 166504
  have htrace : WordTrace (prefixWord ++ tailWord_166504) baseStart_166504 baseEnd_166504 := by
    simpa [prefixWord, tailWord_166504, baseEnd_166504] using wordTrace_append hprefix tailTrace_166504
  have hstable : (prefixWord ++ tailWord_166504).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_166504).length < 2 ^ (prefixWord ++ tailWord_166504).sum := by decide
  have hdescent : baseEnd_166504 < baseStart_166504 := by decide
  rcases family_descends (prefixWord ++ tailWord_166504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_166508 : List Nat := [2, 2, 1, 1, 3, 1, 6, 1, 3]
def baseStart_166508 : Nat := 118140960795 + 166508 * 2 ^ 59
def prefixEnd_166508 : Nat := 4983230072969 + 3 ^ 40 * 166508 * 2
def baseEnd_166508 : Nat := 75998788283502018119333

theorem tailTrace_166508 : CollatzResearch.WordTrace tailWord_166508 prefixEnd_166508 75998788283502018119333 := by
  unfold tailWord_166508
  simp only [CollatzResearch.WordTrace]
  refine ⟨3036522840388714073750089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4048697120518285431666785 3036522840388714073750089)
  ·
    refine ⟨2277392130291535555312567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3036522840388714073750089 2277392130291535555312567)
    ·
      refine ⟨3416088195437303332968851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2277392130291535555312567 3416088195437303332968851)
      ·
        refine ⟨5124132293155954999453277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3416088195437303332968851 5124132293155954999453277)
        ·
          refine ⟨1921549609933483124794979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5124132293155954999453277 1921549609933483124794979)
          ·
            refine ⟨2882324414900224687192469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1921549609933483124794979 2882324414900224687192469)
            ·
              refine ⟨135108956948448032212147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 2882324414900224687192469 135108956948448032212147)
              ·
                refine ⟨202663435422672048318221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 135108956948448032212147 202663435422672048318221)
                ·
                  refine ⟨75998788283502018119333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 202663435422672048318221 75998788283502018119333)
                  ·
                    rfl

theorem cell20_166508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 3].length) (baseStart_166508 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_166508 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_166508 prefixEnd_166508 := by exact prefixLift 166508
  have htrace : WordTrace (prefixWord ++ tailWord_166508) baseStart_166508 baseEnd_166508 := by
    simpa [prefixWord, tailWord_166508, baseEnd_166508] using wordTrace_append hprefix tailTrace_166508
  have hstable : (prefixWord ++ tailWord_166508).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_166508).length < 2 ^ (prefixWord ++ tailWord_166508).sum := by decide
  have hdescent : baseEnd_166508 < baseStart_166508 := by decide
  rcases family_descends (prefixWord ++ tailWord_166508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_166546 : List Nat := [3, 2, 3, 1, 2, 1, 1, 4, 3]
def baseStart_166546 : Nat := 118140960795 + 166546 * 2 ^ 59
def prefixEnd_166546 : Nat := 4983230072969 + 3 ^ 40 * 166546 * 2
def baseEnd_166546 : Nat := 76016132518942774852511

theorem tailTrace_166546 : CollatzResearch.WordTrace tailWord_166546 prefixEnd_166546 76016132518942774852511 := by
  unfold tailWord_166546
  simp only [CollatzResearch.WordTrace]
  refine ⟨1518607913659940159345873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4049621103093173758255661 1518607913659940159345873)
  ·
    refine ⟨1138955935244955119509405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1518607913659940159345873 1138955935244955119509405)
    ·
      refine ⟨427108475716858169816027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1138955935244955119509405 427108475716858169816027)
      ·
        refine ⟨640662713575287254724041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 427108475716858169816027 640662713575287254724041)
        ·
          refine ⟨480497035181465441043031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 640662713575287254724041 480497035181465441043031)
          ·
            refine ⟨720745552772198161564547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 480497035181465441043031 720745552772198161564547)
            ·
              refine ⟨1081118329158297242346821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 720745552772198161564547 1081118329158297242346821)
              ·
                refine ⟨202709686717180732940029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1081118329158297242346821 202709686717180732940029)
                ·
                  refine ⟨76016132518942774852511, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 202709686717180732940029 76016132518942774852511)
                  ·
                    rfl

theorem cell20_166546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 1, 4, 3].length) (baseStart_166546 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_166546 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_166546 prefixEnd_166546 := by exact prefixLift 166546
  have htrace : WordTrace (prefixWord ++ tailWord_166546) baseStart_166546 baseEnd_166546 := by
    simpa [prefixWord, tailWord_166546, baseEnd_166546] using wordTrace_append hprefix tailTrace_166546
  have hstable : (prefixWord ++ tailWord_166546).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_166546).length < 2 ^ (prefixWord ++ tailWord_166546).sum := by decide
  have hdescent : baseEnd_166546 < baseStart_166546 := by decide
  rcases family_descends (prefixWord ++ tailWord_166546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_166553 : List Nat := [1, 2, 1, 2, 1, 2, 5, 4, 2]
def baseStart_166553 : Nat := 118140960795 + 166553 * 2 ^ 59
def prefixEnd_166553 : Nat := 4983230072969 + 3 ^ 40 * 166553 * 2
def baseEnd_166553 : Nat := 76019327509681861619149

theorem tailTrace_166553 : CollatzResearch.WordTrace tailWord_166553 prefixEnd_166553 76019327509681861619149 := by
  unfold tailWord_166553
  simp only [CollatzResearch.WordTrace]
  refine ⟨6074686965614400832888313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4049791310409600555258875 6074686965614400832888313)
  ·
    refine ⟨4556015224210800624666235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6074686965614400832888313 4556015224210800624666235)
    ·
      refine ⟨6834022836316200936999353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4556015224210800624666235 6834022836316200936999353)
      ·
        refine ⟨5125517127237150702749515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6834022836316200936999353 5125517127237150702749515)
        ·
          refine ⟨7688275690855726054124273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5125517127237150702749515 7688275690855726054124273)
          ·
            refine ⟨5766206768141794540593205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7688275690855726054124273 5766206768141794540593205)
            ·
              refine ⟨540581884513293238180613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 5766206768141794540593205 540581884513293238180613)
              ·
                refine ⟨101359103346242482158865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 540581884513293238180613 101359103346242482158865)
                ·
                  refine ⟨76019327509681861619149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 101359103346242482158865 76019327509681861619149)
                  ·
                    rfl

theorem cell20_166553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 5, 4, 2].length) (baseStart_166553 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_166553 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_166553 prefixEnd_166553 := by exact prefixLift 166553
  have htrace : WordTrace (prefixWord ++ tailWord_166553) baseStart_166553 baseEnd_166553 := by
    simpa [prefixWord, tailWord_166553, baseEnd_166553] using wordTrace_append hprefix tailTrace_166553
  have hstable : (prefixWord ++ tailWord_166553).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_166553).length < 2 ^ (prefixWord ++ tailWord_166553).sum := by decide
  have hdescent : baseEnd_166553 < baseStart_166553 := by decide
  rcases family_descends (prefixWord ++ tailWord_166553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_166591 : List Nat := [1, 1, 2, 2, 2, 4, 1, 5, 2]
def baseStart_166591 : Nat := 118140960795 + 166591 * 2 ^ 59
def prefixEnd_166591 : Nat := 4983230072969 + 3 ^ 40 * 166591 * 2
def baseEnd_166591 : Nat := 76036671745122618352327

theorem tailTrace_166591 : CollatzResearch.WordTrace tailWord_166591 prefixEnd_166591 76036671745122618352327 := by
  unfold tailWord_166591
  simp only [CollatzResearch.WordTrace]
  refine ⟨6076072939476733322771627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4050715292984488881847751 6076072939476733322771627)
  ·
    refine ⟨9114109409215099984157441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6076072939476733322771627 9114109409215099984157441)
    ·
      refine ⟨6835582056911324988118081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9114109409215099984157441 6835582056911324988118081)
      ·
        refine ⟨5126686542683493741088561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6835582056911324988118081 5126686542683493741088561)
        ·
          refine ⟨3845014907012620305816421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5126686542683493741088561 3845014907012620305816421)
          ·
            refine ⟨720940295064866307340579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3845014907012620305816421 720940295064866307340579)
            ·
              refine ⟨1081410442597299461010869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 720940295064866307340579 1081410442597299461010869)
              ·
                refine ⟨101382228993496824469769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1081410442597299461010869 101382228993496824469769)
                ·
                  refine ⟨76036671745122618352327, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 101382228993496824469769 76036671745122618352327)
                  ·
                    rfl

theorem cell20_166591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 1, 5, 2].length) (baseStart_166591 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_166591 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_166591 prefixEnd_166591 := by exact prefixLift 166591
  have htrace : WordTrace (prefixWord ++ tailWord_166591) baseStart_166591 baseEnd_166591 := by
    simpa [prefixWord, tailWord_166591, baseEnd_166591] using wordTrace_append hprefix tailTrace_166591
  have hstable : (prefixWord ++ tailWord_166591).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_166591).length < 2 ^ (prefixWord ++ tailWord_166591).sum := by decide
  have hdescent : baseEnd_166591 < baseStart_166591 := by decide
  rcases family_descends (prefixWord ++ tailWord_166591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_166632 : List Nat := [2, 1, 4, 1, 5, 1, 2, 4]
def baseStart_166632 : Nat := 118140960795 + 166632 * 2 ^ 59
def prefixEnd_166632 : Nat := 4983230072969 + 3 ^ 40 * 166632 * 2
def baseEnd_166632 : Nat := 25351795087436232661831

theorem tailTrace_166632 : CollatzResearch.WordTrace tailWord_166632 prefixEnd_166632 25351795087436232661831 := by
  unfold tailWord_166632
  simp only [CollatzResearch.WordTrace]
  refine ⟨3038784166164098662507075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4051712221552131550009433 3038784166164098662507075)
  ·
    refine ⟨4558176249246147993760613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3038784166164098662507075 4558176249246147993760613)
    ·
      refine ⟨854658046733652748830115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4558176249246147993760613 854658046733652748830115)
      ·
        refine ⟨1281987070100479123245173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 854658046733652748830115 1281987070100479123245173)
        ·
          refine ⟨120186287821919917804235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 1281987070100479123245173 120186287821919917804235)
          ·
            refine ⟨180279431732879876706353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 120186287821919917804235 180279431732879876706353)
            ·
              refine ⟨135209573799659907529765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 180279431732879876706353 135209573799659907529765)
              ·
                refine ⟨25351795087436232661831, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 135209573799659907529765 25351795087436232661831)
                ·
                  rfl

theorem cell20_166632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 5, 1, 2, 4].length) (baseStart_166632 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_166632 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_166632 prefixEnd_166632 := by exact prefixLift 166632
  have htrace : WordTrace (prefixWord ++ tailWord_166632) baseStart_166632 baseEnd_166632 := by
    simpa [prefixWord, tailWord_166632, baseEnd_166632] using wordTrace_append hprefix tailTrace_166632
  have hstable : (prefixWord ++ tailWord_166632).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_166632).length < 2 ^ (prefixWord ++ tailWord_166632).sum := by decide
  have hdescent : baseEnd_166632 < baseStart_166632 := by decide
  rcases family_descends (prefixWord ++ tailWord_166632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_166663 : List Nat := [1, 1, 4, 4, 1, 2, 3, 2, 2]
def baseStart_166663 : Nat := 118140960795 + 166663 * 2 ^ 59
def prefixEnd_166663 : Nat := 4983230072969 + 3 ^ 40 * 166663 * 2
def baseEnd_166663 : Nat := 76069534507010367952033

theorem tailTrace_166663 : CollatzResearch.WordTrace tailWord_166663 prefixEnd_166663 76069534507010367952033 := by
  unfold tailWord_166663
  simp only [CollatzResearch.WordTrace]
  refine ⟨6078698995215889619392643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4052465996810593079595095 6078698995215889619392643)
  ·
    refine ⟨9118048492823834429088965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6078698995215889619392643 9118048492823834429088965)
    ·
      refine ⟨1709634092404468955454181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9118048492823834429088965 1709634092404468955454181)
      ·
        refine ⟨320556392325837929147659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1709634092404468955454181 320556392325837929147659)
        ·
          refine ⟨480834588488756893721489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 320556392325837929147659 480834588488756893721489)
          ·
            refine ⟨360625941366567670291117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 480834588488756893721489 360625941366567670291117)
            ·
              refine ⟨135234728012462876359169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 360625941366567670291117 135234728012462876359169)
              ·
                refine ⟨101426046009347157269377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 135234728012462876359169 101426046009347157269377)
                ·
                  refine ⟨76069534507010367952033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 101426046009347157269377 76069534507010367952033)
                  ·
                    rfl

theorem cell20_166663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 2, 3, 2, 2].length) (baseStart_166663 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_166663 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_166663 prefixEnd_166663 := by exact prefixLift 166663
  have htrace : WordTrace (prefixWord ++ tailWord_166663) baseStart_166663 baseEnd_166663 := by
    simpa [prefixWord, tailWord_166663, baseEnd_166663] using wordTrace_append hprefix tailTrace_166663
  have hstable : (prefixWord ++ tailWord_166663).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_166663).length < 2 ^ (prefixWord ++ tailWord_166663).sum := by decide
  have hdescent : baseEnd_166663 < baseStart_166663 := by decide
  rcases family_descends (prefixWord ++ tailWord_166663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_166705 : List Nat := [1, 2, 2, 3, 2, 1, 2, 5, 2]
def baseStart_166705 : Nat := 118140960795 + 166705 * 2 ^ 59
def prefixEnd_166705 : Nat := 4983230072969 + 3 ^ 40 * 166705 * 2
def baseEnd_166705 : Nat := 76088704451444888551861

theorem tailTrace_166705 : CollatzResearch.WordTrace tailWord_166705 prefixEnd_166705 76088704451444888551861 := by
  unfold tailWord_166705
  simp only [CollatzResearch.WordTrace]
  refine ⟨6080230861063730792421569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4053487240709153861614379 6080230861063730792421569)
  ·
    refine ⟨4560173145797798094316177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6080230861063730792421569 4560173145797798094316177)
    ·
      refine ⟨3420129859348348570737133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4560173145797798094316177 3420129859348348570737133)
      ·
        refine ⟨1282548697255630714026425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3420129859348348570737133 1282548697255630714026425)
        ·
          refine ⟨961911522941723035519819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1282548697255630714026425 961911522941723035519819)
          ·
            refine ⟨1442867284412584553279729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 961911522941723035519819 1442867284412584553279729)
            ·
              refine ⟨1082150463309438414959797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1442867284412584553279729 1082150463309438414959797)
              ·
                refine ⟨101451605935259851402481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1082150463309438414959797 101451605935259851402481)
                ·
                  refine ⟨76088704451444888551861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 101451605935259851402481 76088704451444888551861)
                  ·
                    rfl

theorem cell20_166705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 2, 5, 2].length) (baseStart_166705 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_166705 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_166705 prefixEnd_166705 := by exact prefixLift 166705
  have htrace : WordTrace (prefixWord ++ tailWord_166705) baseStart_166705 baseEnd_166705 := by
    simpa [prefixWord, tailWord_166705, baseEnd_166705] using wordTrace_append hprefix tailTrace_166705
  have hstable : (prefixWord ++ tailWord_166705).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_166705).length < 2 ^ (prefixWord ++ tailWord_166705).sum := by decide
  have hdescent : baseEnd_166705 < baseStart_166705 := by decide
  rcases family_descends (prefixWord ++ tailWord_166705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_166718 : List Nat := [4, 2, 1, 2, 3, 2, 2, 2, 2]
def baseStart_166718 : Nat := 118140960795 + 166718 * 2 ^ 59
def prefixEnd_166718 : Nat := 4983230072969 + 3 ^ 40 * 166718 * 2
def baseEnd_166718 : Nat := 76094638005674621118475

theorem tailTrace_166718 : CollatzResearch.WordTrace tailWord_166718 prefixEnd_166718 76094638005674621118475 := by
  unfold tailWord_166718
  simp only [CollatzResearch.WordTrace]
  refine ⟨760088126252079251580601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4053803340011089341763205 760088126252079251580601)
  ·
    refine ⟨570066094689059438685451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 760088126252079251580601 570066094689059438685451)
    ·
      refine ⟨855099142033589158028177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 570066094689059438685451 855099142033589158028177)
      ·
        refine ⟨641324356525191868521133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 855099142033589158028177 641324356525191868521133)
        ·
          refine ⟨240496633696946950695425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 641324356525191868521133 240496633696946950695425)
          ·
            refine ⟨180372475272710213021569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 240496633696946950695425 180372475272710213021569)
            ·
              refine ⟨135279356454532659766177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 180372475272710213021569 135279356454532659766177)
              ·
                refine ⟨101459517340899494824633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 135279356454532659766177 101459517340899494824633)
                ·
                  refine ⟨76094638005674621118475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 101459517340899494824633 76094638005674621118475)
                  ·
                    rfl

theorem cell20_166718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 2, 2, 2, 2].length) (baseStart_166718 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_166718 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_166718 prefixEnd_166718 := by exact prefixLift 166718
  have htrace : WordTrace (prefixWord ++ tailWord_166718) baseStart_166718 baseEnd_166718 := by
    simpa [prefixWord, tailWord_166718, baseEnd_166718] using wordTrace_append hprefix tailTrace_166718
  have hstable : (prefixWord ++ tailWord_166718).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_166718).length < 2 ^ (prefixWord ++ tailWord_166718).sum := by decide
  have hdescent : baseEnd_166718 < baseStart_166718 := by decide
  rcases family_descends (prefixWord ++ tailWord_166718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_166719 : List Nat := [1, 1, 2, 2, 5, 1, 1, 4, 3]
def baseStart_166719 : Nat := 118140960795 + 166719 * 2 ^ 59
def prefixEnd_166719 : Nat := 4983230072969 + 3 ^ 40 * 166719 * 2
def baseEnd_166719 : Nat := 76095094432923062085137

theorem tailTrace_166719 : CollatzResearch.WordTrace tailWord_166719 prefixEnd_166719 76095094432923062085137 := by
  unfold tailWord_166719
  simp only [CollatzResearch.WordTrace]
  refine ⟨6080741483013011183431211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4053827655342007455620807 6080741483013011183431211)
  ·
    refine ⟨9121112224519516775146817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6080741483013011183431211 9121112224519516775146817)
    ·
      refine ⟨6840834168389637581360113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9121112224519516775146817 6840834168389637581360113)
      ·
        refine ⟨5130625626292228186020085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6840834168389637581360113 5130625626292228186020085)
        ·
          refine ⟨480996152464896392439383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 5130625626292228186020085 480996152464896392439383)
          ·
            refine ⟨721494228697344588659075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 480996152464896392439383 721494228697344588659075)
            ·
              refine ⟨1082241343046016882988613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 721494228697344588659075 1082241343046016882988613)
              ·
                refine ⟨202920251821128165560365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1082241343046016882988613 202920251821128165560365)
                ·
                  refine ⟨76095094432923062085137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 202920251821128165560365 76095094432923062085137)
                  ·
                    rfl

theorem cell20_166719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 1, 4, 3].length) (baseStart_166719 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_166719 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_166719 prefixEnd_166719 := by exact prefixLift 166719
  have htrace : WordTrace (prefixWord ++ tailWord_166719) baseStart_166719 baseEnd_166719 := by
    simpa [prefixWord, tailWord_166719, baseEnd_166719] using wordTrace_append hprefix tailTrace_166719
  have hstable : (prefixWord ++ tailWord_166719).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_166719).length < 2 ^ (prefixWord ++ tailWord_166719).sum := by decide
  have hdescent : baseEnd_166719 < baseStart_166719 := by decide
  rcases family_descends (prefixWord ++ tailWord_166719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_166760 : List Nat := [2, 1, 4, 2, 1, 3, 2, 3, 2]
def baseStart_166760 : Nat := 118140960795 + 166760 * 2 ^ 59
def prefixEnd_166760 : Nat := 4983230072969 + 3 ^ 40 * 166760 * 2
def baseEnd_166760 : Nat := 76113807950109141718303

theorem tailTrace_166760 : CollatzResearch.WordTrace tailWord_166760 prefixEnd_166760 76113807950109141718303 := by
  unfold tailWord_166760
  simp only [CollatzResearch.WordTrace]
  refine ⟨3041118437932237592836867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4054824583909650123782489 3041118437932237592836867)
  ·
    refine ⟨4561677656898356389255301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3041118437932237592836867 4561677656898356389255301)
    ·
      refine ⟨855314560668441822985369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4561677656898356389255301 855314560668441822985369)
      ·
        refine ⟨641485920501331367239027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 855314560668441822985369 641485920501331367239027)
        ·
          refine ⟨962228880751997050858541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 641485920501331367239027 962228880751997050858541)
          ·
            refine ⟨360835830281998894071953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 962228880751997050858541 360835830281998894071953)
            ·
              refine ⟨270626872711499170553965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 360835830281998894071953 270626872711499170553965)
              ·
                refine ⟨101485077266812188957737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 270626872711499170553965 101485077266812188957737)
                ·
                  refine ⟨76113807950109141718303, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 101485077266812188957737 76113807950109141718303)
                  ·
                    rfl

theorem cell20_166760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 3, 2, 3, 2].length) (baseStart_166760 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_166760 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_166760 prefixEnd_166760 := by exact prefixLift 166760
  have htrace : WordTrace (prefixWord ++ tailWord_166760) baseStart_166760 baseEnd_166760 := by
    simpa [prefixWord, tailWord_166760, baseEnd_166760] using wordTrace_append hprefix tailTrace_166760
  have hstable : (prefixWord ++ tailWord_166760).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_166760).length < 2 ^ (prefixWord ++ tailWord_166760).sum := by decide
  have hdescent : baseEnd_166760 < baseStart_166760 := by decide
  rcases family_descends (prefixWord ++ tailWord_166760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_166774 : List Nat := [5, 1, 1, 3, 1, 2, 1, 1, 5]
def baseStart_166774 : Nat := 118140960795 + 166774 * 2 ^ 59
def prefixEnd_166774 : Nat := 4983230072969 + 3 ^ 40 * 166774 * 2
def baseEnd_166774 : Nat := 76120197931587315251579

theorem tailTrace_166774 : CollatzResearch.WordTrace tailWord_166774 prefixEnd_166774 76120197931587315251579 := by
  unfold tailWord_166774
  simp only [CollatzResearch.WordTrace]
  refine ⟨380171718613359723542711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 4055164998542503717788917 380171718613359723542711)
  ·
    refine ⟨570257577920039585314067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 380171718613359723542711 570257577920039585314067)
    ·
      refine ⟨855386366880059377971101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 570257577920039585314067 855386366880059377971101)
      ·
        refine ⟨320769887580022266739163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 855386366880059377971101 320769887580022266739163)
        ·
          refine ⟨481154831370033400108745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 320769887580022266739163 481154831370033400108745)
          ·
            refine ⟨360866123527525050081559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 481154831370033400108745 360866123527525050081559)
            ·
              refine ⟨541299185291287575122339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 360866123527525050081559 541299185291287575122339)
              ·
                refine ⟨811948777936931362683509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 541299185291287575122339 811948777936931362683509)
                ·
                  refine ⟨76120197931587315251579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 811948777936931362683509 76120197931587315251579)
                  ·
                    rfl

theorem cell20_166774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 2, 1, 1, 5].length) (baseStart_166774 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_166774 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_166774 prefixEnd_166774 := by exact prefixLift 166774
  have htrace : WordTrace (prefixWord ++ tailWord_166774) baseStart_166774 baseEnd_166774 := by
    simpa [prefixWord, tailWord_166774, baseEnd_166774] using wordTrace_append hprefix tailTrace_166774
  have hstable : (prefixWord ++ tailWord_166774).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_166774).length < 2 ^ (prefixWord ++ tailWord_166774).sum := by decide
  have hdescent : baseEnd_166774 < baseStart_166774 := by decide
  rcases family_descends (prefixWord ++ tailWord_166774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_166781 : List Nat := [1, 4, 1, 1, 2, 1, 4, 4, 2]
def baseStart_166781 : Nat := 118140960795 + 166781 * 2 ^ 59
def prefixEnd_166781 : Nat := 4983230072969 + 3 ^ 40 * 166781 * 2
def baseEnd_166781 : Nat := 76123392922326402018217

theorem tailTrace_166781 : CollatzResearch.WordTrace tailWord_166781 prefixEnd_166781 76123392922326402018217 := by
  unfold tailWord_166781
  simp only [CollatzResearch.WordTrace]
  refine ⟨6083002808788395772188197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4055335205858930514792131 6083002808788395772188197)
  ·
    refine ⟨1140563026647824207285287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6083002808788395772188197 1140563026647824207285287)
    ·
      refine ⟨1710844539971736310927931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1140563026647824207285287 1710844539971736310927931)
      ·
        refine ⟨2566266809957604466391897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1710844539971736310927931 2566266809957604466391897)
        ·
          refine ⟨1924700107468203349793923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2566266809957604466391897 1924700107468203349793923)
          ·
            refine ⟨2887050161202305024690885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1924700107468203349793923 2887050161202305024690885)
            ·
              refine ⟨541321905225432192129541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2887050161202305024690885 541321905225432192129541)
              ·
                refine ⟨101497857229768536024289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 541321905225432192129541 101497857229768536024289)
                ·
                  refine ⟨76123392922326402018217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 101497857229768536024289 76123392922326402018217)
                  ·
                    rfl

theorem cell20_166781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 4, 4, 2].length) (baseStart_166781 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_166781 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_166781 prefixEnd_166781 := by exact prefixLift 166781
  have htrace : WordTrace (prefixWord ++ tailWord_166781) baseStart_166781 baseEnd_166781 := by
    simpa [prefixWord, tailWord_166781, baseEnd_166781] using wordTrace_append hprefix tailTrace_166781
  have hstable : (prefixWord ++ tailWord_166781).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_166781).length < 2 ^ (prefixWord ++ tailWord_166781).sum := by decide
  have hdescent : baseEnd_166781 < baseStart_166781 := by decide
  rcases family_descends (prefixWord ++ tailWord_166781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_166816 : List Nat := [2, 1, 1, 4, 1, 1, 3, 2, 5]
def baseStart_166816 : Nat := 118140960795 + 166816 * 2 ^ 59
def prefixEnd_166816 : Nat := 4983230072969 + 3 ^ 40 * 166816 * 2
def baseEnd_166816 : Nat := 76139367876021835851407

theorem tailTrace_166816 : CollatzResearch.WordTrace tailWord_166816 prefixEnd_166816 76139367876021835851407 := by
  unfold tailWord_166816
  simp only [CollatzResearch.WordTrace]
  refine ⟨3042139681830798374856151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4056186242441064499808201 3042139681830798374856151)
  ·
    refine ⟨4563209522746197562284227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3042139681830798374856151 4563209522746197562284227)
    ·
      refine ⟨6844814284119296343426341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4563209522746197562284227 6844814284119296343426341)
      ·
        refine ⟨1283402678272368064392439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6844814284119296343426341 1283402678272368064392439)
        ·
          refine ⟨1925104017408552096588659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1283402678272368064392439 1925104017408552096588659)
          ·
            refine ⟨2887656026112828144882989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1925104017408552096588659 2887656026112828144882989)
            ·
              refine ⟨1082871009792310554331121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2887656026112828144882989 1082871009792310554331121)
              ·
                refine ⟨812153257344232915748341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1082871009792310554331121 812153257344232915748341)
                ·
                  refine ⟨76139367876021835851407, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 812153257344232915748341 76139367876021835851407)
                  ·
                    rfl

theorem cell20_166816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 3, 2, 5].length) (baseStart_166816 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_166816 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_166816 prefixEnd_166816 := by exact prefixLift 166816
  have htrace : WordTrace (prefixWord ++ tailWord_166816) baseStart_166816 baseEnd_166816 := by
    simpa [prefixWord, tailWord_166816, baseEnd_166816] using wordTrace_append hprefix tailTrace_166816
  have hstable : (prefixWord ++ tailWord_166816).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_166816).length < 2 ^ (prefixWord ++ tailWord_166816).sum := by decide
  have hdescent : baseEnd_166816 < baseStart_166816 := by decide
  rcases family_descends (prefixWord ++ tailWord_166816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_166819 : List Nat := [1, 1, 1, 4, 1, 2, 5, 3, 2]
def baseStart_166819 : Nat := 118140960795 + 166819 * 2 ^ 59
def prefixEnd_166819 : Nat := 4983230072969 + 3 ^ 40 * 166819 * 2
def baseEnd_166819 : Nat := 76140737157767158751395

theorem tailTrace_166819 : CollatzResearch.WordTrace tailWord_166819 prefixEnd_166819 76140737157767158751395 := by
  unfold tailWord_166819
  simp only [CollatzResearch.WordTrace]
  refine ⟨6084388782650728262071511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4056259188433818841381007 6084388782650728262071511)
  ·
    refine ⟨9126583173976092393107267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6084388782650728262071511 9126583173976092393107267)
    ·
      refine ⟨13689874760964138589660901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9126583173976092393107267 13689874760964138589660901)
      ·
        refine ⟨2566851517680775985561419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13689874760964138589660901 2566851517680775985561419)
        ·
          refine ⟨3850277276521163978342129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2566851517680775985561419 3850277276521163978342129)
          ·
            refine ⟨2887707957390872983756597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3850277276521163978342129 2887707957390872983756597)
            ·
              refine ⟨270722621005394342227181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2887707957390872983756597 270722621005394342227181)
              ·
                refine ⟨101520982877022878335193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 270722621005394342227181 101520982877022878335193)
                ·
                  refine ⟨76140737157767158751395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 101520982877022878335193 76140737157767158751395)
                  ·
                    rfl

theorem cell20_166819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 5, 3, 2].length) (baseStart_166819 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_166819 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_166819 prefixEnd_166819 := by exact prefixLift 166819
  have htrace : WordTrace (prefixWord ++ tailWord_166819) baseStart_166819 baseEnd_166819 := by
    simpa [prefixWord, tailWord_166819, baseEnd_166819] using wordTrace_append hprefix tailTrace_166819
  have hstable : (prefixWord ++ tailWord_166819).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_166819).length < 2 ^ (prefixWord ++ tailWord_166819).sum := by decide
  have hdescent : baseEnd_166819 < baseStart_166819 := by decide
  rcases family_descends (prefixWord ++ tailWord_166819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_166836 : List Nat := [2, 5, 2, 1, 1, 1, 3, 1, 4]
def baseStart_166836 : Nat := 118140960795 + 166836 * 2 ^ 59
def prefixEnd_166836 : Nat := 4983230072969 + 3 ^ 40 * 166836 * 2
def baseEnd_166836 : Nat := 76148496420990655184659

theorem tailTrace_166836 : CollatzResearch.WordTrace tailWord_166836 prefixEnd_166836 76148496420990655184659 := by
  unfold tailWord_166836
  simp only [CollatzResearch.WordTrace]
  refine ⟨3042504411794570082720181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4056672549059426776960241 3042504411794570082720181)
  ·
    refine ⟨285234788605740945255017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 3042504411794570082720181 285234788605740945255017)
    ·
      refine ⟨213926091454305708941263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 285234788605740945255017 213926091454305708941263)
      ·
        refine ⟨320889137181458563411895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 213926091454305708941263 320889137181458563411895)
        ·
          refine ⟨481333705772187845117843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 320889137181458563411895 481333705772187845117843)
          ·
            refine ⟨722000558658281767676765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 481333705772187845117843 722000558658281767676765)
            ·
              refine ⟨270750209496855662878787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 722000558658281767676765 270750209496855662878787)
              ·
                refine ⟨406125314245283494318181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 270750209496855662878787 406125314245283494318181)
                ·
                  refine ⟨76148496420990655184659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 406125314245283494318181 76148496420990655184659)
                  ·
                    rfl

theorem cell20_166836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 3, 1, 4].length) (baseStart_166836 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_166836 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_166836 prefixEnd_166836 := by exact prefixLift 166836
  have htrace : WordTrace (prefixWord ++ tailWord_166836) baseStart_166836 baseEnd_166836 := by
    simpa [prefixWord, tailWord_166836, baseEnd_166836] using wordTrace_append hprefix tailTrace_166836
  have hstable : (prefixWord ++ tailWord_166836).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_166836).length < 2 ^ (prefixWord ++ tailWord_166836).sum := by decide
  have hdescent : baseEnd_166836 < baseStart_166836 := by decide
  rcases family_descends (prefixWord ++ tailWord_166836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_166840 : List Nat := [2, 1, 2, 1, 2, 4, 3, 1, 4]
def baseStart_166840 : Nat := 118140960795 + 166840 * 2 ^ 59
def prefixEnd_166840 : Nat := 4983230072969 + 3 ^ 40 * 166840 * 2
def baseEnd_166840 : Nat := 76150322129984419051309

theorem tailTrace_166840 : CollatzResearch.WordTrace tailWord_166840 prefixEnd_166840 76150322129984419051309 := by
  unfold tailWord_166840
  simp only [CollatzResearch.WordTrace]
  refine ⟨3042577357787324424292987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4056769810383099232390649 3042577357787324424292987)
  ·
    refine ⟨4563866036680986636439481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3042577357787324424292987 4563866036680986636439481)
    ·
      refine ⟨3422899527510739977329611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4563866036680986636439481 3422899527510739977329611)
      ·
        refine ⟨5134349291266109965994417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3422899527510739977329611 5134349291266109965994417)
        ·
          refine ⟨3850761968449582474495813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5134349291266109965994417 3850761968449582474495813)
          ·
            refine ⟨722017869084296713967965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3850761968449582474495813 722017869084296713967965)
            ·
              refine ⟨270756700906611267737987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 722017869084296713967965 270756700906611267737987)
              ·
                refine ⟨406135051359916901606981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 270756700906611267737987 406135051359916901606981)
                ·
                  refine ⟨76150322129984419051309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 406135051359916901606981 76150322129984419051309)
                  ·
                    rfl

theorem cell20_166840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 3, 1, 4].length) (baseStart_166840 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_166840 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_166840 prefixEnd_166840 := by exact prefixLift 166840
  have htrace : WordTrace (prefixWord ++ tailWord_166840) baseStart_166840 baseEnd_166840 := by
    simpa [prefixWord, tailWord_166840, baseEnd_166840] using wordTrace_append hprefix tailTrace_166840
  have hstable : (prefixWord ++ tailWord_166840).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_166840).length < 2 ^ (prefixWord ++ tailWord_166840).sum := by decide
  have hdescent : baseEnd_166840 < baseStart_166840 := by decide
  rcases family_descends (prefixWord ++ tailWord_166840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_166885 : List Nat := [1, 3, 1, 6, 9]
def baseStart_166885 : Nat := 118140960795 + 166885 * 2 ^ 59
def prefixEnd_166885 : Nat := 4983230072969 + 3 ^ 40 * 166885 * 2
def baseEnd_166885 : Nat := 940381004397089661125

theorem tailTrace_166885 : CollatzResearch.WordTrace tailWord_166885 prefixEnd_166885 940381004397089661125 := by
  unfold tailWord_166885
  simp only [CollatzResearch.WordTrace]
  refine ⟨6086796000411621533974109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4057864000274414355982739 6086796000411621533974109)
  ·
    refine ⟨2282548500154358075240291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6086796000411621533974109 2282548500154358075240291)
    ·
      refine ⟨3423822750231537112860437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2282548500154358075240291 3423822750231537112860437)
      ·
        refine ⟨160491691417103302165333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 3423822750231537112860437 160491691417103302165333)
        ·
          refine ⟨940381004397089661125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 9 160491691417103302165333 940381004397089661125)
          ·
            rfl

theorem cell20_166885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 9].length) (baseStart_166885 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_166885 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_166885 prefixEnd_166885 := by exact prefixLift 166885
  have htrace : WordTrace (prefixWord ++ tailWord_166885) baseStart_166885 baseEnd_166885 := by
    simpa [prefixWord, tailWord_166885, baseEnd_166885] using wordTrace_append hprefix tailTrace_166885
  have hstable : (prefixWord ++ tailWord_166885).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_166885).length < 2 ^ (prefixWord ++ tailWord_166885).sum := by decide
  have hdescent : baseEnd_166885 < baseStart_166885 := by decide
  rcases family_descends (prefixWord ++ tailWord_166885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_166895 : List Nat := [1, 1, 2, 1, 4, 4, 1, 4, 2]
def baseStart_166895 : Nat := 118140960795 + 166895 * 2 ^ 59
def prefixEnd_166895 : Nat := 4983230072969 + 3 ^ 40 * 166895 * 2
def baseEnd_166895 : Nat := 76175425628648672217751

theorem tailTrace_166895 : CollatzResearch.WordTrace tailWord_166895 prefixEnd_166895 76175425628648672217751 := by
  unfold tailWord_166895
  simp only [CollatzResearch.WordTrace]
  refine ⟨6087160730375393241838139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4058107153583595494558759 6087160730375393241838139)
  ·
    refine ⟨9130741095563089862757209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6087160730375393241838139 9130741095563089862757209)
    ·
      refine ⟨6848055821672317397067907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9130741095563089862757209 6848055821672317397067907)
      ·
        refine ⟨10272083732508476095601861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6848055821672317397067907 10272083732508476095601861)
        ·
          refine ⟨1926015699845339267925349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10272083732508476095601861 1926015699845339267925349)
          ·
            refine ⟨361127943721001112736003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1926015699845339267925349 361127943721001112736003)
            ·
              refine ⟨541691915581501669104005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 361127943721001112736003 541691915581501669104005)
              ·
                refine ⟨101567234171531562957001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 541691915581501669104005 101567234171531562957001)
                ·
                  refine ⟨76175425628648672217751, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 101567234171531562957001 76175425628648672217751)
                  ·
                    rfl

theorem cell20_166895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 4, 1, 4, 2].length) (baseStart_166895 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_166895 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_166895 prefixEnd_166895 := by exact prefixLift 166895
  have htrace : WordTrace (prefixWord ++ tailWord_166895) baseStart_166895 baseEnd_166895 := by
    simpa [prefixWord, tailWord_166895, baseEnd_166895] using wordTrace_append hprefix tailTrace_166895
  have hstable : (prefixWord ++ tailWord_166895).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_166895).length < 2 ^ (prefixWord ++ tailWord_166895).sum := by decide
  have hdescent : baseEnd_166895 < baseStart_166895 := by decide
  rcases family_descends (prefixWord ++ tailWord_166895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_166898 : List Nat := [3, 2, 1, 5, 2, 1, 1, 5]
def baseStart_166898 : Nat := 118140960795 + 166898 * 2 ^ 59
def prefixEnd_166898 : Nat := 4983230072969 + 3 ^ 40 * 166898 * 2
def baseEnd_166898 : Nat := 25392264970131331705913

theorem tailTrace_166898 : CollatzResearch.WordTrace tailWord_166898 prefixEnd_166898 25392264970131331705913 := by
  unfold tailWord_166898
  simp only [CollatzResearch.WordTrace]
  refine ⟨1521817537341131188549337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4058180099576349836131565 1521817537341131188549337)
  ·
    refine ⟨1141363153005848391412003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1521817537341131188549337 1141363153005848391412003)
    ·
      refine ⟨1712044729508772587118005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1141363153005848391412003 1712044729508772587118005)
      ·
        refine ⟨160504193391447430042313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 1712044729508772587118005 160504193391447430042313)
        ·
          refine ⟨120378145043585572531735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 160504193391447430042313 120378145043585572531735)
          ·
            refine ⟨180567217565378358797603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 120378145043585572531735 180567217565378358797603)
            ·
              refine ⟨270850826348067538196405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 180567217565378358797603 270850826348067538196405)
              ·
                refine ⟨25392264970131331705913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 270850826348067538196405 25392264970131331705913)
                ·
                  rfl

theorem cell20_166898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 2, 1, 1, 5].length) (baseStart_166898 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_166898 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_166898 prefixEnd_166898 := by exact prefixLift 166898
  have htrace : WordTrace (prefixWord ++ tailWord_166898) baseStart_166898 baseEnd_166898 := by
    simpa [prefixWord, tailWord_166898, baseEnd_166898] using wordTrace_append hprefix tailTrace_166898
  have hstable : (prefixWord ++ tailWord_166898).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_166898).length < 2 ^ (prefixWord ++ tailWord_166898).sum := by decide
  have hdescent : baseEnd_166898 < baseStart_166898 := by decide
  rcases family_descends (prefixWord ++ tailWord_166898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_166902 : List Nat := [5, 1, 1, 1, 3, 1, 3, 5]
def baseStart_166902 : Nat := 118140960795 + 166902 * 2 ^ 59
def prefixEnd_166902 : Nat := 4983230072969 + 3 ^ 40 * 166902 * 2
def baseEnd_166902 : Nat := 25392873539795919661463

theorem tailTrace_166902 : CollatzResearch.WordTrace tailWord_166902 prefixEnd_166902 25392873539795919661463 := by
  unfold tailWord_166902
  simp only [CollatzResearch.WordTrace]
  refine ⟨380463502584377089833935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 4058277360900022291561973 380463502584377089833935)
  ·
    refine ⟨570695253876565634750903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 380463502584377089833935 570695253876565634750903)
    ·
      refine ⟨856042880814848452126355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 570695253876565634750903 856042880814848452126355)
      ·
        refine ⟨1284064321222272678189533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 856042880814848452126355 1284064321222272678189533)
        ·
          refine ⟨481524120458352254321075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1284064321222272678189533 481524120458352254321075)
          ·
            refine ⟨722286180687528381481613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 481524120458352254321075 722286180687528381481613)
            ·
              refine ⟨270857317757823143055605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 722286180687528381481613 270857317757823143055605)
              ·
                refine ⟨25392873539795919661463, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 270857317757823143055605 25392873539795919661463)
                ·
                  rfl

theorem cell20_166902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 3, 5].length) (baseStart_166902 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_166902 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_166902 prefixEnd_166902 := by exact prefixLift 166902
  have htrace : WordTrace (prefixWord ++ tailWord_166902) baseStart_166902 baseEnd_166902 := by
    simpa [prefixWord, tailWord_166902, baseEnd_166902] using wordTrace_append hprefix tailTrace_166902
  have hstable : (prefixWord ++ tailWord_166902).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_166902).length < 2 ^ (prefixWord ++ tailWord_166902).sum := by decide
  have hdescent : baseEnd_166902 < baseStart_166902 := by decide
  rcases family_descends (prefixWord ++ tailWord_166902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_166933 : List Nat := [1, 3, 2, 1, 4, 1, 1, 5, 2]
def baseStart_166933 : Nat := 118140960795 + 166933 * 2 ^ 59
def prefixEnd_166933 : Nat := 4983230072969 + 3 ^ 40 * 166933 * 2
def baseEnd_166933 : Nat := 76192769864089428950929

theorem tailTrace_166933 : CollatzResearch.WordTrace tailWord_166933 prefixEnd_166933 76192769864089428950929 := by
  unfold tailWord_166933
  simp only [CollatzResearch.WordTrace]
  refine ⟨6088546704237725731721453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4059031136158483821147635 6088546704237725731721453)
  ·
    refine ⟨2283205014089147149395545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6088546704237725731721453 2283205014089147149395545)
    ·
      refine ⟨1712403760566860362046659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2283205014089147149395545 1712403760566860362046659)
      ·
        refine ⟨2568605640850290543069989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1712403760566860362046659 2568605640850290543069989)
        ·
          refine ⟨481613557659429476825623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2568605640850290543069989 481613557659429476825623)
          ·
            refine ⟨722420336489144215238435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 481613557659429476825623 722420336489144215238435)
            ·
              refine ⟨1083630504733716322857653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 722420336489144215238435 1083630504733716322857653)
              ·
                refine ⟨101590359818785905267905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1083630504733716322857653 101590359818785905267905)
                ·
                  refine ⟨76192769864089428950929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 101590359818785905267905 76192769864089428950929)
                  ·
                    rfl

theorem cell20_166933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 1, 5, 2].length) (baseStart_166933 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_166933 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_166933 prefixEnd_166933 := by exact prefixLift 166933
  have htrace : WordTrace (prefixWord ++ tailWord_166933) baseStart_166933 baseEnd_166933 := by
    simpa [prefixWord, tailWord_166933, baseEnd_166933] using wordTrace_append hprefix tailTrace_166933
  have hstable : (prefixWord ++ tailWord_166933).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_166933).length < 2 ^ (prefixWord ++ tailWord_166933).sum := by decide
  have hdescent : baseEnd_166933 < baseStart_166933 := by decide
  rcases family_descends (prefixWord ++ tailWord_166933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_166947 : List Nat := [1, 1, 1, 4, 3, 2, 3, 2, 3]
def baseStart_166947 : Nat := 118140960795 + 166947 * 2 ^ 59
def prefixEnd_166947 : Nat := 4983230072969 + 3 ^ 40 * 166947 * 2
def baseEnd_166947 : Nat := 76199159845567602484205

theorem tailTrace_166947 : CollatzResearch.WordTrace tailWord_166947 prefixEnd_166947 76199159845567602484205 := by
  unfold tailWord_166947
  simp only [CollatzResearch.WordTrace]
  refine ⟨6089057326187006122731095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4059371550791337415154063 6089057326187006122731095)
  ·
    refine ⟨9133585989280509184096643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6089057326187006122731095 9133585989280509184096643)
    ·
      refine ⟨13700378983920763776144965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9133585989280509184096643 13700378983920763776144965)
      ·
        refine ⟨2568821059485143208027181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13700378983920763776144965 2568821059485143208027181)
        ·
          refine ⟨963307897306928703010193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2568821059485143208027181 963307897306928703010193)
          ·
            refine ⟨722480922980196527257645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 963307897306928703010193 722480922980196527257645)
            ·
              refine ⟨270930346117573697721617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 722480922980196527257645 270930346117573697721617)
              ·
                refine ⟨203197759588180273291213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 270930346117573697721617 203197759588180273291213)
                ·
                  refine ⟨76199159845567602484205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 203197759588180273291213 76199159845567602484205)
                  ·
                    rfl

theorem cell20_166947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 3, 2, 3].length) (baseStart_166947 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_166947 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_166947 prefixEnd_166947 := by exact prefixLift 166947
  have htrace : WordTrace (prefixWord ++ tailWord_166947) baseStart_166947 baseEnd_166947 := by
    simpa [prefixWord, tailWord_166947, baseEnd_166947] using wordTrace_append hprefix tailTrace_166947
  have hstable : (prefixWord ++ tailWord_166947).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_166947).length < 2 ^ (prefixWord ++ tailWord_166947).sum := by decide
  have hdescent : baseEnd_166947 < baseStart_166947 := by decide
  rcases family_descends (prefixWord ++ tailWord_166947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_167005 : List Nat := [1, 4, 4, 1, 3, 1, 1, 1, 4]
def baseStart_167005 : Nat := 118140960795 + 167005 * 2 ^ 59
def prefixEnd_167005 : Nat := 4983230072969 + 3 ^ 40 * 167005 * 2
def baseEnd_167005 : Nat := 76225632625977178550635

theorem tailTrace_167005 : CollatzResearch.WordTrace tailWord_167005 prefixEnd_167005 76225632625977178550635 := by
  unfold tailWord_167005
  simp only [CollatzResearch.WordTrace]
  refine ⟨6091172759976882028342469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4060781839984588018894979 6091172759976882028342469)
  ·
    refine ⟨1142094892495665380314213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6091172759976882028342469 1142094892495665380314213)
    ·
      refine ⟨214142792342937258808915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1142094892495665380314213 214142792342937258808915)
      ·
        refine ⟨321214188514405888213373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 214142792342937258808915 321214188514405888213373)
        ·
          refine ⟨120455320692902208080015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 321214188514405888213373 120455320692902208080015)
          ·
            refine ⟨180682981039353312120023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 120455320692902208080015 180682981039353312120023)
            ·
              refine ⟨271024471559029968180035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 180682981039353312120023 271024471559029968180035)
              ·
                refine ⟨406536707338544952270053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 271024471559029968180035 406536707338544952270053)
                ·
                  refine ⟨76225632625977178550635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 406536707338544952270053 76225632625977178550635)
                  ·
                    rfl

theorem cell20_167005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 3, 1, 1, 1, 4].length) (baseStart_167005 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_167005 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_167005 prefixEnd_167005 := by exact prefixLift 167005
  have htrace : WordTrace (prefixWord ++ tailWord_167005) baseStart_167005 baseEnd_167005 := by
    simpa [prefixWord, tailWord_167005, baseEnd_167005] using wordTrace_append hprefix tailTrace_167005
  have hstable : (prefixWord ++ tailWord_167005).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_167005).length < 2 ^ (prefixWord ++ tailWord_167005).sum := by decide
  have hdescent : baseEnd_167005 < baseStart_167005 := by decide
  rcases family_descends (prefixWord ++ tailWord_167005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_167030 : List Nat := [5, 1, 1, 2, 1, 1, 2, 1, 6]
def baseStart_167030 : Nat := 118140960795 + 167030 * 2 ^ 59
def prefixEnd_167030 : Nat := 4983230072969 + 3 ^ 40 * 167030 * 2
def baseEnd_167030 : Nat := 76237043307188202717199

theorem tailTrace_167030 : CollatzResearch.WordTrace tailWord_167030 prefixEnd_167030 76237043307188202717199 := by
  unfold tailWord_167030
  simp only [CollatzResearch.WordTrace]
  refine ⟨380755286555394456125159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 4061389723257540865335029 380755286555394456125159)
  ·
    refine ⟨571132929833091684187739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 380755286555394456125159 571132929833091684187739)
    ·
      refine ⟨856699394749637526281609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 571132929833091684187739 856699394749637526281609)
      ·
        refine ⟨642524546062228144711207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 856699394749637526281609 642524546062228144711207)
        ·
          refine ⟨963786819093342217066811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 642524546062228144711207 963786819093342217066811)
          ·
            refine ⟨1445680228640013325600217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 963786819093342217066811 1445680228640013325600217)
            ·
              refine ⟨1084260171480009994200163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1445680228640013325600217 1084260171480009994200163)
              ·
                refine ⟨1626390257220014991300245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1084260171480009994200163 1626390257220014991300245)
                ·
                  refine ⟨76237043307188202717199, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1626390257220014991300245 76237043307188202717199)
                  ·
                    rfl

theorem cell20_167030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 2, 1, 6].length) (baseStart_167030 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_167030 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_167030 prefixEnd_167030 := by exact prefixLift 167030
  have htrace : WordTrace (prefixWord ++ tailWord_167030) baseStart_167030 baseEnd_167030 := by
    simpa [prefixWord, tailWord_167030, baseEnd_167030] using wordTrace_append hprefix tailTrace_167030
  have hstable : (prefixWord ++ tailWord_167030).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_167030).length < 2 ^ (prefixWord ++ tailWord_167030).sum := by decide
  have hdescent : baseEnd_167030 < baseStart_167030 := by decide
  rcases family_descends (prefixWord ++ tailWord_167030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_167064 : List Nat := [2, 1, 2, 4, 2, 1, 4, 2, 2]
def baseStart_167064 : Nat := 118140960795 + 167064 * 2 ^ 59
def prefixEnd_167064 : Nat := 4983230072969 + 3 ^ 40 * 167064 * 2
def baseEnd_167064 : Nat := 76252561833635195583727

theorem tailTrace_167064 : CollatzResearch.WordTrace tailWord_167064 prefixEnd_167064 76252561833635195583727 := by
  unfold tailWord_167064
  simp only [CollatzResearch.WordTrace]
  refine ⟨3046662333381567552370123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4062216444508756736493497 3046662333381567552370123)
  ·
    refine ⟨4569993500072351328555185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3046662333381567552370123 4569993500072351328555185)
    ·
      refine ⟨3427495125054263496416389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4569993500072351328555185 3427495125054263496416389)
      ·
        refine ⟨642655335947674405578073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3427495125054263496416389 642655335947674405578073)
        ·
          refine ⟨481991501960755804183555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 642655335947674405578073 481991501960755804183555)
          ·
            refine ⟨722987252941133706275333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 481991501960755804183555 722987252941133706275333)
            ·
              refine ⟨135560109926462569926625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 722987252941133706275333 135560109926462569926625)
              ·
                refine ⟨101670082444846927444969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 135560109926462569926625 101670082444846927444969)
                ·
                  refine ⟨76252561833635195583727, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 101670082444846927444969 76252561833635195583727)
                  ·
                    rfl

theorem cell20_167064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 4, 2, 2].length) (baseStart_167064 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_167064 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_167064 prefixEnd_167064 := by exact prefixLift 167064
  have htrace : WordTrace (prefixWord ++ tailWord_167064) baseStart_167064 baseEnd_167064 := by
    simpa [prefixWord, tailWord_167064, baseEnd_167064] using wordTrace_append hprefix tailTrace_167064
  have hstable : (prefixWord ++ tailWord_167064).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_167064).length < 2 ^ (prefixWord ++ tailWord_167064).sum := by decide
  have hdescent : baseEnd_167064 < baseStart_167064 := by decide
  rcases family_descends (prefixWord ++ tailWord_167064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_167071 : List Nat := [1, 1, 2, 6, 3, 1, 1, 5]
def baseStart_167071 : Nat := 118140960795 + 167071 * 2 ^ 59
def prefixEnd_167071 : Nat := 4983230072969 + 3 ^ 40 * 167071 * 2
def baseEnd_167071 : Nat := 25418585608124760783455

theorem tailTrace_167071 : CollatzResearch.WordTrace tailWord_167071 prefixEnd_167071 25418585608124760783455 := by
  unfold tailWord_167071
  simp only [CollatzResearch.WordTrace]
  refine ⟨6093579977737775300245067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4062386651825183533496711 6093579977737775300245067)
  ·
    refine ⟨9140369966606662950367601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6093579977737775300245067 9140369966606662950367601)
    ·
      refine ⟨6855277474954997212775701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9140369966606662950367601 6855277474954997212775701)
      ·
        refine ⟨321341131638515494348861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 6855277474954997212775701 321341131638515494348861)
        ·
          refine ⟨120502924364443310380823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 321341131638515494348861 120502924364443310380823)
          ·
            refine ⟨180754386546664965571235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 120502924364443310380823 180754386546664965571235)
            ·
              refine ⟨271131579819997448356853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 180754386546664965571235 271131579819997448356853)
              ·
                refine ⟨25418585608124760783455, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 271131579819997448356853 25418585608124760783455)
                ·
                  rfl

theorem cell20_167071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 3, 1, 1, 5].length) (baseStart_167071 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_167071 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_167071 prefixEnd_167071 := by exact prefixLift 167071
  have htrace : WordTrace (prefixWord ++ tailWord_167071) baseStart_167071 baseEnd_167071 := by
    simpa [prefixWord, tailWord_167071, baseEnd_167071] using wordTrace_append hprefix tailTrace_167071
  have hstable : (prefixWord ++ tailWord_167071).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_167071).length < 2 ^ (prefixWord ++ tailWord_167071).sum := by decide
  have hdescent : baseEnd_167071 < baseStart_167071 := by decide
  rcases family_descends (prefixWord ++ tailWord_167071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_167085 : List Nat := [1, 5, 2, 1, 3, 1, 1, 2, 4]
def baseStart_167085 : Nat := 118140960795 + 167085 * 2 ^ 59
def prefixEnd_167085 : Nat := 4983230072969 + 3 ^ 40 * 167085 * 2
def baseEnd_167085 : Nat := 76262146805852455883641

theorem tailTrace_167085 : CollatzResearch.WordTrace tailWord_167085 prefixEnd_167085 76262146805852455883641 := by
  unfold tailWord_167085
  simp only [CollatzResearch.WordTrace]
  refine ⟨6094090599687055691254709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4062727066458037127503139 6094090599687055691254709)
  ·
    refine ⟨571320993720661471055129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 6094090599687055691254709 571320993720661471055129)
    ·
      refine ⟨428490745290496103291347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 571320993720661471055129 428490745290496103291347)
      ·
        refine ⟨642736117935744154937021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 428490745290496103291347 642736117935744154937021)
        ·
          refine ⟨241026044225904058101383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 642736117935744154937021 241026044225904058101383)
          ·
            refine ⟨361539066338856087152075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 241026044225904058101383 361539066338856087152075)
            ·
              refine ⟨542308599508284130728113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 361539066338856087152075 542308599508284130728113)
              ·
                refine ⟨406731449631213098046085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 542308599508284130728113 406731449631213098046085)
                ·
                  refine ⟨76262146805852455883641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 406731449631213098046085 76262146805852455883641)
                  ·
                    rfl

theorem cell20_167085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 1, 1, 2, 4].length) (baseStart_167085 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_167085 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_167085 prefixEnd_167085 := by exact prefixLift 167085
  have htrace : WordTrace (prefixWord ++ tailWord_167085) baseStart_167085 baseEnd_167085 := by
    simpa [prefixWord, tailWord_167085, baseEnd_167085] using wordTrace_append hprefix tailTrace_167085
  have hstable : (prefixWord ++ tailWord_167085).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_167085).length < 2 ^ (prefixWord ++ tailWord_167085).sum := by decide
  have hdescent : baseEnd_167085 < baseStart_167085 := by decide
  rcases family_descends (prefixWord ++ tailWord_167085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_167102 : List Nat := [4, 2, 1, 1, 3, 2, 2, 3, 2]
def baseStart_167102 : Nat := 118140960795 + 167102 * 2 ^ 59
def prefixEnd_167102 : Nat := 4983230072969 + 3 ^ 40 * 167102 * 2
def baseEnd_167102 : Nat := 76269906069075952316905

theorem tailTrace_167102 : CollatzResearch.WordTrace tailWord_167102 prefixEnd_167102 76269906069075952316905 := by
  unfold tailWord_167102
  simp only [CollatzResearch.WordTrace]
  refine ⟨761838830078183449327945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4063140427083645063082373 761838830078183449327945)
  ·
    refine ⟨571379122558637586995959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 761838830078183449327945 571379122558637586995959)
    ·
      refine ⟨857068683837956380493939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 571379122558637586995959 857068683837956380493939)
      ·
        refine ⟨1285603025756934570740909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 857068683837956380493939 1285603025756934570740909)
        ·
          refine ⟨482101134658850464027841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1285603025756934570740909 482101134658850464027841)
          ·
            refine ⟨361575850994137848020881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 482101134658850464027841 361575850994137848020881)
            ·
              refine ⟨271181888245603386015661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 361575850994137848020881 271181888245603386015661)
              ·
                refine ⟨101693208092101269755873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 271181888245603386015661 101693208092101269755873)
                ·
                  refine ⟨76269906069075952316905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 101693208092101269755873 76269906069075952316905)
                  ·
                    rfl

theorem cell20_167102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 2, 2, 3, 2].length) (baseStart_167102 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_167102 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_167102 prefixEnd_167102 := by exact prefixLift 167102
  have htrace : WordTrace (prefixWord ++ tailWord_167102) baseStart_167102 baseEnd_167102 := by
    simpa [prefixWord, tailWord_167102, baseEnd_167102] using wordTrace_append hprefix tailTrace_167102
  have hstable : (prefixWord ++ tailWord_167102).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_167102).length < 2 ^ (prefixWord ++ tailWord_167102).sum := by decide
  have hdescent : baseEnd_167102 < baseStart_167102 := by decide
  rcases family_descends (prefixWord ++ tailWord_167102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_167127 : List Nat := [1, 1, 3, 2, 1, 2, 3, 3, 4]
def baseStart_167127 : Nat := 118140960795 + 167127 * 2 ^ 59
def prefixEnd_167127 : Nat := 4983230072969 + 3 ^ 40 * 167127 * 2
def baseEnd_167127 : Nat := 76281316750286976483469

theorem tailTrace_167127 : CollatzResearch.WordTrace tailWord_167127 prefixEnd_167127 76281316750286976483469 := by
  unfold tailWord_167127
  simp only [CollatzResearch.WordTrace]
  refine ⟨6095622465534896864283635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4063748310356597909522423 6095622465534896864283635)
  ·
    refine ⟨9143433698302345296425453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6095622465534896864283635 9143433698302345296425453)
    ·
      refine ⟨3428787636863379486159545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9143433698302345296425453 3428787636863379486159545)
      ·
        refine ⟨2571590727647534614619659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3428787636863379486159545 2571590727647534614619659)
        ·
          refine ⟨3857386091471301921929489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2571590727647534614619659 3857386091471301921929489)
          ·
            refine ⟨2893039568603476441447117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3857386091471301921929489 2893039568603476441447117)
            ·
              refine ⟨1084889838226303665542669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2893039568603476441447117 1084889838226303665542669)
              ·
                refine ⟨406833689334863874578501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1084889838226303665542669 406833689334863874578501)
                ·
                  refine ⟨76281316750286976483469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 406833689334863874578501 76281316750286976483469)
                  ·
                    rfl

theorem cell20_167127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 3, 3, 4].length) (baseStart_167127 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_167127 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_167127 prefixEnd_167127 := by exact prefixLift 167127
  have htrace : WordTrace (prefixWord ++ tailWord_167127) baseStart_167127 baseEnd_167127 := by
    simpa [prefixWord, tailWord_167127, baseEnd_167127] using wordTrace_append hprefix tailTrace_167127
  have hstable : (prefixWord ++ tailWord_167127).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_167127).length < 2 ^ (prefixWord ++ tailWord_167127).sum := by decide
  have hdescent : baseEnd_167127 < baseStart_167127 := by decide
  rcases family_descends (prefixWord ++ tailWord_167127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_167133 : List Nat := [1, 4, 3, 2, 2, 1, 3, 1, 3]
def baseStart_167133 : Nat := 118140960795 + 167133 * 2 ^ 59
def prefixEnd_167133 : Nat := 4983230072969 + 3 ^ 40 * 167133 * 2
def baseEnd_167133 : Nat := 76284055313777622283445

theorem tailTrace_167133 : CollatzResearch.WordTrace tailWord_167133 prefixEnd_167133 76284055313777622283445 := by
  unfold tailWord_167133
  simp only [CollatzResearch.WordTrace]
  refine ⟨6095841303513159889002053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4063894202342106592668035 6095841303513159889002053)
  ·
    refine ⟨1142970244408717479187885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6095841303513159889002053 1142970244408717479187885)
    ·
      refine ⟨428613841653269054695457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1142970244408717479187885 428613841653269054695457)
      ·
        refine ⟨321460381239951791021593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 428613841653269054695457 321460381239951791021593)
        ·
          refine ⟨241095285929963843266195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 321460381239951791021593 241095285929963843266195)
          ·
            refine ⟨361642928894945764899293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 241095285929963843266195 361642928894945764899293)
            ·
              refine ⟨135616098335604661837235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 361642928894945764899293 135616098335604661837235)
              ·
                refine ⟨203424147503406992755853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 135616098335604661837235 203424147503406992755853)
                ·
                  refine ⟨76284055313777622283445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 203424147503406992755853 76284055313777622283445)
                  ·
                    rfl

theorem cell20_167133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 1, 3, 1, 3].length) (baseStart_167133 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_167133 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_167133 prefixEnd_167133 := by exact prefixLift 167133
  have htrace : WordTrace (prefixWord ++ tailWord_167133) baseStart_167133 baseEnd_167133 := by
    simpa [prefixWord, tailWord_167133, baseEnd_167133] using wordTrace_append hprefix tailTrace_167133
  have hstable : (prefixWord ++ tailWord_167133).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_167133).length < 2 ^ (prefixWord ++ tailWord_167133).sum := by decide
  have hdescent : baseEnd_167133 < baseStart_167133 := by decide
  rcases family_descends (prefixWord ++ tailWord_167133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_167151 : List Nat := [1, 1, 2, 1, 7, 1, 1, 6]
def baseStart_167151 : Nat := 118140960795 + 167151 * 2 ^ 59
def prefixEnd_167151 : Nat := 4983230072969 + 3 ^ 40 * 167151 * 2
def baseEnd_167151 : Nat := 25430757001416519894457

theorem tailTrace_167151 : CollatzResearch.WordTrace tailWord_167151 prefixEnd_167151 25430757001416519894457 := by
  unfold tailWord_167151
  simp only [CollatzResearch.WordTrace]
  refine ⟨6096497817447948963157307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4064331878298632642104871 6096497817447948963157307)
  ·
    refine ⟨9144746726171923444735961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6096497817447948963157307 9144746726171923444735961)
    ·
      refine ⟨6858560044628942583551971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9144746726171923444735961 6858560044628942583551971)
      ·
        refine ⟨10287840066943413875327957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6858560044628942583551971 10287840066943413875327957)
        ·
          refine ⟨241121251568986262702999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 10287840066943413875327957 241121251568986262702999)
          ·
            refine ⟨361681877353479394054499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 241121251568986262702999 361681877353479394054499)
            ·
              refine ⟨542522816030219091081749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 361681877353479394054499 542522816030219091081749)
              ·
                refine ⟨25430757001416519894457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 542522816030219091081749 25430757001416519894457)
                ·
                  rfl

theorem cell20_167151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 1, 1, 6].length) (baseStart_167151 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_167151 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_167151 prefixEnd_167151 := by exact prefixLift 167151
  have htrace : WordTrace (prefixWord ++ tailWord_167151) baseStart_167151 baseEnd_167151 := by
    simpa [prefixWord, tailWord_167151, baseEnd_167151] using wordTrace_append hprefix tailTrace_167151
  have hstable : (prefixWord ++ tailWord_167151).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_167151).length < 2 ^ (prefixWord ++ tailWord_167151).sum := by decide
  have hdescent : baseEnd_167151 < baseStart_167151 := by decide
  rcases family_descends (prefixWord ++ tailWord_167151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_167182 : List Nat := [4, 1, 1, 2, 1, 3, 3, 1, 4]
def baseStart_167182 : Nat := 118140960795 + 167182 * 2 ^ 59
def prefixEnd_167182 : Nat := 4983230072969 + 3 ^ 40 * 167182 * 2
def baseEnd_167182 : Nat := 76306420248951229649911

theorem tailTrace_167182 : CollatzResearch.WordTrace tailWord_167182 prefixEnd_167182 76306420248951229649911 := by
  unfold tailWord_167182
  simp only [CollatzResearch.WordTrace]
  refine ⟨762203560041955157191975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4065085653557094171690533 762203560041955157191975)
  ·
    refine ⟨1143305340062932735787963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 762203560041955157191975 1143305340062932735787963)
    ·
      refine ⟨1714958010094399103681945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1143305340062932735787963 1714958010094399103681945)
      ·
        refine ⟨1286218507570799327761459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1714958010094399103681945 1286218507570799327761459)
        ·
          refine ⟨1929327761356198991642189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1286218507570799327761459 1929327761356198991642189)
          ·
            refine ⟨723497910508574621865821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1929327761356198991642189 723497910508574621865821)
            ·
              refine ⟨271311716440715483199683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 723497910508574621865821 271311716440715483199683)
              ·
                refine ⟨406967574661073224799525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 271311716440715483199683 406967574661073224799525)
                ·
                  refine ⟨76306420248951229649911, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 406967574661073224799525 76306420248951229649911)
                  ·
                    rfl

theorem cell20_167182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 3, 1, 4].length) (baseStart_167182 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_167182 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_167182 prefixEnd_167182 := by exact prefixLift 167182
  have htrace : WordTrace (prefixWord ++ tailWord_167182) baseStart_167182 baseEnd_167182 := by
    simpa [prefixWord, tailWord_167182, baseEnd_167182] using wordTrace_append hprefix tailTrace_167182
  have hstable : (prefixWord ++ tailWord_167182).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_167182).length < 2 ^ (prefixWord ++ tailWord_167182).sum := by decide
  have hdescent : baseEnd_167182 < baseStart_167182 := by decide
  rcases family_descends (prefixWord ++ tailWord_167182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_167192 : List Nat := [2, 1, 2, 3, 1, 5, 2, 1, 3]
def baseStart_167192 : Nat := 118140960795 + 167192 * 2 ^ 59
def prefixEnd_167192 : Nat := 4983230072969 + 3 ^ 40 * 167192 * 2
def baseEnd_167192 : Nat := 76310984521435639316537

theorem tailTrace_167192 : CollatzResearch.WordTrace tailWord_167192 prefixEnd_167192 76310984521435639316537 := by
  unfold tailWord_167192
  simp only [CollatzResearch.WordTrace]
  refine ⟨3048996605149706482699915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4065328806866275310266553 3048996605149706482699915)
  ·
    refine ⟨4573494907724559724049873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3048996605149706482699915 4573494907724559724049873)
    ·
      refine ⟨3430121180793419793037405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4573494907724559724049873 3430121180793419793037405)
      ·
        refine ⟨1286295442797532422389027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3430121180793419793037405 1286295442797532422389027)
        ·
          refine ⟨1929443164196298633583541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1286295442797532422389027 1929443164196298633583541)
          ·
            refine ⟨180885296643402996898457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1929443164196298633583541 180885296643402996898457)
            ·
              refine ⟨135663972482552247673843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 180885296643402996898457 135663972482552247673843)
              ·
                refine ⟨203495958723828371510765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 135663972482552247673843 203495958723828371510765)
                ·
                  refine ⟨76310984521435639316537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 203495958723828371510765 76310984521435639316537)
                  ·
                    rfl

theorem cell20_167192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 5, 2, 1, 3].length) (baseStart_167192 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_167192 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_167192 prefixEnd_167192 := by exact prefixLift 167192
  have htrace : WordTrace (prefixWord ++ tailWord_167192) baseStart_167192 baseEnd_167192 := by
    simpa [prefixWord, tailWord_167192, baseEnd_167192] using wordTrace_append hprefix tailTrace_167192
  have hstable : (prefixWord ++ tailWord_167192).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_167192).length < 2 ^ (prefixWord ++ tailWord_167192).sum := by decide
  have hdescent : baseEnd_167192 < baseStart_167192 := by decide
  rcases family_descends (prefixWord ++ tailWord_167192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_167233 : List Nat := [1, 2, 5, 2, 1, 3, 2, 2, 2]
def baseStart_167233 : Nat := 118140960795 + 167233 * 2 ^ 59
def prefixEnd_167233 : Nat := 4983230072969 + 3 ^ 40 * 167233 * 2
def baseEnd_167233 : Nat := 76329698038621718949703

theorem tailTrace_167233 : CollatzResearch.WordTrace tailWord_167233 prefixEnd_167233 76329698038621718949703 := by
  unfold tailWord_167233
  simp only [CollatzResearch.WordTrace]
  refine ⟨6099488603150876967642353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4066325735433917978428235 6099488603150876967642353)
  ·
    refine ⟨4574616452363157725731765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6099488603150876967642353 4574616452363157725731765)
    ·
      refine ⟨428870292409046036787353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 4574616452363157725731765 428870292409046036787353)
      ·
        refine ⟨321652719306784527590515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 428870292409046036787353 321652719306784527590515)
        ·
          refine ⟨482479078960176791385773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 321652719306784527590515 482479078960176791385773)
          ·
            refine ⟨180929654610066296769665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 482479078960176791385773 180929654610066296769665)
            ·
              refine ⟨135697240957549722577249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 180929654610066296769665 135697240957549722577249)
              ·
                refine ⟨101772930718162291932937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 135697240957549722577249 101772930718162291932937)
                ·
                  refine ⟨76329698038621718949703, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 101772930718162291932937 76329698038621718949703)
                  ·
                    rfl

theorem cell20_167233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 3, 2, 2, 2].length) (baseStart_167233 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_167233 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_167233 prefixEnd_167233 := by exact prefixLift 167233
  have htrace : WordTrace (prefixWord ++ tailWord_167233) baseStart_167233 baseEnd_167233 := by
    simpa [prefixWord, tailWord_167233, baseEnd_167233] using wordTrace_append hprefix tailTrace_167233
  have hstable : (prefixWord ++ tailWord_167233).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_167233).length < 2 ^ (prefixWord ++ tailWord_167233).sum := by decide
  have hdescent : baseEnd_167233 < baseStart_167233 := by decide
  rcases family_descends (prefixWord ++ tailWord_167233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_167285 : List Nat := [1, 3, 4, 1, 4, 1, 1, 2, 3]
def baseStart_167285 : Nat := 118140960795 + 167285 * 2 ^ 59
def prefixEnd_167285 : Nat := 4983230072969 + 3 ^ 40 * 167285 * 2
def baseEnd_167285 : Nat := 76353432255540649216157

theorem tailTrace_167285 : CollatzResearch.WordTrace tailWord_167285 prefixEnd_167285 76353432255540649216157 := by
  unfold tailWord_167285
  simp only [CollatzResearch.WordTrace]
  refine ⟨6101385198962489848535309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4067590132641659899023539 6101385198962489848535309)
  ·
    refine ⟨2288019449610933693200741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6101385198962489848535309 2288019449610933693200741)
    ·
      refine ⟨429003646802050067475139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2288019449610933693200741 429003646802050067475139)
      ·
        refine ⟨643505470203075101212709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 429003646802050067475139 643505470203075101212709)
        ·
          refine ⟨120657275663076581477383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 643505470203075101212709 120657275663076581477383)
          ·
            refine ⟨180985913494614872216075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 120657275663076581477383 180985913494614872216075)
            ·
              refine ⟨271478870241922308324113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 180985913494614872216075 271478870241922308324113)
              ·
                refine ⟨203609152681441731243085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 271478870241922308324113 203609152681441731243085)
                ·
                  refine ⟨76353432255540649216157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 203609152681441731243085 76353432255540649216157)
                  ·
                    rfl

theorem cell20_167285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 4, 1, 1, 2, 3].length) (baseStart_167285 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_167285 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_167285 prefixEnd_167285 := by exact prefixLift 167285
  have htrace : WordTrace (prefixWord ++ tailWord_167285) baseStart_167285 baseEnd_167285 := by
    simpa [prefixWord, tailWord_167285, baseEnd_167285] using wordTrace_append hprefix tailTrace_167285
  have hstable : (prefixWord ++ tailWord_167285).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_167285).length < 2 ^ (prefixWord ++ tailWord_167285).sum := by decide
  have hdescent : baseEnd_167285 < baseStart_167285 := by decide
  rcases family_descends (prefixWord ++ tailWord_167285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_167317 : List Nat := [1, 3, 2, 1, 1, 2, 4, 2, 4]
def baseStart_167317 : Nat := 118140960795 + 167317 * 2 ^ 59
def prefixEnd_167317 : Nat := 4983230072969 + 3 ^ 40 * 167317 * 2
def baseEnd_167317 : Nat := 76368037927490760149359

theorem tailTrace_167317 : CollatzResearch.WordTrace tailWord_167317 prefixEnd_167317 76368037927490760149359 := by
  unfold tailWord_167317
  simp only [CollatzResearch.WordTrace]
  refine ⟨6102552334846559313700205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4068368223231039542466803 6102552334846559313700205)
  ·
    refine ⟨2288457125567459742637577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6102552334846559313700205 2288457125567459742637577)
    ·
      refine ⟨1716342844175594806978183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2288457125567459742637577 1716342844175594806978183)
      ·
        refine ⟨2574514266263392210467275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1716342844175594806978183 2574514266263392210467275)
        ·
          refine ⟨3861771399395088315700913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2574514266263392210467275 3861771399395088315700913)
          ·
            refine ⟨2896328549546316236775685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3861771399395088315700913 2896328549546316236775685)
            ·
              refine ⟨543061603039934294395441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2896328549546316236775685 543061603039934294395441)
              ·
                refine ⟨407296202279950720796581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 543061603039934294395441 407296202279950720796581)
                ·
                  refine ⟨76368037927490760149359, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 407296202279950720796581 76368037927490760149359)
                  ·
                    rfl

theorem cell20_167317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 4, 2, 4].length) (baseStart_167317 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_167317 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_167317 prefixEnd_167317 := by exact prefixLift 167317
  have htrace : WordTrace (prefixWord ++ tailWord_167317) baseStart_167317 baseEnd_167317 := by
    simpa [prefixWord, tailWord_167317, baseEnd_167317] using wordTrace_append hprefix tailTrace_167317
  have hstable : (prefixWord ++ tailWord_167317).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_167317).length < 2 ^ (prefixWord ++ tailWord_167317).sum := by decide
  have hdescent : baseEnd_167317 < baseStart_167317 := by decide
  rcases family_descends (prefixWord ++ tailWord_167317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_167326 : List Nat := [4, 3, 1, 2, 3, 1, 1, 3, 2]
def baseStart_167326 : Nat := 118140960795 + 167326 * 2 ^ 59
def prefixEnd_167326 : Nat := 4983230072969 + 3 ^ 40 * 167326 * 2
def baseEnd_167326 : Nat := 76372145772726728849323

theorem tailTrace_167326 : CollatzResearch.WordTrace tailWord_167326 prefixEnd_167326 76372145772726728849323 := by
  unfold tailWord_167326
  simp only [CollatzResearch.WordTrace]
  refine ⟨762860073976744231347229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4068587061209302567185221 762860073976744231347229)
  ·
    refine ⟨286072527741279086755211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 762860073976744231347229 286072527741279086755211)
    ·
      refine ⟨429108791611918630132817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 286072527741279086755211 429108791611918630132817)
      ·
        refine ⟨321831593708938972599613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 429108791611918630132817 321831593708938972599613)
        ·
          refine ⟨120686847640852114724855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 321831593708938972599613 120686847640852114724855)
          ·
            refine ⟨181030271461278172087283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 120686847640852114724855 181030271461278172087283)
            ·
              refine ⟨271545407191917258130925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 181030271461278172087283 271545407191917258130925)
              ·
                refine ⟨101829527696968971799097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 271545407191917258130925 101829527696968971799097)
                ·
                  refine ⟨76372145772726728849323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 101829527696968971799097 76372145772726728849323)
                  ·
                    rfl

theorem cell20_167326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 3, 1, 1, 3, 2].length) (baseStart_167326 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_167326 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_167326 prefixEnd_167326 := by exact prefixLift 167326
  have htrace : WordTrace (prefixWord ++ tailWord_167326) baseStart_167326 baseEnd_167326 := by
    simpa [prefixWord, tailWord_167326, baseEnd_167326] using wordTrace_append hprefix tailTrace_167326
  have hstable : (prefixWord ++ tailWord_167326).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_167326).length < 2 ^ (prefixWord ++ tailWord_167326).sum := by decide
  have hdescent : baseEnd_167326 < baseStart_167326 := by decide
  rcases family_descends (prefixWord ++ tailWord_167326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_167330 : List Nat := [3, 3, 1, 2, 1, 4, 1, 3, 2]
def baseStart_167330 : Nat := 118140960795 + 167330 * 2 ^ 59
def prefixEnd_167330 : Nat := 4983230072969 + 3 ^ 40 * 167330 * 2
def baseEnd_167330 : Nat := 76373971481720492715973

theorem tailTrace_167330 : CollatzResearch.WordTrace tailWord_167330 prefixEnd_167330 76373971481720492715973 := by
  unfold tailWord_167330
  simp only [CollatzResearch.WordTrace]
  refine ⟨1525756620949865633480861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4068684322532975022615629 1525756620949865633480861)
  ·
    refine ⟨572158732856199612555323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1525756620949865633480861 572158732856199612555323)
    ·
      refine ⟨858238099284299418832985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 572158732856199612555323 858238099284299418832985)
      ·
        refine ⟨643678574463224564124739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 858238099284299418832985 643678574463224564124739)
        ·
          refine ⟨965517861694836846187109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 643678574463224564124739 965517861694836846187109)
          ·
            refine ⟨181034599067781908660083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 965517861694836846187109 181034599067781908660083)
            ·
              refine ⟨271551898601672862990125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 181034599067781908660083 271551898601672862990125)
              ·
                refine ⟨101831961975627323621297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 271551898601672862990125 101831961975627323621297)
                ·
                  refine ⟨76373971481720492715973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 101831961975627323621297 76373971481720492715973)
                  ·
                    rfl

theorem cell20_167330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 4, 1, 3, 2].length) (baseStart_167330 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_167330 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_167330 prefixEnd_167330 := by exact prefixLift 167330
  have htrace : WordTrace (prefixWord ++ tailWord_167330) baseStart_167330 baseEnd_167330 := by
    simpa [prefixWord, tailWord_167330, baseEnd_167330] using wordTrace_append hprefix tailTrace_167330
  have hstable : (prefixWord ++ tailWord_167330).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_167330).length < 2 ^ (prefixWord ++ tailWord_167330).sum := by decide
  have hdescent : baseEnd_167330 < baseStart_167330 := by decide
  rcases family_descends (prefixWord ++ tailWord_167330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_167331 : List Nat := [1, 1, 1, 4, 1, 3, 1, 1, 7]
def baseStart_167331 : Nat := 118140960795 + 167331 * 2 ^ 59
def prefixEnd_167331 : Nat := 4983230072969 + 3 ^ 40 * 167331 * 2
def baseEnd_167331 : Nat := 76374427908968933682635

theorem tailTrace_167331 : CollatzResearch.WordTrace tailWord_167331 prefixEnd_167331 76374427908968933682635 := by
  unfold tailWord_167331
  simp only [CollatzResearch.WordTrace]
  refine ⟨6103062956795839704709847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4068708637863893136473231 6103062956795839704709847)
  ·
    refine ⟨9154594435193759557064771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6103062956795839704709847 9154594435193759557064771)
    ·
      refine ⟨13731891652790639335597157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9154594435193759557064771 13731891652790639335597157)
      ·
        refine ⟨2574729684898244875424467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13731891652790639335597157 2574729684898244875424467)
        ·
          refine ⟨3862094527347367313136701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2574729684898244875424467 3862094527347367313136701)
          ·
            refine ⟨1448285447755262742426263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3862094527347367313136701 1448285447755262742426263)
            ·
              refine ⟨2172428171632894113639395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1448285447755262742426263 2172428171632894113639395)
              ·
                refine ⟨3258642257449341170459093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2172428171632894113639395 3258642257449341170459093)
                ·
                  refine ⟨76374427908968933682635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3258642257449341170459093 76374427908968933682635)
                  ·
                    rfl

theorem cell20_167331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 1, 1, 7].length) (baseStart_167331 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_167331 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_167331 prefixEnd_167331 := by exact prefixLift 167331
  have htrace : WordTrace (prefixWord ++ tailWord_167331) baseStart_167331 baseEnd_167331 := by
    simpa [prefixWord, tailWord_167331, baseEnd_167331] using wordTrace_append hprefix tailTrace_167331
  have hstable : (prefixWord ++ tailWord_167331).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_167331).length < 2 ^ (prefixWord ++ tailWord_167331).sum := by decide
  have hdescent : baseEnd_167331 < baseStart_167331 := by decide
  rcases family_descends (prefixWord ++ tailWord_167331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_167341 : List Nat := [1, 5, 2, 2, 1, 1, 8]
def baseStart_167341 : Nat := 118140960795 + 167341 * 2 ^ 59
def prefixEnd_167341 : Nat := 4983230072969 + 3 ^ 40 * 167341 * 2
def baseEnd_167341 : Nat := 8486554686828149261029

theorem tailTrace_167341 : CollatzResearch.WordTrace tailWord_167341 prefixEnd_167341 8486554686828149261029 := by
  unfold tailWord_167341
  simp only [CollatzResearch.WordTrace]
  refine ⟨6103427686759611412573877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4068951791173074275049251 6103427686759611412573877)
  ·
    refine ⟨572196345633713569928801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 6103427686759611412573877 572196345633713569928801)
    ·
      refine ⟨429147259225285177446601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 572196345633713569928801 429147259225285177446601)
      ·
        refine ⟨321860444418963883084951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 429147259225285177446601 321860444418963883084951)
        ·
          refine ⟨482790666628445824627427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 321860444418963883084951 482790666628445824627427)
          ·
            refine ⟨724185999942668736941141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 482790666628445824627427 724185999942668736941141)
            ·
              refine ⟨8486554686828149261029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 724185999942668736941141 8486554686828149261029)
              ·
                rfl

theorem cell20_167341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 8].length) (baseStart_167341 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_167341 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_167341 prefixEnd_167341 := by exact prefixLift 167341
  have htrace : WordTrace (prefixWord ++ tailWord_167341) baseStart_167341 baseEnd_167341 := by
    simpa [prefixWord, tailWord_167341, baseEnd_167341] using wordTrace_append hprefix tailTrace_167341
  have hstable : (prefixWord ++ tailWord_167341).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_167341).length < 2 ^ (prefixWord ++ tailWord_167341).sum := by decide
  have hdescent : baseEnd_167341 < baseStart_167341 := by decide
  rcases family_descends (prefixWord ++ tailWord_167341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_167351 : List Nat := [1, 1, 3, 1, 3, 2, 5, 2, 2]
def baseStart_167351 : Nat := 118140960795 + 167351 * 2 ^ 59
def prefixEnd_167351 : Nat := 4983230072969 + 3 ^ 40 * 167351 * 2
def baseEnd_167351 : Nat := 76383556453937753015887

theorem tailTrace_167351 : CollatzResearch.WordTrace tailWord_167351 prefixEnd_167351 76383556453937753015887 := by
  unfold tailWord_167351
  simp only [CollatzResearch.WordTrace]
  refine ⟨6103792416723383120437907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4069194944482255413625271 6103792416723383120437907)
  ·
    refine ⟨9155688625085074680656861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6103792416723383120437907 9155688625085074680656861)
    ·
      refine ⟨3433383234406903005246323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9155688625085074680656861 3433383234406903005246323)
      ·
        refine ⟨5150074851610354507869485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3433383234406903005246323 5150074851610354507869485)
        ·
          refine ⟨1931278069353882940451057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5150074851610354507869485 1931278069353882940451057)
          ·
            refine ⟨1448458552015412205338293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1931278069353882940451057 1448458552015412205338293)
            ·
              refine ⟨135792989251444894250465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1448458552015412205338293 135792989251444894250465)
              ·
                refine ⟨101844741938583670687849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 135792989251444894250465 101844741938583670687849)
                ·
                  refine ⟨76383556453937753015887, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 101844741938583670687849 76383556453937753015887)
                  ·
                    rfl

theorem cell20_167351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 5, 2, 2].length) (baseStart_167351 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_167351 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_167351 prefixEnd_167351 := by exact prefixLift 167351
  have htrace : WordTrace (prefixWord ++ tailWord_167351) baseStart_167351 baseEnd_167351 := by
    simpa [prefixWord, tailWord_167351, baseEnd_167351] using wordTrace_append hprefix tailTrace_167351
  have hstable : (prefixWord ++ tailWord_167351).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_167351).length < 2 ^ (prefixWord ++ tailWord_167351).sum := by decide
  have hdescent : baseEnd_167351 < baseStart_167351 := by decide
  rcases family_descends (prefixWord ++ tailWord_167351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_167407 : List Nat := [1, 1, 2, 1, 4, 1, 2, 3, 5]
def baseStart_167407 : Nat := 118140960795 + 167407 * 2 ^ 59
def prefixEnd_167407 : Nat := 4983230072969 + 3 ^ 40 * 167407 * 2
def baseEnd_167407 : Nat := 76409116379850447148991

theorem tailTrace_167407 : CollatzResearch.WordTrace tailWord_167407 prefixEnd_167407 76409116379850447148991 := by
  unfold tailWord_167407
  simp only [CollatzResearch.WordTrace]
  refine ⟨6105834904520504684476475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4070556603013669789650983 6105834904520504684476475)
  ·
    refine ⟨9158752356780757026714713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6105834904520504684476475 9158752356780757026714713)
    ·
      refine ⟨6869064267585567770036035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9158752356780757026714713 6869064267585567770036035)
      ·
        refine ⟨10303596401378351655054053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6869064267585567770036035 10303596401378351655054053)
        ·
          refine ⟨1931924325258440935322635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10303596401378351655054053 1931924325258440935322635)
          ·
            refine ⟨2897886487887661402983953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1931924325258440935322635 2897886487887661402983953)
            ·
              refine ⟨2173414865915746052237965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2897886487887661402983953 2173414865915746052237965)
              ·
                refine ⟨815030574718404769589237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2173414865915746052237965 815030574718404769589237)
                ·
                  refine ⟨76409116379850447148991, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 815030574718404769589237 76409116379850447148991)
                  ·
                    rfl

theorem cell20_167407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 2, 3, 5].length) (baseStart_167407 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_167407 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_167407 prefixEnd_167407 := by exact prefixLift 167407
  have htrace : WordTrace (prefixWord ++ tailWord_167407) baseStart_167407 baseEnd_167407 := by
    simpa [prefixWord, tailWord_167407, baseEnd_167407] using wordTrace_append hprefix tailTrace_167407
  have hstable : (prefixWord ++ tailWord_167407).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_167407).length < 2 ^ (prefixWord ++ tailWord_167407).sum := by decide
  have hdescent : baseEnd_167407 < baseStart_167407 := by decide
  rcases family_descends (prefixWord ++ tailWord_167407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_167431 : List Nat := [1, 1, 4, 3, 2, 1, 1, 1, 6]
def baseStart_167431 : Nat := 118140960795 + 167431 * 2 ^ 59
def prefixEnd_167431 : Nat := 4983230072969 + 3 ^ 40 * 167431 * 2
def baseEnd_167431 : Nat := 76420070633813030348893

theorem tailTrace_167431 : CollatzResearch.WordTrace tailWord_167431 prefixEnd_167431 76420070633813030348893 := by
  unfold tailWord_167431
  simp only [CollatzResearch.WordTrace]
  refine ⟨6106710256433556783350147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4071140170955704522233431 6106710256433556783350147)
  ·
    refine ⟨9160065384650335175025221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6106710256433556783350147 9160065384650335175025221)
    ·
      refine ⟨1717512259621937845317229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9160065384650335175025221 1717512259621937845317229)
      ·
        refine ⟨644067097358226691993961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1717512259621937845317229 644067097358226691993961)
        ·
          refine ⟨483050323018670018995471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 644067097358226691993961 483050323018670018995471)
          ·
            refine ⟨724575484528005028493207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 483050323018670018995471 724575484528005028493207)
            ·
              refine ⟨1086863226792007542739811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 724575484528005028493207 1086863226792007542739811)
              ·
                refine ⟨1630294840188011314109717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1086863226792007542739811 1630294840188011314109717)
                ·
                  refine ⟨76420070633813030348893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1630294840188011314109717 76420070633813030348893)
                  ·
                    rfl

theorem cell20_167431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 1, 1, 6].length) (baseStart_167431 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_167431 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_167431 prefixEnd_167431 := by exact prefixLift 167431
  have htrace : WordTrace (prefixWord ++ tailWord_167431) baseStart_167431 baseEnd_167431 := by
    simpa [prefixWord, tailWord_167431, baseEnd_167431] using wordTrace_append hprefix tailTrace_167431
  have hstable : (prefixWord ++ tailWord_167431).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_167431).length < 2 ^ (prefixWord ++ tailWord_167431).sum := by decide
  have hdescent : baseEnd_167431 < baseStart_167431 := by decide
  rcases family_descends (prefixWord ++ tailWord_167431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_167479 : List Nat := [1, 1, 3, 1, 2, 5, 3, 1, 3]
def baseStart_167479 : Nat := 118140960795 + 167479 * 2 ^ 59
def prefixEnd_167479 : Nat := 4983230072969 + 3 ^ 40 * 167479 * 2
def baseEnd_167479 : Nat := 76441979141738196748697

theorem tailTrace_167479 : CollatzResearch.WordTrace tailWord_167479 prefixEnd_167479 76441979141738196748697 := by
  unfold tailWord_167479
  simp only [CollatzResearch.WordTrace]
  refine ⟨6108460960259660981097491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4072307306839773987398327 6108460960259660981097491)
  ·
    refine ⟨9162691440389491471646237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6108460960259660981097491 9162691440389491471646237)
    ·
      refine ⟨3436009290146059301867339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9162691440389491471646237 3436009290146059301867339)
      ·
        refine ⟨5154013935219088952801009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3436009290146059301867339 5154013935219088952801009)
        ·
          refine ⟨3865510451414316714600757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5154013935219088952801009 3865510451414316714600757)
          ·
            refine ⟨362391604820092191993821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 3865510451414316714600757 362391604820092191993821)
            ·
              refine ⟨135896851807534571997683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 362391604820092191993821 135896851807534571997683)
              ·
                refine ⟨203845277711301857996525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 135896851807534571997683 203845277711301857996525)
                ·
                  refine ⟨76441979141738196748697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 203845277711301857996525 76441979141738196748697)
                  ·
                    rfl

theorem cell20_167479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 5, 3, 1, 3].length) (baseStart_167479 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_167479 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_167479 prefixEnd_167479 := by exact prefixLift 167479
  have htrace : WordTrace (prefixWord ++ tailWord_167479) baseStart_167479 baseEnd_167479 := by
    simpa [prefixWord, tailWord_167479, baseEnd_167479] using wordTrace_append hprefix tailTrace_167479
  have hstable : (prefixWord ++ tailWord_167479).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_167479).length < 2 ^ (prefixWord ++ tailWord_167479).sum := by decide
  have hdescent : baseEnd_167479 < baseStart_167479 := by decide
  rcases family_descends (prefixWord ++ tailWord_167479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_167521 : List Nat := [1, 2, 3, 1, 1, 3, 1, 3, 5]
def baseStart_167521 : Nat := 118140960795 + 167521 * 2 ^ 59
def prefixEnd_167521 : Nat := 4983230072969 + 3 ^ 40 * 167521 * 2
def baseEnd_167521 : Nat := 76461149086172717348525

theorem tailTrace_167521 : CollatzResearch.WordTrace tailWord_167521 prefixEnd_167521 76461149086172717348525 := by
  unfold tailWord_167521
  simp only [CollatzResearch.WordTrace]
  refine ⟨6109992826107502154126417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4073328550738334769417611 6109992826107502154126417)
  ·
    refine ⟨4582494619580626615594813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6109992826107502154126417 4582494619580626615594813)
    ·
      refine ⟨1718435482342734980848055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4582494619580626615594813 1718435482342734980848055)
      ·
        refine ⟨2577653223514102471272083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1718435482342734980848055 2577653223514102471272083)
        ·
          refine ⟨3866479835271153706908125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2577653223514102471272083 3866479835271153706908125)
          ·
            refine ⟨1449929938226682640090547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3866479835271153706908125 1449929938226682640090547)
            ·
              refine ⟨2174894907340023960135821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1449929938226682640090547 2174894907340023960135821)
              ·
                refine ⟨815585590252508985050933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2174894907340023960135821 815585590252508985050933)
                ·
                  refine ⟨76461149086172717348525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 815585590252508985050933 76461149086172717348525)
                  ·
                    rfl

theorem cell20_167521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 1, 3, 5].length) (baseStart_167521 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_167521 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_167521 prefixEnd_167521 := by exact prefixLift 167521
  have htrace : WordTrace (prefixWord ++ tailWord_167521) baseStart_167521 baseEnd_167521 := by
    simpa [prefixWord, tailWord_167521, baseEnd_167521] using wordTrace_append hprefix tailTrace_167521
  have hstable : (prefixWord ++ tailWord_167521).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_167521).length < 2 ^ (prefixWord ++ tailWord_167521).sum := by decide
  have hdescent : baseEnd_167521 < baseStart_167521 := by decide
  rcases family_descends (prefixWord ++ tailWord_167521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_167524 : List Nat := [2, 3, 1, 1, 2, 5, 1, 1, 4]
def baseStart_167524 : Nat := 118140960795 + 167524 * 2 ^ 59
def prefixEnd_167524 : Nat := 4983230072969 + 3 ^ 40 * 167524 * 2
def baseEnd_167524 : Nat := 76462518367918040248513

theorem tailTrace_167524 : CollatzResearch.WordTrace tailWord_167524 prefixEnd_167524 76462518367918040248513 := by
  unfold tailWord_167524
  simp only [CollatzResearch.WordTrace]
  refine ⟨3055051122548316833242813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4073401496731089110990417 3055051122548316833242813)
  ·
    refine ⟨1145644170955618812466055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3055051122548316833242813 1145644170955618812466055)
    ·
      refine ⟨1718466256433428218699083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1145644170955618812466055 1718466256433428218699083)
      ·
        refine ⟨2577699384650142328048625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1718466256433428218699083 2577699384650142328048625)
        ·
          refine ⟨1933274538487606746036469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2577699384650142328048625 1933274538487606746036469)
          ·
            refine ⟨181244487983213132440919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1933274538487606746036469 181244487983213132440919)
            ·
              refine ⟨271866731974819698661379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 181244487983213132440919 271866731974819698661379)
              ·
                refine ⟨407800097962229547992069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 271866731974819698661379 407800097962229547992069)
                ·
                  refine ⟨76462518367918040248513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 407800097962229547992069 76462518367918040248513)
                  ·
                    rfl

theorem cell20_167524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 5, 1, 1, 4].length) (baseStart_167524 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_167524 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_167524 prefixEnd_167524 := by exact prefixLift 167524
  have htrace : WordTrace (prefixWord ++ tailWord_167524) baseStart_167524 baseEnd_167524 := by
    simpa [prefixWord, tailWord_167524, baseEnd_167524] using wordTrace_append hprefix tailTrace_167524
  have hstable : (prefixWord ++ tailWord_167524).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_167524).length < 2 ^ (prefixWord ++ tailWord_167524).sum := by decide
  have hdescent : baseEnd_167524 < baseStart_167524 := by decide
  rcases family_descends (prefixWord ++ tailWord_167524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_167572 : List Nat := [2, 4, 2, 2, 2, 1, 2, 2, 3]
def baseStart_167572 : Nat := 118140960795 + 167572 * 2 ^ 59
def prefixEnd_167572 : Nat := 4983230072969 + 3 ^ 40 * 167572 * 2
def baseEnd_167572 : Nat := 76484426875843206648317

theorem tailTrace_167572 : CollatzResearch.WordTrace tailWord_167572 prefixEnd_167572 76484426875843206648317 := by
  unfold tailWord_167572
  simp only [CollatzResearch.WordTrace]
  refine ⟨3055926474461368932116485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4074568632615158576155313 3055926474461368932116485)
  ·
    refine ⟨572986213961506674771841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3055926474461368932116485 572986213961506674771841)
    ·
      refine ⟨429739660471130006078881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 572986213961506674771841 429739660471130006078881)
      ·
        refine ⟨322304745353347504559161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 429739660471130006078881 322304745353347504559161)
        ·
          refine ⟨241728559015010628419371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 322304745353347504559161 241728559015010628419371)
          ·
            refine ⟨362592838522515942629057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 241728559015010628419371 362592838522515942629057)
            ·
              refine ⟨271944628891886956971793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 362592838522515942629057 271944628891886956971793)
              ·
                refine ⟨203958471668915217728845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 271944628891886956971793 203958471668915217728845)
                ·
                  refine ⟨76484426875843206648317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 203958471668915217728845 76484426875843206648317)
                  ·
                    rfl

theorem cell20_167572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 1, 2, 2, 3].length) (baseStart_167572 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_167572 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_167572 prefixEnd_167572 := by exact prefixLift 167572
  have htrace : WordTrace (prefixWord ++ tailWord_167572) baseStart_167572 baseEnd_167572 := by
    simpa [prefixWord, tailWord_167572, baseEnd_167572] using wordTrace_append hprefix tailTrace_167572
  have hstable : (prefixWord ++ tailWord_167572).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_167572).length < 2 ^ (prefixWord ++ tailWord_167572).sum := by decide
  have hdescent : baseEnd_167572 < baseStart_167572 := by decide
  rcases family_descends (prefixWord ++ tailWord_167572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_167576 : List Nat := [2, 1, 2, 4, 1, 2, 1, 4, 3]
def baseStart_167576 : Nat := 118140960795 + 167576 * 2 ^ 59
def prefixEnd_167576 : Nat := 4983230072969 + 3 ^ 40 * 167576 * 2
def baseEnd_167576 : Nat := 76486252584836970514967

theorem tailTrace_167576 : CollatzResearch.WordTrace tailWord_167576 prefixEnd_167576 76486252584836970514967 := by
  unfold tailWord_167576
  simp only [CollatzResearch.WordTrace]
  refine ⟨3055999420454123273689291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4074665893938831031585721 3055999420454123273689291)
  ·
    refine ⟨4583999130681184910533937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3055999420454123273689291 4583999130681184910533937)
    ·
      refine ⟨3437999348010888682900453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4583999130681184910533937 3437999348010888682900453)
      ·
        refine ⟨644624877752041628043835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3437999348010888682900453 644624877752041628043835)
        ·
          refine ⟨966937316628062442065753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 644624877752041628043835 966937316628062442065753)
          ·
            refine ⟨725202987471046831549315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 966937316628062442065753 725202987471046831549315)
            ·
              refine ⟨1087804481206570247323973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 725202987471046831549315 1087804481206570247323973)
              ·
                refine ⟨203963340226231921373245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1087804481206570247323973 203963340226231921373245)
                ·
                  refine ⟨76486252584836970514967, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 203963340226231921373245 76486252584836970514967)
                  ·
                    rfl

theorem cell20_167576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 1, 4, 3].length) (baseStart_167576 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_167576 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_167576 prefixEnd_167576 := by exact prefixLift 167576
  have htrace : WordTrace (prefixWord ++ tailWord_167576) baseStart_167576 baseEnd_167576 := by
    simpa [prefixWord, tailWord_167576, baseEnd_167576] using wordTrace_append hprefix tailTrace_167576
  have hstable : (prefixWord ++ tailWord_167576).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_167576).length < 2 ^ (prefixWord ++ tailWord_167576).sum := by decide
  have hdescent : baseEnd_167576 < baseStart_167576 := by decide
  rcases family_descends (prefixWord ++ tailWord_167576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_167607 : List Nat := [1, 1, 3, 1, 5, 2, 3, 4]
def baseStart_167607 : Nat := 118140960795 + 167607 * 2 ^ 59
def prefixEnd_167607 : Nat := 4983230072969 + 3 ^ 40 * 167607 * 2
def baseEnd_167607 : Nat := 25500133943179546827169

theorem tailTrace_167607 : CollatzResearch.WordTrace tailWord_167607 prefixEnd_167607 25500133943179546827169 := by
  unfold tailWord_167607
  simp only [CollatzResearch.WordTrace]
  refine ⟨6113129503795938841757075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4075419669197292561171383 6113129503795938841757075)
  ·
    refine ⟨9169694255693908262635613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6113129503795938841757075 9169694255693908262635613)
    ·
      refine ⟨3438635345885215598488355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9169694255693908262635613 3438635345885215598488355)
      ·
        refine ⟨5157953018827823397732533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3438635345885215598488355 5157953018827823397732533)
        ·
          refine ⟨483558095515108443537425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 5157953018827823397732533 483558095515108443537425)
          ·
            refine ⟨362668571636331332653069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 483558095515108443537425 362668571636331332653069)
            ·
              refine ⟨136000714363624249744901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 362668571636331332653069 136000714363624249744901)
              ·
                refine ⟨25500133943179546827169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 136000714363624249744901 25500133943179546827169)
                ·
                  rfl

theorem cell20_167607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 2, 3, 4].length) (baseStart_167607 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_167607 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_167607 prefixEnd_167607 := by exact prefixLift 167607
  have htrace : WordTrace (prefixWord ++ tailWord_167607) baseStart_167607 baseEnd_167607 := by
    simpa [prefixWord, tailWord_167607, baseEnd_167607] using wordTrace_append hprefix tailTrace_167607
  have hstable : (prefixWord ++ tailWord_167607).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_167607).length < 2 ^ (prefixWord ++ tailWord_167607).sum := by decide
  have hdescent : baseEnd_167607 < baseStart_167607 := by decide
  rcases family_descends (prefixWord ++ tailWord_167607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_167611 : List Nat := [1, 1, 1, 1, 1, 2, 3, 10]
def baseStart_167611 : Nat := 118140960795 + 167611 * 2 ^ 59
def prefixEnd_167611 : Nat := 4983230072969 + 3 ^ 40 * 167611 * 2
def baseEnd_167611 : Nat := 25500742512844134782719

theorem tailTrace_167611 : CollatzResearch.WordTrace tailWord_167611 prefixEnd_167611 25500742512844134782719 := by
  unfold tailWord_167611
  simp only [CollatzResearch.WordTrace]
  refine ⟨6113275395781447524902687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4075516930520965016601791 6113275395781447524902687)
  ·
    refine ⟨9169913093672171287354031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6113275395781447524902687 9169913093672171287354031)
    ·
      refine ⟨13754869640508256931031047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9169913093672171287354031 13754869640508256931031047)
      ·
        refine ⟨20632304460762385396546571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13754869640508256931031047 20632304460762385396546571)
        ·
          refine ⟨30948456691143578094819857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20632304460762385396546571 30948456691143578094819857)
          ·
            refine ⟨23211342518357683571114893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30948456691143578094819857 23211342518357683571114893)
            ·
              refine ⟨8704253444384131339168085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23211342518357683571114893 8704253444384131339168085)
              ·
                refine ⟨25500742512844134782719, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 8704253444384131339168085 25500742512844134782719)
                ·
                  rfl

theorem cell20_167611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 10].length) (baseStart_167611 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_167611 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_167611 prefixEnd_167611 := by exact prefixLift 167611
  have htrace : WordTrace (prefixWord ++ tailWord_167611) baseStart_167611 baseEnd_167611 := by
    simpa [prefixWord, tailWord_167611, baseEnd_167611] using wordTrace_append hprefix tailTrace_167611
  have hstable : (prefixWord ++ tailWord_167611).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_167611).length < 2 ^ (prefixWord ++ tailWord_167611).sum := by decide
  have hdescent : baseEnd_167611 < baseStart_167611 := by decide
  rcases family_descends (prefixWord ++ tailWord_167611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_167666 : List Nat := [3, 2, 1, 3, 1, 1, 3, 6]
def baseStart_167666 : Nat := 118140960795 + 167666 * 2 ^ 59
def prefixEnd_167666 : Nat := 4983230072969 + 3 ^ 40 * 167666 * 2
def baseEnd_167666 : Nat := 25509110345732219171533

theorem tailTrace_167666 : CollatzResearch.WordTrace tailWord_167666 prefixEnd_167666 25509110345732219171533 := by
  unfold tailWord_167666
  simp only [CollatzResearch.WordTrace]
  refine ⟨1528820352645547979538713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4076854273721461278769901 1528820352645547979538713)
  ·
    refine ⟨1146615264484160984654035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1528820352645547979538713 1146615264484160984654035)
    ·
      refine ⟨1719922896726241476981053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1146615264484160984654035 1719922896726241476981053)
      ·
        refine ⟨644971086272340553867895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1719922896726241476981053 644971086272340553867895)
        ·
          refine ⟨967456629408510830801843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 644971086272340553867895 967456629408510830801843)
          ·
            refine ⟨1451184944112766246202765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 967456629408510830801843 1451184944112766246202765)
            ·
              refine ⟨544194354042287342326037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1451184944112766246202765 544194354042287342326037)
              ·
                refine ⟨25509110345732219171533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 544194354042287342326037 25509110345732219171533)
                ·
                  rfl

theorem cell20_167666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 3, 6].length) (baseStart_167666 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_167666 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_167666 prefixEnd_167666 := by exact prefixLift 167666
  have htrace : WordTrace (prefixWord ++ tailWord_167666) baseStart_167666 baseEnd_167666 := by
    simpa [prefixWord, tailWord_167666, baseEnd_167666] using wordTrace_append hprefix tailTrace_167666
  have hstable : (prefixWord ++ tailWord_167666).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_167666).length < 2 ^ (prefixWord ++ tailWord_167666).sum := by decide
  have hdescent : baseEnd_167666 < baseStart_167666 := by decide
  rcases family_descends (prefixWord ++ tailWord_167666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_167742 : List Nat := [4, 2, 1, 2, 2, 9]
def baseStart_167742 : Nat := 118140960795 + 167742 * 2 ^ 59
def prefixEnd_167742 : Nat := 4983230072969 + 3 ^ 40 * 167742 * 2
def baseEnd_167742 : Nat := 2835630352151043369665

theorem tailTrace_167742 : CollatzResearch.WordTrace tailWord_167742 prefixEnd_167742 2835630352151043369665 := by
  unfold tailWord_167742
  simp only [CollatzResearch.WordTrace]
  refine ⟨764756669788357112240185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4078702238871237931947653 764756669788357112240185)
  ·
    refine ⟨573567502341267834180139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 764756669788357112240185 573567502341267834180139)
    ·
      refine ⟨860351253511901751270209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 573567502341267834180139 860351253511901751270209)
      ·
        refine ⟨645263440133926313452657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 860351253511901751270209 645263440133926313452657)
        ·
          refine ⟨483947580100444735089493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 645263440133926313452657 483947580100444735089493)
          ·
            refine ⟨2835630352151043369665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 483947580100444735089493 2835630352151043369665)
            ·
              rfl

theorem cell20_167742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 9].length) (baseStart_167742 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_167742 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_167742 prefixEnd_167742 := by exact prefixLift 167742
  have htrace : WordTrace (prefixWord ++ tailWord_167742) baseStart_167742 baseEnd_167742 := by
    simpa [prefixWord, tailWord_167742, baseEnd_167742] using wordTrace_append hprefix tailTrace_167742
  have hstable : (prefixWord ++ tailWord_167742).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_167742).length < 2 ^ (prefixWord ++ tailWord_167742).sum := by decide
  have hdescent : baseEnd_167742 < baseStart_167742 := by decide
  rcases family_descends (prefixWord ++ tailWord_167742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_167752 : List Nat := [2, 1, 3, 1, 1, 5, 1, 4, 2]
def baseStart_167752 : Nat := 118140960795 + 167752 * 2 ^ 59
def prefixEnd_167752 : Nat := 4983230072969 + 3 ^ 40 * 167752 * 2
def baseEnd_167752 : Nat := 76566583780562580647581

theorem tailTrace_167752 : CollatzResearch.WordTrace tailWord_167752 prefixEnd_167752 76566583780562580647581 := by
  unfold tailWord_167752
  simp only [CollatzResearch.WordTrace]
  refine ⟨3059209044135314302892755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4078945392180419070523673 3059209044135314302892755)
  ·
    refine ⟨4588813566202971454339133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3059209044135314302892755 4588813566202971454339133)
    ·
      refine ⟨1720805087326114295377175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4588813566202971454339133 1720805087326114295377175)
      ·
        refine ⟨2581207630989171443065763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1720805087326114295377175 2581207630989171443065763)
        ·
          refine ⟨3871811446483757164598645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2581207630989171443065763 3871811446483757164598645)
          ·
            refine ⟨362982323107852234181123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 3871811446483757164598645 362982323107852234181123)
            ·
              refine ⟨544473484661778351271685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 362982323107852234181123 544473484661778351271685)
              ·
                refine ⟨102088778374083440863441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 544473484661778351271685 102088778374083440863441)
                ·
                  refine ⟨76566583780562580647581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 102088778374083440863441 76566583780562580647581)
                  ·
                    rfl

theorem cell20_167752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 5, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 5, 1, 4, 2].length) (baseStart_167752 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_167752 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_167752 prefixEnd_167752 := by exact prefixLift 167752
  have htrace : WordTrace (prefixWord ++ tailWord_167752) baseStart_167752 baseEnd_167752 := by
    simpa [prefixWord, tailWord_167752, baseEnd_167752] using wordTrace_append hprefix tailTrace_167752
  have hstable : (prefixWord ++ tailWord_167752).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_167752).length < 2 ^ (prefixWord ++ tailWord_167752).sum := by decide
  have hdescent : baseEnd_167752 < baseStart_167752 := by decide
  rcases family_descends (prefixWord ++ tailWord_167752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_167786 : List Nat := [3, 1, 3, 4, 1, 1, 2, 3, 2]
def baseStart_167786 : Nat := 118140960795 + 167786 * 2 ^ 59
def prefixEnd_167786 : Nat := 4983230072969 + 3 ^ 40 * 167786 * 2
def baseEnd_167786 : Nat := 76582102307009573514109

theorem tailTrace_167786 : CollatzResearch.WordTrace tailWord_167786 prefixEnd_167786 76582102307009573514109 := by
  unfold tailWord_167786
  simp only [CollatzResearch.WordTrace]
  refine ⟨1529914542536863103130803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4079772113431634941682141 1529914542536863103130803)
  ·
    refine ⟨2294871813805294654696205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1529914542536863103130803 2294871813805294654696205)
    ·
      refine ⟨860576930176985495511077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2294871813805294654696205 860576930176985495511077)
      ·
        refine ⟨161358174408184780408327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 860576930176985495511077 161358174408184780408327)
        ·
          refine ⟨242037261612277170612491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 161358174408184780408327 242037261612277170612491)
          ·
            refine ⟨363055892418415755918737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 242037261612277170612491 363055892418415755918737)
            ·
              refine ⟨272291919313811816939053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 363055892418415755918737 272291919313811816939053)
              ·
                refine ⟨102109469742679431352145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 272291919313811816939053 102109469742679431352145)
                ·
                  refine ⟨76582102307009573514109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 102109469742679431352145 76582102307009573514109)
                  ·
                    rfl

theorem cell20_167786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 1, 2, 3, 2].length) (baseStart_167786 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_167786 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_167786 prefixEnd_167786 := by exact prefixLift 167786
  have htrace : WordTrace (prefixWord ++ tailWord_167786) baseStart_167786 baseEnd_167786 := by
    simpa [prefixWord, tailWord_167786, baseEnd_167786] using wordTrace_append hprefix tailTrace_167786
  have hstable : (prefixWord ++ tailWord_167786).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_167786).length < 2 ^ (prefixWord ++ tailWord_167786).sum := by decide
  have hdescent : baseEnd_167786 < baseStart_167786 := by decide
  rcases family_descends (prefixWord ++ tailWord_167786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_167794 : List Nat := [3, 2, 1, 2, 1, 1, 1, 1, 8]
def baseStart_167794 : Nat := 118140960795 + 167794 * 2 ^ 59
def prefixEnd_167794 : Nat := 4983230072969 + 3 ^ 40 * 167794 * 2
def baseEnd_167794 : Nat := 76585753724997101247409

theorem tailTrace_167794 : CollatzResearch.WordTrace tailWord_167794 prefixEnd_167794 76585753724997101247409 := by
  unfold tailWord_167794
  simp only [CollatzResearch.WordTrace]
  refine ⟨1529987488529617444703609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4079966636078979852542957 1529987488529617444703609)
  ·
    refine ⟨1147490616397213083527707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1529987488529617444703609 1147490616397213083527707)
    ·
      refine ⟨1721235924595819625291561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1147490616397213083527707 1721235924595819625291561)
      ·
        refine ⟨1290926943446864718968671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1721235924595819625291561 1290926943446864718968671)
        ·
          refine ⟨1936390415170297078453007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1290926943446864718968671 1936390415170297078453007)
          ·
            refine ⟨2904585622755445617679511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1936390415170297078453007 2904585622755445617679511)
            ·
              refine ⟨4356878434133168426519267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2904585622755445617679511 4356878434133168426519267)
              ·
                refine ⟨6535317651199752639778901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4356878434133168426519267 6535317651199752639778901)
                ·
                  refine ⟨76585753724997101247409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 6535317651199752639778901 76585753724997101247409)
                  ·
                    rfl

theorem cell20_167794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 1, 8].length) (baseStart_167794 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_167794 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_167794 prefixEnd_167794 := by exact prefixLift 167794
  have htrace : WordTrace (prefixWord ++ tailWord_167794) baseStart_167794 baseEnd_167794 := by
    simpa [prefixWord, tailWord_167794, baseEnd_167794] using wordTrace_append hprefix tailTrace_167794
  have hstable : (prefixWord ++ tailWord_167794).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_167794).length < 2 ^ (prefixWord ++ tailWord_167794).sum := by decide
  have hdescent : baseEnd_167794 < baseStart_167794 := by decide
  rcases family_descends (prefixWord ++ tailWord_167794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_167801 : List Nat := [1, 2, 1, 3, 2, 2, 9]
def baseStart_167801 : Nat := 118140960795 + 167801 * 2 ^ 59
def prefixEnd_167801 : Nat := 4983230072969 + 3 ^ 40 * 167801 * 2
def baseEnd_167801 : Nat := 8509883190637354223783

theorem tailTrace_167801 : CollatzResearch.WordTrace tailWord_167801 prefixEnd_167801 8509883190637354223783 := by
  unfold tailWord_167801
  simp only [CollatzResearch.WordTrace]
  refine ⟨6120205265093109974319257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4080136843395406649546171 6120205265093109974319257)
  ·
    refine ⟨4590153948819832480739443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6120205265093109974319257 4590153948819832480739443)
    ·
      refine ⟨6885230923229748721109165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4590153948819832480739443 6885230923229748721109165)
      ·
        refine ⟨2581961596211155770415937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6885230923229748721109165 2581961596211155770415937)
        ·
          refine ⟨1936471197158366827811953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2581961596211155770415937 1936471197158366827811953)
          ·
            refine ⟨1452353397868775120858965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1936471197158366827811953 1452353397868775120858965)
            ·
              refine ⟨8509883190637354223783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 1452353397868775120858965 8509883190637354223783)
              ·
                rfl

theorem cell20_167801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 9].length) (baseStart_167801 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_167801 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_167801 prefixEnd_167801 := by exact prefixLift 167801
  have htrace : WordTrace (prefixWord ++ tailWord_167801) baseStart_167801 baseEnd_167801 := by
    simpa [prefixWord, tailWord_167801, baseEnd_167801] using wordTrace_append hprefix tailTrace_167801
  have hstable : (prefixWord ++ tailWord_167801).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_167801).length < 2 ^ (prefixWord ++ tailWord_167801).sum := by decide
  have hdescent : baseEnd_167801 < baseStart_167801 := by decide
  rcases family_descends (prefixWord ++ tailWord_167801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_167811 : List Nat := [1, 1, 1, 3, 4, 3, 2, 1, 4]
def baseStart_167811 : Nat := 118140960795 + 167811 * 2 ^ 59
def prefixEnd_167811 : Nat := 4983230072969 + 3 ^ 40 * 167811 * 2
def baseEnd_167811 : Nat := 76593512988220597680673

theorem tailTrace_167811 : CollatzResearch.WordTrace tailWord_167811 prefixEnd_167811 76593512988220597680673 := by
  unfold tailWord_167811
  simp only [CollatzResearch.WordTrace]
  refine ⟨6120569995056881682183287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4080379996704587788122191 6120569995056881682183287)
  ·
    refine ⟨9180854992585322523274931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6120569995056881682183287 9180854992585322523274931)
    ·
      refine ⟨13771282488877983784912397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9180854992585322523274931 13771282488877983784912397)
      ·
        refine ⟨5164230933329243919342149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13771282488877983784912397 5164230933329243919342149)
        ·
          refine ⟨968293299999233234876653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5164230933329243919342149 968293299999233234876653)
          ·
            refine ⟨363109987499712463078745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 968293299999233234876653 363109987499712463078745)
            ·
              refine ⟨272332490624784347309059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 363109987499712463078745 272332490624784347309059)
              ·
                refine ⟨408498735937176520963589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 272332490624784347309059 408498735937176520963589)
                ·
                  refine ⟨76593512988220597680673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 408498735937176520963589 76593512988220597680673)
                  ·
                    rfl

theorem cell20_167811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 3, 2, 1, 4].length) (baseStart_167811 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_167811 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_167811 prefixEnd_167811 := by exact prefixLift 167811
  have htrace : WordTrace (prefixWord ++ tailWord_167811) baseStart_167811 baseEnd_167811 := by
    simpa [prefixWord, tailWord_167811, baseEnd_167811] using wordTrace_append hprefix tailTrace_167811
  have hstable : (prefixWord ++ tailWord_167811).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_167811).length < 2 ^ (prefixWord ++ tailWord_167811).sum := by decide
  have hdescent : baseEnd_167811 < baseStart_167811 := by decide
  rcases family_descends (prefixWord ++ tailWord_167811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_167825 : List Nat := [1, 2, 2, 1, 1, 1, 4, 5, 3]
def baseStart_167825 : Nat := 118140960795 + 167825 * 2 ^ 59
def prefixEnd_167825 : Nat := 4983230072969 + 3 ^ 40 * 167825 * 2
def baseEnd_167825 : Nat := 76599902969698771213949

theorem tailTrace_167825 : CollatzResearch.WordTrace tailWord_167825 prefixEnd_167825 76599902969698771213949 := by
  unfold tailWord_167825
  simp only [CollatzResearch.WordTrace]
  refine ⟨6121080617006162073192929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4080720411337441382128619 6121080617006162073192929)
  ·
    refine ⟨4590810462754621554894697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6121080617006162073192929 4590810462754621554894697)
    ·
      refine ⟨3443107847065966166171023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4590810462754621554894697 3443107847065966166171023)
      ·
        refine ⟨5164661770598949249256535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3443107847065966166171023 5164661770598949249256535)
        ·
          refine ⟨7746992655898423873884803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5164661770598949249256535 7746992655898423873884803)
          ·
            refine ⟨11620488983847635810827205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7746992655898423873884803 11620488983847635810827205)
            ·
              refine ⟨2178841684471431714530101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11620488983847635810827205 2178841684471431714530101)
              ·
                refine ⟨204266407919196723237197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2178841684471431714530101 204266407919196723237197)
                ·
                  refine ⟨76599902969698771213949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 204266407919196723237197 76599902969698771213949)
                  ·
                    rfl

theorem cell20_167825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 4, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 4, 5, 3].length) (baseStart_167825 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_167825 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_167825 prefixEnd_167825 := by exact prefixLift 167825
  have htrace : WordTrace (prefixWord ++ tailWord_167825) baseStart_167825 baseEnd_167825 := by
    simpa [prefixWord, tailWord_167825, baseEnd_167825] using wordTrace_append hprefix tailTrace_167825
  have hstable : (prefixWord ++ tailWord_167825).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_167825).length < 2 ^ (prefixWord ++ tailWord_167825).sum := by decide
  have hdescent : baseEnd_167825 < baseStart_167825 := by decide
  rcases family_descends (prefixWord ++ tailWord_167825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_167849 : List Nat := [1, 2, 1, 1, 1, 1, 4, 7, 2]
def baseStart_167849 : Nat := 118140960795 + 167849 * 2 ^ 59
def prefixEnd_167849 : Nat := 4983230072969 + 3 ^ 40 * 167849 * 2
def baseEnd_167849 : Nat := 76610857223661354413851

theorem tailTrace_167849 : CollatzResearch.WordTrace tailWord_167849 prefixEnd_167849 76610857223661354413851 := by
  unfold tailWord_167849
  simp only [CollatzResearch.WordTrace]
  refine ⟨6121955968919214172066601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4081303979279476114711067 6121955968919214172066601)
  ·
    refine ⟨4591466976689410629049951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6121955968919214172066601 4591466976689410629049951)
    ·
      refine ⟨6887200465034115943574927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4591466976689410629049951 6887200465034115943574927)
      ·
        refine ⟨10330800697551173915362391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6887200465034115943574927 10330800697551173915362391)
        ·
          refine ⟨15496201046326760873043587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10330800697551173915362391 15496201046326760873043587)
          ·
            refine ⟨23244301569490141309565381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15496201046326760873043587 23244301569490141309565381)
            ·
              refine ⟨4358306544279401495543509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23244301569490141309565381 4358306544279401495543509)
              ·
                refine ⟨102147809631548472551801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4358306544279401495543509 102147809631548472551801)
                ·
                  refine ⟨76610857223661354413851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 102147809631548472551801 76610857223661354413851)
                  ·
                    rfl

theorem cell20_167849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 7, 2].length) (baseStart_167849 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_167849 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_167849 prefixEnd_167849 := by exact prefixLift 167849
  have htrace : WordTrace (prefixWord ++ tailWord_167849) baseStart_167849 baseEnd_167849 := by
    simpa [prefixWord, tailWord_167849, baseEnd_167849] using wordTrace_append hprefix tailTrace_167849
  have hstable : (prefixWord ++ tailWord_167849).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_167849).length < 2 ^ (prefixWord ++ tailWord_167849).sum := by decide
  have hdescent : baseEnd_167849 < baseStart_167849 := by decide
  rcases family_descends (prefixWord ++ tailWord_167849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_167863 : List Nat := [1, 1, 3, 1, 3, 1, 1, 6, 3]
def baseStart_167863 : Nat := 118140960795 + 167863 * 2 ^ 59
def prefixEnd_167863 : Nat := 4983230072969 + 3 ^ 40 * 167863 * 2
def baseEnd_167863 : Nat := 76617247205139527947127

theorem tailTrace_167863 : CollatzResearch.WordTrace tailWord_167863 prefixEnd_167863 76617247205139527947127 := by
  unfold tailWord_167863
  simp only [CollatzResearch.WordTrace]
  refine ⟨6122466590868494563076243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4081644393912329708717495 6122466590868494563076243)
  ·
    refine ⟨9183699886302741844614365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6122466590868494563076243 9183699886302741844614365)
    ·
      refine ⟨3443887457363528191730387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9183699886302741844614365 3443887457363528191730387)
      ·
        refine ⟨5165831186045292287595581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3443887457363528191730387 5165831186045292287595581)
        ·
          refine ⟨1937186694766984607848343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5165831186045292287595581 1937186694766984607848343)
          ·
            refine ⟨2905780042150476911772515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1937186694766984607848343 2905780042150476911772515)
            ·
              refine ⟨4358670063225715367658773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2905780042150476911772515 4358670063225715367658773)
              ·
                refine ⟨204312659213705407859005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 4358670063225715367658773 204312659213705407859005)
                ·
                  refine ⟨76617247205139527947127, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 204312659213705407859005 76617247205139527947127)
                  ·
                    rfl

theorem cell20_167863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 6, 3].length) (baseStart_167863 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_167863 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_167863 prefixEnd_167863 := by exact prefixLift 167863
  have htrace : WordTrace (prefixWord ++ tailWord_167863) baseStart_167863 baseEnd_167863 := by
    simpa [prefixWord, tailWord_167863, baseEnd_167863] using wordTrace_append hprefix tailTrace_167863
  have hstable : (prefixWord ++ tailWord_167863).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_167863).length < 2 ^ (prefixWord ++ tailWord_167863).sum := by decide
  have hdescent : baseEnd_167863 < baseStart_167863 := by decide
  rcases family_descends (prefixWord ++ tailWord_167863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_167880 : List Nat := [2, 1, 3, 1, 4, 2, 1, 3, 3]
def baseStart_167880 : Nat := 118140960795 + 167880 * 2 ^ 59
def prefixEnd_167880 : Nat := 4983230072969 + 3 ^ 40 * 167880 * 2
def baseEnd_167880 : Nat := 76625006468363024380391

theorem tailTrace_167880 : CollatzResearch.WordTrace tailWord_167880 prefixEnd_167880 76625006468363024380391 := by
  unfold tailWord_167880
  simp only [CollatzResearch.WordTrace]
  refine ⟨3061543315903453233222547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4082057754537937644296729 3061543315903453233222547)
  ·
    refine ⟨4592314973855179849833821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3061543315903453233222547 4592314973855179849833821)
    ·
      refine ⟨1722118115195692443687683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4592314973855179849833821 1722118115195692443687683)
      ·
        refine ⟨2583177172793538665531525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1722118115195692443687683 2583177172793538665531525)
        ·
          refine ⟨484345719898788499787161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2583177172793538665531525 484345719898788499787161)
          ·
            refine ⟨363259289924091374840371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 484345719898788499787161 363259289924091374840371)
            ·
              refine ⟨544888934886137062260557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 363259289924091374840371 544888934886137062260557)
              ·
                refine ⟨204333350582301398347709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 544888934886137062260557 204333350582301398347709)
                ·
                  refine ⟨76625006468363024380391, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 204333350582301398347709 76625006468363024380391)
                  ·
                    rfl

theorem cell20_167880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 2, 1, 3, 3].length) (baseStart_167880 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_167880 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_167880 prefixEnd_167880 := by exact prefixLift 167880
  have htrace : WordTrace (prefixWord ++ tailWord_167880) baseStart_167880 baseEnd_167880 := by
    simpa [prefixWord, tailWord_167880, baseEnd_167880] using wordTrace_append hprefix tailTrace_167880
  have hstable : (prefixWord ++ tailWord_167880).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_167880).length < 2 ^ (prefixWord ++ tailWord_167880).sum := by decide
  have hdescent : baseEnd_167880 < baseStart_167880 := by decide
  rcases family_descends (prefixWord ++ tailWord_167880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_167917 : List Nat := [1, 5, 1, 4, 1, 2, 2, 2, 2]
def baseStart_167917 : Nat := 118140960795 + 167917 * 2 ^ 59
def prefixEnd_167917 : Nat := 4983230072969 + 3 ^ 40 * 167917 * 2
def baseEnd_167917 : Nat := 76641894276555340146907

theorem tailTrace_167917 : CollatzResearch.WordTrace tailWord_167917 prefixEnd_167917 76641894276555340146907 := by
  unfold tailWord_167917
  simp only [CollatzResearch.WordTrace]
  refine ⟨6124436132672861785542005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4082957421781907857028003 6124436132672861785542005)
  ·
    refine ⟨574165887438080792394563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 6124436132672861785542005 574165887438080792394563)
    ·
      refine ⟨861248831157121188591845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 574165887438080792394563 861248831157121188591845)
      ·
        refine ⟨161484155841960222860971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 861248831157121188591845 161484155841960222860971)
        ·
          refine ⟨242226233762940334291457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 161484155841960222860971 242226233762940334291457)
          ·
            refine ⟨181669675322205250718593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 242226233762940334291457 181669675322205250718593)
            ·
              refine ⟨136252256491653938038945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 181669675322205250718593 136252256491653938038945)
              ·
                refine ⟨102189192368740453529209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 136252256491653938038945 102189192368740453529209)
                ·
                  refine ⟨76641894276555340146907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 102189192368740453529209 76641894276555340146907)
                  ·
                    rfl

theorem cell20_167917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 2, 2, 2, 2].length) (baseStart_167917 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_167917 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_167917 prefixEnd_167917 := by exact prefixLift 167917
  have htrace : WordTrace (prefixWord ++ tailWord_167917) baseStart_167917 baseEnd_167917 := by
    simpa [prefixWord, tailWord_167917, baseEnd_167917] using wordTrace_append hprefix tailTrace_167917
  have hstable : (prefixWord ++ tailWord_167917).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_167917).length < 2 ^ (prefixWord ++ tailWord_167917).sum := by decide
  have hdescent : baseEnd_167917 < baseStart_167917 := by decide
  rcases family_descends (prefixWord ++ tailWord_167917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_167918 : List Nat := [4, 1, 2, 1, 3, 1, 1, 4, 3]
def baseStart_167918 : Nat := 118140960795 + 167918 * 2 ^ 59
def prefixEnd_167918 : Nat := 4983230072969 + 3 ^ 40 * 167918 * 2
def baseEnd_167918 : Nat := 76642350703803781113569

theorem tailTrace_167918 : CollatzResearch.WordTrace tailWord_167918 prefixEnd_167918 76642350703803781113569 := by
  unfold tailWord_167918
  simp only [CollatzResearch.WordTrace]
  refine ⟨765559075708654869541051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4082981737112825970885605 765559075708654869541051)
  ·
    refine ⟨1148338613562982304311577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 765559075708654869541051 1148338613562982304311577)
    ·
      refine ⟨861253960172236728233683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1148338613562982304311577 861253960172236728233683)
      ·
        refine ⟨1291880940258355092350525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 861253960172236728233683 1291880940258355092350525)
        ·
          refine ⟨484455352596883159631447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1291880940258355092350525 484455352596883159631447)
          ·
            refine ⟨726683028895324739447171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 484455352596883159631447 726683028895324739447171)
            ·
              refine ⟨1090024543342987109170757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 726683028895324739447171 1090024543342987109170757)
              ·
                refine ⟨204379601876810082969517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1090024543342987109170757 204379601876810082969517)
                ·
                  refine ⟨76642350703803781113569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 204379601876810082969517 76642350703803781113569)
                  ·
                    rfl

theorem cell20_167918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 1, 4, 3].length) (baseStart_167918 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_167918 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_167918 prefixEnd_167918 := by exact prefixLift 167918
  have htrace : WordTrace (prefixWord ++ tailWord_167918) baseStart_167918 baseEnd_167918 := by
    simpa [prefixWord, tailWord_167918, baseEnd_167918] using wordTrace_append hprefix tailTrace_167918
  have hstable : (prefixWord ++ tailWord_167918).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_167918).length < 2 ^ (prefixWord ++ tailWord_167918).sum := by decide
  have hdescent : baseEnd_167918 < baseStart_167918 := by decide
  rcases family_descends (prefixWord ++ tailWord_167918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_167959 : List Nat := [1, 1, 3, 5, 2, 1, 2, 3, 2]
def baseStart_167959 : Nat := 118140960795 + 167959 * 2 ^ 59
def prefixEnd_167959 : Nat := 4983230072969 + 3 ^ 40 * 167959 * 2
def baseEnd_167959 : Nat := 76661064220989860746735

theorem tailTrace_167959 : CollatzResearch.WordTrace tailWord_167959 prefixEnd_167959 76661064220989860746735 := by
  unfold tailWord_167959
  simp only [CollatzResearch.WordTrace]
  refine ⟨6125967998520702958570931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4083978665680468639047287 6125967998520702958570931)
  ·
    refine ⟨9188951997781054437856397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6125967998520702958570931 9188951997781054437856397)
    ·
      refine ⟨3445856999167895414196149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9188951997781054437856397 3445856999167895414196149)
      ·
        refine ⟨323049093671990195080889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 3445856999167895414196149 323049093671990195080889)
        ·
          refine ⟨242286820253992646310667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 323049093671990195080889 242286820253992646310667)
          ·
            refine ⟨363430230380988969466001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 242286820253992646310667 363430230380988969466001)
            ·
              refine ⟨272572672785741727099501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 363430230380988969466001 272572672785741727099501)
              ·
                refine ⟨102214752294653147662313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 272572672785741727099501 102214752294653147662313)
                ·
                  refine ⟨76661064220989860746735, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 102214752294653147662313 76661064220989860746735)
                  ·
                    rfl

theorem cell20_167959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 1, 2, 3, 2].length) (baseStart_167959 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_167959 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_167959 prefixEnd_167959 := by exact prefixLift 167959
  have htrace : WordTrace (prefixWord ++ tailWord_167959) baseStart_167959 baseEnd_167959 := by
    simpa [prefixWord, tailWord_167959, baseEnd_167959] using wordTrace_append hprefix tailTrace_167959
  have hstable : (prefixWord ++ tailWord_167959).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_167959).length < 2 ^ (prefixWord ++ tailWord_167959).sum := by decide
  have hdescent : baseEnd_167959 < baseStart_167959 := by decide
  rcases family_descends (prefixWord ++ tailWord_167959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_167984 : List Nat := [2, 1, 1, 1, 2, 5, 1, 3, 4]
def baseStart_167984 : Nat := 118140960795 + 167984 * 2 ^ 59
def prefixEnd_167984 : Nat := 4983230072969 + 3 ^ 40 * 167984 * 2
def baseEnd_167984 : Nat := 76672474902200884913299

theorem tailTrace_167984 : CollatzResearch.WordTrace tailWord_167984 prefixEnd_167984 76672474902200884913299 := by
  unfold tailWord_167984
  simp only [CollatzResearch.WordTrace]
  refine ⟨3063439911715066114115503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4084586548953421485487337 3063439911715066114115503)
  ·
    refine ⟨4595159867572599171173255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3063439911715066114115503 4595159867572599171173255)
    ·
      refine ⟨6892739801358898756759883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4595159867572599171173255 6892739801358898756759883)
      ·
        refine ⟨10339109702038348135139825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6892739801358898756759883 10339109702038348135139825)
        ·
          refine ⟨7754332276528761101354869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10339109702038348135139825 7754332276528761101354869)
          ·
            refine ⟨726968650924571353252019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 7754332276528761101354869 726968650924571353252019)
            ·
              refine ⟨1090452976386857029878029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 726968650924571353252019 1090452976386857029878029)
              ·
                refine ⟨408919866145071386204261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1090452976386857029878029 408919866145071386204261)
                ·
                  refine ⟨76672474902200884913299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 408919866145071386204261 76672474902200884913299)
                  ·
                    rfl

theorem cell20_167984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 1, 3, 4].length) (baseStart_167984 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_167984 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_167984 prefixEnd_167984 := by exact prefixLift 167984
  have htrace : WordTrace (prefixWord ++ tailWord_167984) baseStart_167984 baseEnd_167984 := by
    simpa [prefixWord, tailWord_167984, baseEnd_167984] using wordTrace_append hprefix tailTrace_167984
  have hstable : (prefixWord ++ tailWord_167984).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_167984).length < 2 ^ (prefixWord ++ tailWord_167984).sum := by decide
  have hdescent : baseEnd_167984 < baseStart_167984 := by decide
  rcases family_descends (prefixWord ++ tailWord_167984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_168001 : List Nat := [1, 2, 5, 1, 2, 1, 2, 2, 4]
def baseStart_168001 : Nat := 118140960795 + 168001 * 2 ^ 59
def prefixEnd_168001 : Nat := 4983230072969 + 3 ^ 40 * 168001 * 2
def baseEnd_168001 : Nat := 76680234165424381346563

theorem tailTrace_168001 : CollatzResearch.WordTrace tailWord_168001 prefixEnd_168001 76680234165424381346563 := by
  unfold tailWord_168001
  simp only [CollatzResearch.WordTrace]
  refine ⟨6127499864368544131599857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4084999909579029421066571 6127499864368544131599857)
  ·
    refine ⟨4595624898276408098699893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6127499864368544131599857 4595624898276408098699893)
    ·
      refine ⟨430839834213413259253115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 4595624898276408098699893 430839834213413259253115)
      ·
        refine ⟨646259751320119888879673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 430839834213413259253115 646259751320119888879673)
        ·
          refine ⟨484694813490089916659755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 646259751320119888879673 484694813490089916659755)
          ·
            refine ⟨727042220235134874989633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 484694813490089916659755 727042220235134874989633)
            ·
              refine ⟨545281665176351156242225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 727042220235134874989633 545281665176351156242225)
              ·
                refine ⟨408961248882263367181669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 545281665176351156242225 408961248882263367181669)
                ·
                  refine ⟨76680234165424381346563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 408961248882263367181669 76680234165424381346563)
                  ·
                    rfl

theorem cell20_168001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 2, 2, 4].length) (baseStart_168001 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_168001 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_168001 prefixEnd_168001 := by exact prefixLift 168001
  have htrace : WordTrace (prefixWord ++ tailWord_168001) baseStart_168001 baseEnd_168001 := by
    simpa [prefixWord, tailWord_168001, baseEnd_168001] using wordTrace_append hprefix tailTrace_168001
  have hstable : (prefixWord ++ tailWord_168001).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_168001).length < 2 ^ (prefixWord ++ tailWord_168001).sum := by decide
  have hdescent : baseEnd_168001 < baseStart_168001 := by decide
  rcases family_descends (prefixWord ++ tailWord_168001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_168046 : List Nat := [4, 1, 2, 2, 1, 1, 4, 5]
def baseStart_168046 : Nat := 118140960795 + 168046 * 2 ^ 59
def prefixEnd_168046 : Nat := 4983230072969 + 3 ^ 40 * 168046 * 2
def baseEnd_168046 : Nat := 25566924463868074948793

theorem tailTrace_168046 : CollatzResearch.WordTrace tailWord_168046 prefixEnd_168046 25566924463868074948793 := by
  unfold tailWord_168046
  simp only [CollatzResearch.WordTrace]
  refine ⟨766142643650689602123499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4086094099470344544658661 766142643650689602123499)
  ·
    refine ⟨1149213965476034403185249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 766142643650689602123499 1149213965476034403185249)
    ·
      refine ⟨861910474107025802388937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1149213965476034403185249 861910474107025802388937)
      ·
        refine ⟨646432855580269351791703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 861910474107025802388937 646432855580269351791703)
        ·
          refine ⟨969649283370404027687555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 646432855580269351791703 969649283370404027687555)
          ·
            refine ⟨1454473925055606041531333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 969649283370404027687555 1454473925055606041531333)
            ·
              refine ⟨272713860947926132787125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1454473925055606041531333 272713860947926132787125)
              ·
                refine ⟨25566924463868074948793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 272713860947926132787125 25566924463868074948793)
                ·
                  rfl

theorem cell20_168046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 4, 5].length) (baseStart_168046 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_168046 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_168046 prefixEnd_168046 := by exact prefixLift 168046
  have htrace : WordTrace (prefixWord ++ tailWord_168046) baseStart_168046 baseEnd_168046 := by
    simpa [prefixWord, tailWord_168046, baseEnd_168046] using wordTrace_append hprefix tailTrace_168046
  have hstable : (prefixWord ++ tailWord_168046).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_168046).length < 2 ^ (prefixWord ++ tailWord_168046).sum := by decide
  have hdescent : baseEnd_168046 < baseStart_168046 := by decide
  rcases family_descends (prefixWord ++ tailWord_168046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_168067 : List Nat := [1, 1, 1, 3, 3, 3, 2, 6]
def baseStart_168067 : Nat := 118140960795 + 168067 * 2 ^ 59
def prefixEnd_168067 : Nat := 4983230072969 + 3 ^ 40 * 168067 * 2
def baseEnd_168067 : Nat := 25570119454607161715431

theorem tailTrace_168067 : CollatzResearch.WordTrace tailWord_168067 prefixEnd_168067 25570119454607161715431 := by
  unfold tailWord_168067
  simp only [CollatzResearch.WordTrace]
  refine ⟨6129907082129437403502455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4086604721419624935668303 6129907082129437403502455)
  ·
    refine ⟨9194860623194156105253683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6129907082129437403502455 9194860623194156105253683)
    ·
      refine ⟨13792290934791234157880525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9194860623194156105253683 13792290934791234157880525)
      ·
        refine ⟨5172109100546712809205197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13792290934791234157880525 5172109100546712809205197)
        ·
          refine ⟨1939540912705017303451949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5172109100546712809205197 1939540912705017303451949)
          ·
            refine ⟨727327842264381488794481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1939540912705017303451949 727327842264381488794481)
            ·
              refine ⟨545495881698286116595861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 727327842264381488794481 545495881698286116595861)
              ·
                refine ⟨25570119454607161715431, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 545495881698286116595861 25570119454607161715431)
                ·
                  rfl

theorem cell20_168067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 2, 6].length) (baseStart_168067 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_168067 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_168067 prefixEnd_168067 := by exact prefixLift 168067
  have htrace : WordTrace (prefixWord ++ tailWord_168067) baseStart_168067 baseEnd_168067 := by
    simpa [prefixWord, tailWord_168067, baseEnd_168067] using wordTrace_append hprefix tailTrace_168067
  have hstable : (prefixWord ++ tailWord_168067).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_168067).length < 2 ^ (prefixWord ++ tailWord_168067).sum := by decide
  have hdescent : baseEnd_168067 < baseStart_168067 := by decide
  rcases family_descends (prefixWord ++ tailWord_168067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_168084 : List Nat := [2, 4, 2, 3, 9]
def baseStart_168084 : Nat := 118140960795 + 168084 * 2 ^ 59
def prefixEnd_168084 : Nat := 4983230072969 + 3 ^ 40 * 168084 * 2
def baseEnd_168084 : Nat := 947137254654876315797

theorem tailTrace_168084 : CollatzResearch.WordTrace tailWord_168084 prefixEnd_168084 947137254654876315797 := by
  unfold tailWord_168084
  simp only [CollatzResearch.WordTrace]
  refine ⟨3065263561533924653435653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4087018082045232871247537 3065263561533924653435653)
  ·
    refine ⟨574736917787610872519185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3065263561533924653435653 574736917787610872519185)
    ·
      refine ⟨431052688340708154389389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 574736917787610872519185 431052688340708154389389)
      ·
        refine ⟨161644758127765557896021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 431052688340708154389389 161644758127765557896021)
        ·
          refine ⟨947137254654876315797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 9 161644758127765557896021 947137254654876315797)
          ·
            rfl

theorem cell20_168084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 9].length) (baseStart_168084 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_168084 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_168084 prefixEnd_168084 := by exact prefixLift 168084
  have htrace : WordTrace (prefixWord ++ tailWord_168084) baseStart_168084 baseEnd_168084 := by
    simpa [prefixWord, tailWord_168084, baseEnd_168084] using wordTrace_append hprefix tailTrace_168084
  have hstable : (prefixWord ++ tailWord_168084).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_168084).length < 2 ^ (prefixWord ++ tailWord_168084).sum := by decide
  have hdescent : baseEnd_168084 < baseStart_168084 := by decide
  rcases family_descends (prefixWord ++ tailWord_168084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_168086 : List Nat := [5, 3, 2, 1, 1, 1, 1, 4, 2]
def baseStart_168086 : Nat := 118140960795 + 168086 * 2 ^ 59
def prefixEnd_168086 : Nat := 4983230072969 + 3 ^ 40 * 168086 * 2
def baseEnd_168086 : Nat := 76719030481541863512883

theorem tailTrace_168086 : CollatzResearch.WordTrace tailWord_168086 prefixEnd_168086 76719030481541863512883 := by
  unfold tailWord_168086
  simp only [CollatzResearch.WordTrace]
  refine ⟨383162504316287728027757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 4087066712707069098962741 383162504316287728027757)
  ·
    refine ⟨143685939118607898010409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 383162504316287728027757 143685939118607898010409)
    ·
      refine ⟨107764454338955923507807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 143685939118607898010409 107764454338955923507807)
      ·
        refine ⟨161646681508433885261711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107764454338955923507807 161646681508433885261711)
        ·
          refine ⟨242470022262650827892567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 161646681508433885261711 242470022262650827892567)
          ·
            refine ⟨363705033393976241838851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 242470022262650827892567 363705033393976241838851)
            ·
              refine ⟨545557550090964362758277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 363705033393976241838851 545557550090964362758277)
              ·
                refine ⟨102292040642055818017177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 545557550090964362758277 102292040642055818017177)
                ·
                  refine ⟨76719030481541863512883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 102292040642055818017177 76719030481541863512883)
                  ·
                    rfl

theorem cell20_168086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 1, 1, 4, 2].length) (baseStart_168086 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_168086 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_168086 prefixEnd_168086 := by exact prefixLift 168086
  have htrace : WordTrace (prefixWord ++ tailWord_168086) baseStart_168086 baseEnd_168086 := by
    simpa [prefixWord, tailWord_168086, baseEnd_168086] using wordTrace_append hprefix tailTrace_168086
  have hstable : (prefixWord ++ tailWord_168086).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_168086).length < 2 ^ (prefixWord ++ tailWord_168086).sum := by decide
  have hdescent : baseEnd_168086 < baseStart_168086 := by decide
  rcases family_descends (prefixWord ++ tailWord_168086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_168090 : List Nat := [3, 1, 1, 5, 2, 2, 2, 2, 2]
def baseStart_168090 : Nat := 118140960795 + 168090 * 2 ^ 59
def prefixEnd_168090 : Nat := 4983230072969 + 3 ^ 40 * 168090 * 2
def baseEnd_168090 : Nat := 76720856190535627379533

theorem tailTrace_168090 : CollatzResearch.WordTrace tailWord_168090 prefixEnd_168090 76720856190535627379533 := by
  unfold tailWord_168090
  simp only [CollatzResearch.WordTrace]
  refine ⟨1532686490261528082897431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4087163974030741554393149 1532686490261528082897431)
  ·
    refine ⟨2299029735392292124346147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1532686490261528082897431 2299029735392292124346147)
    ·
      refine ⟨3448544603088438186519221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2299029735392292124346147 3448544603088438186519221)
      ·
        refine ⟨323301056539541079986177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 3448544603088438186519221 323301056539541079986177)
        ·
          refine ⟨242475792404655809989633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 323301056539541079986177 242475792404655809989633)
          ·
            refine ⟨181856844303491857492225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 242475792404655809989633 181856844303491857492225)
            ·
              refine ⟨136392633227618893119169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 181856844303491857492225 136392633227618893119169)
              ·
                refine ⟨102294474920714169839377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 136392633227618893119169 102294474920714169839377)
                ·
                  refine ⟨76720856190535627379533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 102294474920714169839377 76720856190535627379533)
                  ·
                    rfl

theorem cell20_168090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 2, 2, 2, 2].length) (baseStart_168090 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_168090 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_168090 prefixEnd_168090 := by exact prefixLift 168090
  have htrace : WordTrace (prefixWord ++ tailWord_168090) baseStart_168090 baseEnd_168090 := by
    simpa [prefixWord, tailWord_168090, baseEnd_168090] using wordTrace_append hprefix tailTrace_168090
  have hstable : (prefixWord ++ tailWord_168090).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_168090).length < 2 ^ (prefixWord ++ tailWord_168090).sum := by decide
  have hdescent : baseEnd_168090 < baseStart_168090 := by decide
  rcases family_descends (prefixWord ++ tailWord_168090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_168132 : List Nat := [2, 3, 3, 1, 2, 1, 1, 5, 2]
def baseStart_168132 : Nat := 118140960795 + 168132 * 2 ^ 59
def prefixEnd_168132 : Nat := 4983230072969 + 3 ^ 40 * 168132 * 2
def baseEnd_168132 : Nat := 76740026134970147979361

theorem tailTrace_168132 : CollatzResearch.WordTrace tailWord_168132 prefixEnd_168132 76740026134970147979361 := by
  unfold tailWord_168132
  simp only [CollatzResearch.WordTrace]
  refine ⟨3066138913446976752309325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4088185217929302336412433 3066138913446976752309325)
  ·
    refine ⟨1149802092542616282115997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3066138913446976752309325 1149802092542616282115997)
    ·
      refine ⟨431175784703481105793499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1149802092542616282115997 431175784703481105793499)
      ·
        refine ⟨646763677055221658690249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 431175784703481105793499 646763677055221658690249)
        ·
          refine ⟨485072757791416244017687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 646763677055221658690249 485072757791416244017687)
          ·
            refine ⟨727609136687124366026531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 485072757791416244017687 727609136687124366026531)
            ·
              refine ⟨1091413705030686549039797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 727609136687124366026531 1091413705030686549039797)
              ·
                refine ⟨102320034846626863972481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1091413705030686549039797 102320034846626863972481)
                ·
                  refine ⟨76740026134970147979361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 102320034846626863972481 76740026134970147979361)
                  ·
                    rfl

theorem cell20_168132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 1, 5, 2].length) (baseStart_168132 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_168132 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_168132 prefixEnd_168132 := by exact prefixLift 168132
  have htrace : WordTrace (prefixWord ++ tailWord_168132) baseStart_168132 baseEnd_168132 := by
    simpa [prefixWord, tailWord_168132, baseEnd_168132] using wordTrace_append hprefix tailTrace_168132
  have hstable : (prefixWord ++ tailWord_168132).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_168132).length < 2 ^ (prefixWord ++ tailWord_168132).sum := by decide
  have hdescent : baseEnd_168132 < baseStart_168132 := by decide
  rcases family_descends (prefixWord ++ tailWord_168132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_168146 : List Nat := [3, 2, 2, 2, 1, 2, 3, 2, 3]
def baseStart_168146 : Nat := 118140960795 + 168146 * 2 ^ 59
def prefixEnd_168146 : Nat := 4983230072969 + 3 ^ 40 * 168146 * 2
def baseEnd_168146 : Nat := 76746416116448321512637

theorem tailTrace_168146 : CollatzResearch.WordTrace tailWord_168146 prefixEnd_168146 76746416116448321512637 := by
  unfold tailWord_168146
  simp only [CollatzResearch.WordTrace]
  refine ⟨1533197112210808473907073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4088525632562155930418861 1533197112210808473907073)
  ·
    refine ⟨1149897834158106355430305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1533197112210808473907073 1149897834158106355430305)
    ·
      refine ⟨862423375618579766572729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1149897834158106355430305 862423375618579766572729)
      ·
        refine ⟨646817531713934824929547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 862423375618579766572729 646817531713934824929547)
        ·
          refine ⟨970226297570902237394321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 646817531713934824929547 970226297570902237394321)
          ·
            refine ⟨727669723178176678045741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 970226297570902237394321 727669723178176678045741)
            ·
              refine ⟨272876146191816254267153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 727669723178176678045741 272876146191816254267153)
              ·
                refine ⟨204657109643862190700365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 272876146191816254267153 204657109643862190700365)
                ·
                  refine ⟨76746416116448321512637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 204657109643862190700365 76746416116448321512637)
                  ·
                    rfl

theorem cell20_168146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 3, 2, 3].length) (baseStart_168146 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_168146 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_168146 prefixEnd_168146 := by exact prefixLift 168146
  have htrace : WordTrace (prefixWord ++ tailWord_168146) baseStart_168146 baseEnd_168146 := by
    simpa [prefixWord, tailWord_168146, baseEnd_168146] using wordTrace_append hprefix tailTrace_168146
  have hstable : (prefixWord ++ tailWord_168146).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_168146).length < 2 ^ (prefixWord ++ tailWord_168146).sum := by decide
  have hdescent : baseEnd_168146 < baseStart_168146 := by decide
  rcases family_descends (prefixWord ++ tailWord_168146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_168153 : List Nat := [1, 2, 1, 2, 3, 1, 4, 4, 2]
def baseStart_168153 : Nat := 118140960795 + 168153 * 2 ^ 59
def prefixEnd_168153 : Nat := 4983230072969 + 3 ^ 40 * 168153 * 2
def baseEnd_168153 : Nat := 76749611107187408279275

theorem tailTrace_168153 : CollatzResearch.WordTrace tailWord_168153 prefixEnd_168153 76749611107187408279275 := by
  unfold tailWord_168153
  simp only [CollatzResearch.WordTrace]
  refine ⟨6133043759817874091133113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4088695839878582727422075 6133043759817874091133113)
  ·
    refine ⟨4599782819863405568349835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6133043759817874091133113 4599782819863405568349835)
    ·
      refine ⟨6899674229795108352524753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4599782819863405568349835 6899674229795108352524753)
      ·
        refine ⟨5174755672346331264393565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6899674229795108352524753 5174755672346331264393565)
        ·
          refine ⟨1940533377129874224147587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5174755672346331264393565 1940533377129874224147587)
          ·
            refine ⟨2910800065694811336221381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1940533377129874224147587 2910800065694811336221381)
            ·
              refine ⟨545775012317777125541509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2910800065694811336221381 545775012317777125541509)
              ·
                refine ⟨102332814809583211039033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 545775012317777125541509 102332814809583211039033)
                ·
                  refine ⟨76749611107187408279275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 102332814809583211039033 76749611107187408279275)
                  ·
                    rfl

theorem cell20_168153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 4, 4, 2].length) (baseStart_168153 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_168153 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_168153 prefixEnd_168153 := by exact prefixLift 168153
  have htrace : WordTrace (prefixWord ++ tailWord_168153) baseStart_168153 baseEnd_168153 := by
    simpa [prefixWord, tailWord_168153, baseEnd_168153] using wordTrace_append hprefix tailTrace_168153
  have hstable : (prefixWord ++ tailWord_168153).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_168153).length < 2 ^ (prefixWord ++ tailWord_168153).sum := by decide
  have hdescent : baseEnd_168153 < baseStart_168153 := by decide
  rcases family_descends (prefixWord ++ tailWord_168153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_168218 : List Nat := [3, 1, 1, 3, 5, 1, 2, 1, 3]
def baseStart_168218 : Nat := 118140960795 + 168218 * 2 ^ 59
def prefixEnd_168218 : Nat := 4983230072969 + 3 ^ 40 * 168218 * 2
def baseEnd_168218 : Nat := 76779278878336071112343

theorem tailTrace_168218 : CollatzResearch.WordTrace tailWord_168218 prefixEnd_168218 76779278878336071112343 := by
  unfold tailWord_168218
  simp only [CollatzResearch.WordTrace]
  refine ⟨1533853626145597548062327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4090276336388260128166205 1533853626145597548062327)
  ·
    refine ⟨2300780439218396322093491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1533853626145597548062327 2300780439218396322093491)
    ·
      refine ⟨3451170658827594483140237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2300780439218396322093491 3451170658827594483140237)
      ·
        refine ⟨1294188997060347931177589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3451170658827594483140237 1294188997060347931177589)
        ·
          refine ⟨121330218474407618547899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 1294188997060347931177589 121330218474407618547899)
          ·
            refine ⟨181995327711611427821849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 121330218474407618547899 181995327711611427821849)
            ·
              refine ⟨136496495783708570866387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 181995327711611427821849 136496495783708570866387)
              ·
                refine ⟨204744743675562856299581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 136496495783708570866387 204744743675562856299581)
                ·
                  refine ⟨76779278878336071112343, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 204744743675562856299581 76779278878336071112343)
                  ·
                    rfl

theorem cell20_168218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 5, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 5, 1, 2, 1, 3].length) (baseStart_168218 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_168218 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_168218 prefixEnd_168218 := by exact prefixLift 168218
  have htrace : WordTrace (prefixWord ++ tailWord_168218) baseStart_168218 baseEnd_168218 := by
    simpa [prefixWord, tailWord_168218, baseEnd_168218] using wordTrace_append hprefix tailTrace_168218
  have hstable : (prefixWord ++ tailWord_168218).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_168218).length < 2 ^ (prefixWord ++ tailWord_168218).sum := by decide
  have hdescent : baseEnd_168218 < baseStart_168218 := by decide
  rcases family_descends (prefixWord ++ tailWord_168218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_168257 : List Nat := [1, 2, 5, 2, 10]
def baseStart_168257 : Nat := 118140960795 + 168257 * 2 ^ 59
def prefixEnd_168257 : Nat := 4983230072969 + 3 ^ 40 * 168257 * 2
def baseEnd_168257 : Nat := 948112093099077392743

theorem tailTrace_168257 : CollatzResearch.WordTrace tailWord_168257 prefixEnd_168257 948112093099077392743 := by
  unfold tailWord_168257
  simp only [CollatzResearch.WordTrace]
  refine ⟨6136836951441099852919025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4091224634294066568612683 6136836951441099852919025)
  ·
    refine ⟨4602627713580824889689269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6136836951441099852919025 4602627713580824889689269)
    ·
      refine ⟨431496348148202333408369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 4602627713580824889689269 431496348148202333408369)
      ·
        refine ⟨323622261111151750056277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 431496348148202333408369 323622261111151750056277)
        ·
          refine ⟨948112093099077392743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 10 323622261111151750056277 948112093099077392743)
          ·
            rfl

theorem cell20_168257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 10].length) (baseStart_168257 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_168257 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_168257 prefixEnd_168257 := by exact prefixLift 168257
  have htrace : WordTrace (prefixWord ++ tailWord_168257) baseStart_168257 baseEnd_168257 := by
    simpa [prefixWord, tailWord_168257, baseEnd_168257] using wordTrace_append hprefix tailTrace_168257
  have hstable : (prefixWord ++ tailWord_168257).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_168257).length < 2 ^ (prefixWord ++ tailWord_168257).sum := by decide
  have hdescent : baseEnd_168257 < baseStart_168257 := by decide
  rcases family_descends (prefixWord ++ tailWord_168257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_168264 : List Nat := [2, 1, 3, 1, 1, 2, 2, 3, 5]
def baseStart_168264 : Nat := 118140960795 + 168264 * 2 ^ 59
def prefixEnd_168264 : Nat := 4983230072969 + 3 ^ 40 * 168264 * 2
def baseEnd_168264 : Nat := 76800274531764355578821

theorem tailTrace_168264 : CollatzResearch.WordTrace tailWord_168264 prefixEnd_168264 76800274531764355578821 := by
  unfold tailWord_168264
  simp only [CollatzResearch.WordTrace]
  refine ⟨3068546131207870024211923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4091394841610493365615897 3068546131207870024211923)
  ·
    refine ⟨4602819196811805036317885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3068546131207870024211923 4602819196811805036317885)
    ·
      refine ⟨1726057198804426888619207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4602819196811805036317885 1726057198804426888619207)
      ·
        refine ⟨2589085798206640332928811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1726057198804426888619207 2589085798206640332928811)
        ·
          refine ⟨3883628697309960499393217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2589085798206640332928811 3883628697309960499393217)
          ·
            refine ⟨2912721522982470374544913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3883628697309960499393217 2912721522982470374544913)
            ·
              refine ⟨2184541142236852780908685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2912721522982470374544913 2184541142236852780908685)
              ·
                refine ⟨819202928338819792840757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2184541142236852780908685 819202928338819792840757)
                ·
                  refine ⟨76800274531764355578821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 819202928338819792840757 76800274531764355578821)
                  ·
                    rfl

theorem cell20_168264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 2, 3, 5].length) (baseStart_168264 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_168264 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_168264 prefixEnd_168264 := by exact prefixLift 168264
  have htrace : WordTrace (prefixWord ++ tailWord_168264) baseStart_168264 baseEnd_168264 := by
    simpa [prefixWord, tailWord_168264, baseEnd_168264] using wordTrace_append hprefix tailTrace_168264
  have hstable : (prefixWord ++ tailWord_168264).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_168264).length < 2 ^ (prefixWord ++ tailWord_168264).sum := by decide
  have hdescent : baseEnd_168264 < baseStart_168264 := by decide
  rcases family_descends (prefixWord ++ tailWord_168264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_168284 : List Nat := [2, 2, 4, 3, 1, 1, 1, 2, 4]
def baseStart_168284 : Nat := 118140960795 + 168284 * 2 ^ 59
def prefixEnd_168284 : Nat := 4983230072969 + 3 ^ 40 * 168284 * 2
def baseEnd_168284 : Nat := 76809403076733174912073

theorem tailTrace_168284 : CollatzResearch.WordTrace tailWord_168284 prefixEnd_168284 76809403076733174912073 := by
  unfold tailWord_168284
  simp only [CollatzResearch.WordTrace]
  refine ⟨3068910861171641732075953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4091881148228855642767937 3068910861171641732075953)
  ·
    refine ⟨2301683145878731299056965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3068910861171641732075953 2301683145878731299056965)
    ·
      refine ⟨431565589852262118573181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2301683145878731299056965 431565589852262118573181)
      ·
        refine ⟨161837096194598294464943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 431565589852262118573181 161837096194598294464943)
        ·
          refine ⟨242755644291897441697415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 161837096194598294464943 242755644291897441697415)
          ·
            refine ⟨364133466437846162546123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 242755644291897441697415 364133466437846162546123)
            ·
              refine ⟨546200199656769243819185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 364133466437846162546123 546200199656769243819185)
              ·
                refine ⟨409650149742576932864389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 546200199656769243819185 409650149742576932864389)
                ·
                  refine ⟨76809403076733174912073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 409650149742576932864389 76809403076733174912073)
                  ·
                    rfl

theorem cell20_168284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 1, 1, 2, 4].length) (baseStart_168284 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_168284 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_168284 prefixEnd_168284 := by exact prefixLift 168284
  have htrace : WordTrace (prefixWord ++ tailWord_168284) baseStart_168284 baseEnd_168284 := by
    simpa [prefixWord, tailWord_168284, baseEnd_168284] using wordTrace_append hprefix tailTrace_168284
  have hstable : (prefixWord ++ tailWord_168284).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_168284).length < 2 ^ (prefixWord ++ tailWord_168284).sum := by decide
  have hdescent : baseEnd_168284 < baseStart_168284 := by decide
  rcases family_descends (prefixWord ++ tailWord_168284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_168342 : List Nat := [5, 3, 1, 2, 1, 2, 2, 4]
def baseStart_168342 : Nat := 118140960795 + 168342 * 2 ^ 59
def prefixEnd_168342 : Nat := 4983230072969 + 3 ^ 40 * 168342 * 2
def baseEnd_168342 : Nat := 25611958619047583659501

theorem tailTrace_168342 : CollatzResearch.WordTrace tailWord_168342 prefixEnd_168342 25611958619047583659501 := by
  unfold tailWord_168342
  simp only [CollatzResearch.WordTrace]
  refine ⟨383746072258322460610205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 4093291437422106246508853 383746072258322460610205)
  ·
    refine ⟨143904777096870922728827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 383746072258322460610205 143904777096870922728827)
    ·
      refine ⟨215857165645306384093241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 143904777096870922728827 215857165645306384093241)
      ·
        refine ⟨161892874233979788069931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 215857165645306384093241 161892874233979788069931)
        ·
          refine ⟨242839311350969682104897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 161892874233979788069931 242839311350969682104897)
          ·
            refine ⟨182129483513227261578673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 242839311350969682104897 182129483513227261578673)
            ·
              refine ⟨136597112634920446184005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 182129483513227261578673 136597112634920446184005)
              ·
                refine ⟨25611958619047583659501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 136597112634920446184005 25611958619047583659501)
                ·
                  rfl

theorem cell20_168342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 2, 2, 4].length) (baseStart_168342 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_168342 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_168342 prefixEnd_168342 := by exact prefixLift 168342
  have htrace : WordTrace (prefixWord ++ tailWord_168342) baseStart_168342 baseEnd_168342 := by
    simpa [prefixWord, tailWord_168342, baseEnd_168342] using wordTrace_append hprefix tailTrace_168342
  have hstable : (prefixWord ++ tailWord_168342).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_168342).length < 2 ^ (prefixWord ++ tailWord_168342).sum := by decide
  have hdescent : baseEnd_168342 < baseStart_168342 := by decide
  rcases family_descends (prefixWord ++ tailWord_168342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_168381 : List Nat := [1, 4, 1, 2, 2, 4, 1, 1, 4]
def baseStart_168381 : Nat := 118140960795 + 168381 * 2 ^ 59
def prefixEnd_168381 : Nat := 4983230072969 + 3 ^ 40 * 168381 * 2
def baseEnd_168381 : Nat := 76853676519831948678343

theorem tailTrace_168381 : CollatzResearch.WordTrace tailWord_168381 prefixEnd_168381 76853676519831948678343 := by
  unfold tailWord_168381
  simp only [CollatzResearch.WordTrace]
  refine ⟨6141359602991869030432997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4094239735327912686955331 6141359602991869030432997)
  ·
    refine ⟨1151504925560975443206187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6141359602991869030432997 1151504925560975443206187)
    ·
      refine ⟨1727257388341463164809281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1151504925560975443206187 1727257388341463164809281)
      ·
        refine ⟨1295443041256097373606961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1727257388341463164809281 1295443041256097373606961)
        ·
          refine ⟨971582280942073030205221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1295443041256097373606961 971582280942073030205221)
          ·
            refine ⟨182171677676638693163479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 971582280942073030205221 182171677676638693163479)
            ·
              refine ⟨273257516514958039745219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 182171677676638693163479 273257516514958039745219)
              ·
                refine ⟨409886274772437059617829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 273257516514958039745219 409886274772437059617829)
                ·
                  refine ⟨76853676519831948678343, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 409886274772437059617829 76853676519831948678343)
                  ·
                    rfl

theorem cell20_168381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 4, 1, 1, 4].length) (baseStart_168381 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_168381 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_168381 prefixEnd_168381 := by exact prefixLift 168381
  have htrace : WordTrace (prefixWord ++ tailWord_168381) baseStart_168381 baseEnd_168381 := by
    simpa [prefixWord, tailWord_168381, baseEnd_168381] using wordTrace_append hprefix tailTrace_168381
  have hstable : (prefixWord ++ tailWord_168381).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_168381).length < 2 ^ (prefixWord ++ tailWord_168381).sum := by decide
  have hdescent : baseEnd_168381 < baseStart_168381 := by decide
  rcases family_descends (prefixWord ++ tailWord_168381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_168433 : List Nat := [1, 2, 2, 2, 3, 1, 4, 2, 3]
def baseStart_168433 : Nat := 118140960795 + 168433 * 2 ^ 59
def prefixEnd_168433 : Nat := 4983230072969 + 3 ^ 40 * 168433 * 2
def baseEnd_168433 : Nat := 76877410736750878944797

theorem tailTrace_168433 : CollatzResearch.WordTrace tailWord_168433 prefixEnd_168433 76877410736750878944797 := by
  unfold tailWord_168433
  simp only [CollatzResearch.WordTrace]
  refine ⟨6143256198803481911325953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4095504132535654607550635 6143256198803481911325953)
  ·
    refine ⟨4607442149102611433494465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6143256198803481911325953 4607442149102611433494465)
    ·
      refine ⟨3455581611826958575120849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4607442149102611433494465 3455581611826958575120849)
      ·
        refine ⟨2591686208870218931340637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3455581611826958575120849 2591686208870218931340637)
        ·
          refine ⟨971882328326332099252739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2591686208870218931340637 971882328326332099252739)
          ·
            refine ⟨1457823492489498148879109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 971882328326332099252739 1457823492489498148879109)
            ·
              refine ⟨273341904841780902914833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1457823492489498148879109 273341904841780902914833)
              ·
                refine ⟨205006428631335677186125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 273341904841780902914833 205006428631335677186125)
                ·
                  refine ⟨76877410736750878944797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 205006428631335677186125 76877410736750878944797)
                  ·
                    rfl

theorem cell20_168433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 4, 2, 3].length) (baseStart_168433 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_168433 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_168433 prefixEnd_168433 := by exact prefixLift 168433
  have htrace : WordTrace (prefixWord ++ tailWord_168433) baseStart_168433 baseEnd_168433 := by
    simpa [prefixWord, tailWord_168433, baseEnd_168433] using wordTrace_append hprefix tailTrace_168433
  have hstable : (prefixWord ++ tailWord_168433).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_168433).length < 2 ^ (prefixWord ++ tailWord_168433).sum := by decide
  have hdescent : baseEnd_168433 < baseStart_168433 := by decide
  rcases family_descends (prefixWord ++ tailWord_168433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_168484 : List Nat := [2, 3, 1, 5, 2, 1, 1, 2, 3]
def baseStart_168484 : Nat := 118140960795 + 168484 * 2 ^ 59
def prefixEnd_168484 : Nat := 4983230072969 + 3 ^ 40 * 168484 * 2
def baseEnd_168484 : Nat := 76900688526421368244589

theorem tailTrace_168484 : CollatzResearch.WordTrace tailWord_168484 prefixEnd_168484 76900688526421368244589 := by
  unfold tailWord_168484
  simp only [CollatzResearch.WordTrace]
  refine ⟨3072558160809358810716253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4096744214412478414288337 3072558160809358810716253)
  ·
    refine ⟨1152209310303509554018595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3072558160809358810716253 1152209310303509554018595)
    ·
      refine ⟨1728313965455264331027893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1152209310303509554018595 1728313965455264331027893)
      ·
        refine ⟨162029434261431031033865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 1728313965455264331027893 162029434261431031033865)
        ·
          refine ⟨121522075696073273275399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 162029434261431031033865 121522075696073273275399)
          ·
            refine ⟨182283113544109909913099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 121522075696073273275399 182283113544109909913099)
            ·
              refine ⟨273424670316164864869649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 182283113544109909913099 273424670316164864869649)
              ·
                refine ⟨205068502737123648652237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 273424670316164864869649 205068502737123648652237)
                ·
                  refine ⟨76900688526421368244589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 205068502737123648652237 76900688526421368244589)
                  ·
                    rfl

theorem cell20_168484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 2, 1, 1, 2, 3].length) (baseStart_168484 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_168484 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_168484 prefixEnd_168484 := by exact prefixLift 168484
  have htrace : WordTrace (prefixWord ++ tailWord_168484) baseStart_168484 baseEnd_168484 := by
    simpa [prefixWord, tailWord_168484, baseEnd_168484] using wordTrace_append hprefix tailTrace_168484
  have hstable : (prefixWord ++ tailWord_168484).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_168484).length < 2 ^ (prefixWord ++ tailWord_168484).sum := by decide
  have hdescent : baseEnd_168484 < baseStart_168484 := by decide
  rcases family_descends (prefixWord ++ tailWord_168484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_168488 : List Nat := [2, 1, 5, 2, 1, 1, 3, 2, 3]
def baseStart_168488 : Nat := 118140960795 + 168488 * 2 ^ 59
def prefixEnd_168488 : Nat := 4983230072969 + 3 ^ 40 * 168488 * 2
def baseEnd_168488 : Nat := 76902514235415132111239

theorem tailTrace_168488 : CollatzResearch.WordTrace tailWord_168488 prefixEnd_168488 76902514235415132111239 := by
  unfold tailWord_168488
  simp only [CollatzResearch.WordTrace]
  refine ⟨3072631106802113152289059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4096841475736150869718745 3072631106802113152289059)
  ·
    refine ⟨4608946660203169728433589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3072631106802113152289059 4608946660203169728433589)
    ·
      refine ⟨432088749394047162040649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 4608946660203169728433589 432088749394047162040649)
      ·
        refine ⟨324066562045535371530487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 432088749394047162040649 324066562045535371530487)
        ·
          refine ⟨486099843068303057295731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 324066562045535371530487 486099843068303057295731)
          ·
            refine ⟨729149764602454585943597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 486099843068303057295731 729149764602454585943597)
            ·
              refine ⟨273431161725920469728849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 729149764602454585943597 273431161725920469728849)
              ·
                refine ⟨205073371294440352296637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 273431161725920469728849 205073371294440352296637)
                ·
                  refine ⟨76902514235415132111239, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 205073371294440352296637 76902514235415132111239)
                  ·
                    rfl

theorem cell20_168488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 3, 2, 3].length) (baseStart_168488 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_168488 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_168488 prefixEnd_168488 := by exact prefixLift 168488
  have htrace : WordTrace (prefixWord ++ tailWord_168488) baseStart_168488 baseEnd_168488 := by
    simpa [prefixWord, tailWord_168488, baseEnd_168488] using wordTrace_append hprefix tailTrace_168488
  have hstable : (prefixWord ++ tailWord_168488).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_168488).length < 2 ^ (prefixWord ++ tailWord_168488).sum := by decide
  have hdescent : baseEnd_168488 < baseStart_168488 := by decide
  rcases family_descends (prefixWord ++ tailWord_168488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_168523 : List Nat := [1, 1, 1, 1, 3, 1, 8, 4]
def baseStart_168523 : Nat := 118140960795 + 168523 * 2 ^ 59
def prefixEnd_168523 : Nat := 4983230072969 + 3 ^ 40 * 168523 * 2
def baseEnd_168523 : Nat := 25639496396370188648143

theorem tailTrace_168523 : CollatzResearch.WordTrace tailWord_168523 prefixEnd_168523 25639496396370188648143 := by
  unfold tailWord_168523
  simp only [CollatzResearch.WordTrace]
  refine ⟨6146538768477427282102223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4097692512318284854734815 6146538768477427282102223)
  ·
    refine ⟨9219808152716140923153335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6146538768477427282102223 9219808152716140923153335)
    ·
      refine ⟨13829712229074211384730003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9219808152716140923153335 13829712229074211384730003)
      ·
        refine ⟨20744568343611317077095005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13829712229074211384730003 20744568343611317077095005)
        ·
          refine ⟨7779213128854243903910627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20744568343611317077095005 7779213128854243903910627)
          ·
            refine ⟨11668819693281365855865941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7779213128854243903910627 11668819693281365855865941)
            ·
              refine ⟨136743980780641006123429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 11668819693281365855865941 136743980780641006123429)
              ·
                refine ⟨25639496396370188648143, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 136743980780641006123429 25639496396370188648143)
                ·
                  rfl

theorem cell20_168523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 8, 4].length) (baseStart_168523 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_168523 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_168523 prefixEnd_168523 := by exact prefixLift 168523
  have htrace : WordTrace (prefixWord ++ tailWord_168523) baseStart_168523 baseEnd_168523 := by
    simpa [prefixWord, tailWord_168523, baseEnd_168523] using wordTrace_append hprefix tailTrace_168523
  have hstable : (prefixWord ++ tailWord_168523).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_168523).length < 2 ^ (prefixWord ++ tailWord_168523).sum := by decide
  have hdescent : baseEnd_168523 < baseStart_168523 := by decide
  rcases family_descends (prefixWord ++ tailWord_168523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_168530 : List Nat := [3, 2, 2, 1, 2, 1, 1, 1, 7]
def baseStart_168530 : Nat := 118140960795 + 168530 * 2 ^ 59
def prefixEnd_168530 : Nat := 4983230072969 + 3 ^ 40 * 168530 * 2
def baseEnd_168530 : Nat := 76921684179849652711067

theorem tailTrace_168530 : CollatzResearch.WordTrace tailWord_168530 prefixEnd_168530 76921684179849652711067 := by
  unfold tailWord_168530
  simp only [CollatzResearch.WordTrace]
  refine ⟨1536698519863016869401761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4097862719634711651738029 1536698519863016869401761)
  ·
    refine ⟨1152523889897262652051321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1536698519863016869401761 1152523889897262652051321)
    ·
      refine ⟨864392917422946989038491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1152523889897262652051321 864392917422946989038491)
      ·
        refine ⟨1296589376134420483557737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 864392917422946989038491 1296589376134420483557737)
        ·
          refine ⟨972442032100815362668303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1296589376134420483557737 972442032100815362668303)
          ·
            refine ⟨1458663048151223044002455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 972442032100815362668303 1458663048151223044002455)
            ·
              refine ⟨2187994572226834566003683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1458663048151223044002455 2187994572226834566003683)
              ·
                refine ⟨3281991858340251849005525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2187994572226834566003683 3281991858340251849005525)
                ·
                  refine ⟨76921684179849652711067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3281991858340251849005525 76921684179849652711067)
                  ·
                    rfl

theorem cell20_168530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 1, 1, 7].length) (baseStart_168530 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_168530 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_168530 prefixEnd_168530 := by exact prefixLift 168530
  have htrace : WordTrace (prefixWord ++ tailWord_168530) baseStart_168530 baseEnd_168530 := by
    simpa [prefixWord, tailWord_168530, baseEnd_168530] using wordTrace_append hprefix tailTrace_168530
  have hstable : (prefixWord ++ tailWord_168530).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_168530).length < 2 ^ (prefixWord ++ tailWord_168530).sum := by decide
  have hdescent : baseEnd_168530 < baseStart_168530 := by decide
  rcases family_descends (prefixWord ++ tailWord_168530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_168533 : List Nat := [1, 3, 2, 2, 1, 1, 5, 3, 2]
def baseStart_168533 : Nat := 118140960795 + 168533 * 2 ^ 59
def prefixEnd_168533 : Nat := 4983230072969 + 3 ^ 40 * 168533 * 2
def baseEnd_168533 : Nat := 76923053461594975611055

theorem tailTrace_168533 : CollatzResearch.WordTrace tailWord_168533 prefixEnd_168533 76923053461594975611055 := by
  unfold tailWord_168533
  simp only [CollatzResearch.WordTrace]
  refine ⟨6146903498441198989966253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4097935665627465993310835 6146903498441198989966253)
  ·
    refine ⟨2305088811915449621237345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6146903498441198989966253 2305088811915449621237345)
    ·
      refine ⟨1728816608936587215928009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2305088811915449621237345 1728816608936587215928009)
      ·
        refine ⟨1296612456702440411946007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1728816608936587215928009 1296612456702440411946007)
        ·
          refine ⟨1944918685053660617919011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1296612456702440411946007 1944918685053660617919011)
          ·
            refine ⟨2917378027580490926878517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1944918685053660617919011 2917378027580490926878517)
            ·
              refine ⟨273504190085671024394861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2917378027580490926878517 273504190085671024394861)
              ·
                refine ⟨102564071282126634148073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 273504190085671024394861 102564071282126634148073)
                ·
                  refine ⟨76923053461594975611055, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 102564071282126634148073 76923053461594975611055)
                  ·
                    rfl

theorem cell20_168533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 5, 3, 2].length) (baseStart_168533 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_168533 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_168533 prefixEnd_168533 := by exact prefixLift 168533
  have htrace : WordTrace (prefixWord ++ tailWord_168533) baseStart_168533 baseEnd_168533 := by
    simpa [prefixWord, tailWord_168533, baseEnd_168533] using wordTrace_append hprefix tailTrace_168533
  have hstable : (prefixWord ++ tailWord_168533).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_168533).length < 2 ^ (prefixWord ++ tailWord_168533).sum := by decide
  have hdescent : baseEnd_168533 < baseStart_168533 := by decide
  rcases family_descends (prefixWord ++ tailWord_168533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_168540 : List Nat := [2, 2, 4, 1, 3, 2, 6]
def baseStart_168540 : Nat := 118140960795 + 168540 * 2 ^ 59
def prefixEnd_168540 : Nat := 4983230072969 + 3 ^ 40 * 168540 * 2
def baseEnd_168540 : Nat := 8547360939148229153077

theorem tailTrace_168540 : CollatzResearch.WordTrace tailWord_168540 prefixEnd_168540 8547360939148229153077 := by
  unfold tailWord_168540
  simp only [CollatzResearch.WordTrace]
  refine ⟨3073579404707919592735537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4098105872943892790314049 3073579404707919592735537)
  ·
    refine ⟨2305184553530939694551653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3073579404707919592735537 2305184553530939694551653)
    ·
      refine ⟨432222103787051192728435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2305184553530939694551653 432222103787051192728435)
      ·
        refine ⟨648333155680576789092653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 432222103787051192728435 648333155680576789092653)
        ·
          refine ⟨243124933380216295909745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 648333155680576789092653 243124933380216295909745)
          ·
            refine ⟨182343700035162221932309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 243124933380216295909745 182343700035162221932309)
            ·
              refine ⟨8547360939148229153077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 182343700035162221932309 8547360939148229153077)
              ·
                rfl

theorem cell20_168540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 2, 6].length) (baseStart_168540 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_168540 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_168540 prefixEnd_168540 := by exact prefixLift 168540
  have htrace : WordTrace (prefixWord ++ tailWord_168540) baseStart_168540 baseEnd_168540 := by
    simpa [prefixWord, tailWord_168540, baseEnd_168540] using wordTrace_append hprefix tailTrace_168540
  have hstable : (prefixWord ++ tailWord_168540).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_168540).length < 2 ^ (prefixWord ++ tailWord_168540).sum := by decide
  have hdescent : baseEnd_168540 < baseStart_168540 := by decide
  rcases family_descends (prefixWord ++ tailWord_168540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_168544 : List Nat := [2, 1, 1, 3, 2, 1, 10]
def baseStart_168544 : Nat := 118140960795 + 168544 * 2 ^ 59
def prefixEnd_168544 : Nat := 4983230072969 + 3 ^ 40 * 168544 * 2
def baseEnd_168544 : Nat := 8547563795703091804927

theorem tailTrace_168544 : CollatzResearch.WordTrace tailWord_168544 prefixEnd_168544 8547563795703091804927 := by
  unfold tailWord_168544
  simp only [CollatzResearch.WordTrace]
  refine ⟨3073652350700673934308343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4098203134267565245744457 3073652350700673934308343)
  ·
    refine ⟨4610478526051010901462515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3073652350700673934308343 4610478526051010901462515)
    ·
      refine ⟨6915717789076516352193773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4610478526051010901462515 6915717789076516352193773)
      ·
        refine ⟨2593394170903693632072665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6915717789076516352193773 2593394170903693632072665)
        ·
          refine ⟨1945045628177770224054499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2593394170903693632072665 1945045628177770224054499)
          ·
            refine ⟨2917568442266655336081749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1945045628177770224054499 2917568442266655336081749)
            ·
              refine ⟨8547563795703091804927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 2917568442266655336081749 8547563795703091804927)
              ·
                rfl

theorem cell20_168544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 10].length) (baseStart_168544 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_168544 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_168544 prefixEnd_168544 := by exact prefixLift 168544
  have htrace : WordTrace (prefixWord ++ tailWord_168544) baseStart_168544 baseEnd_168544 := by
    simpa [prefixWord, tailWord_168544, baseEnd_168544] using wordTrace_append hprefix tailTrace_168544
  have hstable : (prefixWord ++ tailWord_168544).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_168544).length < 2 ^ (prefixWord ++ tailWord_168544).sum := by decide
  have hdescent : baseEnd_168544 < baseStart_168544 := by decide
  rcases family_descends (prefixWord ++ tailWord_168544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_168546 : List Nat := [3, 3, 2, 3, 1, 1, 3, 2, 2]
def baseStart_168546 : Nat := 118140960795 + 168546 * 2 ^ 59
def prefixEnd_168546 : Nat := 4983230072969 + 3 ^ 40 * 168546 * 2
def baseEnd_168546 : Nat := 76928987015824708177669

theorem tailTrace_168546 : CollatzResearch.WordTrace tailWord_168546 prefixEnd_168546 76928987015824708177669 := by
  unfold tailWord_168546
  simp only [CollatzResearch.WordTrace]
  refine ⟨1536844411848525552547373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4098251764929401473459661 1536844411848525552547373)
  ·
    refine ⟨576316654443197082205265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1536844411848525552547373 576316654443197082205265)
    ·
      refine ⟨432237490832397811653949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 576316654443197082205265 432237490832397811653949)
      ·
        refine ⟨162089059062149179370231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 432237490832397811653949 162089059062149179370231)
        ·
          refine ⟨243133588593223769055347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 162089059062149179370231 243133588593223769055347)
          ·
            refine ⟨364700382889835653583021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 243133588593223769055347 364700382889835653583021)
            ·
              refine ⟨136762643583688370093633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 364700382889835653583021 136762643583688370093633)
              ·
                refine ⟨102571982687766277570225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 136762643583688370093633 102571982687766277570225)
                ·
                  refine ⟨76928987015824708177669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 102571982687766277570225 76928987015824708177669)
                  ·
                    rfl

theorem cell20_168546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 1, 3, 2, 2].length) (baseStart_168546 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_168546 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_168546 prefixEnd_168546 := by exact prefixLift 168546
  have htrace : WordTrace (prefixWord ++ tailWord_168546) baseStart_168546 baseEnd_168546 := by
    simpa [prefixWord, tailWord_168546, baseEnd_168546] using wordTrace_append hprefix tailTrace_168546
  have hstable : (prefixWord ++ tailWord_168546).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_168546).length < 2 ^ (prefixWord ++ tailWord_168546).sum := by decide
  have hdescent : baseEnd_168546 < baseStart_168546 := by decide
  rcases family_descends (prefixWord ++ tailWord_168546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_168568 : List Nat := [2, 1, 2, 1, 1, 1, 2, 7, 3]
def baseStart_168568 : Nat := 118140960795 + 168568 * 2 ^ 59
def prefixEnd_168568 : Nat := 4983230072969 + 3 ^ 40 * 168568 * 2
def baseEnd_168568 : Nat := 76939028415290409444245

theorem tailTrace_168568 : CollatzResearch.WordTrace tailWord_168568 prefixEnd_168568 76939028415290409444245 := by
  unfold tailWord_168568
  simp only [CollatzResearch.WordTrace]
  refine ⟨3074090026657199983745179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4098786702209599978326905 3074090026657199983745179)
  ·
    refine ⟨4611135039985799975617769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3074090026657199983745179 4611135039985799975617769)
    ·
      refine ⟨3458351279989349981713327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4611135039985799975617769 3458351279989349981713327)
      ·
        refine ⟨5187526919984024972569991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3458351279989349981713327 5187526919984024972569991)
        ·
          refine ⟨7781290379976037458854987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5187526919984024972569991 7781290379976037458854987)
          ·
            refine ⟨11671935569964056188282481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7781290379976037458854987 11671935569964056188282481)
            ·
              refine ⟨8753951677473042141211861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11671935569964056188282481 8753951677473042141211861)
              ·
                refine ⟨205170742440774425184653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 8753951677473042141211861 205170742440774425184653)
                ·
                  refine ⟨76939028415290409444245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 205170742440774425184653 76939028415290409444245)
                  ·
                    rfl

theorem cell20_168568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 7, 3].length) (baseStart_168568 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_168568 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_168568 prefixEnd_168568 := by exact prefixLift 168568
  have htrace : WordTrace (prefixWord ++ tailWord_168568) baseStart_168568 baseEnd_168568 := by
    simpa [prefixWord, tailWord_168568, baseEnd_168568] using wordTrace_append hprefix tailTrace_168568
  have hstable : (prefixWord ++ tailWord_168568).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_168568).length < 2 ^ (prefixWord ++ tailWord_168568).sum := by decide
  have hdescent : baseEnd_168568 < baseStart_168568 := by decide
  rcases family_descends (prefixWord ++ tailWord_168568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_168613 : List Nat := [1, 3, 1, 2, 1, 2, 1, 5, 4]
def baseStart_168613 : Nat := 118140960795 + 168613 * 2 ^ 59
def prefixEnd_168613 : Nat := 4983230072969 + 3 ^ 40 * 168613 * 2
def baseEnd_168613 : Nat := 76959567641470252944061

theorem tailTrace_168613 : CollatzResearch.WordTrace tailWord_168613 prefixEnd_168613 76959567641470252944061 := by
  unfold tailWord_168613
  simp only [CollatzResearch.WordTrace]
  refine ⟨6149821338151372652878493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4099880892100915101918995 6149821338151372652878493)
  ·
    refine ⟨2306183001806764744829435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6149821338151372652878493 2306183001806764744829435)
    ·
      refine ⟨3459274502710147117244153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2306183001806764744829435 3459274502710147117244153)
      ·
        refine ⟨2594455877032610337933115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3459274502710147117244153 2594455877032610337933115)
        ·
          refine ⟨3891683815548915506899673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2594455877032610337933115 3891683815548915506899673)
          ·
            refine ⟨2918762861661686630174755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3891683815548915506899673 2918762861661686630174755)
            ·
              refine ⟨4378144292492529945262133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2918762861661686630174755 4378144292492529945262133)
              ·
                refine ⟨410451027421174682368325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4378144292492529945262133 410451027421174682368325)
                ·
                  refine ⟨76959567641470252944061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 410451027421174682368325 76959567641470252944061)
                  ·
                    rfl

theorem cell20_168613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 5, 4].length) (baseStart_168613 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_168613 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_168613 prefixEnd_168613 := by exact prefixLift 168613
  have htrace : WordTrace (prefixWord ++ tailWord_168613) baseStart_168613 baseEnd_168613 := by
    simpa [prefixWord, tailWord_168613, baseEnd_168613] using wordTrace_append hprefix tailTrace_168613
  have hstable : (prefixWord ++ tailWord_168613).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_168613).length < 2 ^ (prefixWord ++ tailWord_168613).sum := by decide
  have hdescent : baseEnd_168613 < baseStart_168613 := by decide
  rcases family_descends (prefixWord ++ tailWord_168613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_168689 : List Nat := [1, 2, 2, 2, 2, 2, 1, 4, 4]
def baseStart_168689 : Nat := 118140960795 + 168689 * 2 ^ 59
def prefixEnd_168689 : Nat := 4983230072969 + 3 ^ 40 * 168689 * 2
def baseEnd_168689 : Nat := 76994256112351766410417

theorem tailTrace_168689 : CollatzResearch.WordTrace tailWord_168689 prefixEnd_168689 76994256112351766410417 := by
  unfold tailWord_168689
  simp only [CollatzResearch.WordTrace]
  refine ⟨6152593285876037632645121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4101728857250691755096747 6152593285876037632645121)
  ·
    refine ⟨4614444964407028224483841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6152593285876037632645121 4614444964407028224483841)
    ·
      refine ⟨3460833723305271168362881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4614444964407028224483841 3460833723305271168362881)
      ·
        refine ⟨2595625292478953376272161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3460833723305271168362881 2595625292478953376272161)
        ·
          refine ⟨1946718969359215032204121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2595625292478953376272161 1946718969359215032204121)
          ·
            refine ⟨1460039227019411274153091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1946718969359215032204121 1460039227019411274153091)
            ·
              refine ⟨2190058840529116911229637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1460039227019411274153091 2190058840529116911229637)
              ·
                refine ⟨410636032599209420855557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2190058840529116911229637 410636032599209420855557)
                ·
                  refine ⟨76994256112351766410417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 410636032599209420855557 76994256112351766410417)
                  ·
                    rfl

theorem cell20_168689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 1, 4, 4].length) (baseStart_168689 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_168689 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_168689 prefixEnd_168689 := by exact prefixLift 168689
  have htrace : WordTrace (prefixWord ++ tailWord_168689) baseStart_168689 baseEnd_168689 := by
    simpa [prefixWord, tailWord_168689, baseEnd_168689] using wordTrace_append hprefix tailTrace_168689
  have hstable : (prefixWord ++ tailWord_168689).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_168689).length < 2 ^ (prefixWord ++ tailWord_168689).sum := by decide
  have hdescent : baseEnd_168689 < baseStart_168689 := by decide
  rcases family_descends (prefixWord ++ tailWord_168689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_168696 : List Nat := [2, 1, 2, 1, 1, 2, 5, 6]
def baseStart_168696 : Nat := 118140960795 + 168696 * 2 ^ 59
def prefixEnd_168696 : Nat := 4983230072969 + 3 ^ 40 * 168696 * 2
def baseEnd_168696 : Nat := 25665817034363617725685

theorem tailTrace_168696 : CollatzResearch.WordTrace tailWord_168696 prefixEnd_168696 25665817034363617725685 := by
  unfold tailWord_168696
  simp only [CollatzResearch.WordTrace]
  refine ⟨3076424298425338914074971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4101899064567118552099961 3076424298425338914074971)
  ·
    refine ⟨4614636447638008371112457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3076424298425338914074971 4614636447638008371112457)
    ·
      refine ⟨3460977335728506278334343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4614636447638008371112457 3460977335728506278334343)
      ·
        refine ⟨5191466003592759417501515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3460977335728506278334343 5191466003592759417501515)
        ·
          refine ⟨7787199005389139126252273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5191466003592759417501515 7787199005389139126252273)
          ·
            refine ⟨5840399254041854344689205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7787199005389139126252273 5840399254041854344689205)
            ·
              refine ⟨547537430066423844814613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 5840399254041854344689205 547537430066423844814613)
              ·
                refine ⟨25665817034363617725685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 547537430066423844814613 25665817034363617725685)
                ·
                  rfl

theorem cell20_168696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 5, 6].length) (baseStart_168696 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_168696 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_168696 prefixEnd_168696 := by exact prefixLift 168696
  have htrace : WordTrace (prefixWord ++ tailWord_168696) baseStart_168696 baseEnd_168696 := by
    simpa [prefixWord, tailWord_168696, baseEnd_168696] using wordTrace_append hprefix tailTrace_168696
  have hstable : (prefixWord ++ tailWord_168696).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_168696).length < 2 ^ (prefixWord ++ tailWord_168696).sum := by decide
  have hdescent : baseEnd_168696 < baseStart_168696 := by decide
  rcases family_descends (prefixWord ++ tailWord_168696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_168702 : List Nat := [4, 2, 2, 1, 2, 1, 3, 3, 2]
def baseStart_168702 : Nat := 118140960795 + 168702 * 2 ^ 59
def prefixEnd_168702 : Nat := 4983230072969 + 3 ^ 40 * 168702 * 2
def baseEnd_168702 : Nat := 77000189666581498977031

theorem tailTrace_168702 : CollatzResearch.WordTrace tailWord_168702 prefixEnd_168702 77000189666581498977031 := by
  unfold tailWord_168702
  simp only [CollatzResearch.WordTrace]
  refine ⟨769133429353617606608545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4102044956552627235245573 769133429353617606608545)
  ·
    refine ⟨576850072015213204956409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 769133429353617606608545 576850072015213204956409)
    ·
      refine ⟨432637554011409903717307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 576850072015213204956409 432637554011409903717307)
      ·
        refine ⟨648956331017114855575961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 432637554011409903717307 648956331017114855575961)
        ·
          refine ⟨486717248262836141681971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 648956331017114855575961 486717248262836141681971)
          ·
            refine ⟨730075872394254212522957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 486717248262836141681971 730075872394254212522957)
            ·
              refine ⟨273778452147845329696109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 730075872394254212522957 273778452147845329696109)
              ·
                refine ⟨102666919555441998636041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 273778452147845329696109 102666919555441998636041)
                ·
                  refine ⟨77000189666581498977031, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 102666919555441998636041 77000189666581498977031)
                  ·
                    rfl

theorem cell20_168702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 3, 3, 2].length) (baseStart_168702 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_168702 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_168702 prefixEnd_168702 := by exact prefixLift 168702
  have htrace : WordTrace (prefixWord ++ tailWord_168702) baseStart_168702 baseEnd_168702 := by
    simpa [prefixWord, tailWord_168702, baseEnd_168702] using wordTrace_append hprefix tailTrace_168702
  have hstable : (prefixWord ++ tailWord_168702).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_168702).length < 2 ^ (prefixWord ++ tailWord_168702).sum := by decide
  have hdescent : baseEnd_168702 < baseStart_168702 := by decide
  rcases family_descends (prefixWord ++ tailWord_168702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_168723 : List Nat := [1, 1, 1, 2, 1, 3, 7, 2, 2]
def baseStart_168723 : Nat := 118140960795 + 168723 * 2 ^ 59
def prefixEnd_168723 : Nat := 4983230072969 + 3 ^ 40 * 168723 * 2
def baseEnd_168723 : Nat := 77009774638798759276945

theorem tailTrace_168723 : CollatzResearch.WordTrace tailWord_168723 prefixEnd_168723 77009774638798759276945 := by
  unfold tailWord_168723
  simp only [CollatzResearch.WordTrace]
  refine ⟨6153833367752861439382823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4102555578501907626255215 6153833367752861439382823)
  ·
    refine ⟨9230750051629292159074235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6153833367752861439382823 9230750051629292159074235)
    ·
      refine ⟨13846125077443938238611353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9230750051629292159074235 13846125077443938238611353)
      ·
        refine ⟨10384593808082953678958515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13846125077443938238611353 10384593808082953678958515)
        ·
          refine ⟨15576890712124430518437773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10384593808082953678958515 15576890712124430518437773)
          ·
            refine ⟨5841334017046661444414165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15576890712124430518437773 5841334017046661444414165)
            ·
              refine ⟨136906266024531127603457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 5841334017046661444414165 136906266024531127603457)
              ·
                refine ⟨102679699518398345702593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 136906266024531127603457 102679699518398345702593)
                ·
                  refine ⟨77009774638798759276945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 102679699518398345702593 77009774638798759276945)
                  ·
                    rfl

theorem cell20_168723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 7, 2, 2].length) (baseStart_168723 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_168723 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_168723 prefixEnd_168723 := by exact prefixLift 168723
  have htrace : WordTrace (prefixWord ++ tailWord_168723) baseStart_168723 baseEnd_168723 := by
    simpa [prefixWord, tailWord_168723, baseEnd_168723] using wordTrace_append hprefix tailTrace_168723
  have hstable : (prefixWord ++ tailWord_168723).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_168723).length < 2 ^ (prefixWord ++ tailWord_168723).sum := by decide
  have hdescent : baseEnd_168723 < baseStart_168723 := by decide
  rcases family_descends (prefixWord ++ tailWord_168723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_168803 : List Nat := [1, 1, 1, 5, 3, 1, 1, 1, 6]
def baseStart_168803 : Nat := 118140960795 + 168803 * 2 ^ 59
def prefixEnd_168803 : Nat := 4983230072969 + 3 ^ 40 * 168803 * 2
def baseEnd_168803 : Nat := 77046288818674036609951

theorem tailTrace_168803 : CollatzResearch.WordTrace tailWord_168803 prefixEnd_168803 77046288818674036609951 := by
  unfold tailWord_168803
  simp only [CollatzResearch.WordTrace]
  refine ⟨6156751207463035102295063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4104500804975356734863375 6156751207463035102295063)
  ·
    refine ⟨9235126811194552653442595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6156751207463035102295063 9235126811194552653442595)
    ·
      refine ⟨13852690216791828980163893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9235126811194552653442595 13852690216791828980163893)
      ·
        refine ⟨1298689707824233966890365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 13852690216791828980163893 1298689707824233966890365)
        ·
          refine ⟨487008640434087737583887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1298689707824233966890365 487008640434087737583887)
          ·
            refine ⟨730512960651131606375831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 487008640434087737583887 730512960651131606375831)
            ·
              refine ⟨1095769440976697409563747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 730512960651131606375831 1095769440976697409563747)
              ·
                refine ⟨1643654161465046114345621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1095769440976697409563747 1643654161465046114345621)
                ·
                  refine ⟨77046288818674036609951, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1643654161465046114345621 77046288818674036609951)
                  ·
                    rfl

theorem cell20_168803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 1, 1, 6].length) (baseStart_168803 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_168803 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_168803 prefixEnd_168803 := by exact prefixLift 168803
  have htrace : WordTrace (prefixWord ++ tailWord_168803) baseStart_168803 baseEnd_168803 := by
    simpa [prefixWord, tailWord_168803, baseEnd_168803] using wordTrace_append hprefix tailTrace_168803
  have hstable : (prefixWord ++ tailWord_168803).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_168803).length < 2 ^ (prefixWord ++ tailWord_168803).sum := by decide
  have hdescent : baseEnd_168803 < baseStart_168803 := by decide
  rcases family_descends (prefixWord ++ tailWord_168803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_168830 : List Nat := [4, 2, 3, 1, 2, 1, 1, 1, 5]
def baseStart_168830 : Nat := 118140960795 + 168830 * 2 ^ 59
def prefixEnd_168830 : Nat := 4983230072969 + 3 ^ 40 * 168830 * 2
def baseEnd_168830 : Nat := 77058612354381942709841

theorem tailTrace_168830 : CollatzResearch.WordTrace tailWord_168830 prefixEnd_168830 77058612354381942709841 := by
  unfold tailWord_168830
  simp only [CollatzResearch.WordTrace]
  refine ⟨769716997295652339190993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4105157318910145809018629 769716997295652339190993)
  ·
    refine ⟨577287747971739254393245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 769716997295652339190993 577287747971739254393245)
    ·
      refine ⟨216482905489402220397467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 577287747971739254393245 216482905489402220397467)
      ·
        refine ⟨324724358234103330596201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 216482905489402220397467 324724358234103330596201)
        ·
          refine ⟨243543268675577497947151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 324724358234103330596201 243543268675577497947151)
          ·
            refine ⟨365314903013366246920727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 243543268675577497947151 365314903013366246920727)
            ·
              refine ⟨547972354520049370381091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 365314903013366246920727 547972354520049370381091)
              ·
                refine ⟨821958531780074055571637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 547972354520049370381091 821958531780074055571637)
                ·
                  refine ⟨77058612354381942709841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 821958531780074055571637 77058612354381942709841)
                  ·
                    rfl

theorem cell20_168830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 1, 1, 1, 5].length) (baseStart_168830 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_168830 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_168830 prefixEnd_168830 := by exact prefixLift 168830
  have htrace : WordTrace (prefixWord ++ tailWord_168830) baseStart_168830 baseEnd_168830 := by
    simpa [prefixWord, tailWord_168830, baseEnd_168830] using wordTrace_append hprefix tailTrace_168830
  have hstable : (prefixWord ++ tailWord_168830).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_168830).length < 2 ^ (prefixWord ++ tailWord_168830).sum := by decide
  have hdescent : baseEnd_168830 < baseStart_168830 := by decide
  rcases family_descends (prefixWord ++ tailWord_168830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_168841 : List Nat := [1, 2, 1, 1, 5, 2, 1, 3, 4]
def baseStart_168841 : Nat := 118140960795 + 168841 * 2 ^ 59
def prefixEnd_168841 : Nat := 4983230072969 + 3 ^ 40 * 168841 * 2
def baseEnd_168841 : Nat := 77063633054114793343129

theorem tailTrace_168841 : CollatzResearch.WordTrace tailWord_168841 prefixEnd_168841 77063633054114793343129 := by
  unfold tailWord_168841
  simp only [CollatzResearch.WordTrace]
  refine ⟨6158137181325367592178377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4105424787550245061452251 6158137181325367592178377)
  ·
    refine ⟨4618602885994025694133783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6158137181325367592178377 4618602885994025694133783)
    ·
      refine ⟨6927904328991038541200675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4618602885994025694133783 6927904328991038541200675)
      ·
        refine ⟨10391856493486557811801013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6927904328991038541200675 10391856493486557811801013)
        ·
          refine ⟨974236546264364794856345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 10391856493486557811801013 974236546264364794856345)
          ·
            refine ⟨730677409698273596142259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 974236546264364794856345 730677409698273596142259)
            ·
              refine ⟨1096016114547410394213389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 730677409698273596142259 1096016114547410394213389)
              ·
                refine ⟨411006042955278897830021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1096016114547410394213389 411006042955278897830021)
                ·
                  refine ⟨77063633054114793343129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 411006042955278897830021 77063633054114793343129)
                  ·
                    rfl

theorem cell20_168841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 1, 3, 4].length) (baseStart_168841 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_168841 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_168841 prefixEnd_168841 := by exact prefixLift 168841
  have htrace : WordTrace (prefixWord ++ tailWord_168841) baseStart_168841 baseEnd_168841 := by
    simpa [prefixWord, tailWord_168841, baseEnd_168841] using wordTrace_append hprefix tailTrace_168841
  have hstable : (prefixWord ++ tailWord_168841).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_168841).length < 2 ^ (prefixWord ++ tailWord_168841).sum := by decide
  have hdescent : baseEnd_168841 < baseStart_168841 := by decide
  rcases family_descends (prefixWord ++ tailWord_168841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_168854 : List Nat := [5, 3, 1, 1, 1, 1, 2, 2, 4]
def baseStart_168854 : Nat := 118140960795 + 168854 * 2 ^ 59
def prefixEnd_168854 : Nat := 4983230072969 + 3 ^ 40 * 168854 * 2
def baseEnd_168854 : Nat := 77069566608344525909743

theorem tailTrace_168854 : CollatzResearch.WordTrace tailWord_168854 prefixEnd_168854 77069566608344525909743 := by
  unfold tailWord_168854
  simp only [CollatzResearch.WordTrace]
  refine ⟨384913208142391925775101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 4105740886852180541601077 384913208142391925775101)
  ·
    refine ⟨144342453053396972165663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 384913208142391925775101 144342453053396972165663)
    ·
      refine ⟨216513679580095458248495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 144342453053396972165663 216513679580095458248495)
      ·
        refine ⟨324770519370143187372743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 216513679580095458248495 324770519370143187372743)
        ·
          refine ⟨487155779055214781059115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 324770519370143187372743 487155779055214781059115)
          ·
            refine ⟨730733668582822171588673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 487155779055214781059115 730733668582822171588673)
            ·
              refine ⟨548050251437116628691505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 730733668582822171588673 548050251437116628691505)
              ·
                refine ⟨411037688577837471518629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 548050251437116628691505 411037688577837471518629)
                ·
                  refine ⟨77069566608344525909743, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 411037688577837471518629 77069566608344525909743)
                  ·
                    rfl

theorem cell20_168854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 2, 2, 4].length) (baseStart_168854 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_168854 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_168854 prefixEnd_168854 := by exact prefixLift 168854
  have htrace : WordTrace (prefixWord ++ tailWord_168854) baseStart_168854 baseEnd_168854 := by
    simpa [prefixWord, tailWord_168854, baseEnd_168854] using wordTrace_append hprefix tailTrace_168854
  have hstable : (prefixWord ++ tailWord_168854).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_168854).length < 2 ^ (prefixWord ++ tailWord_168854).sum := by decide
  have hdescent : baseEnd_168854 < baseStart_168854 := by decide
  rcases family_descends (prefixWord ++ tailWord_168854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_168865 : List Nat := [1, 2, 3, 4, 1, 2, 1, 6]
def baseStart_168865 : Nat := 118140960795 + 168865 * 2 ^ 59
def prefixEnd_168865 : Nat := 4983230072969 + 3 ^ 40 * 168865 * 2
def baseEnd_168865 : Nat := 25691529102692458847677

theorem tailTrace_168865 : CollatzResearch.WordTrace tailWord_168865 prefixEnd_168865 25691529102692458847677 := by
  unfold tailWord_168865
  simp only [CollatzResearch.WordTrace]
  refine ⟨6159012533238419691052049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4106008355492279794034699 6159012533238419691052049)
  ·
    refine ⟨4619259399928814768289037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6159012533238419691052049 4619259399928814768289037)
    ·
      refine ⟨1732222274973305538108389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4619259399928814768289037 1732222274973305538108389)
      ·
        refine ⟨324791676557494788395323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1732222274973305538108389 324791676557494788395323)
        ·
          refine ⟨487187514836242182592985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 324791676557494788395323 487187514836242182592985)
          ·
            refine ⟨365390636127181636944739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 487187514836242182592985 365390636127181636944739)
            ·
              refine ⟨548085954190772455417109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 365390636127181636944739 548085954190772455417109)
              ·
                refine ⟨25691529102692458847677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 548085954190772455417109 25691529102692458847677)
                ·
                  rfl

theorem cell20_168865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 2, 1, 6].length) (baseStart_168865 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_168865 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_168865 prefixEnd_168865 := by exact prefixLift 168865
  have htrace : WordTrace (prefixWord ++ tailWord_168865) baseStart_168865 baseEnd_168865 := by
    simpa [prefixWord, tailWord_168865, baseEnd_168865] using wordTrace_append hprefix tailTrace_168865
  have hstable : (prefixWord ++ tailWord_168865).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_168865).length < 2 ^ (prefixWord ++ tailWord_168865).sum := by decide
  have hdescent : baseEnd_168865 < baseStart_168865 := by decide
  rcases family_descends (prefixWord ++ tailWord_168865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_168871 : List Nat := [1, 1, 6, 1, 4, 1, 1, 3, 2]
def baseStart_168871 : Nat := 118140960795 + 168871 * 2 ^ 59
def prefixEnd_168871 : Nat := 4983230072969 + 3 ^ 40 * 168871 * 2
def baseEnd_168871 : Nat := 77077325871568022343007

theorem tailTrace_168871 : CollatzResearch.WordTrace tailWord_168871 prefixEnd_168871 77077325871568022343007 := by
  unfold tailWord_168871
  simp only [CollatzResearch.WordTrace]
  refine ⟨6159231371216682715770467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4106154247477788477180311 6159231371216682715770467)
  ·
    refine ⟨9238847056825024073655701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6159231371216682715770467 9238847056825024073655701)
    ·
      refine ⟨433070955788673003452611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 9238847056825024073655701 433070955788673003452611)
      ·
        refine ⟨649606433683009505178917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 433070955788673003452611 649606433683009505178917)
        ·
          refine ⟨121801206315564282221047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 649606433683009505178917 121801206315564282221047)
          ·
            refine ⟨182701809473346423331571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 121801206315564282221047 182701809473346423331571)
            ·
              refine ⟨274052714210019634997357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 182701809473346423331571 274052714210019634997357)
              ·
                refine ⟨102769767828757363124009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 274052714210019634997357 102769767828757363124009)
                ·
                  refine ⟨77077325871568022343007, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 102769767828757363124009 77077325871568022343007)
                  ·
                    rfl

theorem cell20_168871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 4, 1, 1, 3, 2].length) (baseStart_168871 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_168871 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_168871 prefixEnd_168871 := by exact prefixLift 168871
  have htrace : WordTrace (prefixWord ++ tailWord_168871) baseStart_168871 baseEnd_168871 := by
    simpa [prefixWord, tailWord_168871, baseEnd_168871] using wordTrace_append hprefix tailTrace_168871
  have hstable : (prefixWord ++ tailWord_168871).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_168871).length < 2 ^ (prefixWord ++ tailWord_168871).sum := by decide
  have hdescent : baseEnd_168871 < baseStart_168871 := by decide
  rcases family_descends (prefixWord ++ tailWord_168871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_168896 : List Nat := [2, 1, 1, 2, 3, 5, 1, 1, 4]
def baseStart_168896 : Nat := 118140960795 + 168896 * 2 ^ 59
def prefixEnd_168896 : Nat := 4983230072969 + 3 ^ 40 * 168896 * 2
def baseEnd_168896 : Nat := 77088736552779046509571

theorem tailTrace_168896 : CollatzResearch.WordTrace tailWord_168896 prefixEnd_168896 77088736552779046509571 := by
  unfold tailWord_168896
  simp only [CollatzResearch.WordTrace]
  refine ⟨3080071598063055992715271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4106762130750741323620361 3080071598063055992715271)
  ·
    refine ⟨4620107397094583989072907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3080071598063055992715271 4620107397094583989072907)
    ·
      refine ⟨6930161095641875983609361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4620107397094583989072907 6930161095641875983609361)
      ·
        refine ⟨5197620821731406987707021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6930161095641875983609361 5197620821731406987707021)
        ·
          refine ⟨1949107808149277620390133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5197620821731406987707021 1949107808149277620390133)
          ·
            refine ⟨182728857013994776911575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1949107808149277620390133 182728857013994776911575)
            ·
              refine ⟨274093285520992165367363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 182728857013994776911575 274093285520992165367363)
              ·
                refine ⟨411139928281488248051045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 274093285520992165367363 411139928281488248051045)
                ·
                  refine ⟨77088736552779046509571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 411139928281488248051045 77088736552779046509571)
                  ·
                    rfl

theorem cell20_168896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 5, 1, 1, 4].length) (baseStart_168896 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_168896 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_168896 prefixEnd_168896 := by exact prefixLift 168896
  have htrace : WordTrace (prefixWord ++ tailWord_168896) baseStart_168896 baseEnd_168896 := by
    simpa [prefixWord, tailWord_168896, baseEnd_168896] using wordTrace_append hprefix tailTrace_168896
  have hstable : (prefixWord ++ tailWord_168896).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_168896).length < 2 ^ (prefixWord ++ tailWord_168896).sum := by decide
  have hdescent : baseEnd_168896 < baseStart_168896 := by decide
  rcases family_descends (prefixWord ++ tailWord_168896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_169010 : List Nat := [3, 2, 1, 1, 2, 2, 1, 6, 2]
def baseStart_169010 : Nat := 118140960795 + 169010 * 2 ^ 59
def prefixEnd_169010 : Nat := 4983230072969 + 3 ^ 40 * 169010 * 2
def baseEnd_169010 : Nat := 77140769259101316709105

theorem tailTrace_169010 : CollatzResearch.WordTrace tailWord_169010 prefixEnd_169010 77140769259101316709105 := by
  unfold tailWord_169010
  simp only [CollatzResearch.WordTrace]
  refine ⟨1541075279428277363770121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4109534078475406303386989 1541075279428277363770121)
  ·
    refine ⟨1155806459571208022827591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1541075279428277363770121 1155806459571208022827591)
    ·
      refine ⟨1733709689356812034241387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1155806459571208022827591 1733709689356812034241387)
      ·
        refine ⟨2600564534035218051362081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1733709689356812034241387 2600564534035218051362081)
        ·
          refine ⟨1950423400526413538521561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2600564534035218051362081 1950423400526413538521561)
          ·
            refine ⟨1462817550394810153891171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1950423400526413538521561 1462817550394810153891171)
            ·
              refine ⟨2194226325592215230836757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1462817550394810153891171 2194226325592215230836757)
              ·
                refine ⟨102854359012135088945473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2194226325592215230836757 102854359012135088945473)
                ·
                  refine ⟨77140769259101316709105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 102854359012135088945473 77140769259101316709105)
                  ·
                    rfl

theorem cell20_169010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 1, 6, 2].length) (baseStart_169010 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_169010 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_169010 prefixEnd_169010 := by exact prefixLift 169010
  have htrace : WordTrace (prefixWord ++ tailWord_169010) baseStart_169010 baseEnd_169010 := by
    simpa [prefixWord, tailWord_169010, baseEnd_169010] using wordTrace_append hprefix tailTrace_169010
  have hstable : (prefixWord ++ tailWord_169010).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_169010).length < 2 ^ (prefixWord ++ tailWord_169010).sum := by decide
  have hdescent : baseEnd_169010 < baseStart_169010 := by decide
  rcases family_descends (prefixWord ++ tailWord_169010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_169031 : List Nat := [1, 1, 4, 1, 3, 2, 2, 2, 4]
def baseStart_169031 : Nat := 118140960795 + 169031 * 2 ^ 59
def prefixEnd_169031 : Nat := 4983230072969 + 3 ^ 40 * 169031 * 2
def baseEnd_169031 : Nat := 77150354231318577009019

theorem tailTrace_169031 : CollatzResearch.WordTrace tailWord_169031 prefixEnd_169031 77150354231318577009019 := by
  unfold tailWord_169031
  simp only [CollatzResearch.WordTrace]
  refine ⟨6165067050637030041594947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4110044700424686694396631 6165067050637030041594947)
  ·
    refine ⟨9247600575955545062392421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6165067050637030041594947 9247600575955545062392421)
    ·
      refine ⟨1733925107991664699198579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9247600575955545062392421 1733925107991664699198579)
      ·
        refine ⟨2600887661987497048797869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1733925107991664699198579 2600887661987497048797869)
        ·
          refine ⟨975332873245311393299201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2600887661987497048797869 975332873245311393299201)
          ·
            refine ⟨731499654933983544974401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 975332873245311393299201 731499654933983544974401)
            ·
              refine ⟨548624741200487658730801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 731499654933983544974401 548624741200487658730801)
              ·
                refine ⟨411468555900365744048101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 548624741200487658730801 411468555900365744048101)
                ·
                  refine ⟨77150354231318577009019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 411468555900365744048101 77150354231318577009019)
                  ·
                    rfl

theorem cell20_169031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 2, 2, 4].length) (baseStart_169031 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_169031 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_169031 prefixEnd_169031 := by exact prefixLift 169031
  have htrace : WordTrace (prefixWord ++ tailWord_169031) baseStart_169031 baseEnd_169031 := by
    simpa [prefixWord, tailWord_169031, baseEnd_169031] using wordTrace_append hprefix tailTrace_169031
  have hstable : (prefixWord ++ tailWord_169031).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_169031).length < 2 ^ (prefixWord ++ tailWord_169031).sum := by decide
  have hdescent : baseEnd_169031 < baseStart_169031 := by decide
  rcases family_descends (prefixWord ++ tailWord_169031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_169038 : List Nat := [4, 1, 1, 1, 1, 3, 3, 6]
def baseStart_169038 : Nat := 118140960795 + 169038 * 2 ^ 59
def prefixEnd_169038 : Nat := 4983230072969 + 3 ^ 40 * 169038 * 2
def baseEnd_169038 : Nat := 25717849740685887925219

theorem tailTrace_169038 : CollatzResearch.WordTrace tailWord_169038 prefixEnd_169038 25717849740685887925219 := by
  unfold tailWord_169038
  simp only [CollatzResearch.WordTrace]
  refine ⟨770665295201458779637471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4110214907741113491399845 770665295201458779637471)
  ·
    refine ⟨1155997942802188169456207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 770665295201458779637471 1155997942802188169456207)
    ·
      refine ⟨1733996914203282254184311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1155997942802188169456207 1733996914203282254184311)
      ·
        refine ⟨2600995371304923381276467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1733996914203282254184311 2600995371304923381276467)
        ·
          refine ⟨3901493056957385071914701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2600995371304923381276467 3901493056957385071914701)
          ·
            refine ⟨1463059896359019401968013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3901493056957385071914701 1463059896359019401968013)
            ·
              refine ⟨548647461134632275738005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1463059896359019401968013 548647461134632275738005)
              ·
                refine ⟨25717849740685887925219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 548647461134632275738005 25717849740685887925219)
                ·
                  rfl

theorem cell20_169038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 3, 6].length) (baseStart_169038 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_169038 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_169038 prefixEnd_169038 := by exact prefixLift 169038
  have htrace : WordTrace (prefixWord ++ tailWord_169038) baseStart_169038 baseEnd_169038 := by
    simpa [prefixWord, tailWord_169038, baseEnd_169038] using wordTrace_append hprefix tailTrace_169038
  have hstable : (prefixWord ++ tailWord_169038).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_169038).length < 2 ^ (prefixWord ++ tailWord_169038).sum := by decide
  have hdescent : baseEnd_169038 < baseStart_169038 := by decide
  rcases family_descends (prefixWord ++ tailWord_169038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_169045 : List Nat := [1, 3, 2, 2, 1, 2, 1, 1, 7]
def baseStart_169045 : Nat := 118140960795 + 169045 * 2 ^ 59
def prefixEnd_169045 : Nat := 4983230072969 + 3 ^ 40 * 169045 * 2
def baseEnd_169045 : Nat := 77156744212796750542295

theorem tailTrace_169045 : CollatzResearch.WordTrace tailWord_169045 prefixEnd_169045 77156744212796750542295 := by
  unfold tailWord_169045
  simp only [CollatzResearch.WordTrace]
  refine ⟨6165577672586310432604589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4110385115057540288403059 6165577672586310432604589)
  ·
    refine ⟨2312091627219866412226721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6165577672586310432604589 2312091627219866412226721)
    ·
      refine ⟨1734068720414899809170041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2312091627219866412226721 1734068720414899809170041)
      ·
        refine ⟨1300551540311174856877531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1734068720414899809170041 1300551540311174856877531)
        ·
          refine ⟨1950827310466762285316297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1300551540311174856877531 1950827310466762285316297)
          ·
            refine ⟨1463120482850071713987223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1950827310466762285316297 1463120482850071713987223)
            ·
              refine ⟨2194680724275107570980835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1463120482850071713987223 2194680724275107570980835)
              ·
                refine ⟨3292021086412661356471253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2194680724275107570980835 3292021086412661356471253)
                ·
                  refine ⟨77156744212796750542295, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3292021086412661356471253 77156744212796750542295)
                  ·
                    rfl

theorem cell20_169045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 1, 1, 7].length) (baseStart_169045 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_169045 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_169045 prefixEnd_169045 := by exact prefixLift 169045
  have htrace : WordTrace (prefixWord ++ tailWord_169045) baseStart_169045 baseEnd_169045 := by
    simpa [prefixWord, tailWord_169045, baseEnd_169045] using wordTrace_append hprefix tailTrace_169045
  have hstable : (prefixWord ++ tailWord_169045).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_169045).length < 2 ^ (prefixWord ++ tailWord_169045).sum := by decide
  have hdescent : baseEnd_169045 < baseStart_169045 := by decide
  rcases family_descends (prefixWord ++ tailWord_169045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_169065 : List Nat := [1, 2, 1, 1, 1, 7, 3, 2, 2]
def baseStart_169065 : Nat := 118140960795 + 169065 * 2 ^ 59
def prefixEnd_169065 : Nat := 4983230072969 + 3 ^ 40 * 169065 * 2
def baseEnd_169065 : Nat := 77165872757765569875547

theorem tailTrace_169065 : CollatzResearch.WordTrace tailWord_169065 prefixEnd_169065 77165872757765569875547 := by
  unfold tailWord_169065
  simp only [CollatzResearch.WordTrace]
  refine ⟨6166307132513853848332649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4110871421675902565555099 6166307132513853848332649)
  ·
    refine ⟨4624730349385390386249487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6166307132513853848332649 4624730349385390386249487)
    ·
      refine ⟨6937095524078085579374231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4624730349385390386249487 6937095524078085579374231)
      ·
        refine ⟨10405643286117128369061347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6937095524078085579374231 10405643286117128369061347)
        ·
          refine ⟨15608464929175692553592021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10405643286117128369061347 15608464929175692553592021)
          ·
            refine ⟨365823396777555294224813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 15608464929175692553592021 365823396777555294224813)
            ·
              refine ⟨137183773791583235334305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 365823396777555294224813 137183773791583235334305)
              ·
                refine ⟨102887830343687426500729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 137183773791583235334305 102887830343687426500729)
                ·
                  refine ⟨77165872757765569875547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 102887830343687426500729 77165872757765569875547)
                  ·
                    rfl

theorem cell20_169065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 7, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 7, 3, 2, 2].length) (baseStart_169065 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_169065 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_169065 prefixEnd_169065 := by exact prefixLift 169065
  have htrace : WordTrace (prefixWord ++ tailWord_169065) baseStart_169065 baseEnd_169065 := by
    simpa [prefixWord, tailWord_169065, baseEnd_169065] using wordTrace_append hprefix tailTrace_169065
  have hstable : (prefixWord ++ tailWord_169065).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_169065).length < 2 ^ (prefixWord ++ tailWord_169065).sum := by decide
  have hdescent : baseEnd_169065 < baseStart_169065 := by decide
  rcases family_descends (prefixWord ++ tailWord_169065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_169110 : List Nat := [5, 3, 2, 10]
def baseStart_169110 : Nat := 118140960795 + 169110 * 2 ^ 59
def prefixEnd_169110 : Nat := 4983230072969 + 3 ^ 40 * 169110 * 2
def baseEnd_169110 : Nat := 317639555489487297841

theorem tailTrace_169110 : CollatzResearch.WordTrace tailWord_169110 prefixEnd_169110 317639555489487297841 := by
  unfold tailWord_169110
  simp only [CollatzResearch.WordTrace]
  refine ⟨385496776084426658357549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 4111965611567217689147189 385496776084426658357549)
  ·
    refine ⟨144561291031659996884081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 385496776084426658357549 144561291031659996884081)
    ·
      refine ⟨108420968273744997663061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 144561291031659996884081 108420968273744997663061)
      ·
        refine ⟨317639555489487297841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 10 108420968273744997663061 317639555489487297841)
        ·
          rfl

theorem cell20_169110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 10].length) (baseStart_169110 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_169110 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_169110 prefixEnd_169110 := by exact prefixLift 169110
  have htrace : WordTrace (prefixWord ++ tailWord_169110) baseStart_169110 baseEnd_169110 := by
    simpa [prefixWord, tailWord_169110, baseEnd_169110] using wordTrace_append hprefix tailTrace_169110
  have hstable : (prefixWord ++ tailWord_169110).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_169110).length < 2 ^ (prefixWord ++ tailWord_169110).sum := by decide
  have hdescent : baseEnd_169110 < baseStart_169110 := by decide
  rcases family_descends (prefixWord ++ tailWord_169110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_169114 : List Nat := [3, 1, 1, 5, 1, 9]
def baseStart_169114 : Nat := 118140960795 + 169114 * 2 ^ 59
def prefixEnd_169114 : Nat := 4983230072969 + 3 ^ 40 * 169114 * 2
def baseEnd_169114 : Nat := 2858823618257006564519

theorem tailTrace_169114 : CollatzResearch.WordTrace tailWord_169114 prefixEnd_169114 2858823618257006564519 := by
  unfold tailWord_169114
  simp only [CollatzResearch.WordTrace]
  refine ⟨1542023577334083804216599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4112062872890890144577597 1542023577334083804216599)
  ·
    refine ⟨2313035366001125706324899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1542023577334083804216599 2313035366001125706324899)
    ·
      refine ⟨3469553049001688559487349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2313035366001125706324899 3469553049001688559487349)
      ·
        refine ⟨325270598343908302451939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 3469553049001688559487349 325270598343908302451939)
        ·
          refine ⟨487905897515862453677909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 325270598343908302451939 487905897515862453677909)
          ·
            refine ⟨2858823618257006564519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 487905897515862453677909 2858823618257006564519)
            ·
              rfl

theorem cell20_169114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 9].length) (baseStart_169114 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_169114 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_169114 prefixEnd_169114 := by exact prefixLift 169114
  have htrace : WordTrace (prefixWord ++ tailWord_169114) baseStart_169114 baseEnd_169114 := by
    simpa [prefixWord, tailWord_169114, baseEnd_169114] using wordTrace_append hprefix tailTrace_169114
  have hstable : (prefixWord ++ tailWord_169114).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_169114).length < 2 ^ (prefixWord ++ tailWord_169114).sum := by decide
  have hdescent : baseEnd_169114 < baseStart_169114 := by decide
  rcases family_descends (prefixWord ++ tailWord_169114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_169138 : List Nat := [3, 2, 1, 1, 1, 4, 2, 3, 3]
def baseStart_169138 : Nat := 118140960795 + 169138 * 2 ^ 59
def prefixEnd_169138 : Nat := 4983230072969 + 3 ^ 40 * 169138 * 2
def baseEnd_169138 : Nat := 77199191946901760441915

theorem tailTrace_169138 : CollatzResearch.WordTrace tailWord_169138 prefixEnd_169138 77199191946901760441915 := by
  unfold tailWord_169138
  simp only [CollatzResearch.WordTrace]
  refine ⟨1542242415312346828935017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4112646440832924877160045 1542242415312346828935017)
  ·
    refine ⟨1156681811484260121701263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1542242415312346828935017 1156681811484260121701263)
    ·
      refine ⟨1735022717226390182551895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1156681811484260121701263 1735022717226390182551895)
      ·
        refine ⟨2602534075839585273827843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1735022717226390182551895 2602534075839585273827843)
        ·
          refine ⟨3903801113759377910741765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2602534075839585273827843 3903801113759377910741765)
          ·
            refine ⟨731962708829883358264081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3903801113759377910741765 731962708829883358264081)
            ·
              refine ⟨548972031622412518698061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 731962708829883358264081 548972031622412518698061)
              ·
                refine ⟨205864511858404694511773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 548972031622412518698061 205864511858404694511773)
                ·
                  refine ⟨77199191946901760441915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 205864511858404694511773 77199191946901760441915)
                  ·
                    rfl

theorem cell20_169138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 2, 3, 3].length) (baseStart_169138 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_169138 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_169138 prefixEnd_169138 := by exact prefixLift 169138
  have htrace : WordTrace (prefixWord ++ tailWord_169138) baseStart_169138 baseEnd_169138 := by
    simpa [prefixWord, tailWord_169138, baseEnd_169138] using wordTrace_append hprefix tailTrace_169138
  have hstable : (prefixWord ++ tailWord_169138).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_169138).length < 2 ^ (prefixWord ++ tailWord_169138).sum := by decide
  have hdescent : baseEnd_169138 < baseStart_169138 := by decide
  rcases family_descends (prefixWord ++ tailWord_169138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_169145 : List Nat := [1, 2, 1, 4, 1, 4, 1, 2, 4]
def baseStart_169145 : Nat := 118140960795 + 169145 * 2 ^ 59
def prefixEnd_169145 : Nat := 4983230072969 + 3 ^ 40 * 169145 * 2
def baseEnd_169145 : Nat := 77202386937640847208553

theorem tailTrace_169145 : CollatzResearch.WordTrace tailWord_169145 prefixEnd_169145 77202386937640847208553 := by
  unfold tailWord_169145
  simp only [CollatzResearch.WordTrace]
  refine ⟨6169224972224027511244889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4112816648149351674163259 6169224972224027511244889)
  ·
    refine ⟨4626918729168020633433667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6169224972224027511244889 4626918729168020633433667)
    ·
      refine ⟨6940378093752030950150501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4626918729168020633433667 6940378093752030950150501)
      ·
        refine ⟨1301320892578505803153219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6940378093752030950150501 1301320892578505803153219)
        ·
          refine ⟨1951981338867758704729829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1301320892578505803153219 1951981338867758704729829)
          ·
            refine ⟨365996501037704757136843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1951981338867758704729829 365996501037704757136843)
            ·
              refine ⟨548994751556557135705265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 365996501037704757136843 548994751556557135705265)
              ·
                refine ⟨411746063667417851778949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 548994751556557135705265 411746063667417851778949)
                ·
                  refine ⟨77202386937640847208553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 411746063667417851778949 77202386937640847208553)
                  ·
                    rfl

theorem cell20_169145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 4, 1, 2, 4].length) (baseStart_169145 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_169145 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_169145 prefixEnd_169145 := by exact prefixLift 169145
  have htrace : WordTrace (prefixWord ++ tailWord_169145) baseStart_169145 baseEnd_169145 := by
    simpa [prefixWord, tailWord_169145, baseEnd_169145] using wordTrace_append hprefix tailTrace_169145
  have hstable : (prefixWord ++ tailWord_169145).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_169145).length < 2 ^ (prefixWord ++ tailWord_169145).sum := by decide
  have hdescent : baseEnd_169145 < baseStart_169145 := by decide
  rcases family_descends (prefixWord ++ tailWord_169145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_169162 : List Nat := [3, 1, 2, 1, 3, 2, 1, 5, 2]
def baseStart_169162 : Nat := 118140960795 + 169162 * 2 ^ 59
def prefixEnd_169162 : Nat := 4983230072969 + 3 ^ 40 * 169162 * 2
def baseEnd_169162 : Nat := 77210146200864343641817

theorem tailTrace_169162 : CollatzResearch.WordTrace tailWord_169162 prefixEnd_169162 77210146200864343641817 := by
  unfold tailWord_169162
  simp only [CollatzResearch.WordTrace]
  refine ⟨1542461253290609853653435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4113230008774959609742493 1542461253290609853653435)
  ·
    refine ⟨2313691879935914780480153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1542461253290609853653435 2313691879935914780480153)
    ·
      refine ⟨1735268909951936085360115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2313691879935914780480153 1735268909951936085360115)
      ·
        refine ⟨2602903364927904128040173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1735268909951936085360115 2602903364927904128040173)
        ·
          refine ⟨976088761847964048015065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2602903364927904128040173 976088761847964048015065)
          ·
            refine ⟨732066571385973036011299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 976088761847964048015065 732066571385973036011299)
            ·
              refine ⟨1098099857078959554016949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 732066571385973036011299 1098099857078959554016949)
              ·
                refine ⟨102946861601152458189089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1098099857078959554016949 102946861601152458189089)
                ·
                  refine ⟨77210146200864343641817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 102946861601152458189089 77210146200864343641817)
                  ·
                    rfl

theorem cell20_169162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 1, 5, 2].length) (baseStart_169162 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_169162 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_169162 prefixEnd_169162 := by exact prefixLift 169162
  have htrace : WordTrace (prefixWord ++ tailWord_169162) baseStart_169162 baseEnd_169162 := by
    simpa [prefixWord, tailWord_169162, baseEnd_169162] using wordTrace_append hprefix tailTrace_169162
  have hstable : (prefixWord ++ tailWord_169162).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_169162).length < 2 ^ (prefixWord ++ tailWord_169162).sum := by decide
  have hdescent : baseEnd_169162 < baseStart_169162 := by decide
  rcases family_descends (prefixWord ++ tailWord_169162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_169176 : List Nat := [2, 1, 2, 2, 5, 1, 1, 1, 5]
def baseStart_169176 : Nat := 118140960795 + 169176 * 2 ^ 59
def prefixEnd_169176 : Nat := 4983230072969 + 3 ^ 40 * 169176 * 2
def baseEnd_169176 : Nat := 77216536182342517175093

theorem tailTrace_169176 : CollatzResearch.WordTrace tailWord_169176 prefixEnd_169176 77216536182342517175093 := by
  unfold tailWord_169176
  simp only [CollatzResearch.WordTrace]
  refine ⟨3085177817555859902811691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4113570423407813203748921 3085177817555859902811691)
  ·
    refine ⟨4627766726333789854217537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3085177817555859902811691 4627766726333789854217537)
    ·
      refine ⟨3470825044750342390663153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4627766726333789854217537 3470825044750342390663153)
      ·
        refine ⟨2603118783562756792997365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3470825044750342390663153 2603118783562756792997365)
        ·
          refine ⟨244042385959008449343503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 2603118783562756792997365 244042385959008449343503)
          ·
            refine ⟨366063578938512674015255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 244042385959008449343503 366063578938512674015255)
            ·
              refine ⟨549095368407769011022883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 366063578938512674015255 549095368407769011022883)
              ·
                refine ⟨823643052611653516534325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 549095368407769011022883 823643052611653516534325)
                ·
                  refine ⟨77216536182342517175093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 823643052611653516534325 77216536182342517175093)
                  ·
                    rfl

theorem cell20_169176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 1, 1, 1, 5].length) (baseStart_169176 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_169176 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_169176 prefixEnd_169176 := by exact prefixLift 169176
  have htrace : WordTrace (prefixWord ++ tailWord_169176) baseStart_169176 baseEnd_169176 := by
    simpa [prefixWord, tailWord_169176, baseEnd_169176] using wordTrace_append hprefix tailTrace_169176
  have hstable : (prefixWord ++ tailWord_169176).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_169176).length < 2 ^ (prefixWord ++ tailWord_169176).sum := by decide
  have hdescent : baseEnd_169176 < baseStart_169176 := by decide
  rcases family_descends (prefixWord ++ tailWord_169176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_169214 : List Nat := [4, 2, 2, 1, 1, 2, 1, 2, 5]
def baseStart_169214 : Nat := 118140960795 + 169214 * 2 ^ 59
def prefixEnd_169214 : Nat := 4983230072969 + 3 ^ 40 * 169214 * 2
def baseEnd_169214 : Nat := 77233880417783273908271

theorem tailTrace_169214 : CollatzResearch.WordTrace tailWord_169214 prefixEnd_169214 77233880417783273908271 := by
  unfold tailWord_169214
  simp only [CollatzResearch.WordTrace]
  refine ⟨771467701121756536938337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4114494405982701530337797 771467701121756536938337)
  ·
    refine ⟨578600775841317402703753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 771467701121756536938337 578600775841317402703753)
    ·
      refine ⟨433950581880988052027815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 578600775841317402703753 433950581880988052027815)
      ·
        refine ⟨650925872821482078041723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 433950581880988052027815 650925872821482078041723)
        ·
          refine ⟨976388809232223117062585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 650925872821482078041723 976388809232223117062585)
          ·
            refine ⟨732291606924167337796939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 976388809232223117062585 732291606924167337796939)
            ·
              refine ⟨1098437410386251006695409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 732291606924167337796939 1098437410386251006695409)
              ·
                refine ⟨823828057789688255021557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1098437410386251006695409 823828057789688255021557)
                ·
                  refine ⟨77233880417783273908271, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 823828057789688255021557 77233880417783273908271)
                  ·
                    rfl

theorem cell20_169214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 1, 2, 5].length) (baseStart_169214 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_169214 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_169214 prefixEnd_169214 := by exact prefixLift 169214
  have htrace : WordTrace (prefixWord ++ tailWord_169214) baseStart_169214 baseEnd_169214 := by
    simpa [prefixWord, tailWord_169214, baseEnd_169214] using wordTrace_append hprefix tailTrace_169214
  have hstable : (prefixWord ++ tailWord_169214).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_169214).length < 2 ^ (prefixWord ++ tailWord_169214).sum := by decide
  have hdescent : baseEnd_169214 < baseStart_169214 := by decide
  rcases family_descends (prefixWord ++ tailWord_169214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_169217 : List Nat := [1, 2, 4, 1, 1, 5, 1, 3, 2]
def baseStart_169217 : Nat := 118140960795 + 169217 * 2 ^ 59
def prefixEnd_169217 : Nat := 4983230072969 + 3 ^ 40 * 169217 * 2
def baseEnd_169217 : Nat := 77235249699528596808259

theorem tailTrace_169217 : CollatzResearch.WordTrace tailWord_169217 prefixEnd_169217 77235249699528596808259 := by
  unfold tailWord_169217
  simp only [CollatzResearch.WordTrace]
  refine ⟨6171851027963183807865905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4114567351975455871910603 6171851027963183807865905)
  ·
    refine ⟨4628888270972387855899429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6171851027963183807865905 4628888270972387855899429)
    ·
      refine ⟨867916550807322722981143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4628888270972387855899429 867916550807322722981143)
      ·
        refine ⟨1301874826210984084471715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 867916550807322722981143 1301874826210984084471715)
        ·
          refine ⟨1952812239316476126707573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1301874826210984084471715 1952812239316476126707573)
          ·
            refine ⟨183076147435919636878835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1952812239316476126707573 183076147435919636878835)
            ·
              refine ⟨274614221153879455318253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 183076147435919636878835 274614221153879455318253)
              ·
                refine ⟨102980332932704795744345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 274614221153879455318253 102980332932704795744345)
                ·
                  refine ⟨77235249699528596808259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 102980332932704795744345 77235249699528596808259)
                  ·
                    rfl

theorem cell20_169217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 5, 1, 3, 2].length) (baseStart_169217 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_169217 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_169217 prefixEnd_169217 := by exact prefixLift 169217
  have htrace : WordTrace (prefixWord ++ tailWord_169217) baseStart_169217 baseEnd_169217 := by
    simpa [prefixWord, tailWord_169217, baseEnd_169217] using wordTrace_append hprefix tailTrace_169217
  have hstable : (prefixWord ++ tailWord_169217).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_169217).length < 2 ^ (prefixWord ++ tailWord_169217).sum := by decide
  have hdescent : baseEnd_169217 < baseStart_169217 := by decide
  rcases family_descends (prefixWord ++ tailWord_169217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_169228 : List Nat := [2, 2, 1, 2, 2, 5, 6]
def baseStart_169228 : Nat := 118140960795 + 169228 * 2 ^ 59
def prefixEnd_169228 : Nat := 4983230072969 + 3 ^ 40 * 169228 * 2
def baseEnd_169228 : Nat := 8582252266584605271283

theorem tailTrace_169228 : CollatzResearch.WordTrace tailWord_169228 prefixEnd_169228 8582252266584605271283 := by
  unfold tailWord_169228
  simp only [CollatzResearch.WordTrace]
  refine ⟨3086126115461666343258169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4114834820615555124344225 3086126115461666343258169)
  ·
    refine ⟨2314594586596249757443627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3086126115461666343258169 2314594586596249757443627)
    ·
      refine ⟨3471891879894374636165441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2314594586596249757443627 3471891879894374636165441)
      ·
        refine ⟨2603918909920780977124081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3471891879894374636165441 2603918909920780977124081)
        ·
          refine ⟨1952939182440585732843061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2603918909920780977124081 1952939182440585732843061)
          ·
            refine ⟨183088048353804912454037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1952939182440585732843061 183088048353804912454037)
            ·
              refine ⟨8582252266584605271283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 183088048353804912454037 8582252266584605271283)
              ·
                rfl

theorem cell20_169228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 5, 6].length) (baseStart_169228 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_169228 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_169228 prefixEnd_169228 := by exact prefixLift 169228
  have htrace : WordTrace (prefixWord ++ tailWord_169228) baseStart_169228 baseEnd_169228 := by
    simpa [prefixWord, tailWord_169228, baseEnd_169228] using wordTrace_append hprefix tailTrace_169228
  have hstable : (prefixWord ++ tailWord_169228).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_169228).length < 2 ^ (prefixWord ++ tailWord_169228).sum := by decide
  have hdescent : baseEnd_169228 < baseStart_169228 := by decide
  rcases family_descends (prefixWord ++ tailWord_169228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_169234 : List Nat := [3, 2, 4, 2, 1, 2, 1, 1, 4]
def baseStart_169234 : Nat := 118140960795 + 169234 * 2 ^ 59
def prefixEnd_169234 : Nat := 4983230072969 + 3 ^ 40 * 169234 * 2
def baseEnd_169234 : Nat := 77243008962752093241523

theorem tailTrace_169234 : CollatzResearch.WordTrace tailWord_169234 prefixEnd_169234 77243008962752093241523 := by
  unfold tailWord_169234
  simp only [CollatzResearch.WordTrace]
  refine ⟨1543117767225398927808689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4114980712601063807489837 1543117767225398927808689)
  ·
    refine ⟨1157338325419049195856517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1543117767225398927808689 1157338325419049195856517)
    ·
      refine ⟨217000936016071724223097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1157338325419049195856517 217000936016071724223097)
      ·
        refine ⟨162750702012053793167323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 217000936016071724223097 162750702012053793167323)
        ·
          refine ⟨244126053018080689750985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 162750702012053793167323 244126053018080689750985)
          ·
            refine ⟨183094539763560517313239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 244126053018080689750985 183094539763560517313239)
            ·
              refine ⟨274641809645340775969859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 183094539763560517313239 274641809645340775969859)
              ·
                refine ⟨411962714468011163954789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 274641809645340775969859 411962714468011163954789)
                ·
                  refine ⟨77243008962752093241523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 411962714468011163954789 77243008962752093241523)
                  ·
                    rfl

theorem cell20_169234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 2, 1, 1, 4].length) (baseStart_169234 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_169234 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_169234 prefixEnd_169234 := by exact prefixLift 169234
  have htrace : WordTrace (prefixWord ++ tailWord_169234) baseStart_169234 baseEnd_169234 := by
    simpa [prefixWord, tailWord_169234, baseEnd_169234] using wordTrace_append hprefix tailTrace_169234
  have hstable : (prefixWord ++ tailWord_169234).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_169234).length < 2 ^ (prefixWord ++ tailWord_169234).sum := by decide
  have hdescent : baseEnd_169234 < baseStart_169234 := by decide
  rcases family_descends (prefixWord ++ tailWord_169234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_169245 : List Nat := [1, 4, 2, 3, 1, 2, 2, 5]
def baseStart_169245 : Nat := 118140960795 + 169245 * 2 ^ 59
def prefixEnd_169245 : Nat := 4983230072969 + 3 ^ 40 * 169245 * 2
def baseEnd_169245 : Nat := 25749343220828314624937

theorem tailTrace_169245 : CollatzResearch.WordTrace tailWord_169245 prefixEnd_169245 25749343220828314624937 := by
  unfold tailWord_169245
  simp only [CollatzResearch.WordTrace]
  refine ⟨6172872271861744589885189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4115248181241163059923459 6172872271861744589885189)
  ·
    refine ⟨1157413550974077110603473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6172872271861744589885189 1157413550974077110603473)
    ·
      refine ⟨868060163230557832952605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1157413550974077110603473 868060163230557832952605)
      ·
        refine ⟨325522561211459187357227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 868060163230557832952605 325522561211459187357227)
        ·
          refine ⟨488283841817188781035841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 325522561211459187357227 488283841817188781035841)
          ·
            refine ⟨366212881362891585776881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 488283841817188781035841 366212881362891585776881)
            ·
              refine ⟨274659661022168689332661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 366212881362891585776881 274659661022168689332661)
              ·
                refine ⟨25749343220828314624937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 274659661022168689332661 25749343220828314624937)
                ·
                  rfl

theorem cell20_169245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 2, 2, 5].length) (baseStart_169245 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_169245 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_169245 prefixEnd_169245 := by exact prefixLift 169245
  have htrace : WordTrace (prefixWord ++ tailWord_169245) baseStart_169245 baseEnd_169245 := by
    simpa [prefixWord, tailWord_169245, baseEnd_169245] using wordTrace_append hprefix tailTrace_169245
  have hstable : (prefixWord ++ tailWord_169245).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_169245).length < 2 ^ (prefixWord ++ tailWord_169245).sum := by decide
  have hdescent : baseEnd_169245 < baseStart_169245 := by decide
  rcases family_descends (prefixWord ++ tailWord_169245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_169248 : List Nat := [2, 1, 1, 5, 3, 2, 2, 1, 3]
def baseStart_169248 : Nat := 118140960795 + 169248 * 2 ^ 59
def prefixEnd_169248 : Nat := 4983230072969 + 3 ^ 40 * 169248 * 2
def baseEnd_169248 : Nat := 77249398944230266774799

theorem tailTrace_169248 : CollatzResearch.WordTrace tailWord_169248 prefixEnd_169248 77249398944230266774799 := by
  unfold tailWord_169248
  simp only [CollatzResearch.WordTrace]
  refine ⟨3086490845425438051122199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4115321127233917401496265 3086490845425438051122199)
  ·
    refine ⟨4629736268138157076683299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3086490845425438051122199 4629736268138157076683299)
    ·
      refine ⟨6944604402207235615024949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4629736268138157076683299 6944604402207235615024949)
      ·
        refine ⟨651056662706928338908589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 6944604402207235615024949 651056662706928338908589)
        ·
          refine ⟨244146248515098127090721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 651056662706928338908589 244146248515098127090721)
          ·
            refine ⟨183109686386323595318041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 244146248515098127090721 183109686386323595318041)
            ·
              refine ⟨137332264789742696488531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 183109686386323595318041 137332264789742696488531)
              ·
                refine ⟨205998397184614044732797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 137332264789742696488531 205998397184614044732797)
                ·
                  refine ⟨77249398944230266774799, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 205998397184614044732797 77249398944230266774799)
                  ·
                    rfl

theorem cell20_169248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 2, 2, 1, 3].length) (baseStart_169248 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_169248 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_169248 prefixEnd_169248 := by exact prefixLift 169248
  have htrace : WordTrace (prefixWord ++ tailWord_169248) baseStart_169248 baseEnd_169248 := by
    simpa [prefixWord, tailWord_169248, baseEnd_169248] using wordTrace_append hprefix tailTrace_169248
  have hstable : (prefixWord ++ tailWord_169248).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_169248).length < 2 ^ (prefixWord ++ tailWord_169248).sum := by decide
  have hdescent : baseEnd_169248 < baseStart_169248 := by decide
  rcases family_descends (prefixWord ++ tailWord_169248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_169252 : List Nat := [2, 3, 1, 3, 1, 1, 3, 3, 3]
def baseStart_169252 : Nat := 118140960795 + 169252 * 2 ^ 59
def prefixEnd_169252 : Nat := 4983230072969 + 3 ^ 40 * 169252 * 2
def baseEnd_169252 : Nat := 77251224653224030641449

theorem tailTrace_169252 : CollatzResearch.WordTrace tailWord_169252 prefixEnd_169252 77251224653224030641449 := by
  unfold tailWord_169252
  simp only [CollatzResearch.WordTrace]
  refine ⟨3086563791418192392695005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4115418388557589856926673 3086563791418192392695005)
  ·
    refine ⟨1157461421781822147260627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3086563791418192392695005 1157461421781822147260627)
    ·
      refine ⟨1736192132672733220890941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1157461421781822147260627 1736192132672733220890941)
      ·
        refine ⟨651072049752274957834103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1736192132672733220890941 651072049752274957834103)
        ·
          refine ⟨976608074628412436751155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 651072049752274957834103 976608074628412436751155)
          ·
            refine ⟨1464912111942618655126733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 976608074628412436751155 1464912111942618655126733)
            ·
              refine ⟨549342041978481995672525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1464912111942618655126733 549342041978481995672525)
              ·
                refine ⟨206003265741930748377197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 549342041978481995672525 206003265741930748377197)
                ·
                  refine ⟨77251224653224030641449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 206003265741930748377197 77251224653224030641449)
                  ·
                    rfl

theorem cell20_169252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 3, 3, 3].length) (baseStart_169252 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_169252 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_169252 prefixEnd_169252 := by exact prefixLift 169252
  have htrace : WordTrace (prefixWord ++ tailWord_169252) baseStart_169252 baseEnd_169252 := by
    simpa [prefixWord, tailWord_169252, baseEnd_169252] using wordTrace_append hprefix tailTrace_169252
  have hstable : (prefixWord ++ tailWord_169252).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_169252).length < 2 ^ (prefixWord ++ tailWord_169252).sum := by decide
  have hdescent : baseEnd_169252 < baseStart_169252 := by decide
  rcases family_descends (prefixWord ++ tailWord_169252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_169266 : List Nat := [3, 2, 1, 1, 4, 1, 2, 6]
def baseStart_169266 : Nat := 118140960795 + 169266 * 2 ^ 59
def prefixEnd_169266 : Nat := 4983230072969 + 3 ^ 40 * 169266 * 2
def baseEnd_169266 : Nat := 25752538211567401391575

theorem tailTrace_169266 : CollatzResearch.WordTrace tailWord_169266 prefixEnd_169266 25752538211567401391575 := by
  unfold tailWord_169266
  simp only [CollatzResearch.WordTrace]
  refine ⟨1543409551196416294099913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4115758803190443450933101 1543409551196416294099913)
  ·
    refine ⟨1157557163397312220574935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1543409551196416294099913 1157557163397312220574935)
    ·
      refine ⟨1736335745095968330862403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1157557163397312220574935 1736335745095968330862403)
      ·
        refine ⟨2604503617643952496293605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1736335745095968330862403 2604503617643952496293605)
        ·
          refine ⟨488344428308241093055051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2604503617643952496293605 488344428308241093055051)
          ·
            refine ⟨732516642462361639582577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 488344428308241093055051 732516642462361639582577)
            ·
              refine ⟨549387481846771229686933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 732516642462361639582577 549387481846771229686933)
              ·
                refine ⟨25752538211567401391575, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 549387481846771229686933 25752538211567401391575)
                ·
                  rfl

theorem cell20_169266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 2, 6].length) (baseStart_169266 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_169266 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_169266 prefixEnd_169266 := by exact prefixLift 169266
  have htrace : WordTrace (prefixWord ++ tailWord_169266) baseStart_169266 baseEnd_169266 := by
    simpa [prefixWord, tailWord_169266, baseEnd_169266] using wordTrace_append hprefix tailTrace_169266
  have hstable : (prefixWord ++ tailWord_169266).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_169266).length < 2 ^ (prefixWord ++ tailWord_169266).sum := by decide
  have hdescent : baseEnd_169266 < baseStart_169266 := by decide
  rcases family_descends (prefixWord ++ tailWord_169266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_169287 : List Nat := [1, 1, 4, 1, 2, 11]
def baseStart_169287 : Nat := 118140960795 + 169287 * 2 ^ 59
def prefixEnd_169287 : Nat := 4983230072969 + 3 ^ 40 * 169287 * 2
def baseEnd_169287 : Nat := 2861748133589609795357

theorem tailTrace_169287 : CollatzResearch.WordTrace tailWord_169287 prefixEnd_169287 2861748133589609795357 := by
  unfold tailWord_169287
  simp only [CollatzResearch.WordTrace]
  refine ⟨6174404137709585762914115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4116269425139723841942743 6174404137709585762914115)
  ·
    refine ⟨9261606206564378644371173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6174404137709585762914115 9261606206564378644371173)
    ·
      refine ⟨1736551163730820995819595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9261606206564378644371173 1736551163730820995819595)
      ·
        refine ⟨2604826745596231493729393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1736551163730820995819595 2604826745596231493729393)
        ·
          refine ⟨1953620059197173620297045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2604826745596231493729393 1953620059197173620297045)
          ·
            refine ⟨2861748133589609795357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 1953620059197173620297045 2861748133589609795357)
            ·
              rfl

theorem cell20_169287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 11].length) (baseStart_169287 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_169287 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_169287 prefixEnd_169287 := by exact prefixLift 169287
  have htrace : WordTrace (prefixWord ++ tailWord_169287) baseStart_169287 baseEnd_169287 := by
    simpa [prefixWord, tailWord_169287, baseEnd_169287] using wordTrace_append hprefix tailTrace_169287
  have hstable : (prefixWord ++ tailWord_169287).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_169287).length < 2 ^ (prefixWord ++ tailWord_169287).sum := by decide
  have hdescent : baseEnd_169287 < baseStart_169287 := by decide
  rcases family_descends (prefixWord ++ tailWord_169287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_169352 : List Nat := [2, 1, 3, 3, 1, 2, 2, 4, 2]
def baseStart_169352 : Nat := 118140960795 + 169352 * 2 ^ 59
def prefixEnd_169352 : Nat := 4983230072969 + 3 ^ 40 * 169352 * 2
def baseEnd_169352 : Nat := 77296867378068127307707

theorem tailTrace_169352 : CollatzResearch.WordTrace tailWord_169352 prefixEnd_169352 77296867378068127307707 := by
  unfold tailWord_169352
  simp only [CollatzResearch.WordTrace]
  refine ⟨3088387441237050932015155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4117849921649401242686873 3088387441237050932015155)
  ·
    refine ⟨4632581161855576398022733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3088387441237050932015155 4632581161855576398022733)
    ·
      refine ⟨1737217935695841149258525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4632581161855576398022733 1737217935695841149258525)
      ·
        refine ⟨651456725885940430971947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1737217935695841149258525 651456725885940430971947)
        ·
          refine ⟨977185088828910646457921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 651456725885940430971947 977185088828910646457921)
          ·
            refine ⟨732888816621682984843441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 977185088828910646457921 732888816621682984843441)
            ·
              refine ⟨549666612466262238632581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 732888816621682984843441 549666612466262238632581)
              ·
                refine ⟨103062489837424169743609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 549666612466262238632581 103062489837424169743609)
                ·
                  refine ⟨77296867378068127307707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 103062489837424169743609 77296867378068127307707)
                  ·
                    rfl

theorem cell20_169352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 2, 4, 2].length) (baseStart_169352 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_169352 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_169352 prefixEnd_169352 := by exact prefixLift 169352
  have htrace : WordTrace (prefixWord ++ tailWord_169352) baseStart_169352 baseEnd_169352 := by
    simpa [prefixWord, tailWord_169352, baseEnd_169352] using wordTrace_append hprefix tailTrace_169352
  have hstable : (prefixWord ++ tailWord_169352).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_169352).length < 2 ^ (prefixWord ++ tailWord_169352).sum := by decide
  have hdescent : baseEnd_169352 < baseStart_169352 := by decide
  rcases family_descends (prefixWord ++ tailWord_169352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_169373 : List Nat := [1, 4, 2, 1, 3, 1, 2, 2, 4]
def baseStart_169373 : Nat := 118140960795 + 169373 * 2 ^ 59
def prefixEnd_169373 : Nat := 4983230072969 + 3 ^ 40 * 169373 * 2
def baseEnd_169373 : Nat := 77306452350285387607621

theorem tailTrace_169373 : CollatzResearch.WordTrace tailWord_169373 prefixEnd_169373 77306452350285387607621 := by
  unfold tailWord_169373
  simp only [CollatzResearch.WordTrace]
  refine ⟨6177540815398022450544773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4118360543598681633696515 6177540815398022450544773)
  ·
    refine ⟨1158288902887129209477145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6177540815398022450544773 1158288902887129209477145)
    ·
      refine ⟨868716677165346907107859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1158288902887129209477145 868716677165346907107859)
      ·
        refine ⟨1303075015748020360661789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 868716677165346907107859 1303075015748020360661789)
        ·
          refine ⟨488653130905507635248171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1303075015748020360661789 488653130905507635248171)
          ·
            refine ⟨732979696358261452872257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 488653130905507635248171 732979696358261452872257)
            ·
              refine ⟨549734772268696089654193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 732979696358261452872257 549734772268696089654193)
              ·
                refine ⟨412301079201522067240645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 549734772268696089654193 412301079201522067240645)
                ·
                  refine ⟨77306452350285387607621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 412301079201522067240645 77306452350285387607621)
                  ·
                    rfl

theorem cell20_169373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 2, 2, 4].length) (baseStart_169373 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_169373 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_169373 prefixEnd_169373 := by exact prefixLift 169373
  have htrace : WordTrace (prefixWord ++ tailWord_169373) baseStart_169373 baseEnd_169373 := by
    simpa [prefixWord, tailWord_169373, baseEnd_169373] using wordTrace_append hprefix tailTrace_169373
  have hstable : (prefixWord ++ tailWord_169373).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_169373).length < 2 ^ (prefixWord ++ tailWord_169373).sum := by decide
  have hdescent : baseEnd_169373 < baseStart_169373 := by decide
  rcases family_descends (prefixWord ++ tailWord_169373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_169410 : List Nat := [3, 5, 2, 1, 1, 1, 2, 5]
def baseStart_169410 : Nat := 118140960795 + 169410 * 2 ^ 59
def prefixEnd_169410 : Nat := 4983230072969 + 3 ^ 40 * 169410 * 2
def baseEnd_169410 : Nat := 25774446719492567791379

theorem tailTrace_169410 : CollatzResearch.WordTrace tailWord_169410 prefixEnd_169410 25774446719492567791379 := by
  unfold tailWord_169410
  simp only [CollatzResearch.WordTrace]
  refine ⟨1544722579065994442410421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4119260210842651846427789 1544722579065994442410421)
  ·
    refine ⟨144817741787436978975977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 1544722579065994442410421 144817741787436978975977)
    ·
      refine ⟨108613306340577734231983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 144817741787436978975977 108613306340577734231983)
      ·
        refine ⟨162919959510866601347975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108613306340577734231983 162919959510866601347975)
        ·
          refine ⟨244379939266299902021963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 162919959510866601347975 244379939266299902021963)
          ·
            refine ⟨366569908899449853032945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 244379939266299902021963 366569908899449853032945)
            ·
              refine ⟨274927431674587389774709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 366569908899449853032945 274927431674587389774709)
              ·
                refine ⟨25774446719492567791379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 274927431674587389774709 25774446719492567791379)
                ·
                  rfl

theorem cell20_169410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 1, 2, 5].length) (baseStart_169410 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_169410 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_169410 prefixEnd_169410 := by exact prefixLift 169410
  have htrace : WordTrace (prefixWord ++ tailWord_169410) baseStart_169410 baseEnd_169410 := by
    simpa [prefixWord, tailWord_169410, baseEnd_169410] using wordTrace_append hprefix tailTrace_169410
  have hstable : (prefixWord ++ tailWord_169410).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_169410).length < 2 ^ (prefixWord ++ tailWord_169410).sum := by decide
  have hdescent : baseEnd_169410 < baseStart_169410 := by decide
  rcases family_descends (prefixWord ++ tailWord_169410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_169411 : List Nat := [1, 1, 1, 3, 1, 1, 4, 6, 2]
def baseStart_169411 : Nat := 118140960795 + 169411 * 2 ^ 59
def prefixEnd_169411 : Nat := 4983230072969 + 3 ^ 40 * 169411 * 2
def baseEnd_169411 : Nat := 77323796585726144340799

theorem tailTrace_169411 : CollatzResearch.WordTrace tailWord_169411 prefixEnd_169411 77323796585726144340799 := by
  unfold tailWord_169411
  simp only [CollatzResearch.WordTrace]
  refine ⟨6178926789260354940428087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4119284526173569960285391 6178926789260354940428087)
  ·
    refine ⟨9268390183890532410642131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6178926789260354940428087 9268390183890532410642131)
    ·
      refine ⟨13902585275835798615963197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9268390183890532410642131 13902585275835798615963197)
      ·
        refine ⟨5213469478438424480986199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13902585275835798615963197 5213469478438424480986199)
        ·
          refine ⟨7820204217657636721479299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5213469478438424480986199 7820204217657636721479299)
          ·
            refine ⟨11730306326486455082218949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7820204217657636721479299 11730306326486455082218949)
            ·
              refine ⟨2199432436216210327916053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11730306326486455082218949 2199432436216210327916053)
              ·
                refine ⟨103098395447634859121065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2199432436216210327916053 103098395447634859121065)
                ·
                  refine ⟨77323796585726144340799, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 103098395447634859121065 77323796585726144340799)
                  ·
                    rfl

theorem cell20_169411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 4, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 4, 6, 2].length) (baseStart_169411 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_169411 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_169411 prefixEnd_169411 := by exact prefixLift 169411
  have htrace : WordTrace (prefixWord ++ tailWord_169411) baseStart_169411 baseEnd_169411 := by
    simpa [prefixWord, tailWord_169411, baseEnd_169411] using wordTrace_append hprefix tailTrace_169411
  have hstable : (prefixWord ++ tailWord_169411).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_169411).length < 2 ^ (prefixWord ++ tailWord_169411).sum := by decide
  have hdescent : baseEnd_169411 < baseStart_169411 := by decide
  rcases family_descends (prefixWord ++ tailWord_169411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_169418 : List Nat := [3, 1, 2, 1, 2, 4, 2, 5]
def baseStart_169418 : Nat := 118140960795 + 169418 * 2 ^ 59
def prefixEnd_169418 : Nat := 4983230072969 + 3 ^ 40 * 169418 * 2
def baseEnd_169418 : Nat := 25775663858821743702479

theorem tailTrace_169418 : CollatzResearch.WordTrace tailWord_169418 prefixEnd_169418 25775663858821743702479 := by
  unfold tailWord_169418
  simp only [CollatzResearch.WordTrace]
  refine ⟨1544795525058748783983227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4119454733489996757288605 1544795525058748783983227)
  ·
    refine ⟨2317193287588123175974841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1544795525058748783983227 2317193287588123175974841)
    ·
      refine ⟨1737894965691092381981131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2317193287588123175974841 1737894965691092381981131)
      ·
        refine ⟨2606842448536638572971697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1737894965691092381981131 2606842448536638572971697)
        ·
          refine ⟨1955131836402478929728773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2606842448536638572971697 1955131836402478929728773)
          ·
            refine ⟨366587219325464799324145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1955131836402478929728773 366587219325464799324145)
            ·
              refine ⟨274940414494098599493109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 366587219325464799324145 274940414494098599493109)
              ·
                refine ⟨25775663858821743702479, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 274940414494098599493109 25775663858821743702479)
                ·
                  rfl

theorem cell20_169418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 4, 2, 5].length) (baseStart_169418 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_169418 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_169418 prefixEnd_169418 := by exact prefixLift 169418
  have htrace : WordTrace (prefixWord ++ tailWord_169418) baseStart_169418 baseEnd_169418 := by
    simpa [prefixWord, tailWord_169418, baseEnd_169418] using wordTrace_append hprefix tailTrace_169418
  have hstable : (prefixWord ++ tailWord_169418).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_169418).length < 2 ^ (prefixWord ++ tailWord_169418).sum := by decide
  have hdescent : baseEnd_169418 < baseStart_169418 := by decide
  rcases family_descends (prefixWord ++ tailWord_169418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_169432 : List Nat := [2, 1, 2, 2, 2, 1, 2, 4, 4]
def baseStart_169432 : Nat := 118140960795 + 169432 * 2 ^ 59
def prefixEnd_169432 : Nat := 4983230072969 + 3 ^ 40 * 169432 * 2
def baseEnd_169432 : Nat := 77333381557943404640713

theorem tailTrace_169432 : CollatzResearch.WordTrace tailWord_169432 prefixEnd_169432 77333381557943404640713 := by
  unfold tailWord_169432
  simp only [CollatzResearch.WordTrace]
  refine ⟨3089846361092137763471275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4119795148122850351295033 3089846361092137763471275)
  ·
    refine ⟨4634769541638206645206913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3089846361092137763471275 4634769541638206645206913)
    ·
      refine ⟨3476077156228654983905185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4634769541638206645206913 3476077156228654983905185)
      ·
        refine ⟨2607057867171491237928889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3476077156228654983905185 2607057867171491237928889)
        ·
          refine ⟨1955293400378618428446667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2607057867171491237928889 1955293400378618428446667)
          ·
            refine ⟨2932940100567927642670001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1955293400378618428446667 2932940100567927642670001)
            ·
              refine ⟨2199705075425945732002501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2932940100567927642670001 2199705075425945732002501)
              ·
                refine ⟨412444701642364824750469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2199705075425945732002501 412444701642364824750469)
                ·
                  refine ⟨77333381557943404640713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 412444701642364824750469 77333381557943404640713)
                  ·
                    rfl

theorem cell20_169432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 2, 4, 4].length) (baseStart_169432 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_169432 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_169432 prefixEnd_169432 := by exact prefixLift 169432
  have htrace : WordTrace (prefixWord ++ tailWord_169432) baseStart_169432 baseEnd_169432 := by
    simpa [prefixWord, tailWord_169432, baseEnd_169432] using wordTrace_append hprefix tailTrace_169432
  have hstable : (prefixWord ++ tailWord_169432).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_169432).length < 2 ^ (prefixWord ++ tailWord_169432).sum := by decide
  have hdescent : baseEnd_169432 < baseStart_169432 := by decide
  rcases family_descends (prefixWord ++ tailWord_169432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_169439 : List Nat := [1, 1, 2, 3, 3, 1, 1, 8]
def baseStart_169439 : Nat := 118140960795 + 169439 * 2 ^ 59
def prefixEnd_169439 : Nat := 4983230072969 + 3 ^ 40 * 169439 * 2
def baseEnd_169439 : Nat := 25778858849560830469117

theorem tailTrace_169439 : CollatzResearch.WordTrace tailWord_169439 prefixEnd_169439 25778858849560830469117 := by
  unfold tailWord_169439
  simp only [CollatzResearch.WordTrace]
  refine ⟨6179948033158915722447371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4119965355439277148298247 6179948033158915722447371)
  ·
    refine ⟨9269922049738373583671057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6179948033158915722447371 9269922049738373583671057)
    ·
      refine ⟨6952441537303780187753293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9269922049738373583671057 6952441537303780187753293)
      ·
        refine ⟨2607165576488917570407485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6952441537303780187753293 2607165576488917570407485)
        ·
          refine ⟨977687091183344088902807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2607165576488917570407485 977687091183344088902807)
          ·
            refine ⟨1466530636775016133354211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 977687091183344088902807 1466530636775016133354211)
            ·
              refine ⟨2199795955162524200031317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1466530636775016133354211 2199795955162524200031317)
              ·
                refine ⟨25778858849560830469117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2199795955162524200031317 25778858849560830469117)
                ·
                  rfl

theorem cell20_169439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 1, 8].length) (baseStart_169439 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_169439 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_169439 prefixEnd_169439 := by exact prefixLift 169439
  have htrace : WordTrace (prefixWord ++ tailWord_169439) baseStart_169439 baseEnd_169439 := by
    simpa [prefixWord, tailWord_169439, baseEnd_169439] using wordTrace_append hprefix tailTrace_169439
  have hstable : (prefixWord ++ tailWord_169439).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_169439).length < 2 ^ (prefixWord ++ tailWord_169439).sum := by decide
  have hdescent : baseEnd_169439 < baseStart_169439 := by decide
  rcases family_descends (prefixWord ++ tailWord_169439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_169462 : List Nat := [5, 1, 1, 1, 2, 4, 2, 2, 2]
def baseStart_169462 : Nat := 118140960795 + 169462 * 2 ^ 59
def prefixEnd_169462 : Nat := 4983230072969 + 3 ^ 40 * 169462 * 2
def baseEnd_169462 : Nat := 77347074375396633640591

theorem tailTrace_169462 : CollatzResearch.WordTrace tailWord_169462 prefixEnd_169462 77347074375396633640591 := by
  unfold tailWord_169462
  simp only [CollatzResearch.WordTrace]
  refine ⟨386299182004724415658415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 4120524608050393767023093 386299182004724415658415)
  ·
    refine ⟨579448773007086623487623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 386299182004724415658415 579448773007086623487623)
    ·
      refine ⟨869173159510629935231435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 579448773007086623487623 869173159510629935231435)
      ·
        refine ⟨1303759739265944902847153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 869173159510629935231435 1303759739265944902847153)
        ·
          refine ⟨977819804449458677135365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1303759739265944902847153 977819804449458677135365)
          ·
            refine ⟨183341213334273501962881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 977819804449458677135365 183341213334273501962881)
            ·
              refine ⟨137505910000705126472161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 183341213334273501962881 137505910000705126472161)
              ·
                refine ⟨103129432500528844854121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 137505910000705126472161 103129432500528844854121)
                ·
                  refine ⟨77347074375396633640591, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 103129432500528844854121 77347074375396633640591)
                  ·
                    rfl

theorem cell20_169462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 4, 2, 2, 2].length) (baseStart_169462 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_169462 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_169462 prefixEnd_169462 := by exact prefixLift 169462
  have htrace : WordTrace (prefixWord ++ tailWord_169462) baseStart_169462 baseEnd_169462 := by
    simpa [prefixWord, tailWord_169462, baseEnd_169462] using wordTrace_append hprefix tailTrace_169462
  have hstable : (prefixWord ++ tailWord_169462).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_169462).length < 2 ^ (prefixWord ++ tailWord_169462).sum := by decide
  have hdescent : baseEnd_169462 < baseStart_169462 := by decide
  rcases family_descends (prefixWord ++ tailWord_169462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_169473 : List Nat := [1, 2, 4, 1, 4, 2, 1, 5]
def baseStart_169473 : Nat := 118140960795 + 169473 * 2 ^ 59
def prefixEnd_169473 : Nat := 4983230072969 + 3 ^ 40 * 169473 * 2
def baseEnd_169473 : Nat := 25784031691709828091293

theorem tailTrace_169473 : CollatzResearch.WordTrace tailWord_169473 prefixEnd_169473 25784031691709828091293 := by
  unfold tailWord_169473
  simp only [CollatzResearch.WordTrace]
  refine ⟨6181188115035739529185073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4120792076690493019456715 6181188115035739529185073)
  ·
    refine ⟨4635891086276804646888805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6181188115035739529185073 4635891086276804646888805)
    ·
      refine ⟨869229578676900871291651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4635891086276804646888805 869229578676900871291651)
      ·
        refine ⟨1303844368015351306937477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 869229578676900871291651 1303844368015351306937477)
        ·
          refine ⟨244470819002878370050777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1303844368015351306937477 244470819002878370050777)
          ·
            refine ⟨183353114252158777538083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 244470819002878370050777 183353114252158777538083)
            ·
              refine ⟨275029671378238166307125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 183353114252158777538083 275029671378238166307125)
              ·
                refine ⟨25784031691709828091293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 275029671378238166307125 25784031691709828091293)
                ·
                  rfl

theorem cell20_169473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 2, 1, 5].length) (baseStart_169473 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_169473 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_169473 prefixEnd_169473 := by exact prefixLift 169473
  have htrace : WordTrace (prefixWord ++ tailWord_169473) baseStart_169473 baseEnd_169473 := by
    simpa [prefixWord, tailWord_169473, baseEnd_169473] using wordTrace_append hprefix tailTrace_169473
  have hstable : (prefixWord ++ tailWord_169473).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_169473).length < 2 ^ (prefixWord ++ tailWord_169473).sum := by decide
  have hdescent : baseEnd_169473 < baseStart_169473 := by decide
  rcases family_descends (prefixWord ++ tailWord_169473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_169501 : List Nat := [1, 4, 2, 2, 1, 1, 2, 2, 5]
def baseStart_169501 : Nat := 118140960795 + 169501 * 2 ^ 59
def prefixEnd_169501 : Nat := 4983230072969 + 3 ^ 40 * 169501 * 2
def baseEnd_169501 : Nat := 77364875038085831340431

theorem tailTrace_169501 : CollatzResearch.WordTrace tailWord_169501 prefixEnd_169501 77364875038085831340431 := by
  unfold tailWord_169501
  simp only [CollatzResearch.WordTrace]
  refine ⟨6182209358934300311204357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4121472905956200207469571 6182209358934300311204357)
  ·
    refine ⟨1159164254800181308350817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6182209358934300311204357 1159164254800181308350817)
    ·
      refine ⟨869373191100135981263113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1159164254800181308350817 869373191100135981263113)
      ·
        refine ⟨652029893325101985947335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 869373191100135981263113 652029893325101985947335)
        ·
          refine ⟨978044839987652978921003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 652029893325101985947335 978044839987652978921003)
          ·
            refine ⟨1467067259981479468381505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 978044839987652978921003 1467067259981479468381505)
            ·
              refine ⟨1100300444986109601286129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1467067259981479468381505 1100300444986109601286129)
              ·
                refine ⟨825225333739582200964597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1100300444986109601286129 825225333739582200964597)
                ·
                  refine ⟨77364875038085831340431, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 825225333739582200964597 77364875038085831340431)
                  ·
                    rfl

theorem cell20_169501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 2, 2, 5].length) (baseStart_169501 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_169501 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_169501 prefixEnd_169501 := by exact prefixLift 169501
  have htrace : WordTrace (prefixWord ++ tailWord_169501) baseStart_169501 baseEnd_169501 := by
    simpa [prefixWord, tailWord_169501, baseEnd_169501] using wordTrace_append hprefix tailTrace_169501
  have hstable : (prefixWord ++ tailWord_169501).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_169501).length < 2 ^ (prefixWord ++ tailWord_169501).sum := by decide
  have hdescent : baseEnd_169501 < baseStart_169501 := by decide
  rcases family_descends (prefixWord ++ tailWord_169501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_169504 : List Nat := [2, 1, 1, 6, 1, 1, 1, 5, 2]
def baseStart_169504 : Nat := 118140960795 + 169504 * 2 ^ 59
def prefixEnd_169504 : Nat := 4983230072969 + 3 ^ 40 * 169504 * 2
def baseEnd_169504 : Nat := 77366244319831154240419

theorem tailTrace_169504 : CollatzResearch.WordTrace tailWord_169504 prefixEnd_169504 77366244319831154240419 := by
  unfold tailWord_169504
  simp only [CollatzResearch.WordTrace]
  refine ⟨3091159388961715911781783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4121545851948954549042377 3091159388961715911781783)
  ·
    refine ⟨4636739083442573867672675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3091159388961715911781783 4636739083442573867672675)
    ·
      refine ⟨6955108625163860801509013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4636739083442573867672675 6955108625163860801509013)
      ·
        refine ⟨326020716804555975070735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 6955108625163860801509013 326020716804555975070735)
        ·
          refine ⟨489031075206833962606103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 326020716804555975070735 489031075206833962606103)
          ·
            refine ⟨733546612810250943909155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 489031075206833962606103 733546612810250943909155)
            ·
              refine ⟨1100319919215376415863733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 733546612810250943909155 1100319919215376415863733)
              ·
                refine ⟨103154992426441538987225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1100319919215376415863733 103154992426441538987225)
                ·
                  refine ⟨77366244319831154240419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 103154992426441538987225 77366244319831154240419)
                  ·
                    rfl

theorem cell20_169504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 1, 5, 2].length) (baseStart_169504 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_169504 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_169504 prefixEnd_169504 := by exact prefixLift 169504
  have htrace : WordTrace (prefixWord ++ tailWord_169504) baseStart_169504 baseEnd_169504 := by
    simpa [prefixWord, tailWord_169504, baseEnd_169504] using wordTrace_append hprefix tailTrace_169504
  have hstable : (prefixWord ++ tailWord_169504).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_169504).length < 2 ^ (prefixWord ++ tailWord_169504).sum := by decide
  have hdescent : baseEnd_169504 < baseStart_169504 := by decide
  rcases family_descends (prefixWord ++ tailWord_169504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_169518 : List Nat := [4, 1, 3, 1, 2, 2, 1, 1, 5]
def baseStart_169518 : Nat := 118140960795 + 169518 * 2 ^ 59
def prefixEnd_169518 : Nat := 4983230072969 + 3 ^ 40 * 169518 * 2
def baseEnd_169518 : Nat := 77372634301309327773695

theorem tailTrace_169518 : CollatzResearch.WordTrace tailWord_169518 prefixEnd_169518 77372634301309327773695 := by
  unfold tailWord_169518
  simp only [CollatzResearch.WordTrace]
  refine ⟨772853674984089026821651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4121886266581808143048805 772853674984089026821651)
  ·
    refine ⟨1159280512476133540232477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 772853674984089026821651 1159280512476133540232477)
    ·
      refine ⟨434730192178550077587179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1159280512476133540232477 434730192178550077587179)
      ·
        refine ⟨652095288267825116380769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 434730192178550077587179 652095288267825116380769)
        ·
          refine ⟨489071466200868837285577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 652095288267825116380769 489071466200868837285577)
          ·
            refine ⟨366803599650651627964183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 489071466200868837285577 366803599650651627964183)
            ·
              refine ⟨550205399475977441946275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 366803599650651627964183 550205399475977441946275)
              ·
                refine ⟨825308099213966162919413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 550205399475977441946275 825308099213966162919413)
                ·
                  refine ⟨77372634301309327773695, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 825308099213966162919413 77372634301309327773695)
                  ·
                    rfl

theorem cell20_169518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 2, 1, 1, 5].length) (baseStart_169518 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_169518 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_169518 prefixEnd_169518 := by exact prefixLift 169518
  have htrace : WordTrace (prefixWord ++ tailWord_169518) baseStart_169518 baseEnd_169518 := by
    simpa [prefixWord, tailWord_169518, baseEnd_169518] using wordTrace_append hprefix tailTrace_169518
  have hstable : (prefixWord ++ tailWord_169518).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_169518).length < 2 ^ (prefixWord ++ tailWord_169518).sum := by decide
  have hdescent : baseEnd_169518 < baseStart_169518 := by decide
  rcases family_descends (prefixWord ++ tailWord_169518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_169525 : List Nat := [1, 3, 3, 1, 1, 4, 2, 1, 4]
def baseStart_169525 : Nat := 118140960795 + 169525 * 2 ^ 59
def prefixEnd_169525 : Nat := 4983230072969 + 3 ^ 40 * 169525 * 2
def baseEnd_169525 : Nat := 77375829292048414540333

theorem tailTrace_169525 : CollatzResearch.WordTrace tailWord_169525 prefixEnd_169525 77375829292048414540333 := by
  unfold tailWord_169525
  simp only [CollatzResearch.WordTrace]
  refine ⟨6183084710847352410078029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4122056473898234940052019 6183084710847352410078029)
  ·
    refine ⟨2318656766567757153779261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6183084710847352410078029 2318656766567757153779261)
    ·
      refine ⟨869496287462908932667223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2318656766567757153779261 869496287462908932667223)
      ·
        refine ⟨1304244431194363399000835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 869496287462908932667223 1304244431194363399000835)
        ·
          refine ⟨1956366646791545098501253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1304244431194363399000835 1956366646791545098501253)
          ·
            refine ⟨366818746273414705968985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1956366646791545098501253 366818746273414705968985)
            ·
              refine ⟨275114059705061029476739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 366818746273414705968985 275114059705061029476739)
              ·
                refine ⟨412671089557591544215109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 275114059705061029476739 412671089557591544215109)
                ·
                  refine ⟨77375829292048414540333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 412671089557591544215109 77375829292048414540333)
                  ·
                    rfl

theorem cell20_169525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 4, 2, 1, 4].length) (baseStart_169525 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_169525 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_169525 prefixEnd_169525 := by exact prefixLift 169525
  have htrace : WordTrace (prefixWord ++ tailWord_169525) baseStart_169525 baseEnd_169525 := by
    simpa [prefixWord, tailWord_169525, baseEnd_169525] using wordTrace_append hprefix tailTrace_169525
  have hstable : (prefixWord ++ tailWord_169525).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_169525).length < 2 ^ (prefixWord ++ tailWord_169525).sum := by decide
  have hdescent : baseEnd_169525 < baseStart_169525 := by decide
  rcases family_descends (prefixWord ++ tailWord_169525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_169546 : List Nat := [3, 1, 2, 1, 1, 3, 1, 4, 4]
def baseStart_169546 : Nat := 118140960795 + 169546 * 2 ^ 59
def prefixEnd_169546 : Nat := 4983230072969 + 3 ^ 40 * 169546 * 2
def baseEnd_169546 : Nat := 77385414264265674840247

theorem tailTrace_169546 : CollatzResearch.WordTrace tailWord_169546 prefixEnd_169546 77385414264265674840247 := by
  unfold tailWord_169546
  simp only [CollatzResearch.WordTrace]
  refine ⟨1545962660942818249148123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4122567095847515331061661 1545962660942818249148123)
  ·
    refine ⟨2318943991414227373722185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1545962660942818249148123 2318943991414227373722185)
    ·
      refine ⟨1739207993560670530291639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2318943991414227373722185 1739207993560670530291639)
      ·
        refine ⟨2608811990341005795437459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1739207993560670530291639 2608811990341005795437459)
        ·
          refine ⟨3913217985511508693156189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2608811990341005795437459 3913217985511508693156189)
          ·
            refine ⟨1467456744566815759933571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3913217985511508693156189 1467456744566815759933571)
            ·
              refine ⟨2201185116850223639900357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1467456744566815759933571 2201185116850223639900357)
              ·
                refine ⟨412722209409416932481317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2201185116850223639900357 412722209409416932481317)
                ·
                  refine ⟨77385414264265674840247, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 412722209409416932481317 77385414264265674840247)
                  ·
                    rfl

theorem cell20_169546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 1, 4, 4].length) (baseStart_169546 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_169546 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_169546 prefixEnd_169546 := by exact prefixLift 169546
  have htrace : WordTrace (prefixWord ++ tailWord_169546) baseStart_169546 baseEnd_169546 := by
    simpa [prefixWord, tailWord_169546, baseEnd_169546] using wordTrace_append hprefix tailTrace_169546
  have hstable : (prefixWord ++ tailWord_169546).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_169546).length < 2 ^ (prefixWord ++ tailWord_169546).sum := by decide
  have hdescent : baseEnd_169546 < baseStart_169546 := by decide
  rcases family_descends (prefixWord ++ tailWord_169546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_169549 : List Nat := [1, 6, 1, 1, 3, 1, 1, 6]
def baseStart_169549 : Nat := 118140960795 + 169549 * 2 ^ 59
def prefixEnd_169549 : Nat := 4983230072969 + 3 ^ 40 * 169549 * 2
def baseEnd_169549 : Nat := 25795594515336999246745

theorem tailTrace_169549 : CollatzResearch.WordTrace tailWord_169549 prefixEnd_169549 25795594515336999246745 := by
  unfold tailWord_169549
  simp only [CollatzResearch.WordTrace]
  refine ⟨6183960062760404508951701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4122640041840269672634467 6183960062760404508951701)
  ·
    refine ⟨289873127941893961357111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 6183960062760404508951701 289873127941893961357111)
    ·
      refine ⟨434809691912840942035667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 289873127941893961357111 434809691912840942035667)
      ·
        refine ⟨652214537869261413053501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 434809691912840942035667 652214537869261413053501)
        ·
          refine ⟨244580451700973029895063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 652214537869261413053501 244580451700973029895063)
          ·
            refine ⟨366870677551459544842595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 244580451700973029895063 366870677551459544842595)
            ·
              refine ⟨550306016327189317263893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 366870677551459544842595 550306016327189317263893)
              ·
                refine ⟨25795594515336999246745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 550306016327189317263893 25795594515336999246745)
                ·
                  rfl

theorem cell20_169549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 1, 1, 6].length) (baseStart_169549 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_169549 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_169549 prefixEnd_169549 := by exact prefixLift 169549
  have htrace : WordTrace (prefixWord ++ tailWord_169549) baseStart_169549 baseEnd_169549 := by
    simpa [prefixWord, tailWord_169549, baseEnd_169549] using wordTrace_append hprefix tailTrace_169549
  have hstable : (prefixWord ++ tailWord_169549).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_169549).length < 2 ^ (prefixWord ++ tailWord_169549).sum := by decide
  have hdescent : baseEnd_169549 < baseStart_169549 := by decide
  rcases family_descends (prefixWord ++ tailWord_169549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_169553 : List Nat := [1, 2, 2, 1, 3, 2, 3, 6]
def baseStart_169553 : Nat := 118140960795 + 169553 * 2 ^ 59
def prefixEnd_169553 : Nat := 4983230072969 + 3 ^ 40 * 169553 * 2
def baseEnd_169553 : Nat := 25796203085001587202295

theorem tailTrace_169553 : CollatzResearch.WordTrace tailWord_169553 prefixEnd_169553 25796203085001587202295 := by
  unfold tailWord_169553
  simp only [CollatzResearch.WordTrace]
  refine ⟨6184105954745913192097313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4122737303163942128064875 6184105954745913192097313)
  ·
    refine ⟨4638079466059434894072985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6184105954745913192097313 4638079466059434894072985)
    ·
      refine ⟨3478559599544576170554739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4638079466059434894072985 3478559599544576170554739)
      ·
        refine ⟨5217839399316864255832109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3478559599544576170554739 5217839399316864255832109)
        ·
          refine ⟨1956689774743824095937041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5217839399316864255832109 1956689774743824095937041)
          ·
            refine ⟨1467517331057868071952781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1956689774743824095937041 1467517331057868071952781)
            ·
              refine ⟨550318999146700526982293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1467517331057868071952781 550318999146700526982293)
              ·
                refine ⟨25796203085001587202295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 550318999146700526982293 25796203085001587202295)
                ·
                  rfl

theorem cell20_169553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 3, 6].length) (baseStart_169553 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_169553 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_169553 prefixEnd_169553 := by exact prefixLift 169553
  have htrace : WordTrace (prefixWord ++ tailWord_169553) baseStart_169553 baseEnd_169553 := by
    simpa [prefixWord, tailWord_169553, baseEnd_169553] using wordTrace_append hprefix tailTrace_169553
  have hstable : (prefixWord ++ tailWord_169553).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_169553).length < 2 ^ (prefixWord ++ tailWord_169553).sum := by decide
  have hdescent : baseEnd_169553 < baseStart_169553 := by decide
  rcases family_descends (prefixWord ++ tailWord_169553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_169590 : List Nat := [5, 1, 1, 2, 2, 3, 2, 1, 3]
def baseStart_169590 : Nat := 118140960795 + 169590 * 2 ^ 59
def prefixEnd_169590 : Nat := 4983230072969 + 3 ^ 40 * 169590 * 2
def baseEnd_169590 : Nat := 77405497063197077373401

theorem tailTrace_169590 : CollatzResearch.WordTrace tailWord_169590 prefixEnd_169590 77405497063197077373401 := by
  unfold tailWord_169590
  simp only [CollatzResearch.WordTrace]
  refine ⟨386590965975741781949639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 4123636970407912340796149 386590965975741781949639)
  ·
    refine ⟨579886448963612672924459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 386590965975741781949639 579886448963612672924459)
    ·
      refine ⟨869829673445419009386689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 579886448963612672924459 869829673445419009386689)
      ·
        refine ⟨652372255084064257040017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 869829673445419009386689 652372255084064257040017)
        ·
          refine ⟨489279191313048192780013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 652372255084064257040017 489279191313048192780013)
          ·
            refine ⟨183479696742393072292505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 489279191313048192780013 183479696742393072292505)
            ·
              refine ⟨137609772556794804219379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 183479696742393072292505 137609772556794804219379)
              ·
                refine ⟨206414658835192206329069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 137609772556794804219379 206414658835192206329069)
                ·
                  refine ⟨77405497063197077373401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 206414658835192206329069 77405497063197077373401)
                  ·
                    rfl

theorem cell20_169590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 3, 2, 1, 3].length) (baseStart_169590 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_169590 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_169590 prefixEnd_169590 := by exact prefixLift 169590
  have htrace : WordTrace (prefixWord ++ tailWord_169590) baseStart_169590 baseEnd_169590 := by
    simpa [prefixWord, tailWord_169590, baseEnd_169590] using wordTrace_append hprefix tailTrace_169590
  have hstable : (prefixWord ++ tailWord_169590).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_169590).length < 2 ^ (prefixWord ++ tailWord_169590).sum := by decide
  have hdescent : baseEnd_169590 < baseStart_169590 := by decide
  rcases family_descends (prefixWord ++ tailWord_169590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_169631 : List Nat := [1, 1, 2, 7, 2, 1, 2, 2, 2]
def baseStart_169631 : Nat := 118140960795 + 169631 * 2 ^ 59
def prefixEnd_169631 : Nat := 4983230072969 + 3 ^ 40 * 169631 * 2
def baseEnd_169631 : Nat := 77424210580383157006567

theorem tailTrace_169631 : CollatzResearch.WordTrace tailWord_169631 prefixEnd_169631 77424210580383157006567 := by
  unfold tailWord_169631
  simp only [CollatzResearch.WordTrace]
  refine ⟨6186950848463332513436747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4124633898975555008957831 6186950848463332513436747)
  ·
    refine ⟨9280426272694998770155121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6186950848463332513436747 9280426272694998770155121)
    ·
      refine ⟨6960319704521249077616341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9280426272694998770155121 6960319704521249077616341)
      ·
        refine ⟨163132493074716775256633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 6960319704521249077616341 163132493074716775256633)
        ·
          refine ⟨122349369806037581442475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 163132493074716775256633 122349369806037581442475)
          ·
            refine ⟨183524054709056372163713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 122349369806037581442475 183524054709056372163713)
            ·
              refine ⟨137643041031792279122785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 183524054709056372163713 137643041031792279122785)
              ·
                refine ⟨103232280773844209342089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 137643041031792279122785 103232280773844209342089)
                ·
                  refine ⟨77424210580383157006567, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 103232280773844209342089 77424210580383157006567)
                  ·
                    rfl

theorem cell20_169631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 2, 1, 2, 2, 2].length) (baseStart_169631 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_169631 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_169631 prefixEnd_169631 := by exact prefixLift 169631
  have htrace : WordTrace (prefixWord ++ tailWord_169631) baseStart_169631 baseEnd_169631 := by
    simpa [prefixWord, tailWord_169631, baseEnd_169631] using wordTrace_append hprefix tailTrace_169631
  have hstable : (prefixWord ++ tailWord_169631).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_169631).length < 2 ^ (prefixWord ++ tailWord_169631).sum := by decide
  have hdescent : baseEnd_169631 < baseStart_169631 := by decide
  rcases family_descends (prefixWord ++ tailWord_169631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_169632 : List Nat := [2, 1, 1, 4, 3, 2, 2, 2, 3]
def baseStart_169632 : Nat := 118140960795 + 169632 * 2 ^ 59
def prefixEnd_169632 : Nat := 4983230072969 + 3 ^ 40 * 169632 * 2
def baseEnd_169632 : Nat := 77424667007631597973229

theorem tailTrace_169632 : CollatzResearch.WordTrace tailWord_169632 prefixEnd_169632 77424667007631597973229 := by
  unfold tailWord_169632
  simp only [CollatzResearch.WordTrace]
  refine ⟨3093493660729854842111575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4124658214306473122815433 3093493660729854842111575)
  ·
    refine ⟨4640240491094782263167363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3093493660729854842111575 4640240491094782263167363)
    ·
      refine ⟨6960360736642173394751045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4640240491094782263167363 6960360736642173394751045)
      ·
        refine ⟨1305067638120407511515821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6960360736642173394751045 1305067638120407511515821)
        ·
          refine ⟨489400364295152816818433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1305067638120407511515821 489400364295152816818433)
          ·
            refine ⟨367050273221364612613825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 489400364295152816818433 367050273221364612613825)
            ·
              refine ⟨275287704916023459460369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 367050273221364612613825 275287704916023459460369)
              ·
                refine ⟨206465778687017594595277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 275287704916023459460369 206465778687017594595277)
                ·
                  refine ⟨77424667007631597973229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 206465778687017594595277 77424667007631597973229)
                  ·
                    rfl

theorem cell20_169632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 2, 2, 2, 3].length) (baseStart_169632 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_169632 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_169632 prefixEnd_169632 := by exact prefixLift 169632
  have htrace : WordTrace (prefixWord ++ tailWord_169632) baseStart_169632 baseEnd_169632 := by
    simpa [prefixWord, tailWord_169632, baseEnd_169632] using wordTrace_append hprefix tailTrace_169632
  have hstable : (prefixWord ++ tailWord_169632).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_169632).length < 2 ^ (prefixWord ++ tailWord_169632).sum := by decide
  have hdescent : baseEnd_169632 < baseStart_169632 := by decide
  rcases family_descends (prefixWord ++ tailWord_169632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_169660 : List Nat := [2, 2, 2, 3, 1, 2, 1, 1, 6]
def baseStart_169660 : Nat := 118140960795 + 169660 * 2 ^ 59
def prefixEnd_169660 : Nat := 4983230072969 + 3 ^ 40 * 169660 * 2
def baseEnd_169660 : Nat := 77437446970587945039781

theorem tailTrace_169660 : CollatzResearch.WordTrace tailWord_169660 prefixEnd_169660 77437446970587945039781 := by
  unfold tailWord_169660
  simp only [CollatzResearch.WordTrace]
  refine ⟨3094004282679135233121217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4125339043572180310828289 3094004282679135233121217)
  ·
    refine ⟨2320503212009351424840913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3094004282679135233121217 2320503212009351424840913)
    ·
      refine ⟨1740377409007013568630685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2320503212009351424840913 1740377409007013568630685)
      ·
        refine ⟨652641528377630088236507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1740377409007013568630685 652641528377630088236507)
        ·
          refine ⟨978962292566445132354761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 652641528377630088236507 978962292566445132354761)
          ·
            refine ⟨734221719424833849266071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 978962292566445132354761 734221719424833849266071)
            ·
              refine ⟨1101332579137250773899107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 734221719424833849266071 1101332579137250773899107)
              ·
                refine ⟨1651998868705876160848661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1101332579137250773899107 1651998868705876160848661)
                ·
                  refine ⟨77437446970587945039781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1651998868705876160848661 77437446970587945039781)
                  ·
                    rfl

theorem cell20_169660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 1, 1, 6].length) (baseStart_169660 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_169660 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_169660 prefixEnd_169660 := by exact prefixLift 169660
  have htrace : WordTrace (prefixWord ++ tailWord_169660) baseStart_169660 baseEnd_169660 := by
    simpa [prefixWord, tailWord_169660, baseEnd_169660] using wordTrace_append hprefix tailTrace_169660
  have hstable : (prefixWord ++ tailWord_169660).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_169660).length < 2 ^ (prefixWord ++ tailWord_169660).sum := by decide
  have hdescent : baseEnd_169660 < baseStart_169660 := by decide
  rcases family_descends (prefixWord ++ tailWord_169660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_169684 : List Nat := [2, 4, 1, 3, 1, 2, 7]
def baseStart_169684 : Nat := 118140960795 + 169684 * 2 ^ 59
def prefixEnd_169684 : Nat := 4983230072969 + 3 ^ 40 * 169684 * 2
def baseEnd_169684 : Nat := 8605377913838947582187

theorem tailTrace_169684 : CollatzResearch.WordTrace tailWord_169684 prefixEnd_169684 8605377913838947582187 := by
  unfold tailWord_169684
  simp only [CollatzResearch.WordTrace]
  refine ⟨3094441958635661282558053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4125922611514215043410737 3094441958635661282558053)
  ·
    refine ⟨580207867244186490479635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3094441958635661282558053 580207867244186490479635)
    ·
      refine ⟨870311800866279735719453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 580207867244186490479635 870311800866279735719453)
      ·
        refine ⟨326366925324854900894795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 870311800866279735719453 326366925324854900894795)
        ·
          refine ⟨489550387987282351342193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 326366925324854900894795 489550387987282351342193)
          ·
            refine ⟨367162790990461763506645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 489550387987282351342193 367162790990461763506645)
            ·
              refine ⟨8605377913838947582187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 367162790990461763506645 8605377913838947582187)
              ·
                rfl

theorem cell20_169684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 2, 7].length) (baseStart_169684 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_169684 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_169684 prefixEnd_169684 := by exact prefixLift 169684
  have htrace : WordTrace (prefixWord ++ tailWord_169684) baseStart_169684 baseEnd_169684 := by
    simpa [prefixWord, tailWord_169684, baseEnd_169684] using wordTrace_append hprefix tailTrace_169684
  have hstable : (prefixWord ++ tailWord_169684).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_169684).length < 2 ^ (prefixWord ++ tailWord_169684).sum := by decide
  have hdescent : baseEnd_169684 < baseStart_169684 := by decide
  rcases family_descends (prefixWord ++ tailWord_169684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_169732 : List Nat := [2, 3, 2, 2, 1, 2, 3, 3, 2]
def baseStart_169732 : Nat := 118140960795 + 169732 * 2 ^ 59
def prefixEnd_169732 : Nat := 4983230072969 + 3 ^ 40 * 169732 * 2
def baseEnd_169732 : Nat := 77470309732475694639487

theorem tailTrace_169732 : CollatzResearch.WordTrace tailWord_169732 prefixEnd_169732 77470309732475694639487 := by
  unfold tailWord_169732
  simp only [CollatzResearch.WordTrace]
  refine ⟨3095317310548713381431725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4127089747398284508575633 3095317310548713381431725)
  ·
    refine ⟨1160743991455767518036897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3095317310548713381431725 1160743991455767518036897)
    ·
      refine ⟨870557993591825638527673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1160743991455767518036897 870557993591825638527673)
      ·
        refine ⟨652918495193869228895755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 870557993591825638527673 652918495193869228895755)
        ·
          refine ⟨979377742790803843343633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 652918495193869228895755 979377742790803843343633)
          ·
            refine ⟨734533307093102882507725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 979377742790803843343633 734533307093102882507725)
            ·
              refine ⟨275449990159913580940397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 734533307093102882507725 275449990159913580940397)
              ·
                refine ⟨103293746309967592852649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 275449990159913580940397 103293746309967592852649)
                ·
                  refine ⟨77470309732475694639487, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 103293746309967592852649 77470309732475694639487)
                  ·
                    rfl

theorem cell20_169732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 3, 3, 2].length) (baseStart_169732 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_169732 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_169732 prefixEnd_169732 := by exact prefixLift 169732
  have htrace : WordTrace (prefixWord ++ tailWord_169732) baseStart_169732 baseEnd_169732 := by
    simpa [prefixWord, tailWord_169732, baseEnd_169732] using wordTrace_append hprefix tailTrace_169732
  have hstable : (prefixWord ++ tailWord_169732).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_169732).length < 2 ^ (prefixWord ++ tailWord_169732).sum := by decide
  have hdescent : baseEnd_169732 < baseStart_169732 := by decide
  rcases family_descends (prefixWord ++ tailWord_169732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_169746 : List Nat := [3, 2, 4, 1, 1, 1, 2, 1, 5]
def baseStart_169746 : Nat := 118140960795 + 169746 * 2 ^ 59
def prefixEnd_169746 : Nat := 4983230072969 + 3 ^ 40 * 169746 * 2
def baseEnd_169746 : Nat := 77476699713953868172763

theorem tailTrace_169746 : CollatzResearch.WordTrace tailWord_169746 prefixEnd_169746 77476699713953868172763 := by
  unfold tailWord_169746
  simp only [CollatzResearch.WordTrace]
  refine ⟨1547786310761676788468273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 4127430162031138102582061 1547786310761676788468273)
  ·
    refine ⟨1160839733071257591351205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1547786310761676788468273 1160839733071257591351205)
    ·
      refine ⟨217657449950860798378351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1160839733071257591351205 217657449950860798378351)
      ·
        refine ⟨326486174926291197567527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 217657449950860798378351 326486174926291197567527)
        ·
          refine ⟨489729262389436796351291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 326486174926291197567527 489729262389436796351291)
          ·
            refine ⟨734593893584155194526937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 489729262389436796351291 734593893584155194526937)
            ·
              refine ⟨550945420188116395895203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 734593893584155194526937 550945420188116395895203)
              ·
                refine ⟨826418130282174593842805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 550945420188116395895203 826418130282174593842805)
                ·
                  refine ⟨77476699713953868172763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 826418130282174593842805 77476699713953868172763)
                  ·
                    rfl

theorem cell20_169746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 2, 1, 5].length) (baseStart_169746 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_169746 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_169746 prefixEnd_169746 := by exact prefixLift 169746
  have htrace : WordTrace (prefixWord ++ tailWord_169746) baseStart_169746 baseEnd_169746 := by
    simpa [prefixWord, tailWord_169746, baseEnd_169746] using wordTrace_append hprefix tailTrace_169746
  have hstable : (prefixWord ++ tailWord_169746).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_169746).length < 2 ^ (prefixWord ++ tailWord_169746).sum := by decide
  have hdescent : baseEnd_169746 < baseStart_169746 := by decide
  rcases family_descends (prefixWord ++ tailWord_169746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_169788 : List Nat := [2, 2, 2, 2, 1, 1, 2, 1, 7]
def baseStart_169788 : Nat := 118140960795 + 169788 * 2 ^ 59
def prefixEnd_169788 : Nat := 4983230072969 + 3 ^ 40 * 169788 * 2
def baseEnd_169788 : Nat := 77495869658388388772591

theorem tailTrace_169788 : CollatzResearch.WordTrace tailWord_169788 prefixEnd_169788 77495869658388388772591 := by
  unfold tailWord_169788
  simp only [CollatzResearch.WordTrace]
  refine ⟨3096338554447274163451009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4128451405929698884601345 3096338554447274163451009)
  ·
    refine ⟨2322253915835455622588257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3096338554447274163451009 2322253915835455622588257)
    ·
      refine ⟨1741690436876591716941193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2322253915835455622588257 1741690436876591716941193)
      ·
        refine ⟨1306267827657443787705895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1741690436876591716941193 1306267827657443787705895)
        ·
          refine ⟨1959401741486165681558843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1306267827657443787705895 1959401741486165681558843)
          ·
            refine ⟨2939102612229248522338265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1959401741486165681558843 2939102612229248522338265)
            ·
              refine ⟨2204326959171936391753699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2939102612229248522338265 2204326959171936391753699)
              ·
                refine ⟨3306490438757904587630549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2204326959171936391753699 3306490438757904587630549)
                ·
                  refine ⟨77495869658388388772591, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3306490438757904587630549 77495869658388388772591)
                  ·
                    rfl

theorem cell20_169788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 2, 1, 7].length) (baseStart_169788 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_169788 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_169788 prefixEnd_169788 := by exact prefixLift 169788
  have htrace : WordTrace (prefixWord ++ tailWord_169788) baseStart_169788 baseEnd_169788 := by
    simpa [prefixWord, tailWord_169788, baseEnd_169788] using wordTrace_append hprefix tailTrace_169788
  have hstable : (prefixWord ++ tailWord_169788).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_169788).length < 2 ^ (prefixWord ++ tailWord_169788).sum := by decide
  have hdescent : baseEnd_169788 < baseStart_169788 := by decide
  rcases family_descends (prefixWord ++ tailWord_169788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_169804 : List Nat := [2, 2, 1, 3, 5, 1, 2, 2, 2]
def baseStart_169804 : Nat := 118140960795 + 169804 * 2 ^ 59
def prefixEnd_169804 : Nat := 4983230072969 + 3 ^ 40 * 169804 * 2
def baseEnd_169804 : Nat := 77503172494363444239193

theorem tailTrace_169804 : CollatzResearch.WordTrace tailWord_169804 prefixEnd_169804 77503172494363444239193 := by
  unfold tailWord_169804
  simp only [CollatzResearch.WordTrace]
  refine ⟨3096630338418291529742233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4128840451224388706322977 3096630338418291529742233)
  ·
    refine ⟨2322472753813718647306675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3096630338418291529742233 2322472753813718647306675)
    ·
      refine ⟨3483709130720577970960013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2322472753813718647306675 3483709130720577970960013)
      ·
        refine ⟨1306390924020216739110005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3483709130720577970960013 1306390924020216739110005)
        ·
          refine ⟨122474149126895319291563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 1306390924020216739110005 122474149126895319291563)
          ·
            refine ⟨183711223690342978937345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 122474149126895319291563 183711223690342978937345)
            ·
              refine ⟨137783417767757234203009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 183711223690342978937345 137783417767757234203009)
              ·
                refine ⟨103337563325817925652257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 137783417767757234203009 103337563325817925652257)
                ·
                  refine ⟨77503172494363444239193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 103337563325817925652257 77503172494363444239193)
                  ·
                    rfl

theorem cell20_169804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 5, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 5, 1, 2, 2, 2].length) (baseStart_169804 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_169804 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_169804 prefixEnd_169804 := by exact prefixLift 169804
  have htrace : WordTrace (prefixWord ++ tailWord_169804) baseStart_169804 baseEnd_169804 := by
    simpa [prefixWord, tailWord_169804, baseEnd_169804] using wordTrace_append hprefix tailTrace_169804
  have hstable : (prefixWord ++ tailWord_169804).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_169804).length < 2 ^ (prefixWord ++ tailWord_169804).sum := by decide
  have hdescent : baseEnd_169804 < baseStart_169804 := by decide
  rcases family_descends (prefixWord ++ tailWord_169804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_169815 : List Nat := [1, 1, 3, 2, 6, 1, 1, 5]
def baseStart_169815 : Nat := 118140960795 + 169815 * 2 ^ 59
def prefixEnd_169815 : Nat := 4983230072969 + 3 ^ 40 * 169815 * 2
def baseEnd_169815 : Nat := 25836064398032098290827

theorem tailTrace_169815 : CollatzResearch.WordTrace tailWord_169815 prefixEnd_169815 25836064398032098290827 := by
  unfold tailWord_169815
  simp only [CollatzResearch.WordTrace]
  refine ⟨6193661879796731938134899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4129107919864487958756599 6193661879796731938134899)
  ·
    refine ⟨9290492819695097907202349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6193661879796731938134899 9290492819695097907202349)
    ·
      refine ⟨3483934807385661715200881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9290492819695097907202349 3483934807385661715200881)
      ·
        refine ⟨2612951105539246286400661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3483934807385661715200881 2612951105539246286400661)
        ·
          refine ⟨122482083072152169675031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 2612951105539246286400661 122482083072152169675031)
          ·
            refine ⟨183723124608228254512547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 122482083072152169675031 183723124608228254512547)
            ·
              refine ⟨275584686912342381768821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 183723124608228254512547 275584686912342381768821)
              ·
                refine ⟨25836064398032098290827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 275584686912342381768821 25836064398032098290827)
                ·
                  rfl

theorem cell20_169815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 6, 1, 1, 5].length) (baseStart_169815 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_169815 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_169815 prefixEnd_169815 := by exact prefixLift 169815
  have htrace : WordTrace (prefixWord ++ tailWord_169815) baseStart_169815 baseEnd_169815 := by
    simpa [prefixWord, tailWord_169815, baseEnd_169815] using wordTrace_append hprefix tailTrace_169815
  have hstable : (prefixWord ++ tailWord_169815).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_169815).length < 2 ^ (prefixWord ++ tailWord_169815).sum := by decide
  have hdescent : baseEnd_169815 < baseStart_169815 := by decide
  rcases family_descends (prefixWord ++ tailWord_169815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_169836 : List Nat := [2, 2, 1, 1, 4, 3, 3, 4]
def baseStart_169836 : Nat := 118140960795 + 169836 * 2 ^ 59
def prefixEnd_169836 : Nat := 4983230072969 + 3 ^ 40 * 169836 * 2
def baseEnd_169836 : Nat := 25839259388771185057465

theorem tailTrace_169836 : CollatzResearch.WordTrace tailWord_169836 prefixEnd_169836 25839259388771185057465 := by
  unfold tailWord_169836
  simp only [CollatzResearch.WordTrace]
  refine ⟨3097213906360326262324681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4129618541813768349766241 3097213906360326262324681)
  ·
    refine ⟨2322910429770244696743511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3097213906360326262324681 2322910429770244696743511)
    ·
      refine ⟨3484365644655367045115267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2322910429770244696743511 3484365644655367045115267)
      ·
        refine ⟨5226548466983050567672901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3484365644655367045115267 5226548466983050567672901)
        ·
          refine ⟨979977837559321981438669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5226548466983050567672901 979977837559321981438669)
          ·
            refine ⟨367491689084745743039501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 979977837559321981438669 367491689084745743039501)
            ·
              refine ⟨137809383406779653639813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 367491689084745743039501 137809383406779653639813)
              ·
                refine ⟨25839259388771185057465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 137809383406779653639813 25839259388771185057465)
                ·
                  rfl

theorem cell20_169836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 3, 3, 4].length) (baseStart_169836 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_169836 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_169836 prefixEnd_169836 := by exact prefixLift 169836
  have htrace : WordTrace (prefixWord ++ tailWord_169836) baseStart_169836 baseEnd_169836 := by
    simpa [prefixWord, tailWord_169836, baseEnd_169836] using wordTrace_append hprefix tailTrace_169836
  have hstable : (prefixWord ++ tailWord_169836).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_169836).length < 2 ^ (prefixWord ++ tailWord_169836).sum := by decide
  have hdescent : baseEnd_169836 < baseStart_169836 := by decide
  rcases family_descends (prefixWord ++ tailWord_169836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_169908 : List Nat := [2, 5, 2, 1, 3, 1, 6]
def baseStart_169908 : Nat := 118140960795 + 169908 * 2 ^ 59
def prefixEnd_169908 : Nat := 4983230072969 + 3 ^ 40 * 169908 * 2
def baseEnd_169908 : Nat := 8616737880911256085789

theorem tailTrace_169908 : CollatzResearch.WordTrace tailWord_169908 prefixEnd_169908 8616737880911256085789 := by
  unfold tailWord_169908
  simp only [CollatzResearch.WordTrace]
  refine ⟨3098526934229904410635189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4131369245639872547513585 3098526934229904410635189)
  ·
    refine ⟨290486900084053538497049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 3098526934229904410635189 290486900084053538497049)
    ·
      refine ⟨217865175063040153872787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 290486900084053538497049 217865175063040153872787)
      ·
        refine ⟨326797762594560230809181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 217865175063040153872787 326797762594560230809181)
        ·
          refine ⟨122549160972960086553443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 326797762594560230809181 122549160972960086553443)
          ·
            refine ⟨183823741459440129830165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 122549160972960086553443 183823741459440129830165)
            ·
              refine ⟨8616737880911256085789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 183823741459440129830165 8616737880911256085789)
              ·
                rfl

theorem cell20_169908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 3, 1, 6].length) (baseStart_169908 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_169908 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_169908 prefixEnd_169908 := by exact prefixLift 169908
  have htrace : WordTrace (prefixWord ++ tailWord_169908) baseStart_169908 baseEnd_169908 := by
    simpa [prefixWord, tailWord_169908, baseEnd_169908] using wordTrace_append hprefix tailTrace_169908
  have hstable : (prefixWord ++ tailWord_169908).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_169908).length < 2 ^ (prefixWord ++ tailWord_169908).sum := by decide
  have hdescent : baseEnd_169908 < baseStart_169908 := by decide
  rcases family_descends (prefixWord ++ tailWord_169908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_170019 : List Nat := [1, 1, 1, 4, 3, 1, 4, 3, 2]
def baseStart_170019 : Nat := 118140960795 + 170019 * 2 ^ 59
def prefixEnd_170019 : Nat := 4983230072969 + 3 ^ 40 * 170019 * 2
def baseEnd_170019 : Nat := 77601304352778252071647

theorem tailTrace_170019 : CollatzResearch.WordTrace tailWord_170019 prefixEnd_170019 77601304352778252071647 := by
  unfold tailWord_170019
  simp only [CollatzResearch.WordTrace]
  refine ⟨6201102371057674778561111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4134068247371783185707407 6201102371057674778561111)
  ·
    refine ⟨9301653556586512167841667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6201102371057674778561111 9301653556586512167841667)
    ·
      refine ⟨13952480334879768251762501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9301653556586512167841667 13952480334879768251762501)
      ·
        refine ⟨2616090062789956547205469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13952480334879768251762501 2616090062789956547205469)
        ·
          refine ⟨981033773546233705202051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2616090062789956547205469 981033773546233705202051)
          ·
            refine ⟨1471550660319350557803077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 981033773546233705202051 1471550660319350557803077)
            ·
              refine ⟨275915748809878229588077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1471550660319350557803077 275915748809878229588077)
              ·
                refine ⟨103468405803704336095529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 275915748809878229588077 103468405803704336095529)
                ·
                  refine ⟨77601304352778252071647, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 103468405803704336095529 77601304352778252071647)
                  ·
                    rfl

theorem cell20_170019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 4, 3, 2].length) (baseStart_170019 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_170019 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_170019 prefixEnd_170019 := by exact prefixLift 170019
  have htrace : WordTrace (prefixWord ++ tailWord_170019) baseStart_170019 baseEnd_170019 := by
    simpa [prefixWord, tailWord_170019, baseEnd_170019] using wordTrace_append hprefix tailTrace_170019
  have hstable : (prefixWord ++ tailWord_170019).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_170019).length < 2 ^ (prefixWord ++ tailWord_170019).sum := by decide
  have hdescent : baseEnd_170019 < baseStart_170019 := by decide
  rcases family_descends (prefixWord ++ tailWord_170019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_170033 : List Nat := [1, 2, 2, 3, 1, 3, 3, 2, 3]
def baseStart_170033 : Nat := 118140960795 + 170033 * 2 ^ 59
def prefixEnd_170033 : Nat := 4983230072969 + 3 ^ 40 * 170033 * 2
def baseEnd_170033 : Nat := 77607694334256425604923

theorem tailTrace_170033 : CollatzResearch.WordTrace tailWord_170033 prefixEnd_170033 77607694334256425604923 := by
  unfold tailWord_170033
  simp only [CollatzResearch.WordTrace]
  refine ⟨6201612993006955169570753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4134408662004636779713835 6201612993006955169570753)
  ·
    refine ⟨4651209744755216377178065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6201612993006955169570753 4651209744755216377178065)
    ·
      refine ⟨3488407308566412282883549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4651209744755216377178065 3488407308566412282883549)
      ·
        refine ⟨1308152740712404606081331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3488407308566412282883549 1308152740712404606081331)
        ·
          refine ⟨1962229111068606909121997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1308152740712404606081331 1962229111068606909121997)
          ·
            refine ⟨735835916650727590920749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1962229111068606909121997 735835916650727590920749)
            ·
              refine ⟨275938468744022846595281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 735835916650727590920749 275938468744022846595281)
              ·
                refine ⟨206953851558017134946461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 275938468744022846595281 206953851558017134946461)
                ·
                  refine ⟨77607694334256425604923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 206953851558017134946461 77607694334256425604923)
                  ·
                    rfl

theorem cell20_170033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 3, 2, 3].length) (baseStart_170033 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_170033 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_170033 prefixEnd_170033 := by exact prefixLift 170033
  have htrace : WordTrace (prefixWord ++ tailWord_170033) baseStart_170033 baseEnd_170033 := by
    simpa [prefixWord, tailWord_170033, baseEnd_170033] using wordTrace_append hprefix tailTrace_170033
  have hstable : (prefixWord ++ tailWord_170033).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_170033).length < 2 ^ (prefixWord ++ tailWord_170033).sum := by decide
  have hdescent : baseEnd_170033 < baseStart_170033 := by decide
  rcases family_descends (prefixWord ++ tailWord_170033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_170036 : List Nat := [2, 5, 1, 2, 2, 1, 2, 1, 4]
def baseStart_170036 : Nat := 118140960795 + 170036 * 2 ^ 59
def prefixEnd_170036 : Nat := 4983230072969 + 3 ^ 40 * 170036 * 2
def baseEnd_170036 : Nat := 77609063616001748504911

theorem tailTrace_170036 : CollatzResearch.WordTrace tailWord_170036 prefixEnd_170036 77609063616001748504911 := by
  unfold tailWord_170036
  simp only [CollatzResearch.WordTrace]
  refine ⟨3100861205998043340964981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4134481607997391121286641 3100861205998043340964981)
  ·
    refine ⟨290705738062316563215467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 3100861205998043340964981 290705738062316563215467)
    ·
      refine ⟨436058607093474844823201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 290705738062316563215467 436058607093474844823201)
      ·
        refine ⟨327043955320106133617401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 436058607093474844823201 327043955320106133617401)
        ·
          refine ⟨245282966490079600213051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 327043955320106133617401 245282966490079600213051)
          ·
            refine ⟨367924449735119400319577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 245282966490079600213051 367924449735119400319577)
            ·
              refine ⟨275943337301339550239683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 367924449735119400319577 275943337301339550239683)
              ·
                refine ⟨413915005952009325359525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 275943337301339550239683 413915005952009325359525)
                ·
                  refine ⟨77609063616001748504911, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 413915005952009325359525 77609063616001748504911)
                  ·
                    rfl

theorem cell20_170036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 1, 2, 1, 4].length) (baseStart_170036 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_170036 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_170036 prefixEnd_170036 := by exact prefixLift 170036
  have htrace : WordTrace (prefixWord ++ tailWord_170036) baseStart_170036 baseEnd_170036 := by
    simpa [prefixWord, tailWord_170036, baseEnd_170036] using wordTrace_append hprefix tailTrace_170036
  have hstable : (prefixWord ++ tailWord_170036).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_170036).length < 2 ^ (prefixWord ++ tailWord_170036).sum := by decide
  have hdescent : baseEnd_170036 < baseStart_170036 := by decide
  rcases family_descends (prefixWord ++ tailWord_170036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_170070 : List Nat := [5, 2, 2, 1, 1, 3, 1, 3, 2]
def baseStart_170070 : Nat := 118140960795 + 170070 * 2 ^ 59
def prefixEnd_170070 : Nat := 4983230072969 + 3 ^ 40 * 170070 * 2
def baseEnd_170070 : Nat := 77624582142448741371439

theorem tailTrace_170070 : CollatzResearch.WordTrace tailWord_170070 prefixEnd_170070 77624582142448741371439 := by
  unfold tailWord_170070
  simp only [CollatzResearch.WordTrace]
  refine ⟨387685155867056905541729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 4135308329248606992445109 387685155867056905541729)
  ·
    refine ⟨290763866900292679156297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 387685155867056905541729 290763866900292679156297)
    ·
      refine ⟨218072900175219509367223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 290763866900292679156297 218072900175219509367223)
      ·
        refine ⟨327109350262829264050835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 218072900175219509367223 327109350262829264050835)
        ·
          refine ⟨490664025394243896076253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 327109350262829264050835 490664025394243896076253)
          ·
            refine ⟨183999009522841461028595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 490664025394243896076253 183999009522841461028595)
            ·
              refine ⟨275998514284262191542893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 183999009522841461028595 275998514284262191542893)
              ·
                refine ⟨103499442856598321828585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 275998514284262191542893 103499442856598321828585)
                ·
                  refine ⟨77624582142448741371439, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 103499442856598321828585 77624582142448741371439)
                  ·
                    rfl

theorem cell20_170070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 3, 1, 3, 2].length) (baseStart_170070 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_170070 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_170070 prefixEnd_170070 := by exact prefixLift 170070
  have htrace : WordTrace (prefixWord ++ tailWord_170070) baseStart_170070 baseEnd_170070 := by
    simpa [prefixWord, tailWord_170070, baseEnd_170070] using wordTrace_append hprefix tailTrace_170070
  have hstable : (prefixWord ++ tailWord_170070).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_170070).length < 2 ^ (prefixWord ++ tailWord_170070).sum := by decide
  have hdescent : baseEnd_170070 < baseStart_170070 := by decide
  rcases family_descends (prefixWord ++ tailWord_170070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_170085 : List Nat := [1, 3, 1, 3, 2, 4, 6]
def baseStart_170085 : Nat := 118140960795 + 170085 * 2 ^ 59
def prefixEnd_170085 : Nat := 4983230072969 + 3 ^ 40 * 170085 * 2
def baseEnd_170085 : Nat := 8625714283463928430153

theorem tailTrace_170085 : CollatzResearch.WordTrace tailWord_170085 prefixEnd_170085 8625714283463928430153 := by
  unfold tailWord_170085
  simp only [CollatzResearch.WordTrace]
  refine ⟨6203509588818568050463709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4135673059212378700309139 6203509588818568050463709)
  ·
    refine ⟨2326316095806963018923891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6203509588818568050463709 2326316095806963018923891)
    ·
      refine ⟨3489474143710444528385837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2326316095806963018923891 3489474143710444528385837)
      ·
        refine ⟨1308552803891416698144689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3489474143710444528385837 1308552803891416698144689)
        ·
          refine ⟨981414602918562523608517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1308552803891416698144689 981414602918562523608517)
          ·
            refine ⟨184015238047230473176597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 981414602918562523608517 184015238047230473176597)
            ·
              refine ⟨8625714283463928430153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 184015238047230473176597 8625714283463928430153)
              ·
                rfl

theorem cell20_170085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 4, 6].length) (baseStart_170085 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_170085 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_170085 prefixEnd_170085 := by exact prefixLift 170085
  have htrace : WordTrace (prefixWord ++ tailWord_170085) baseStart_170085 baseEnd_170085 := by
    simpa [prefixWord, tailWord_170085, baseEnd_170085] using wordTrace_append hprefix tailTrace_170085
  have hstable : (prefixWord ++ tailWord_170085).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_170085).length < 2 ^ (prefixWord ++ tailWord_170085).sum := by decide
  have hdescent : baseEnd_170085 < baseStart_170085 := by decide
  rcases family_descends (prefixWord ++ tailWord_170085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_170092 : List Nat := [2, 2, 1, 1, 3, 3, 2, 1, 5]
def baseStart_170092 : Nat := 118140960795 + 170092 * 2 ^ 59
def prefixEnd_170092 : Nat := 4983230072969 + 3 ^ 40 * 170092 * 2
def baseEnd_170092 : Nat := 77634623541914442638015

theorem tailTrace_170092 : CollatzResearch.WordTrace tailWord_170092 prefixEnd_170092 77634623541914442638015 := by
  unfold tailWord_170092
  simp only [CollatzResearch.WordTrace]
  refine ⟨3101882449896604122984265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4135843266528805497312353 3101882449896604122984265)
  ·
    refine ⟨2326411837422453092238199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3101882449896604122984265 2326411837422453092238199)
    ·
      refine ⟨3489617756133679638357299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2326411837422453092238199 3489617756133679638357299)
      ·
        refine ⟨5234426634200519457535949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3489617756133679638357299 5234426634200519457535949)
        ·
          refine ⟨1962909987825194796575981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5234426634200519457535949 1962909987825194796575981)
          ·
            refine ⟨736091245434448048715993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1962909987825194796575981 736091245434448048715993)
            ·
              refine ⟨552068434075836036536995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 736091245434448048715993 552068434075836036536995)
              ·
                refine ⟨828102651113754054805493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 552068434075836036536995 828102651113754054805493)
                ·
                  refine ⟨77634623541914442638015, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 828102651113754054805493 77634623541914442638015)
                  ·
                    rfl

theorem cell20_170092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 5].length) (baseStart_170092 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_170092 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_170092 prefixEnd_170092 := by exact prefixLift 170092
  have htrace : WordTrace (prefixWord ++ tailWord_170092) baseStart_170092 baseEnd_170092 := by
    simpa [prefixWord, tailWord_170092, baseEnd_170092] using wordTrace_append hprefix tailTrace_170092
  have hstable : (prefixWord ++ tailWord_170092).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_170092).length < 2 ^ (prefixWord ++ tailWord_170092).sum := by decide
  have hdescent : baseEnd_170092 < baseStart_170092 := by decide
  rcases family_descends (prefixWord ++ tailWord_170092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_170102 : List Nat := [5, 1, 1, 2, 1, 3, 2, 5]
def baseStart_170102 : Nat := 118140960795 + 170102 * 2 ^ 59
def prefixEnd_170102 : Nat := 4983230072969 + 3 ^ 40 * 170102 * 2
def baseEnd_170102 : Nat := 25879729271466284101547

theorem tailTrace_170102 : CollatzResearch.WordTrace tailWord_170102 prefixEnd_170102 25879729271466284101547 := by
  unfold tailWord_170102
  simp only [CollatzResearch.WordTrace]
  refine ⟨387758101859811247114535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 4136086419837986635888373 387758101859811247114535)
  ·
    refine ⟨581637152789716870671803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 387758101859811247114535 581637152789716870671803)
    ·
      refine ⟨872455729184575306007705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 581637152789716870671803 872455729184575306007705)
      ·
        refine ⟨654341796888431479505779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 872455729184575306007705 654341796888431479505779)
        ·
          refine ⟨981512695332647219258669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 654341796888431479505779 981512695332647219258669)
          ·
            refine ⟨368067260749742707222001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 981512695332647219258669 368067260749742707222001)
            ·
              refine ⟨276050445562307030416501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 368067260749742707222001 276050445562307030416501)
              ·
                refine ⟨25879729271466284101547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 276050445562307030416501 25879729271466284101547)
                ·
                  rfl

theorem cell20_170102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 3, 2, 5].length) (baseStart_170102 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_170102 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_170102 prefixEnd_170102 := by exact prefixLift 170102
  have htrace : WordTrace (prefixWord ++ tailWord_170102) baseStart_170102 baseEnd_170102 := by
    simpa [prefixWord, tailWord_170102, baseEnd_170102] using wordTrace_append hprefix tailTrace_170102
  have hstable : (prefixWord ++ tailWord_170102).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_170102).length < 2 ^ (prefixWord ++ tailWord_170102).sum := by decide
  have hdescent : baseEnd_170102 < baseStart_170102 := by decide
  rcases family_descends (prefixWord ++ tailWord_170102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_170109 : List Nat := [1, 4, 1, 1, 3, 3, 1, 3, 3]
def baseStart_170109 : Nat := 118140960795 + 170109 * 2 ^ 59
def prefixEnd_170109 : Nat := 4983230072969 + 3 ^ 40 * 170109 * 2
def baseEnd_170109 : Nat := 77642382805137939071279

theorem tailTrace_170109 : CollatzResearch.WordTrace tailWord_170109 prefixEnd_170109 77642382805137939071279 := by
  unfold tailWord_170109
  simp only [CollatzResearch.WordTrace]
  refine ⟨6204384940731620149337381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4136256627154413432891587 6204384940731620149337381)
  ·
    refine ⟨1163322176387178778000759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6204384940731620149337381 1163322176387178778000759)
    ·
      refine ⟨1744983264580768167001139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1163322176387178778000759 1744983264580768167001139)
      ·
        refine ⟨2617474896871152250501709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1744983264580768167001139 2617474896871152250501709)
        ·
          refine ⟨981553086326682093938141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2617474896871152250501709 981553086326682093938141)
          ·
            refine ⟨368082407372505785226803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 981553086326682093938141 368082407372505785226803)
            ·
              refine ⟨552123611058758677840205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 368082407372505785226803 552123611058758677840205)
              ·
                refine ⟨207046354147034504190077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 552123611058758677840205 207046354147034504190077)
                ·
                  refine ⟨77642382805137939071279, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 207046354147034504190077 77642382805137939071279)
                  ·
                    rfl

theorem cell20_170109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 3, 1, 3, 3].length) (baseStart_170109 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_170109 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_170109 prefixEnd_170109 := by exact prefixLift 170109
  have htrace : WordTrace (prefixWord ++ tailWord_170109) baseStart_170109 baseEnd_170109 := by
    simpa [prefixWord, tailWord_170109, baseEnd_170109] using wordTrace_append hprefix tailTrace_170109
  have hstable : (prefixWord ++ tailWord_170109).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_170109).length < 2 ^ (prefixWord ++ tailWord_170109).sum := by decide
  have hdescent : baseEnd_170109 < baseStart_170109 := by decide
  rcases family_descends (prefixWord ++ tailWord_170109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_170144 : List Nat := [2, 1, 1, 4, 2, 10]
def baseStart_170144 : Nat := 118140960795 + 170144 * 2 ^ 59
def prefixEnd_170144 : Nat := 4983230072969 + 3 ^ 40 * 170144 * 2
def baseEnd_170144 : Nat := 2876235472549384181647

theorem tailTrace_170144 : CollatzResearch.WordTrace tailWord_170144 prefixEnd_170144 2876235472549384181647 := by
  unfold tailWord_170144
  simp only [CollatzResearch.WordTrace]
  refine ⟨3102830747802410563430743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4137107663736547417907657 3102830747802410563430743)
  ·
    refine ⟨4654246121703615845146115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3102830747802410563430743 4654246121703615845146115)
    ·
      refine ⟨6981369182555423767719173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4654246121703615845146115 6981369182555423767719173)
      ·
        refine ⟨1309006721729141956447345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6981369182555423767719173 1309006721729141956447345)
        ·
          refine ⟨981755041296856467335509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1309006721729141956447345 981755041296856467335509)
          ·
            refine ⟨2876235472549384181647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 981755041296856467335509 2876235472549384181647)
            ·
              rfl

theorem cell20_170144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 10].length) (baseStart_170144 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_170144 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_170144 prefixEnd_170144 := by exact prefixLift 170144
  have htrace : WordTrace (prefixWord ++ tailWord_170144) baseStart_170144 baseEnd_170144 := by
    simpa [prefixWord, tailWord_170144, baseEnd_170144] using wordTrace_append hprefix tailTrace_170144
  have hstable : (prefixWord ++ tailWord_170144).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_170144).length < 2 ^ (prefixWord ++ tailWord_170144).sum := by decide
  have hdescent : baseEnd_170144 < baseStart_170144 := by decide
  rcases family_descends (prefixWord ++ tailWord_170144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_170168 : List Nat := [2, 1, 2, 1, 2, 1, 3, 5, 3]
def baseStart_170168 : Nat := 118140960795 + 170168 * 2 ^ 59
def prefixEnd_170168 : Nat := 4983230072969 + 3 ^ 40 * 170168 * 2
def baseEnd_170168 : Nat := 77669312012795956104371

theorem tailTrace_170168 : CollatzResearch.WordTrace tailWord_170168 prefixEnd_170168 77669312012795956104371 := by
  unfold tailWord_170168
  simp only [CollatzResearch.WordTrace]
  refine ⟨3103268423758936612867579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4137691231678582150490105 3103268423758936612867579)
  ·
    refine ⟨4654902635638404919301369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3103268423758936612867579 4654902635638404919301369)
    ·
      refine ⟨3491176976728803689476027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4654902635638404919301369 3491176976728803689476027)
      ·
        refine ⟨5236765465093205534214041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3491176976728803689476027 5236765465093205534214041)
        ·
          refine ⟨3927574098819904150660531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5236765465093205534214041 3927574098819904150660531)
          ·
            refine ⟨5891361148229856225990797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3927574098819904150660531 5891361148229856225990797)
            ·
              refine ⟨2209260430586196084746549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5891361148229856225990797 2209260430586196084746549)
              ·
                refine ⟨207118165367455882944989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2209260430586196084746549 207118165367455882944989)
                ·
                  refine ⟨77669312012795956104371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 207118165367455882944989 77669312012795956104371)
                  ·
                    rfl

theorem cell20_170168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 3, 5, 3].length) (baseStart_170168 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_170168 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_170168 prefixEnd_170168 := by exact prefixLift 170168
  have htrace : WordTrace (prefixWord ++ tailWord_170168) baseStart_170168 baseEnd_170168 := by
    simpa [prefixWord, tailWord_170168, baseEnd_170168] using wordTrace_append hprefix tailTrace_170168
  have hstable : (prefixWord ++ tailWord_170168).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_170168).length < 2 ^ (prefixWord ++ tailWord_170168).sum := by decide
  have hdescent : baseEnd_170168 < baseStart_170168 := by decide
  rcases family_descends (prefixWord ++ tailWord_170168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_170220 : List Nat := [2, 2, 1, 1, 2, 3, 2, 7]
def baseStart_170220 : Nat := 118140960795 + 170220 * 2 ^ 59
def prefixEnd_170220 : Nat := 4983230072969 + 3 ^ 40 * 170220 * 2
def baseEnd_170220 : Nat := 25897682076571628790275

theorem tailTrace_170220 : CollatzResearch.WordTrace tailWord_170220 prefixEnd_170220 25897682076571628790275 := by
  unfold tailWord_170220
  simp only [CollatzResearch.WordTrace]
  refine ⟨3104216721664743053314057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4138955628886324071085409 3104216721664743053314057)
  ·
    refine ⟨2328162541248557289985543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3104216721664743053314057 2328162541248557289985543)
    ·
      refine ⟨3492243811872835934978315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2328162541248557289985543 3492243811872835934978315)
      ·
        refine ⟨5238365717809253902467473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3492243811872835934978315 5238365717809253902467473)
        ·
          refine ⟨3928774288356940426850605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5238365717809253902467473 3928774288356940426850605)
          ·
            refine ⟨1473290358133852660068977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3928774288356940426850605 1473290358133852660068977)
            ·
              refine ⟨1104967768600389495051733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1473290358133852660068977 1104967768600389495051733)
              ·
                refine ⟨25897682076571628790275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1104967768600389495051733 25897682076571628790275)
                ·
                  rfl

theorem cell20_170220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 2, 7].length) (baseStart_170220 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_170220 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_170220 prefixEnd_170220 := by exact prefixLift 170220
  have htrace : WordTrace (prefixWord ++ tailWord_170220) baseStart_170220 baseEnd_170220 := by
    simpa [prefixWord, tailWord_170220, baseEnd_170220] using wordTrace_append hprefix tailTrace_170220
  have hstable : (prefixWord ++ tailWord_170220).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_170220).length < 2 ^ (prefixWord ++ tailWord_170220).sum := by decide
  have hdescent : baseEnd_170220 < baseStart_170220 := by decide
  rcases family_descends (prefixWord ++ tailWord_170220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_170230 : List Nat := [5, 1, 1, 1, 1, 1, 4, 2, 4]
def baseStart_170230 : Nat := 118140960795 + 170230 * 2 ^ 59
def prefixEnd_170230 : Nat := 4983230072969 + 3 ^ 40 * 170230 * 2
def baseEnd_170230 : Nat := 77697610502199296037451

theorem tailTrace_170230 : CollatzResearch.WordTrace tailWord_170230 prefixEnd_170230 77697610502199296037451 := by
  unfold tailWord_170230
  simp only [CollatzResearch.WordTrace]
  refine ⟨388049885830828613405759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 4139198782195505209661429 388049885830828613405759)
  ·
    refine ⟨582074828746242920108639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 388049885830828613405759 582074828746242920108639)
    ·
      refine ⟨873112243119364380162959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 582074828746242920108639 873112243119364380162959)
      ·
        refine ⟨1309668364679046570244439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 873112243119364380162959 1309668364679046570244439)
        ·
          refine ⟨1964502547018569855366659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1309668364679046570244439 1964502547018569855366659)
          ·
            refine ⟨2946753820527854783049989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1964502547018569855366659 2946753820527854783049989)
            ·
              refine ⟨552516341348972771821873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2946753820527854783049989 552516341348972771821873)
              ·
                refine ⟨414387256011729578866405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 552516341348972771821873 414387256011729578866405)
                ·
                  refine ⟨77697610502199296037451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 414387256011729578866405 77697610502199296037451)
                  ·
                    rfl

theorem cell20_170230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 4, 2, 4].length) (baseStart_170230 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_170230 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_170230 prefixEnd_170230 := by exact prefixLift 170230
  have htrace : WordTrace (prefixWord ++ tailWord_170230) baseStart_170230 baseEnd_170230 := by
    simpa [prefixWord, tailWord_170230, baseEnd_170230] using wordTrace_append hprefix tailTrace_170230
  have hstable : (prefixWord ++ tailWord_170230).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_170230).length < 2 ^ (prefixWord ++ tailWord_170230).sum := by decide
  have hdescent : baseEnd_170230 < baseStart_170230 := by decide
  rcases family_descends (prefixWord ++ tailWord_170230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_170296 : List Nat := [2, 1, 2, 1, 3, 1, 4, 6]
def baseStart_170296 : Nat := 118140960795 + 170296 * 2 ^ 59
def prefixEnd_170296 : Nat := 4983230072969 + 3 ^ 40 * 170296 * 2
def baseEnd_170296 : Nat := 25909244900198799945727

theorem tailTrace_170296 : CollatzResearch.WordTrace tailWord_170296 prefixEnd_170296 25909244900198799945727 := by
  unfold tailWord_170296
  simp only [CollatzResearch.WordTrace]
  refine ⟨3105602695527075543197371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4140803594036100724263161 3105602695527075543197371)
  ·
    refine ⟨4658404043290613314796057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3105602695527075543197371 4658404043290613314796057)
    ·
      refine ⟨3493803032467959986097043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4658404043290613314796057 3493803032467959986097043)
      ·
        refine ⟨5240704548701939979145565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3493803032467959986097043 5240704548701939979145565)
        ·
          refine ⟨1965264205763227492179587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5240704548701939979145565 1965264205763227492179587)
          ·
            refine ⟨2947896308644841238269381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1965264205763227492179587 2947896308644841238269381)
            ·
              refine ⟨552730557870907732175509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2947896308644841238269381 552730557870907732175509)
              ·
                refine ⟨25909244900198799945727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 552730557870907732175509 25909244900198799945727)
                ·
                  rfl

theorem cell20_170296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 4, 6].length) (baseStart_170296 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_170296 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_170296 prefixEnd_170296 := by exact prefixLift 170296
  have htrace : WordTrace (prefixWord ++ tailWord_170296) baseStart_170296 baseEnd_170296 := by
    simpa [prefixWord, tailWord_170296, baseEnd_170296] using wordTrace_append hprefix tailTrace_170296
  have hstable : (prefixWord ++ tailWord_170296).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_170296).length < 2 ^ (prefixWord ++ tailWord_170296).sum := by decide
  have hdescent : baseEnd_170296 < baseStart_170296 := by decide
  rcases family_descends (prefixWord ++ tailWord_170296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_170320 : List Nat := [2, 1, 1, 1, 1, 6, 1, 4, 3]
def baseStart_170320 : Nat := 118140960795 + 170320 * 2 ^ 59
def prefixEnd_170320 : Nat := 4983230072969 + 3 ^ 40 * 170320 * 2
def baseEnd_170320 : Nat := 77738688954558983037083

theorem tailTrace_170320 : CollatzResearch.WordTrace tailWord_170320 prefixEnd_170320 77738688954558983037083 := by
  unfold tailWord_170320
  simp only [CollatzResearch.WordTrace]
  refine ⟨3106040371483601592634207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4141387161978135456845609 3106040371483601592634207)
  ·
    refine ⟨4659060557225402388951311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3106040371483601592634207 4659060557225402388951311)
    ·
      refine ⟨6988590835838103583426967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4659060557225402388951311 6988590835838103583426967)
      ·
        refine ⟨10482886253757155375140451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6988590835838103583426967 10482886253757155375140451)
        ·
          refine ⟨15724329380635733062710677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10482886253757155375140451 15724329380635733062710677)
          ·
            refine ⟨737077939717299987314563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 15724329380635733062710677 737077939717299987314563)
            ·
              refine ⟨1105616909575949980971845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 737077939717299987314563 1105616909575949980971845)
              ·
                refine ⟨207303170545490621432221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1105616909575949980971845 207303170545490621432221)
                ·
                  refine ⟨77738688954558983037083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 207303170545490621432221 77738688954558983037083)
                  ·
                    rfl

theorem cell20_170320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 1, 4, 3].length) (baseStart_170320 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_170320 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_170320 prefixEnd_170320 := by exact prefixLift 170320
  have htrace : WordTrace (prefixWord ++ tailWord_170320) baseStart_170320 baseEnd_170320 := by
    simpa [prefixWord, tailWord_170320, baseEnd_170320] using wordTrace_append hprefix tailTrace_170320
  have hstable : (prefixWord ++ tailWord_170320).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_170320).length < 2 ^ (prefixWord ++ tailWord_170320).sum := by decide
  have hdescent : baseEnd_170320 < baseStart_170320 := by decide
  rcases family_descends (prefixWord ++ tailWord_170320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_170327 : List Nat := [1, 1, 3, 2, 3, 1, 2, 3, 4]
def baseStart_170327 : Nat := 118140960795 + 170327 * 2 ^ 59
def prefixEnd_170327 : Nat := 4983230072969 + 3 ^ 40 * 170327 * 2
def baseEnd_170327 : Nat := 77741883945298069803721

theorem tailTrace_170327 : CollatzResearch.WordTrace tailWord_170327 prefixEnd_170327 77741883945298069803721 := by
  unfold tailWord_170327
  simp only [CollatzResearch.WordTrace]
  refine ⟨6212336053941843380773235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4141557369294562253848823 6212336053941843380773235)
  ·
    refine ⟨9318504080912765071159853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6212336053941843380773235 9318504080912765071159853)
    ·
      refine ⟨3494439030342286901684945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9318504080912765071159853 3494439030342286901684945)
      ·
        refine ⟨2620829272756715176263709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3494439030342286901684945 2620829272756715176263709)
        ·
          refine ⟨982810977283768191098891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2620829272756715176263709 982810977283768191098891)
          ·
            refine ⟨1474216465925652286648337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 982810977283768191098891 1474216465925652286648337)
            ·
              refine ⟨1105662349444239214986253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1474216465925652286648337 1105662349444239214986253)
              ·
                refine ⟨414623381041589705619845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1105662349444239214986253 414623381041589705619845)
                ·
                  refine ⟨77741883945298069803721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 414623381041589705619845 77741883945298069803721)
                  ·
                    rfl

theorem cell20_170327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 2, 3, 4].length) (baseStart_170327 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_170327 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_170327 prefixEnd_170327 := by exact prefixLift 170327
  have htrace : WordTrace (prefixWord ++ tailWord_170327) baseStart_170327 baseEnd_170327 := by
    simpa [prefixWord, tailWord_170327, baseEnd_170327] using wordTrace_append hprefix tailTrace_170327
  have hstable : (prefixWord ++ tailWord_170327).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_170327).length < 2 ^ (prefixWord ++ tailWord_170327).sum := by decide
  have hdescent : baseEnd_170327 < baseStart_170327 := by decide
  rcases family_descends (prefixWord ++ tailWord_170327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_170344 : List Nat := [2, 1, 4, 2, 2, 2, 1, 2, 4]
def baseStart_170344 : Nat := 118140960795 + 170344 * 2 ^ 59
def prefixEnd_170344 : Nat := 4983230072969 + 3 ^ 40 * 170344 * 2
def baseEnd_170344 : Nat := 77749643208521566236985

theorem tailTrace_170344 : CollatzResearch.WordTrace tailWord_170344 prefixEnd_170344 77749643208521566236985 := by
  unfold tailWord_170344
  simp only [CollatzResearch.WordTrace]
  refine ⟨3106478047440127642071043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4141970729920170189428057 3106478047440127642071043)
  ·
    refine ⟨4659717071160191463106565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3106478047440127642071043 4659717071160191463106565)
    ·
      refine ⟨873696950842535899332481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4659717071160191463106565 873696950842535899332481)
      ·
        refine ⟨655272713131901924499361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 873696950842535899332481 655272713131901924499361)
        ·
          refine ⟨491454534848926443374521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 655272713131901924499361 491454534848926443374521)
          ·
            refine ⟨368590901136694832530891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 491454534848926443374521 368590901136694832530891)
            ·
              refine ⟨552886351705042248796337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 368590901136694832530891 552886351705042248796337)
              ·
                refine ⟨414664763778781686597253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 552886351705042248796337 414664763778781686597253)
                ·
                  refine ⟨77749643208521566236985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 414664763778781686597253 77749643208521566236985)
                  ·
                    rfl

theorem cell20_170344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 2, 1, 2, 4].length) (baseStart_170344 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_170344 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_170344 prefixEnd_170344 := by exact prefixLift 170344
  have htrace : WordTrace (prefixWord ++ tailWord_170344) baseStart_170344 baseEnd_170344 := by
    simpa [prefixWord, tailWord_170344, baseEnd_170344] using wordTrace_append hprefix tailTrace_170344
  have hstable : (prefixWord ++ tailWord_170344).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_170344).length < 2 ^ (prefixWord ++ tailWord_170344).sum := by decide
  have hdescent : baseEnd_170344 < baseStart_170344 := by decide
  rcases family_descends (prefixWord ++ tailWord_170344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_170372 : List Nat := [2, 3, 2, 1, 1, 2, 9]
def baseStart_170372 : Nat := 118140960795 + 170372 * 2 ^ 59
def prefixEnd_170372 : Nat := 4983230072969 + 3 ^ 40 * 170372 * 2
def baseEnd_170372 : Nat := 8640269241275323700393

theorem tailTrace_170372 : CollatzResearch.WordTrace tailWord_170372 prefixEnd_170372 8640269241275323700393 := by
  unfold tailWord_170372
  simp only [CollatzResearch.WordTrace]
  refine ⟨3106988669389408033080685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4142651559185877377440913 3106988669389408033080685)
  ·
    refine ⟨1165120751021028012405257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3106988669389408033080685 1165120751021028012405257)
    ·
      refine ⟨873840563265771009303943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1165120751021028012405257 873840563265771009303943)
      ·
        refine ⟨1310760844898656513955915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 873840563265771009303943 1310760844898656513955915)
        ·
          refine ⟨1966141267347984770933873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1310760844898656513955915 1966141267347984770933873)
          ·
            refine ⟨1474605950510988578200405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1966141267347984770933873 1474605950510988578200405)
            ·
              refine ⟨8640269241275323700393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 1474605950510988578200405 8640269241275323700393)
              ·
                rfl

theorem cell20_170372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 9].length) (baseStart_170372 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_170372 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_170372 prefixEnd_170372 := by exact prefixLift 170372
  have htrace : WordTrace (prefixWord ++ tailWord_170372) baseStart_170372 baseEnd_170372 := by
    simpa [prefixWord, tailWord_170372, baseEnd_170372] using wordTrace_append hprefix tailTrace_170372
  have hstable : (prefixWord ++ tailWord_170372).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_170372).length < 2 ^ (prefixWord ++ tailWord_170372).sum := by decide
  have hdescent : baseEnd_170372 < baseStart_170372 := by decide
  rcases family_descends (prefixWord ++ tailWord_170372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_170382 : List Nat := [4, 1, 1, 4, 1, 1, 1, 3, 4]
def baseStart_170382 : Nat := 118140960795 + 170382 * 2 ^ 59
def prefixEnd_170382 : Nat := 4983230072969 + 3 ^ 40 * 170382 * 2
def baseEnd_170382 : Nat := 77766987443962322970163

theorem tailTrace_170382 : CollatzResearch.WordTrace tailWord_170382 prefixEnd_170382 77766987443962322970163 := by
  unfold tailWord_170382
  simp only [CollatzResearch.WordTrace]
  refine ⟨776792758592823471753175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4142894712495058516016933 776792758592823471753175)
  ·
    refine ⟨1165189137889235207629763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 776792758592823471753175 1165189137889235207629763)
    ·
      refine ⟨1747783706833852811444645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1165189137889235207629763 1747783706833852811444645)
      ·
        refine ⟨327709445031347402145871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1747783706833852811444645 327709445031347402145871)
        ·
          refine ⟨491564167547021103218807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 327709445031347402145871 491564167547021103218807)
          ·
            refine ⟨737346251320531654828211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 491564167547021103218807 737346251320531654828211)
            ·
              refine ⟨1106019376980797482242317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 737346251320531654828211 1106019376980797482242317)
              ·
                refine ⟨414757266367799055840869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1106019376980797482242317 414757266367799055840869)
                ·
                  refine ⟨77766987443962322970163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 414757266367799055840869 77766987443962322970163)
                  ·
                    rfl

theorem cell20_170382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 1, 3, 4].length) (baseStart_170382 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_170382 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_170382 prefixEnd_170382 := by exact prefixLift 170382
  have htrace : WordTrace (prefixWord ++ tailWord_170382) baseStart_170382 baseEnd_170382 := by
    simpa [prefixWord, tailWord_170382, baseEnd_170382] using wordTrace_append hprefix tailTrace_170382
  have hstable : (prefixWord ++ tailWord_170382).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_170382).length < 2 ^ (prefixWord ++ tailWord_170382).sum := by decide
  have hdescent : baseEnd_170382 < baseStart_170382 := by decide
  rcases family_descends (prefixWord ++ tailWord_170382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_170392 : List Nat := [2, 1, 2, 5, 1, 2, 3, 1, 3]
def baseStart_170392 : Nat := 118140960795 + 170392 * 2 ^ 59
def prefixEnd_170392 : Nat := 4983230072969 + 3 ^ 40 * 170392 * 2
def baseEnd_170392 : Nat := 77771551716446732636789

theorem tailTrace_170392 : CollatzResearch.WordTrace tailWord_170392 prefixEnd_170392 77771551716446732636789 := by
  unfold tailWord_170392
  simp only [CollatzResearch.WordTrace]
  refine ⟨3107353399353179740944715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4143137865804239654592953 3107353399353179740944715)
  ·
    refine ⟨4661030099029769611417073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3107353399353179740944715 4661030099029769611417073)
    ·
      refine ⟨3495772574272327208562805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4661030099029769611417073 3495772574272327208562805)
      ·
        refine ⟨327728678838030675802763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 3495772574272327208562805 327728678838030675802763)
        ·
          refine ⟨491593018257046013704145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 327728678838030675802763 491593018257046013704145)
          ·
            refine ⟨368694763692784510278109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 491593018257046013704145 368694763692784510278109)
            ·
              refine ⟨138260536384794191354291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 368694763692784510278109 138260536384794191354291)
              ·
                refine ⟨207390804577191287031437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 138260536384794191354291 207390804577191287031437)
                ·
                  refine ⟨77771551716446732636789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 207390804577191287031437 77771551716446732636789)
                  ·
                    rfl

theorem cell20_170392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 2, 3, 1, 3].length) (baseStart_170392 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_170392 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_170392 prefixEnd_170392 := by exact prefixLift 170392
  have htrace : WordTrace (prefixWord ++ tailWord_170392) baseStart_170392 baseEnd_170392 := by
    simpa [prefixWord, tailWord_170392, baseEnd_170392] using wordTrace_append hprefix tailTrace_170392
  have hstable : (prefixWord ++ tailWord_170392).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_170392).length < 2 ^ (prefixWord ++ tailWord_170392).sum := by decide
  have hdescent : baseEnd_170392 < baseStart_170392 := by decide
  rcases family_descends (prefixWord ++ tailWord_170392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_170403 : List Nat := [1, 1, 1, 4, 1, 4, 2, 2, 4]
def baseStart_170403 : Nat := 118140960795 + 170403 * 2 ^ 59
def prefixEnd_170403 : Nat := 4983230072969 + 3 ^ 40 * 170403 * 2
def baseEnd_170403 : Nat := 77776572416179583270077

theorem tailTrace_170403 : CollatzResearch.WordTrace tailWord_170403 prefixEnd_170403 77776572416179583270077 := by
  unfold tailWord_170403
  simp only [CollatzResearch.WordTrace]
  refine ⟨6215108001666508360539863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4143405334444338907026575 6215108001666508360539863)
  ·
    refine ⟨9322662002499762540809795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6215108001666508360539863 9322662002499762540809795)
    ·
      refine ⟨13983993003749643811214693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9322662002499762540809795 13983993003749643811214693)
      ·
        refine ⟨2621998688203058214602755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13983993003749643811214693 2621998688203058214602755)
        ·
          refine ⟨3932998032304587321904133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2621998688203058214602755 3932998032304587321904133)
          ·
            refine ⟨737437131057110122857025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3932998032304587321904133 737437131057110122857025)
            ·
              refine ⟨553077848292832592142769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 737437131057110122857025 553077848292832592142769)
              ·
                refine ⟨414808386219624444107077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 553077848292832592142769 414808386219624444107077)
                ·
                  refine ⟨77776572416179583270077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 414808386219624444107077 77776572416179583270077)
                  ·
                    rfl

theorem cell20_170403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 2, 2, 4].length) (baseStart_170403 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_170403 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_170403 prefixEnd_170403 := by exact prefixLift 170403
  have htrace : WordTrace (prefixWord ++ tailWord_170403) baseStart_170403 baseEnd_170403 := by
    simpa [prefixWord, tailWord_170403, baseEnd_170403] using wordTrace_append hprefix tailTrace_170403
  have hstable : (prefixWord ++ tailWord_170403).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_170403).length < 2 ^ (prefixWord ++ tailWord_170403).sum := by decide
  have hdescent : baseEnd_170403 < baseStart_170403 := by decide
  rcases family_descends (prefixWord ++ tailWord_170403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_170433 : List Nat := [1, 2, 7, 1, 1, 2, 1, 1, 4]
def baseStart_170433 : Nat := 118140960795 + 170433 * 2 ^ 59
def prefixEnd_170433 : Nat := 4983230072969 + 3 ^ 40 * 170433 * 2
def baseEnd_170433 : Nat := 77790265233632812269955

theorem tailTrace_170433 : CollatzResearch.WordTrace tailWord_170433 prefixEnd_170433 77790265233632812269955 := by
  unfold tailWord_170433
  simp only [CollatzResearch.WordTrace]
  refine ⟨6216202191557823484131953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4144134794371882322754635 6216202191557823484131953)
  ·
    refine ⟨4662151643668367613098965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6216202191557823484131953 4662151643668367613098965)
    ·
      refine ⟨109269179148477365932007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 4662151643668367613098965 109269179148477365932007)
      ·
        refine ⟨163903768722716048898011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109269179148477365932007 163903768722716048898011)
        ·
          refine ⟨245855653084074073347017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 163903768722716048898011 245855653084074073347017)
          ·
            refine ⟨184391739813055555010263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 245855653084074073347017 184391739813055555010263)
            ·
              refine ⟨276587609719583332515395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 184391739813055555010263 276587609719583332515395)
              ·
                refine ⟨414881414579374998773093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 276587609719583332515395 414881414579374998773093)
                ·
                  refine ⟨77790265233632812269955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 414881414579374998773093 77790265233632812269955)
                  ·
                    rfl

theorem cell20_170433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 2, 1, 1, 4].length) (baseStart_170433 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_170433 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_170433 prefixEnd_170433 := by exact prefixLift 170433
  have htrace : WordTrace (prefixWord ++ tailWord_170433) baseStart_170433 baseEnd_170433 := by
    simpa [prefixWord, tailWord_170433, baseEnd_170433] using wordTrace_append hprefix tailTrace_170433
  have hstable : (prefixWord ++ tailWord_170433).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_170433).length < 2 ^ (prefixWord ++ tailWord_170433).sum := by decide
  have hdescent : baseEnd_170433 < baseStart_170433 := by decide
  rcases family_descends (prefixWord ++ tailWord_170433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_170441 : List Nat := [1, 2, 1, 1, 2, 1, 7, 1, 4]
def baseStart_170441 : Nat := 118140960795 + 170441 * 2 ^ 59
def prefixEnd_170441 : Nat := 4983230072969 + 3 ^ 40 * 170441 * 2
def baseEnd_170441 : Nat := 77793916651620340003255

theorem tailTrace_170441 : CollatzResearch.WordTrace tailWord_170441 prefixEnd_170441 77793916651620340003255 := by
  unfold tailWord_170441
  simp only [CollatzResearch.WordTrace]
  refine ⟨6216493975528840850423177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4144329317019227233615451 6216493975528840850423177)
  ·
    refine ⟨4662370481646630637817383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6216493975528840850423177 4662370481646630637817383)
    ·
      refine ⟨6993555722469945956726075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4662370481646630637817383 6993555722469945956726075)
      ·
        refine ⟨10490333583704918935089113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6993555722469945956726075 10490333583704918935089113)
        ·
          refine ⟨7867750187778689201316835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10490333583704918935089113 7867750187778689201316835)
          ·
            refine ⟨11801625281668033801975253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7867750187778689201316835 11801625281668033801975253)
            ·
              refine ⟨276600592539094542233795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 11801625281668033801975253 276600592539094542233795)
              ·
                refine ⟨414900888808641813350693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 276600592539094542233795 414900888808641813350693)
                ·
                  refine ⟨77793916651620340003255, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 414900888808641813350693 77793916651620340003255)
                  ·
                    rfl

theorem cell20_170441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 7, 1, 4].length) (baseStart_170441 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_170441 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_170441 prefixEnd_170441 := by exact prefixLift 170441
  have htrace : WordTrace (prefixWord ++ tailWord_170441) baseStart_170441 baseEnd_170441 := by
    simpa [prefixWord, tailWord_170441, baseEnd_170441] using wordTrace_append hprefix tailTrace_170441
  have hstable : (prefixWord ++ tailWord_170441).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_170441).length < 2 ^ (prefixWord ++ tailWord_170441).sum := by decide
  have hdescent : baseEnd_170441 < baseStart_170441 := by decide
  rcases family_descends (prefixWord ++ tailWord_170441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_170517 : List Nat := [1, 3, 2, 1, 3, 1, 3, 2, 4]
def baseStart_170517 : Nat := 118140960795 + 170517 * 2 ^ 59
def prefixEnd_170517 : Nat := 4983230072969 + 3 ^ 40 * 170517 * 2
def baseEnd_170517 : Nat := 77828605122501853469611

theorem tailTrace_170517 : CollatzResearch.WordTrace tailWord_170517 prefixEnd_170517 77828605122501853469611 := by
  unfold tailWord_170517
  simp only [CollatzResearch.WordTrace]
  refine ⟨6219265923253505830189805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4146177282169003886793203 6219265923253505830189805)
  ·
    refine ⟨2332224721220064686321177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6219265923253505830189805 2332224721220064686321177)
    ·
      refine ⟨1749168540915048514740883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2332224721220064686321177 1749168540915048514740883)
      ·
        refine ⟨2623752811372572772111325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1749168540915048514740883 2623752811372572772111325)
        ·
          refine ⟨983907304264714789541747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2623752811372572772111325 983907304264714789541747)
          ·
            refine ⟨1475860956397072184312621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 983907304264714789541747 1475860956397072184312621)
            ·
              refine ⟨553447858648902069117233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1475860956397072184312621 553447858648902069117233)
              ·
                refine ⟨415085893986676551837925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 553447858648902069117233 415085893986676551837925)
                ·
                  refine ⟨77828605122501853469611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 415085893986676551837925 77828605122501853469611)
                  ·
                    rfl

theorem cell20_170517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 3, 2, 4].length) (baseStart_170517 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_170517 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_170517 prefixEnd_170517 := by exact prefixLift 170517
  have htrace : WordTrace (prefixWord ++ tailWord_170517) baseStart_170517 baseEnd_170517 := by
    simpa [prefixWord, tailWord_170517, baseEnd_170517] using wordTrace_append hprefix tailTrace_170517
  have hstable : (prefixWord ++ tailWord_170517).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_170517).length < 2 ^ (prefixWord ++ tailWord_170517).sum := by decide
  have hdescent : baseEnd_170517 < baseStart_170517 := by decide
  rcases family_descends (prefixWord ++ tailWord_170517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_170565 : List Nat := [1, 3, 1, 1, 1, 6, 3, 1, 3]
def baseStart_170565 : Nat := 118140960795 + 170565 * 2 ^ 59
def prefixEnd_170565 : Nat := 4983230072969 + 3 ^ 40 * 170565 * 2
def baseEnd_170565 : Nat := 77850513630427019869415

theorem tailTrace_170565 : CollatzResearch.WordTrace tailWord_170565 prefixEnd_170565 77850513630427019869415 := by
  unfold tailWord_170565
  simp only [CollatzResearch.WordTrace]
  refine ⟨6221016627079610027937149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4147344418053073351958099 6221016627079610027937149)
  ·
    refine ⟨2332881235154853760476431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6221016627079610027937149 2332881235154853760476431)
    ·
      refine ⟨3499321852732280640714647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2332881235154853760476431 3499321852732280640714647)
      ·
        refine ⟨5248982779098420961071971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3499321852732280640714647 5248982779098420961071971)
        ·
          refine ⟨7873474168647631441607957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5248982779098420961071971 7873474168647631441607957)
          ·
            refine ⟨369069101655357723825373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 7873474168647631441607957 369069101655357723825373)
            ·
              refine ⟨138400913120759146434515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 369069101655357723825373 138400913120759146434515)
              ·
                refine ⟨207601369681138719651773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 138400913120759146434515 207601369681138719651773)
                ·
                  refine ⟨77850513630427019869415, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 207601369681138719651773 77850513630427019869415)
                  ·
                    rfl

theorem cell20_170565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 6, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 6, 3, 1, 3].length) (baseStart_170565 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_170565 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_170565 prefixEnd_170565 := by exact prefixLift 170565
  have htrace : WordTrace (prefixWord ++ tailWord_170565) baseStart_170565 baseEnd_170565 := by
    simpa [prefixWord, tailWord_170565, baseEnd_170565] using wordTrace_append hprefix tailTrace_170565
  have hstable : (prefixWord ++ tailWord_170565).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_170565).length < 2 ^ (prefixWord ++ tailWord_170565).sum := by decide
  have hdescent : baseEnd_170565 < baseStart_170565 := by decide
  rcases family_descends (prefixWord ++ tailWord_170565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_170576 : List Nat := [2, 1, 1, 1, 1, 3, 2, 3, 6]
def baseStart_170576 : Nat := 118140960795 + 170576 * 2 ^ 59
def prefixEnd_170576 : Nat := 4983230072969 + 3 ^ 40 * 170576 * 2
def baseEnd_170576 : Nat := 77855534330159870502703

theorem tailTrace_170576 : CollatzResearch.WordTrace tailWord_170576 prefixEnd_170576 77855534330159870502703 := by
  unfold tailWord_170576
  simp only [CollatzResearch.WordTrace]
  refine ⟨3110708915019879453293791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4147611886693172604391721 3110708915019879453293791)
  ·
    refine ⟨4666063372529819179940687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3110708915019879453293791 4666063372529819179940687)
    ·
      refine ⟨6999095058794728769911031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4666063372529819179940687 6999095058794728769911031)
      ·
        refine ⟨10498642588192093154866547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6999095058794728769911031 10498642588192093154866547)
        ·
          refine ⟨15747963882288139732299821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10498642588192093154866547 15747963882288139732299821)
          ·
            refine ⟨5905486455858052399612433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15747963882288139732299821 5905486455858052399612433)
            ·
              refine ⟨4429114841893539299709325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5905486455858052399612433 4429114841893539299709325)
              ·
                refine ⟨1660918065710077237390997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4429114841893539299709325 1660918065710077237390997)
                ·
                  refine ⟨77855534330159870502703, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1660918065710077237390997 77855534330159870502703)
                  ·
                    rfl

theorem cell20_170576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 3, 6].length) (baseStart_170576 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_170576 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_170576 prefixEnd_170576 := by exact prefixLift 170576
  have htrace : WordTrace (prefixWord ++ tailWord_170576) baseStart_170576 baseEnd_170576 := by
    simpa [prefixWord, tailWord_170576, baseEnd_170576] using wordTrace_append hprefix tailTrace_170576
  have hstable : (prefixWord ++ tailWord_170576).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_170576).length < 2 ^ (prefixWord ++ tailWord_170576).sum := by decide
  have hdescent : baseEnd_170576 < baseStart_170576 := by decide
  rcases family_descends (prefixWord ++ tailWord_170576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_170606 : List Nat := [4, 1, 2, 2, 2, 2, 3, 2, 2]
def baseStart_170606 : Nat := 118140960795 + 170606 * 2 ^ 59
def prefixEnd_170606 : Nat := 4983230072969 + 3 ^ 40 * 170606 * 2
def baseEnd_170606 : Nat := 77869227147613099502581

theorem tailTrace_170606 : CollatzResearch.WordTrace tailWord_170606 prefixEnd_170606 77869227147613099502581 := by
  unfold tailWord_170606
  simp only [CollatzResearch.WordTrace]
  refine ⟨777814002491384253772459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4148341346620716020119781 777814002491384253772459)
  ·
    refine ⟨1166721003737076380658689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 777814002491384253772459 1166721003737076380658689)
    ·
      refine ⟨875040752802807285494017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1166721003737076380658689 875040752802807285494017)
      ·
        refine ⟨656280564602105464120513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 875040752802807285494017 656280564602105464120513)
        ·
          refine ⟨492210423451579098090385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 656280564602105464120513 492210423451579098090385)
          ·
            refine ⟨369157817588684323567789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 492210423451579098090385 369157817588684323567789)
            ·
              refine ⟨138434181595756621337921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 369157817588684323567789 138434181595756621337921)
              ·
                refine ⟨103825636196817466003441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 138434181595756621337921 103825636196817466003441)
                ·
                  refine ⟨77869227147613099502581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 103825636196817466003441 77869227147613099502581)
                  ·
                    rfl

theorem cell20_170606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 2, 3, 2, 2].length) (baseStart_170606 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_170606 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_170606 prefixEnd_170606 := by exact prefixLift 170606
  have htrace : WordTrace (prefixWord ++ tailWord_170606) baseStart_170606 baseEnd_170606 := by
    simpa [prefixWord, tailWord_170606, baseEnd_170606] using wordTrace_append hprefix tailTrace_170606
  have hstable : (prefixWord ++ tailWord_170606).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_170606).length < 2 ^ (prefixWord ++ tailWord_170606).sum := by decide
  have hdescent : baseEnd_170606 < baseStart_170606 := by decide
  rcases family_descends (prefixWord ++ tailWord_170606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_170607 : List Nat := [1, 1, 2, 1, 3, 2, 4, 1, 5]
def baseStart_170607 : Nat := 118140960795 + 170607 * 2 ^ 59
def prefixEnd_170607 : Nat := 4983230072969 + 3 ^ 40 * 170607 * 2
def baseEnd_170607 : Nat := 77869683574861540469243

theorem tailTrace_170607 : CollatzResearch.WordTrace tailWord_170607 prefixEnd_170607 77869683574861540469243 := by
  unfold tailWord_170607
  simp only [CollatzResearch.WordTrace]
  refine ⟨6222548492927451200966075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4148365661951634133977383 6222548492927451200966075)
  ·
    refine ⟨9333822739391176801449113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6222548492927451200966075 9333822739391176801449113)
    ·
      refine ⟨7000367054543382601086835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9333822739391176801449113 7000367054543382601086835)
      ·
        refine ⟨10500550581815073901630253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7000367054543382601086835 10500550581815073901630253)
        ·
          refine ⟨3937706468180652713111345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10500550581815073901630253 3937706468180652713111345)
          ·
            refine ⟨2953279851135489534833509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3937706468180652713111345 2953279851135489534833509)
            ·
              refine ⟨553739972087904287781283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2953279851135489534833509 553739972087904287781283)
              ·
                refine ⟨830609958131856431671925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 553739972087904287781283 830609958131856431671925)
                ·
                  refine ⟨77869683574861540469243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 830609958131856431671925 77869683574861540469243)
                  ·
                    rfl

theorem cell20_170607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 4, 1, 5].length) (baseStart_170607 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_170607 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_170607 prefixEnd_170607 := by exact prefixLift 170607
  have htrace : WordTrace (prefixWord ++ tailWord_170607) baseStart_170607 baseEnd_170607 := by
    simpa [prefixWord, tailWord_170607, baseEnd_170607] using wordTrace_append hprefix tailTrace_170607
  have hstable : (prefixWord ++ tailWord_170607).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_170607).length < 2 ^ (prefixWord ++ tailWord_170607).sum := by decide
  have hdescent : baseEnd_170607 < baseStart_170607 := by decide
  rcases family_descends (prefixWord ++ tailWord_170607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_170624 : List Nat := [2, 1, 1, 2, 1, 6, 1, 3, 3]
def baseStart_170624 : Nat := 118140960795 + 170624 * 2 ^ 59
def prefixEnd_170624 : Nat := 4983230072969 + 3 ^ 40 * 170624 * 2
def baseEnd_170624 : Nat := 77877442838085036902507

theorem tailTrace_170624 : CollatzResearch.WordTrace tailWord_170624 prefixEnd_170624 77877442838085036902507 := by
  unfold tailWord_170624
  simp only [CollatzResearch.WordTrace]
  refine ⟨3111584266932931552167463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4148779022577242069556617 3111584266932931552167463)
  ·
    refine ⟨4667376400399397328251195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3111584266932931552167463 4667376400399397328251195)
    ·
      refine ⟨7001064600599095992376793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4667376400399397328251195 7001064600599095992376793)
      ·
        refine ⟨5250798450449321994282595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7001064600599095992376793 5250798450449321994282595)
        ·
          refine ⟨7876197675673982991423893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5250798450449321994282595 7876197675673982991423893)
          ·
            refine ⟨369196766047217952722995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 7876197675673982991423893 369196766047217952722995)
            ·
              refine ⟨553795149070826929084493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 369196766047217952722995 553795149070826929084493)
              ·
                refine ⟨207673180901560098406685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 553795149070826929084493 207673180901560098406685)
                ·
                  refine ⟨77877442838085036902507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 207673180901560098406685 77877442838085036902507)
                  ·
                    rfl

theorem cell20_170624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 6, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 6, 1, 3, 3].length) (baseStart_170624 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_170624 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_170624 prefixEnd_170624 := by exact prefixLift 170624
  have htrace : WordTrace (prefixWord ++ tailWord_170624) baseStart_170624 baseEnd_170624 := by
    simpa [prefixWord, tailWord_170624, baseEnd_170624] using wordTrace_append hprefix tailTrace_170624
  have hstable : (prefixWord ++ tailWord_170624).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_170624).length < 2 ^ (prefixWord ++ tailWord_170624).sum := by decide
  have hdescent : baseEnd_170624 < baseStart_170624 := by decide
  rcases family_descends (prefixWord ++ tailWord_170624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_170638 : List Nat := [4, 1, 1, 3, 1, 1, 1, 8]
def baseStart_170638 : Nat := 118140960795 + 170638 * 2 ^ 59
def prefixEnd_170638 : Nat := 4983230072969 + 3 ^ 40 * 170638 * 2
def baseEnd_170638 : Nat := 25961277606521070145261

theorem tailTrace_170638 : CollatzResearch.WordTrace tailWord_170638 prefixEnd_170638 25961277606521070145261 := by
  unfold tailWord_170638
  simp only [CollatzResearch.WordTrace]
  refine ⟨777959894476892936918071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4149119437210095663563045 777959894476892936918071)
  ·
    refine ⟨1166939841715339405377107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 777959894476892936918071 1166939841715339405377107)
    ·
      refine ⟨1750409762573009108065661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1166939841715339405377107 1750409762573009108065661)
      ·
        refine ⟨656403660964878415524623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1750409762573009108065661 656403660964878415524623)
        ·
          refine ⟨984605491447317623286935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 656403660964878415524623 984605491447317623286935)
          ·
            refine ⟨1476908237170976434930403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 984605491447317623286935 1476908237170976434930403)
            ·
              refine ⟨2215362355756464652395605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1476908237170976434930403 2215362355756464652395605)
              ·
                refine ⟨25961277606521070145261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2215362355756464652395605 25961277606521070145261)
                ·
                  rfl

theorem cell20_170638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 1, 8].length) (baseStart_170638 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_170638 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_170638 prefixEnd_170638 := by exact prefixLift 170638
  have htrace : WordTrace (prefixWord ++ tailWord_170638) baseStart_170638 baseEnd_170638 := by
    simpa [prefixWord, tailWord_170638, baseEnd_170638] using wordTrace_append hprefix tailTrace_170638
  have hstable : (prefixWord ++ tailWord_170638).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_170638).length < 2 ^ (prefixWord ++ tailWord_170638).sum := by decide
  have hdescent : baseEnd_170638 < baseStart_170638 := by decide
  rcases family_descends (prefixWord ++ tailWord_170638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_170648 : List Nat := [2, 1, 2, 4, 1, 1, 2, 5, 2]
def baseStart_170648 : Nat := 118140960795 + 170648 * 2 ^ 59
def prefixEnd_170648 : Nat := 4983230072969 + 3 ^ 40 * 170648 * 2
def baseEnd_170648 : Nat := 77888397092047620102409

theorem tailTrace_170648 : CollatzResearch.WordTrace tailWord_170648 prefixEnd_170648 77888397092047620102409 := by
  unfold tailWord_170648
  simp only [CollatzResearch.WordTrace]
  refine ⟨3112021942889457601604299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4149362590519276802139065 3112021942889457601604299)
  ·
    refine ⟨4668032914334186402406449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3112021942889457601604299 4668032914334186402406449)
    ·
      refine ⟨3501024685750639801804837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4668032914334186402406449 3501024685750639801804837)
      ·
        refine ⟨656442128578244962838407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3501024685750639801804837 656442128578244962838407)
        ·
          refine ⟨984663192867367444257611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 656442128578244962838407 984663192867367444257611)
          ·
            refine ⟨1476994789301051166386417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 984663192867367444257611 1476994789301051166386417)
            ·
              refine ⟨1107746091975788374789813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1476994789301051166386417 1107746091975788374789813)
              ·
                refine ⟨103851196122730160136545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1107746091975788374789813 103851196122730160136545)
                ·
                  refine ⟨77888397092047620102409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 103851196122730160136545 77888397092047620102409)
                  ·
                    rfl

theorem cell20_170648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 2, 5, 2].length) (baseStart_170648 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_170648 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_170648 prefixEnd_170648 := by exact prefixLift 170648
  have htrace : WordTrace (prefixWord ++ tailWord_170648) baseStart_170648 baseEnd_170648 := by
    simpa [prefixWord, tailWord_170648, baseEnd_170648] using wordTrace_append hprefix tailTrace_170648
  have hstable : (prefixWord ++ tailWord_170648).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_170648).length < 2 ^ (prefixWord ++ tailWord_170648).sum := by decide
  have hdescent : baseEnd_170648 < baseStart_170648 := by decide
  rcases family_descends (prefixWord ++ tailWord_170648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_170689 : List Nat := [1, 2, 6, 2, 1, 1, 3, 4]
def baseStart_170689 : Nat := 118140960795 + 170689 * 2 ^ 59
def prefixEnd_170689 : Nat := 4983230072969 + 3 ^ 40 * 170689 * 2
def baseEnd_170689 : Nat := 25969036869744566578525

theorem tailTrace_170689 : CollatzResearch.WordTrace tailWord_170689 prefixEnd_170689 25969036869744566578525 := by
  unfold tailWord_170689
  simp only [CollatzResearch.WordTrace]
  refine ⟨6225539278630379205451121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4150359519086919470300747 6225539278630379205451121)
  ·
    refine ⟨4669154458972784404088341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6225539278630379205451121 4669154458972784404088341)
    ·
      refine ⟨218866615264349268941641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 4669154458972784404088341 218866615264349268941641)
      ·
        refine ⟨164149961448261951706231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 218866615264349268941641 164149961448261951706231)
        ·
          refine ⟨246224942172392927559347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 164149961448261951706231 246224942172392927559347)
          ·
            refine ⟨369337413258589391339021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 246224942172392927559347 369337413258589391339021)
            ·
              refine ⟨138501529971971021752133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 369337413258589391339021 138501529971971021752133)
              ·
                refine ⟨25969036869744566578525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 138501529971971021752133 25969036869744566578525)
                ·
                  rfl

theorem cell20_170689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 1, 3, 4].length) (baseStart_170689 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_170689 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_170689 prefixEnd_170689 := by exact prefixLift 170689
  have htrace : WordTrace (prefixWord ++ tailWord_170689) baseStart_170689 baseEnd_170689 := by
    simpa [prefixWord, tailWord_170689, baseEnd_170689] using wordTrace_append hprefix tailTrace_170689
  have hstable : (prefixWord ++ tailWord_170689).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_170689).length < 2 ^ (prefixWord ++ tailWord_170689).sum := by decide
  have hdescent : baseEnd_170689 < baseStart_170689 := by decide
  rcases family_descends (prefixWord ++ tailWord_170689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_170724 : List Nat := [2, 3, 1, 1, 1, 4, 2, 4, 2]
def baseStart_170724 : Nat := 118140960795 + 170724 * 2 ^ 59
def prefixEnd_170724 : Nat := 4983230072969 + 3 ^ 40 * 170724 * 2
def baseEnd_170724 : Nat := 77923085562929133568765

theorem tailTrace_170724 : CollatzResearch.WordTrace tailWord_170724 prefixEnd_170724 77923085562929133568765 := by
  unfold tailWord_170724
  simp only [CollatzResearch.WordTrace]
  refine ⟨3113407916751790091487613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4151210555669053455316817 3113407916751790091487613)
  ·
    refine ⟨1167527968781921284307855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3113407916751790091487613 1167527968781921284307855)
    ·
      refine ⟨1751291953172881926461783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1167527968781921284307855 1751291953172881926461783)
      ·
        refine ⟨2626937929759322889692675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1751291953172881926461783 2626937929759322889692675)
        ·
          refine ⟨3940406894638984334539013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2626937929759322889692675 3940406894638984334539013)
          ·
            refine ⟨738826292744809562726065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3940406894638984334539013 738826292744809562726065)
            ·
              refine ⟨554119719558607172044549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 738826292744809562726065 554119719558607172044549)
              ·
                refine ⟨103897447417238844758353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 554119719558607172044549 103897447417238844758353)
                ·
                  refine ⟨77923085562929133568765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 103897447417238844758353 77923085562929133568765)
                  ·
                    rfl

theorem cell20_170724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 2, 4, 2].length) (baseStart_170724 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_170724 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_170724 prefixEnd_170724 := by exact prefixLift 170724
  have htrace : WordTrace (prefixWord ++ tailWord_170724) baseStart_170724 baseEnd_170724 := by
    simpa [prefixWord, tailWord_170724, baseEnd_170724] using wordTrace_append hprefix tailTrace_170724
  have hstable : (prefixWord ++ tailWord_170724).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_170724).length < 2 ^ (prefixWord ++ tailWord_170724).sum := by decide
  have hdescent : baseEnd_170724 < baseStart_170724 := by decide
  rcases family_descends (prefixWord ++ tailWord_170724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_170783 : List Nat := [1, 1, 2, 4, 2, 2, 3, 1, 4]
def baseStart_170783 : Nat := 118140960795 + 170783 * 2 ^ 59
def prefixEnd_170783 : Nat := 4983230072969 + 3 ^ 40 * 170783 * 2
def baseEnd_170783 : Nat := 77950014770587150601857

theorem tailTrace_170783 : CollatzResearch.WordTrace tailWord_170783 prefixEnd_170783 77950014770587150601857 := by
  unfold tailWord_170783
  simp only [CollatzResearch.WordTrace]
  refine ⟨6228967740289833259373003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4152645160193222172915335 6228967740289833259373003)
  ·
    refine ⟨9343451610434749889059505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6228967740289833259373003 9343451610434749889059505)
    ·
      refine ⟨7007588707826062416794629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9343451610434749889059505 7007588707826062416794629)
      ·
        refine ⟨1313922882717386703148993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7007588707826062416794629 1313922882717386703148993)
        ·
          refine ⟨985442162038040027361745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1313922882717386703148993 985442162038040027361745)
          ·
            refine ⟨739081621528530020521309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 985442162038040027361745 739081621528530020521309)
            ·
              refine ⟨277155608073198757695491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 739081621528530020521309 277155608073198757695491)
              ·
                refine ⟨415733412109798136543237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 277155608073198757695491 415733412109798136543237)
                ·
                  refine ⟨77950014770587150601857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 415733412109798136543237 77950014770587150601857)
                  ·
                    rfl

theorem cell20_170783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 3, 1, 4].length) (baseStart_170783 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_170783 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_170783 prefixEnd_170783 := by exact prefixLift 170783
  have htrace : WordTrace (prefixWord ++ tailWord_170783) baseStart_170783 baseEnd_170783 := by
    simpa [prefixWord, tailWord_170783, baseEnd_170783] using wordTrace_append hprefix tailTrace_170783
  have hstable : (prefixWord ++ tailWord_170783).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_170783).length < 2 ^ (prefixWord ++ tailWord_170783).sum := by decide
  have hdescent : baseEnd_170783 < baseStart_170783 := by decide
  rcases family_descends (prefixWord ++ tailWord_170783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_170849 : List Nat := [1, 2, 3, 1, 1, 1, 2, 9]
def baseStart_170849 : Nat := 118140960795 + 170849 * 2 ^ 59
def prefixEnd_170849 : Nat := 4983230072969 + 3 ^ 40 * 170849 * 2
def baseEnd_170849 : Nat := 25993379656328084800529

theorem tailTrace_170849 : CollatzResearch.WordTrace tailWord_170849 prefixEnd_170849 25993379656328084800529 := by
  unfold tailWord_170849
  simp only [CollatzResearch.WordTrace]
  refine ⟨6231374958050726531275601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 4154249972033817687517067 6231374958050726531275601)
  ·
    refine ⟨4673531218538044898456701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6231374958050726531275601 4673531218538044898456701)
    ·
      refine ⟨1752574206951766836921263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4673531218538044898456701 1752574206951766836921263)
      ·
        refine ⟨2628861310427650255381895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1752574206951766836921263 2628861310427650255381895)
        ·
          refine ⟨3943291965641475383072843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2628861310427650255381895 3943291965641475383072843)
          ·
            refine ⟨5914937948462213074609265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3943291965641475383072843 5914937948462213074609265)
            ·
              refine ⟨4436203461346659805956949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5914937948462213074609265 4436203461346659805956949)
              ·
                refine ⟨25993379656328084800529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 4436203461346659805956949 25993379656328084800529)
                ·
                  rfl

theorem cell20_170849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 9].length) (baseStart_170849 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_170849 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_170849 prefixEnd_170849 := by exact prefixLift 170849
  have htrace : WordTrace (prefixWord ++ tailWord_170849) baseStart_170849 baseEnd_170849 := by
    simpa [prefixWord, tailWord_170849, baseEnd_170849] using wordTrace_append hprefix tailTrace_170849
  have hstable : (prefixWord ++ tailWord_170849).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_170849).length < 2 ^ (prefixWord ++ tailWord_170849).sum := by decide
  have hdescent : baseEnd_170849 < baseStart_170849 := by decide
  rcases family_descends (prefixWord ++ tailWord_170849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_170852 : List Nat := [2, 3, 1, 1, 4, 1, 2, 3, 3]
def baseStart_170852 : Nat := 118140960795 + 170852 * 2 ^ 59
def prefixEnd_170852 : Nat := 4983230072969 + 3 ^ 40 * 170852 * 2
def baseEnd_170852 : Nat := 77981508250729577301575

theorem tailTrace_170852 : CollatzResearch.WordTrace tailWord_170852 prefixEnd_170852 77981508250729577301575 := by
  unfold tailWord_170852
  simp only [CollatzResearch.WordTrace]
  refine ⟨3115742188519929021817405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 4154322918026572029089873 3115742188519929021817405)
  ·
    refine ⟨1168403320694973383181527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3115742188519929021817405 1168403320694973383181527)
    ·
      refine ⟨1752604981042460074772291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1168403320694973383181527 1752604981042460074772291)
      ·
        refine ⟨2628907471563690112158437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1752604981042460074772291 2628907471563690112158437)
        ·
          refine ⟨492920150918191896029707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2628907471563690112158437 492920150918191896029707)
          ·
            refine ⟨739380226377287844044561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 492920150918191896029707 739380226377287844044561)
            ·
              refine ⟨554535169782965883033421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 739380226377287844044561 554535169782965883033421)
              ·
                refine ⟨207950688668612206137533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 554535169782965883033421 207950688668612206137533)
                ·
                  refine ⟨77981508250729577301575, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 207950688668612206137533 77981508250729577301575)
                  ·
                    rfl

theorem cell20_170852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 2, 3, 3].length) (baseStart_170852 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_170852 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_170852 prefixEnd_170852 := by exact prefixLift 170852
  have htrace : WordTrace (prefixWord ++ tailWord_170852) baseStart_170852 baseEnd_170852 := by
    simpa [prefixWord, tailWord_170852, baseEnd_170852] using wordTrace_append hprefix tailTrace_170852
  have hstable : (prefixWord ++ tailWord_170852).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_170852).length < 2 ^ (prefixWord ++ tailWord_170852).sum := by decide
  have hdescent : baseEnd_170852 < baseStart_170852 := by decide
  rcases family_descends (prefixWord ++ tailWord_170852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_170862 : List Nat := [4, 1, 2, 3, 2, 1, 3, 4]
def baseStart_170862 : Nat := 118140960795 + 170862 * 2 ^ 59
def prefixEnd_170862 : Nat := 4983230072969 + 3 ^ 40 * 170862 * 2
def baseEnd_170862 : Nat := 25995357507737995656067

theorem tailTrace_170862 : CollatzResearch.WordTrace tailWord_170862 prefixEnd_170862 25995357507737995656067 := by
  unfold tailWord_170862
  simp only [CollatzResearch.WordTrace]
  refine ⟨778981138375453718937355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 4154566071335753167665893 778981138375453718937355)
  ·
    refine ⟨1168471707563180578406033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 778981138375453718937355 1168471707563180578406033)
    ·
      refine ⟨876353780672385433804525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1168471707563180578406033 876353780672385433804525)
      ·
        refine ⟨328632667752144537676697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 876353780672385433804525 328632667752144537676697)
        ·
          refine ⟨246474500814108403257523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 328632667752144537676697 246474500814108403257523)
          ·
            refine ⟨369711751221162604886285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 246474500814108403257523 369711751221162604886285)
            ·
              refine ⟨138641906707935976832357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 369711751221162604886285 138641906707935976832357)
              ·
                refine ⟨25995357507737995656067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 138641906707935976832357 25995357507737995656067)
                ·
                  rfl

theorem cell20_170862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 1, 3, 4].length) (baseStart_170862 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_170862 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_170862 prefixEnd_170862 := by exact prefixLift 170862
  have htrace : WordTrace (prefixWord ++ tailWord_170862) baseStart_170862 baseEnd_170862 := by
    simpa [prefixWord, tailWord_170862, baseEnd_170862] using wordTrace_append hprefix tailTrace_170862
  have hstable : (prefixWord ++ tailWord_170862).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_170862).length < 2 ^ (prefixWord ++ tailWord_170862).sum := by decide
  have hdescent : baseEnd_170862 < baseStart_170862 := by decide
  rcases family_descends (prefixWord ++ tailWord_170862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan20Incremental
