import V185TrunkScan22Chunk016

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_151857 : List Nat := [1, 2, 2, 3, 4, 2, 1, 2, 5]
def baseStart_151857 : Nat := 118140960795 + 151857 * 2 ^ 59
def prefixEnd_151857 : Nat := 4983230072969 + 3 ^ 40 * 151857 * 2
def baseEnd_151857 : Nat := 17327918166648353886473

theorem tailTrace_151857 : CollatzResearch.WordTrace tailWord_151857 prefixEnd_151857 17327918166648353886473 := by
  unfold tailWord_151857
  simp only [CollatzResearch.WordTrace]
  refine ⟨5538679810855498955909825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3692453207236999303939883 5538679810855498955909825)
  ·
    refine ⟨4154009858141624216932369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5538679810855498955909825 4154009858141624216932369)
    ·
      refine ⟨3115507393606218162699277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4154009858141624216932369 3115507393606218162699277)
      ·
        refine ⟨1168315272602331811012229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3115507393606218162699277 1168315272602331811012229)
        ·
          refine ⟨219059113612937214564793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1168315272602331811012229 219059113612937214564793)
          ·
            refine ⟨164294335209702910923595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 219059113612937214564793 164294335209702910923595)
            ·
              refine ⟨246441502814554366385393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 164294335209702910923595 246441502814554366385393)
              ·
                refine ⟨184831127110915774789045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 246441502814554366385393 184831127110915774789045)
                ·
                  refine ⟨17327918166648353886473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 184831127110915774789045 17327918166648353886473)
                  ·
                    rfl

theorem cell22_151857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 2, 1, 2, 5].length) (baseStart_151857 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_151857 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_151857 prefixEnd_151857 := by exact prefixLift 151857
  have htrace : WordTrace (prefixWord ++ tailWord_151857) baseStart_151857 baseEnd_151857 := by
    simpa [prefixWord, tailWord_151857, baseEnd_151857] using wordTrace_append hprefix tailTrace_151857
  have hstable : (prefixWord ++ tailWord_151857).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_151857).length < 2 ^ (prefixWord ++ tailWord_151857).sum := by decide
  have hdescent : baseEnd_151857 < baseStart_151857 := by decide
  rcases family_descends (prefixWord ++ tailWord_151857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_151883 : List Nat := [1, 1, 1, 1, 3, 1, 1, 7, 1, 5]
def baseStart_151883 : Nat := 118140960795 + 151883 * 2 ^ 59
def prefixEnd_151883 : Nat := 4983230072969 + 3 ^ 40 * 151883 * 2
def baseEnd_151883 : Nat := 51992654831289660509339

theorem tailTrace_151883 : CollatzResearch.WordTrace tailWord_151883 prefixEnd_151883 51992654831289660509339 := by
  unfold tailWord_151883
  simp only [CollatzResearch.WordTrace]
  refine ⟨5539628108761305396356303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3693085405840870264237535 5539628108761305396356303)
  ·
    refine ⟨8309442163141958094534455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5539628108761305396356303 8309442163141958094534455)
    ·
      refine ⟨12464163244712937141801683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8309442163141958094534455 12464163244712937141801683)
      ·
        refine ⟨18696244867069405712702525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12464163244712937141801683 18696244867069405712702525)
        ·
          refine ⟨7011091825151027142263447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18696244867069405712702525 7011091825151027142263447)
          ·
            refine ⟨10516637737726540713395171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7011091825151027142263447 10516637737726540713395171)
            ·
              refine ⟨15774956606589811070092757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10516637737726540713395171 15774956606589811070092757)
              ·
                refine ⟨369725545466948696955299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 15774956606589811070092757 369725545466948696955299)
                ·
                  refine ⟨554588318200423045432949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 369725545466948696955299 554588318200423045432949)
                  ·
                    refine ⟨51992654831289660509339, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 554588318200423045432949 51992654831289660509339)
                    ·
                      rfl

theorem cell22_151883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 7, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 7, 1, 5].length) (baseStart_151883 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_151883 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_151883 prefixEnd_151883 := by exact prefixLift 151883
  have htrace : WordTrace (prefixWord ++ tailWord_151883) baseStart_151883 baseEnd_151883 := by
    simpa [prefixWord, tailWord_151883, baseEnd_151883] using wordTrace_append hprefix tailTrace_151883
  have hstable : (prefixWord ++ tailWord_151883).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_151883).length < 2 ^ (prefixWord ++ tailWord_151883).sum := by decide
  have hdescent : baseEnd_151883 < baseStart_151883 := by decide
  rcases family_descends (prefixWord ++ tailWord_151883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_151917 : List Nat := [1, 5, 1, 1, 1, 2, 2, 4, 2, 3]
def baseStart_151917 : Nat := 118140960795 + 151917 * 2 ^ 59
def prefixEnd_151917 : Nat := 4983230072969 + 3 ^ 40 * 151917 * 2
def baseEnd_151917 : Nat := 52004293726124905159235

theorem tailTrace_151917 : CollatzResearch.WordTrace tailWord_151917 prefixEnd_151917 52004293726124905159235 := by
  unfold tailWord_151917
  simp only [CollatzResearch.WordTrace]
  refine ⟨5540868190638129203094005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3693912127092086135396003 5540868190638129203094005)
  ·
    refine ⟨519456392872324612790063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 5540868190638129203094005 519456392872324612790063)
    ·
      refine ⟨779184589308486919185095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 519456392872324612790063 779184589308486919185095)
      ·
        refine ⟨1168776883962730378777643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 779184589308486919185095 1168776883962730378777643)
        ·
          refine ⟨1753165325944095568166465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1168776883962730378777643 1753165325944095568166465)
          ·
            refine ⟨1314873994458071676124849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1753165325944095568166465 1314873994458071676124849)
            ·
              refine ⟨986155495843553757093637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1314873994458071676124849 986155495843553757093637)
              ·
                refine ⟨184904155470666329455057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 986155495843553757093637 184904155470666329455057)
                ·
                  refine ⟨138678116602999747091293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 184904155470666329455057 138678116602999747091293)
                  ·
                    refine ⟨52004293726124905159235, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 138678116602999747091293 52004293726124905159235)
                    ·
                      rfl

theorem cell22_151917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 2, 4, 2, 3].length) (baseStart_151917 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_151917 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_151917 prefixEnd_151917 := by exact prefixLift 151917
  have htrace : WordTrace (prefixWord ++ tailWord_151917) baseStart_151917 baseEnd_151917 := by
    simpa [prefixWord, tailWord_151917, baseEnd_151917] using wordTrace_append hprefix tailTrace_151917
  have hstable : (prefixWord ++ tailWord_151917).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_151917).length < 2 ^ (prefixWord ++ tailWord_151917).sum := by decide
  have hdescent : baseEnd_151917 < baseStart_151917 := by decide
  rcases family_descends (prefixWord ++ tailWord_151917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_151938 : List Nat := [3, 4, 2, 1, 3, 1, 1, 2, 1, 4]
def baseStart_151938 : Nat := 118140960795 + 151938 * 2 ^ 59
def prefixEnd_151938 : Nat := 4983230072969 + 3 ^ 40 * 151938 * 2
def baseEnd_151938 : Nat := 52011482455287850384171

theorem tailTrace_151938 : CollatzResearch.WordTrace tailWord_151938 prefixEnd_151938 52011482455287850384171 := by
  unfold tailWord_151938
  simp only [CollatzResearch.WordTrace]
  refine ⟨1385408530890512447402117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3694422749041366526405645 1385408530890512447402117)
  ·
    refine ⟨259764099541971083887897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1385408530890512447402117 259764099541971083887897)
    ·
      refine ⟨194823074656478312915923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 259764099541971083887897 194823074656478312915923)
      ·
        refine ⟨292234611984717469373885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 194823074656478312915923 292234611984717469373885)
        ·
          refine ⟨109587979494269051015207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 292234611984717469373885 109587979494269051015207)
          ·
            refine ⟨164381969241403576522811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 109587979494269051015207 164381969241403576522811)
            ·
              refine ⟨246572953862105364784217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 164381969241403576522811 246572953862105364784217)
              ·
                refine ⟨184929715396579023588163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 246572953862105364784217 184929715396579023588163)
                ·
                  refine ⟨277394573094868535382245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 184929715396579023588163 277394573094868535382245)
                  ·
                    refine ⟨52011482455287850384171, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 277394573094868535382245 52011482455287850384171)
                    ·
                      rfl

theorem cell22_151938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 3, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 3, 1, 1, 2, 1, 4].length) (baseStart_151938 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_151938 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_151938 prefixEnd_151938 := by exact prefixLift 151938
  have htrace : WordTrace (prefixWord ++ tailWord_151938) baseStart_151938 baseEnd_151938 := by
    simpa [prefixWord, tailWord_151938, baseEnd_151938] using wordTrace_append hprefix tailTrace_151938
  have hstable : (prefixWord ++ tailWord_151938).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_151938).length < 2 ^ (prefixWord ++ tailWord_151938).sum := by decide
  have hdescent : baseEnd_151938 < baseStart_151938 := by decide
  rcases family_descends (prefixWord ++ tailWord_151938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_152071 : List Nat := [1, 1, 4, 3, 3, 2, 1, 3, 4]
def baseStart_152071 : Nat := 118140960795 + 152071 * 2 ^ 59
def prefixEnd_152071 : Nat := 4983230072969 + 3 ^ 40 * 152071 * 2
def baseEnd_152071 : Nat := 17352337024439945602921

theorem tailTrace_152071 : CollatzResearch.WordTrace tailWord_152071 prefixEnd_152071 17352337024439945602921 := by
  unfold tailWord_152071
  simp only [CollatzResearch.WordTrace]
  refine ⟨5546485032080213504200067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3697656688053475669466711 5546485032080213504200067)
  ·
    refine ⟨8319727548120320256300101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5546485032080213504200067 8319727548120320256300101)
    ·
      refine ⟨1559948915272560048056269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8319727548120320256300101 1559948915272560048056269)
      ·
        refine ⟨584980843227210018021101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1559948915272560048056269 584980843227210018021101)
        ·
          refine ⟨219367816210203756757913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 584980843227210018021101 219367816210203756757913)
          ·
            refine ⟨164525862157652817568435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 219367816210203756757913 164525862157652817568435)
            ·
              refine ⟨246788793236479226352653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 164525862157652817568435 246788793236479226352653)
              ·
                refine ⟨92545797463679709882245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 246788793236479226352653 92545797463679709882245)
                ·
                  refine ⟨17352337024439945602921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 92545797463679709882245 17352337024439945602921)
                  ·
                    rfl

theorem cell22_152071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 2, 1, 3, 4].length) (baseStart_152071 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_152071 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_152071 prefixEnd_152071 := by exact prefixLift 152071
  have htrace : WordTrace (prefixWord ++ tailWord_152071) baseStart_152071 baseEnd_152071 := by
    simpa [prefixWord, tailWord_152071, baseEnd_152071] using wordTrace_append hprefix tailTrace_152071
  have hstable : (prefixWord ++ tailWord_152071).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_152071).length < 2 ^ (prefixWord ++ tailWord_152071).sum := by decide
  have hdescent : baseEnd_152071 < baseStart_152071 := by decide
  rcases family_descends (prefixWord ++ tailWord_152071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_152084 : List Nat := [2, 4, 3, 1, 1, 1, 1, 1, 4, 4]
def baseStart_152084 : Nat := 118140960795 + 152084 * 2 ^ 59
def prefixEnd_152084 : Nat := 4983230072969 + 3 ^ 40 * 152084 * 2
def baseEnd_152084 : Nat := 52061461238992136233723

theorem tailTrace_152084 : CollatzResearch.WordTrace tailWord_152084 prefixEnd_152084 52061461238992136233723 := by
  unfold tailWord_152084
  simp only [CollatzResearch.WordTrace]
  refine ⟨2773479590516558362211653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3697972787355411149615537 2773479590516558362211653)
  ·
    refine ⟨520027423221854692914685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2773479590516558362211653 520027423221854692914685)
    ·
      refine ⟨195010283708195509843007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 520027423221854692914685 195010283708195509843007)
      ·
        refine ⟨292515425562293264764511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 195010283708195509843007 292515425562293264764511)
        ·
          refine ⟨438773138343439897146767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 292515425562293264764511 438773138343439897146767)
          ·
            refine ⟨658159707515159845720151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 438773138343439897146767 658159707515159845720151)
            ·
              refine ⟨987239561272739768580227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 658159707515159845720151 987239561272739768580227)
              ·
                refine ⟨1480859341909109652870341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 987239561272739768580227 1480859341909109652870341)
                ·
                  refine ⟨277661126607958059913189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1480859341909109652870341 277661126607958059913189)
                  ·
                    refine ⟨52061461238992136233723, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 277661126607958059913189 52061461238992136233723)
                    ·
                      rfl

theorem cell22_152084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 1, 1, 4, 4].length) (baseStart_152084 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_152084 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_152084 prefixEnd_152084 := by exact prefixLift 152084
  have htrace : WordTrace (prefixWord ++ tailWord_152084) baseStart_152084 baseEnd_152084 := by
    simpa [prefixWord, tailWord_152084, baseEnd_152084] using wordTrace_append hprefix tailTrace_152084
  have hstable : (prefixWord ++ tailWord_152084).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_152084).length < 2 ^ (prefixWord ++ tailWord_152084).sum := by decide
  have hdescent : baseEnd_152084 < baseStart_152084 := by decide
  rcases family_descends (prefixWord ++ tailWord_152084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_152095 : List Nat := [1, 1, 2, 4, 1, 1, 1, 3, 2, 6]
def baseStart_152095 : Nat := 118140960795 + 152095 * 2 ^ 59
def prefixEnd_152095 : Nat := 4983230072969 + 3 ^ 40 * 152095 * 2
def baseEnd_152095 : Nat := 52065226763791774208689

theorem tailTrace_152095 : CollatzResearch.WordTrace tailWord_152095 prefixEnd_152095 52065226763791774208689 := by
  unfold tailWord_152095
  simp only [CollatzResearch.WordTrace]
  refine ⟨5547360383993265603073739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3698240255995510402049159 5547360383993265603073739)
  ·
    refine ⟨8321040575989898404610609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5547360383993265603073739 8321040575989898404610609)
    ·
      refine ⟨6240780431992423803457957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8321040575989898404610609 6240780431992423803457957)
      ·
        refine ⟨1170146330998579463148367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6240780431992423803457957 1170146330998579463148367)
        ·
          refine ⟨1755219496497869194722551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1170146330998579463148367 1755219496497869194722551)
          ·
            refine ⟨2632829244746803792083827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1755219496497869194722551 2632829244746803792083827)
            ·
              refine ⟨3949243867120205688125741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2632829244746803792083827 3949243867120205688125741)
              ·
                refine ⟨1480966450170077133047153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3949243867120205688125741 1480966450170077133047153)
                ·
                  refine ⟨1110724837627557849785365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1480966450170077133047153 1110724837627557849785365)
                  ·
                    refine ⟨52065226763791774208689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1110724837627557849785365 52065226763791774208689)
                    ·
                      rfl

theorem cell22_152095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 3, 2, 6].length) (baseStart_152095 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_152095 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_152095 prefixEnd_152095 := by exact prefixLift 152095
  have htrace : WordTrace (prefixWord ++ tailWord_152095) baseStart_152095 baseEnd_152095 := by
    simpa [prefixWord, tailWord_152095, baseEnd_152095] using wordTrace_append hprefix tailTrace_152095
  have hstable : (prefixWord ++ tailWord_152095).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_152095).length < 2 ^ (prefixWord ++ tailWord_152095).sum := by decide
  have hdescent : baseEnd_152095 < baseStart_152095 := by decide
  rcases family_descends (prefixWord ++ tailWord_152095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_152103 : List Nat := [1, 1, 7, 2, 1, 1, 1, 3, 2, 3]
def baseStart_152103 : Nat := 118140960795 + 152103 * 2 ^ 59
def prefixEnd_152103 : Nat := 4983230072969 + 3 ^ 40 * 152103 * 2
def baseEnd_152103 : Nat := 52067965327282420008665

theorem tailTrace_152103 : CollatzResearch.WordTrace tailWord_152103 prefixEnd_152103 52067965327282420008665 := by
  unfold tailWord_152103
  simp only [CollatzResearch.WordTrace]
  refine ⟨5547652167964282969364963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3698434778642855312909975 5547652167964282969364963)
  ·
    refine ⟨8321478251946424454047445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5547652167964282969364963 8321478251946424454047445)
    ·
      refine ⟨195034646529994323141737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 8321478251946424454047445 195034646529994323141737)
      ·
        refine ⟨146275984897495742356303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 195034646529994323141737 146275984897495742356303)
        ·
          refine ⟨219413977346243613534455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 146275984897495742356303 219413977346243613534455)
          ·
            refine ⟨329120966019365420301683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 219413977346243613534455 329120966019365420301683)
            ·
              refine ⟨493681449029048130452525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 329120966019365420301683 493681449029048130452525)
              ·
                refine ⟨185130543385893048919697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 493681449029048130452525 185130543385893048919697)
                ·
                  refine ⟨138847907539419786689773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 185130543385893048919697 138847907539419786689773)
                  ·
                    refine ⟨52067965327282420008665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 138847907539419786689773 52067965327282420008665)
                    ·
                      rfl

theorem cell22_152103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 1, 1, 3, 2, 3].length) (baseStart_152103 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_152103 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_152103 prefixEnd_152103 := by exact prefixLift 152103
  have htrace : WordTrace (prefixWord ++ tailWord_152103) baseStart_152103 baseEnd_152103 := by
    simpa [prefixWord, tailWord_152103, baseEnd_152103] using wordTrace_append hprefix tailTrace_152103
  have hstable : (prefixWord ++ tailWord_152103).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_152103).length < 2 ^ (prefixWord ++ tailWord_152103).sum := by decide
  have hdescent : baseEnd_152103 < baseStart_152103 := by decide
  rcases family_descends (prefixWord ++ tailWord_152103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_152148 : List Nat := [2, 4, 1, 1, 1, 3, 4, 2, 1, 3]
def baseStart_152148 : Nat := 118140960795 + 152148 * 2 ^ 59
def prefixEnd_152148 : Nat := 4983230072969 + 3 ^ 40 * 152148 * 2
def baseEnd_152148 : Nat := 52083369746917302633527

theorem tailTrace_152148 : CollatzResearch.WordTrace tailWord_152148 prefixEnd_152148 52083369746917302633527 := by
  unfold tailWord_152148
  simp only [CollatzResearch.WordTrace]
  refine ⟨2774646726400627827376549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3699528968534170436502065 2774646726400627827376549)
  ·
    refine ⟨520246261200117717633103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2774646726400627827376549 520246261200117717633103)
    ·
      refine ⟨780369391800176576449655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 520246261200117717633103 780369391800176576449655)
      ·
        refine ⟨1170554087700264864674483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 780369391800176576449655 1170554087700264864674483)
        ·
          refine ⟨1755831131550397297011725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1170554087700264864674483 1755831131550397297011725)
          ·
            refine ⟨658436674331398986379397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1755831131550397297011725 658436674331398986379397)
            ·
              refine ⟨123456876437137309946137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 658436674331398986379397 123456876437137309946137)
              ·
                refine ⟨92592657327852982459603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 123456876437137309946137 92592657327852982459603)
                ·
                  refine ⟨138888985991779473689405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 92592657327852982459603 138888985991779473689405)
                  ·
                    refine ⟨52083369746917302633527, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 138888985991779473689405 52083369746917302633527)
                    ·
                      rfl

theorem cell22_152148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 4, 2, 1, 3].length) (baseStart_152148 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_152148 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_152148 prefixEnd_152148 := by exact prefixLift 152148
  have htrace : WordTrace (prefixWord ++ tailWord_152148) baseStart_152148 baseEnd_152148 := by
    simpa [prefixWord, tailWord_152148, baseEnd_152148] using wordTrace_append hprefix tailTrace_152148
  have hstable : (prefixWord ++ tailWord_152148).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_152148).length < 2 ^ (prefixWord ++ tailWord_152148).sum := by decide
  have hdescent : baseEnd_152148 < baseStart_152148 := by decide
  rcases family_descends (prefixWord ++ tailWord_152148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_152174 : List Nat := [4, 1, 2, 2, 2, 1, 2, 1, 3, 4]
def baseStart_152174 : Nat := 118140960795 + 152174 * 2 ^ 59
def prefixEnd_152174 : Nat := 4983230072969 + 3 ^ 40 * 152174 * 2
def baseEnd_152174 : Nat := 52092270078261901483447

theorem tailTrace_152174 : CollatzResearch.WordTrace tailWord_152174 prefixEnd_152174 52092270078261901483447 := by
  unfold tailWord_152174
  simp only [CollatzResearch.WordTrace]
  refine ⟨693780218838382761899947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3700161167138041396799717 693780218838382761899947)
  ·
    refine ⟨1040670328257574142849921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 693780218838382761899947 1040670328257574142849921)
    ·
      refine ⟨780502746193180607137441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1040670328257574142849921 780502746193180607137441)
      ·
        refine ⟨585377059644885455353081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 780502746193180607137441 585377059644885455353081)
        ·
          refine ⟨439032794733664091514811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 585377059644885455353081 439032794733664091514811)
          ·
            refine ⟨658549192100496137272217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 439032794733664091514811 658549192100496137272217)
            ·
              refine ⟨493911894075372102954163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 658549192100496137272217 493911894075372102954163)
              ·
                refine ⟨740867841113058154431245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 493911894075372102954163 740867841113058154431245)
                ·
                  refine ⟨277825440417396807911717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 740867841113058154431245 277825440417396807911717)
                  ·
                    refine ⟨52092270078261901483447, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 277825440417396807911717 52092270078261901483447)
                    ·
                      rfl

theorem cell22_152174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 2, 1, 3, 4].length) (baseStart_152174 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_152174 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_152174 prefixEnd_152174 := by exact prefixLift 152174
  have htrace : WordTrace (prefixWord ++ tailWord_152174) baseStart_152174 baseEnd_152174 := by
    simpa [prefixWord, tailWord_152174, baseEnd_152174] using wordTrace_append hprefix tailTrace_152174
  have hstable : (prefixWord ++ tailWord_152174).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_152174).length < 2 ^ (prefixWord ++ tailWord_152174).sum := by decide
  have hdescent : baseEnd_152174 < baseStart_152174 := by decide
  rcases family_descends (prefixWord ++ tailWord_152174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_152204 : List Nat := [2, 2, 1, 2, 1, 1, 2, 6, 2, 3]
def baseStart_152204 : Nat := 118140960795 + 152204 * 2 ^ 59
def prefixEnd_152204 : Nat := 4983230072969 + 3 ^ 40 * 152204 * 2
def baseEnd_152204 : Nat := 52102539691351823233355

theorem tailTrace_152204 : CollatzResearch.WordTrace tailWord_152204 prefixEnd_152204 52102539691351823233355 := by
  unfold tailWord_152204
  simp only [CollatzResearch.WordTrace]
  refine ⟨2775667970299188609395833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3700890627065584812527777 2775667970299188609395833)
  ·
    refine ⟨2081750977724391457046875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2775667970299188609395833 2081750977724391457046875)
    ·
      refine ⟨3122626466586587185570313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2081750977724391457046875 3122626466586587185570313)
      ·
        refine ⟨2341969849939940389177735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3122626466586587185570313 2341969849939940389177735)
        ·
          refine ⟨3512954774909910583766603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2341969849939940389177735 3512954774909910583766603)
          ·
            refine ⟨5269432162364865875649905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3512954774909910583766603 5269432162364865875649905)
            ·
              refine ⟨3952074121773649406737429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5269432162364865875649905 3952074121773649406737429)
              ·
                refine ⟨185253474458139815940817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3952074121773649406737429 185253474458139815940817)
                ·
                  refine ⟨138940105843604861955613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 185253474458139815940817 138940105843604861955613)
                  ·
                    refine ⟨52102539691351823233355, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 138940105843604861955613 52102539691351823233355)
                    ·
                      rfl

theorem cell22_152204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 6, 2, 3].length) (baseStart_152204 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_152204 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_152204 prefixEnd_152204 := by exact prefixLift 152204
  have htrace : WordTrace (prefixWord ++ tailWord_152204) baseStart_152204 baseEnd_152204 := by
    simpa [prefixWord, tailWord_152204, baseEnd_152204] using wordTrace_append hprefix tailTrace_152204
  have hstable : (prefixWord ++ tailWord_152204).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_152204).length < 2 ^ (prefixWord ++ tailWord_152204).sum := by decide
  have hdescent : baseEnd_152204 < baseStart_152204 := by decide
  rcases family_descends (prefixWord ++ tailWord_152204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_152266 : List Nat := [3, 1, 2, 1, 4, 1, 3, 1, 3, 3]
def baseStart_152266 : Nat := 118140960795 + 152266 * 2 ^ 59
def prefixEnd_152266 : Nat := 4983230072969 + 3 ^ 40 * 152266 * 2
def baseEnd_152266 : Nat := 52123763558404328183165

theorem tailTrace_152266 : CollatzResearch.WordTrace tailWord_152266 prefixEnd_152266 52123763558404328183165 := by
  unfold tailWord_152266
  simp only [CollatzResearch.WordTrace]
  refine ⟨1388399316593440451887163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3702398177582507871699101 1388399316593440451887163)
  ·
    refine ⟨2082598974890160677830745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1388399316593440451887163 2082598974890160677830745)
    ·
      refine ⟨1561949231167620508373059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2082598974890160677830745 1561949231167620508373059)
      ·
        refine ⟨2342923846751430762559589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1561949231167620508373059 2342923846751430762559589)
        ·
          refine ⟨439298221265893267979923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2342923846751430762559589 439298221265893267979923)
          ·
            refine ⟨658947331898839901969885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 439298221265893267979923 658947331898839901969885)
            ·
              refine ⟨247105249462064963238707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 658947331898839901969885 247105249462064963238707)
              ·
                refine ⟨370657874193097444858061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 247105249462064963238707 370657874193097444858061)
                ·
                  refine ⟨138996702822411541821773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 370657874193097444858061 138996702822411541821773)
                  ·
                    refine ⟨52123763558404328183165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 138996702822411541821773 52123763558404328183165)
                    ·
                      rfl

theorem cell22_152266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 3, 1, 3, 3].length) (baseStart_152266 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_152266 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_152266 prefixEnd_152266 := by exact prefixLift 152266
  have htrace : WordTrace (prefixWord ++ tailWord_152266) baseStart_152266 baseEnd_152266 := by
    simpa [prefixWord, tailWord_152266, baseEnd_152266] using wordTrace_append hprefix tailTrace_152266
  have hstable : (prefixWord ++ tailWord_152266).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_152266).length < 2 ^ (prefixWord ++ tailWord_152266).sum := by decide
  have hdescent : baseEnd_152266 < baseStart_152266 := by decide
  rcases family_descends (prefixWord ++ tailWord_152266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_152279 : List Nat := [1, 1, 3, 2, 1, 5, 1, 3, 5]
def baseStart_152279 : Nat := 118140960795 + 152279 * 2 ^ 59
def prefixEnd_152279 : Nat := 4983230072969 + 3 ^ 40 * 152279 * 2
def baseEnd_152279 : Nat := 17376071241358875869375

theorem tailTrace_152279 : CollatzResearch.WordTrace tailWord_152279 prefixEnd_152279 17376071241358875869375 := by
  unfold tailWord_152279
  simp only [CollatzResearch.WordTrace]
  refine ⟨5554071415326665027771891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3702714276884443351847927 5554071415326665027771891)
  ·
    refine ⟨8331107122989997541657837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5554071415326665027771891 8331107122989997541657837)
    ·
      refine ⟨3124165171121249078121689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8331107122989997541657837 3124165171121249078121689)
      ·
        refine ⟨2343123878340936808591267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3124165171121249078121689 2343123878340936808591267)
        ·
          refine ⟨3514685817511405212886901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2343123878340936808591267 3514685817511405212886901)
          ·
            refine ⟨329501795391694238708147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 3514685817511405212886901 329501795391694238708147)
            ·
              refine ⟨494252693087541358062221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 329501795391694238708147 494252693087541358062221)
              ·
                refine ⟨185344759907828009273333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 494252693087541358062221 185344759907828009273333)
                ·
                  refine ⟨17376071241358875869375, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 185344759907828009273333 17376071241358875869375)
                  ·
                    rfl

theorem cell22_152279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 5, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 5, 1, 3, 5].length) (baseStart_152279 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_152279 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_152279 prefixEnd_152279 := by exact prefixLift 152279
  have htrace : WordTrace (prefixWord ++ tailWord_152279) baseStart_152279 baseEnd_152279 := by
    simpa [prefixWord, tailWord_152279, baseEnd_152279] using wordTrace_append hprefix tailTrace_152279
  have hstable : (prefixWord ++ tailWord_152279).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_152279).length < 2 ^ (prefixWord ++ tailWord_152279).sum := by decide
  have hdescent : baseEnd_152279 < baseStart_152279 := by decide
  rcases family_descends (prefixWord ++ tailWord_152279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_152324 : List Nat := [2, 3, 2, 2, 1, 1, 2, 3, 6]
def baseStart_152324 : Nat := 118140960795 + 152324 * 2 ^ 59
def prefixEnd_152324 : Nat := 4983230072969 + 3 ^ 40 * 152324 * 2
def baseEnd_152324 : Nat := 17381206047903836744329

theorem tailTrace_152324 : CollatzResearch.WordTrace tailWord_152324 prefixEnd_152324 17381206047903836744329 := by
  unfold tailWord_152324
  simp only [CollatzResearch.WordTrace]
  refine ⟨2777856350081818856580013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3703808466775758475440017 2777856350081818856580013)
  ·
    refine ⟨1041696131280682071217505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2777856350081818856580013 1041696131280682071217505)
    ·
      refine ⟨781272098460511553413129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1041696131280682071217505 781272098460511553413129)
      ·
        refine ⟨585954073845383665059847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 781272098460511553413129 585954073845383665059847)
        ·
          refine ⟨878931110768075497589771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 585954073845383665059847 878931110768075497589771)
          ·
            refine ⟨1318396666152113246384657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 878931110768075497589771 1318396666152113246384657)
            ·
              refine ⟨988797499614084934788493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1318396666152113246384657 988797499614084934788493)
              ·
                refine ⟨370799062355281850545685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 988797499614084934788493 370799062355281850545685)
                ·
                  refine ⟨17381206047903836744329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 370799062355281850545685 17381206047903836744329)
                  ·
                    rfl

theorem cell22_152324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 2, 3, 6].length) (baseStart_152324 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_152324 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_152324 prefixEnd_152324 := by exact prefixLift 152324
  have htrace : WordTrace (prefixWord ++ tailWord_152324) baseStart_152324 baseEnd_152324 := by
    simpa [prefixWord, tailWord_152324, baseEnd_152324] using wordTrace_append hprefix tailTrace_152324
  have hstable : (prefixWord ++ tailWord_152324).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_152324).length < 2 ^ (prefixWord ++ tailWord_152324).sum := by decide
  have hdescent : baseEnd_152324 < baseStart_152324 := by decide
  rcases family_descends (prefixWord ++ tailWord_152324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_152339 : List Nat := [1, 1, 1, 2, 1, 3, 6, 1, 1, 5]
def baseStart_152339 : Nat := 118140960795 + 152339 * 2 ^ 59
def prefixEnd_152339 : Nat := 4983230072969 + 3 ^ 40 * 152339 * 2
def baseEnd_152339 : Nat := 52148752950256471107941

theorem tailTrace_152339 : CollatzResearch.WordTrace tailWord_152339 prefixEnd_152339 52148752950256471107941 := by
  unfold tailWord_152339
  simp only [CollatzResearch.WordTrace]
  refine ⟨5556259795109295274956071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3704173196739530183304047 5556259795109295274956071)
  ·
    refine ⟨8334389692663942912434107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5556259795109295274956071 8334389692663942912434107)
    ·
      refine ⟨12501584538995914368651161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8334389692663942912434107 12501584538995914368651161)
      ·
        refine ⟨9376188404246935776488371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12501584538995914368651161 9376188404246935776488371)
        ·
          refine ⟨14064282606370403664732557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9376188404246935776488371 14064282606370403664732557)
          ·
            refine ⟨5274105977388901374274709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14064282606370403664732557 5274105977388901374274709)
            ·
              refine ⟨247223717690104751919127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 5274105977388901374274709 247223717690104751919127)
              ·
                refine ⟨370835576535157127878691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 247223717690104751919127 370835576535157127878691)
                ·
                  refine ⟨556253364802735691818037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 370835576535157127878691 556253364802735691818037)
                  ·
                    refine ⟨52148752950256471107941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 556253364802735691818037 52148752950256471107941)
                    ·
                      rfl

theorem cell22_152339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 6, 1, 1, 5].length) (baseStart_152339 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_152339 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_152339 prefixEnd_152339 := by exact prefixLift 152339
  have htrace : WordTrace (prefixWord ++ tailWord_152339) baseStart_152339 baseEnd_152339 := by
    simpa [prefixWord, tailWord_152339, baseEnd_152339] using wordTrace_append hprefix tailTrace_152339
  have hstable : (prefixWord ++ tailWord_152339).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_152339).length < 2 ^ (prefixWord ++ tailWord_152339).sum := by decide
  have hdescent : baseEnd_152339 < baseStart_152339 := by decide
  rcases family_descends (prefixWord ++ tailWord_152339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_152373 : List Nat := [1, 3, 3, 1, 3, 1, 3, 2, 2, 3]
def baseStart_152373 : Nat := 118140960795 + 152373 * 2 ^ 59
def prefixEnd_152373 : Nat := 4983230072969 + 3 ^ 40 * 152373 * 2
def baseEnd_152373 : Nat := 52160391845091715757837

theorem tailTrace_152373 : CollatzResearch.WordTrace tailWord_152373 prefixEnd_152373 52160391845091715757837 := by
  unfold tailWord_152373
  simp only [CollatzResearch.WordTrace]
  refine ⟨5557499876986119081693773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3704999917990746054462515 5557499876986119081693773)
  ·
    refine ⟨2084062453869794655635165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5557499876986119081693773 2084062453869794655635165)
    ·
      refine ⟨781523420201172995863187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2084062453869794655635165 781523420201172995863187)
      ·
        refine ⟨1172285130301759493794781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 781523420201172995863187 1172285130301759493794781)
        ·
          refine ⟨439606923863159810173043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1172285130301759493794781 439606923863159810173043)
          ·
            refine ⟨659410385794739715259565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 439606923863159810173043 659410385794739715259565)
            ·
              refine ⟨247278894673027393222337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 659410385794739715259565 247278894673027393222337)
              ·
                refine ⟨185459171004770544916753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 247278894673027393222337 185459171004770544916753)
                ·
                  refine ⟨139094378253577908687565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 185459171004770544916753 139094378253577908687565)
                  ·
                    refine ⟨52160391845091715757837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 139094378253577908687565 52160391845091715757837)
                    ·
                      rfl

theorem cell22_152373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 3, 2, 2, 3].length) (baseStart_152373 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_152373 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_152373 prefixEnd_152373 := by exact prefixLift 152373
  have htrace : WordTrace (prefixWord ++ tailWord_152373) baseStart_152373 baseEnd_152373 := by
    simpa [prefixWord, tailWord_152373, baseEnd_152373] using wordTrace_append hprefix tailTrace_152373
  have hstable : (prefixWord ++ tailWord_152373).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_152373).length < 2 ^ (prefixWord ++ tailWord_152373).sum := by decide
  have hdescent : baseEnd_152373 < baseStart_152373 := by decide
  rcases family_descends (prefixWord ++ tailWord_152373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_152459 : List Nat := [1, 1, 1, 1, 4, 2, 2, 4, 6]
def baseStart_152459 : Nat := 118140960795 + 152459 * 2 ^ 59
def prefixEnd_152459 : Nat := 4983230072969 + 3 ^ 40 * 152459 * 2
def baseEnd_152459 : Nat := 17396610467538719369191

theorem tailTrace_152459 : CollatzResearch.WordTrace tailWord_152459 prefixEnd_152459 17396610467538719369191 := by
  unfold tailWord_152459
  simp only [CollatzResearch.WordTrace]
  refine ⟨5560636554674555769324431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3707091036449703846216287 5560636554674555769324431)
  ·
    refine ⟨8340954832011833653986647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5560636554674555769324431 8340954832011833653986647)
    ·
      refine ⟨12511432248017750480979971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8340954832011833653986647 12511432248017750480979971)
      ·
        refine ⟨18767148372026625721469957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12511432248017750480979971 18767148372026625721469957)
        ·
          refine ⟨3518840319754992322775617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18767148372026625721469957 3518840319754992322775617)
          ·
            refine ⟨2639130239816244242081713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3518840319754992322775617 2639130239816244242081713)
            ·
              refine ⟨1979347679862183181561285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2639130239816244242081713 1979347679862183181561285)
              ·
                refine ⟨371127689974159346542741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1979347679862183181561285 371127689974159346542741)
                ·
                  refine ⟨17396610467538719369191, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 371127689974159346542741 17396610467538719369191)
                  ·
                    rfl

theorem cell22_152459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 2, 4, 6].length) (baseStart_152459 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_152459 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_152459 prefixEnd_152459 := by exact prefixLift 152459
  have htrace : WordTrace (prefixWord ++ tailWord_152459) baseStart_152459 baseEnd_152459 := by
    simpa [prefixWord, tailWord_152459, baseEnd_152459] using wordTrace_append hprefix tailTrace_152459
  have hstable : (prefixWord ++ tailWord_152459).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_152459).length < 2 ^ (prefixWord ++ tailWord_152459).sum := by decide
  have hdescent : baseEnd_152459 < baseStart_152459 := by decide
  rcases family_descends (prefixWord ++ tailWord_152459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_152523 : List Nat := [1, 1, 1, 1, 3, 7, 1, 1, 2, 4]
def baseStart_152523 : Nat := 118140960795 + 152523 * 2 ^ 59
def prefixEnd_152523 : Nat := 4983230072969 + 3 ^ 40 * 152523 * 2
def baseEnd_152523 : Nat := 52211739910541324507377

theorem tailTrace_152523 : CollatzResearch.WordTrace tailWord_152523 prefixEnd_152523 52211739910541324507377 := by
  unfold tailWord_152523
  simp only [CollatzResearch.WordTrace]
  refine ⟨5562970826442694699654223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3708647217628463133102815 5562970826442694699654223)
  ·
    refine ⟨8344456239664042049481335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5562970826442694699654223 8344456239664042049481335)
    ·
      refine ⟨12516684359496063074222003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8344456239664042049481335 12516684359496063074222003)
      ·
        refine ⟨18775026539244094611333005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12516684359496063074222003 18775026539244094611333005)
        ·
          refine ⟨7040634952216535479249877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18775026539244094611333005 7040634952216535479249877)
          ·
            refine ⟨165014881692575050294919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 7040634952216535479249877 165014881692575050294919)
            ·
              refine ⟨247522322538862575442379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 165014881692575050294919 247522322538862575442379)
              ·
                refine ⟨371283483808293863163569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 247522322538862575442379 371283483808293863163569)
                ·
                  refine ⟨278462612856220397372677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 371283483808293863163569 278462612856220397372677)
                  ·
                    refine ⟨52211739910541324507377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 278462612856220397372677 52211739910541324507377)
                    ·
                      rfl

theorem cell22_152523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 7, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 7, 1, 1, 2, 4].length) (baseStart_152523 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_152523 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_152523 prefixEnd_152523 := by exact prefixLift 152523
  have htrace : WordTrace (prefixWord ++ tailWord_152523) baseStart_152523 baseEnd_152523 := by
    simpa [prefixWord, tailWord_152523, baseEnd_152523] using wordTrace_append hprefix tailTrace_152523
  have hstable : (prefixWord ++ tailWord_152523).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_152523).length < 2 ^ (prefixWord ++ tailWord_152523).sum := by decide
  have hdescent : baseEnd_152523 < baseStart_152523 := by decide
  rcases family_descends (prefixWord ++ tailWord_152523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_152587 : List Nat := [1, 1, 1, 1, 6, 4, 1, 3, 1, 3]
def baseStart_152587 : Nat := 118140960795 + 152587 * 2 ^ 59
def prefixEnd_152587 : Nat := 4983230072969 + 3 ^ 40 * 152587 * 2
def baseEnd_152587 : Nat := 52233648418466490907181

theorem tailTrace_152587 : CollatzResearch.WordTrace tailWord_152587 prefixEnd_152587 52233648418466490907181 := by
  unfold tailWord_152587
  simp only [CollatzResearch.WordTrace]
  refine ⟨5565305098210833629984015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3710203398807222419989343 5565305098210833629984015)
  ·
    refine ⟨8347957647316250444976023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5565305098210833629984015 8347957647316250444976023)
    ·
      refine ⟨12521936470974375667464035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8347957647316250444976023 12521936470974375667464035)
      ·
        refine ⟨18782904706461563501196053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12521936470974375667464035 18782904706461563501196053)
        ·
          refine ⟨880448658115385789118565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 18782904706461563501196053 880448658115385789118565)
          ·
            refine ⟨165084123396634835459731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 880448658115385789118565 165084123396634835459731)
            ·
              refine ⟨247626185094952253189597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 165084123396634835459731 247626185094952253189597)
              ·
                refine ⟨92859819410607094946099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 247626185094952253189597 92859819410607094946099)
                ·
                  refine ⟨139289729115910642419149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 92859819410607094946099 139289729115910642419149)
                  ·
                    refine ⟨52233648418466490907181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 139289729115910642419149 52233648418466490907181)
                    ·
                      rfl

theorem cell22_152587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 4, 1, 3, 1, 3].length) (baseStart_152587 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_152587 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_152587 prefixEnd_152587 := by exact prefixLift 152587
  have htrace : WordTrace (prefixWord ++ tailWord_152587) baseStart_152587 baseEnd_152587 := by
    simpa [prefixWord, tailWord_152587, baseEnd_152587] using wordTrace_append hprefix tailTrace_152587
  have hstable : (prefixWord ++ tailWord_152587).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_152587).length < 2 ^ (prefixWord ++ tailWord_152587).sum := by decide
  have hdescent : baseEnd_152587 < baseStart_152587 := by decide
  rcases family_descends (prefixWord ++ tailWord_152587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_152604 : List Nat := [2, 2, 3, 1, 4, 1, 3, 2, 1, 3]
def baseStart_152604 : Nat := 118140960795 + 152604 * 2 ^ 59
def prefixEnd_152604 : Nat := 4983230072969 + 3 ^ 40 * 152604 * 2
def baseEnd_152604 : Nat := 52239467865884113232129

theorem tailTrace_152604 : CollatzResearch.WordTrace tailWord_152604 prefixEnd_152604 52239467865884113232129 := by
  unfold tailWord_152604
  simp only [CollatzResearch.WordTrace]
  refine ⟨2782962569574622766676433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3710616759432830355568577 2782962569574622766676433)
  ·
    refine ⟨2087221927180967075007325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2782962569574622766676433 2087221927180967075007325)
    ·
      refine ⟨782708222692862653127747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2087221927180967075007325 782708222692862653127747)
      ·
        refine ⟨1174062334039293979691621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 782708222692862653127747 1174062334039293979691621)
        ·
          refine ⟨220136687632367621192179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1174062334039293979691621 220136687632367621192179)
          ·
            refine ⟨330205031448551431788269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 220136687632367621192179 330205031448551431788269)
            ·
              refine ⟨123826886793206786920601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 330205031448551431788269 123826886793206786920601)
              ·
                refine ⟨92870165094905090190451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 123826886793206786920601 92870165094905090190451)
                ·
                  refine ⟨139305247642357635285677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 92870165094905090190451 139305247642357635285677)
                  ·
                    refine ⟨52239467865884113232129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 139305247642357635285677 52239467865884113232129)
                    ·
                      rfl

theorem cell22_152604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 1, 3, 2, 1, 3].length) (baseStart_152604 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_152604 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_152604 prefixEnd_152604 := by exact prefixLift 152604
  have htrace : WordTrace (prefixWord ++ tailWord_152604) baseStart_152604 baseEnd_152604 := by
    simpa [prefixWord, tailWord_152604, baseEnd_152604] using wordTrace_append hprefix tailTrace_152604
  have hstable : (prefixWord ++ tailWord_152604).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_152604).length < 2 ^ (prefixWord ++ tailWord_152604).sum := by decide
  have hdescent : baseEnd_152604 < baseStart_152604 := by decide
  rcases family_descends (prefixWord ++ tailWord_152604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_152630 : List Nat := [5, 1, 2, 1, 1, 3, 1, 1, 3, 4]
def baseStart_152630 : Nat := 118140960795 + 152630 * 2 ^ 59
def prefixEnd_152630 : Nat := 4983230072969 + 3 ^ 40 * 152630 * 2
def baseEnd_152630 : Nat := 52248368197228712082049

theorem tailTrace_152630 : CollatzResearch.WordTrace tailWord_152630 prefixEnd_152630 52248368197228712082049 := by
  unfold tailWord_152630
  simp only [CollatzResearch.WordTrace]
  refine ⟨347929589815940748362459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 3711248958036701315866229 347929589815940748362459)
  ·
    refine ⟨521894384723911122543689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 347929589815940748362459 521894384723911122543689)
    ·
      refine ⟨391420788542933341907767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 521894384723911122543689 391420788542933341907767)
      ·
        refine ⟨587131182814400012861651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 391420788542933341907767 587131182814400012861651)
        ·
          refine ⟨880696774221600019292477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 587131182814400012861651 880696774221600019292477)
          ·
            refine ⟨330261290333100007234679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 880696774221600019292477 330261290333100007234679)
            ·
              refine ⟨495391935499650010852019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 330261290333100007234679 495391935499650010852019)
              ·
                refine ⟨743087903249475016278029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 495391935499650010852019 743087903249475016278029)
                ·
                  refine ⟨278657963718553131104261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 743087903249475016278029 278657963718553131104261)
                  ·
                    refine ⟨52248368197228712082049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 278657963718553131104261 52248368197228712082049)
                    ·
                      rfl

theorem cell22_152630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 3, 1, 1, 3, 4].length) (baseStart_152630 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_152630 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_152630 prefixEnd_152630 := by exact prefixLift 152630
  have htrace : WordTrace (prefixWord ++ tailWord_152630) baseStart_152630 baseEnd_152630 := by
    simpa [prefixWord, tailWord_152630, baseEnd_152630] using wordTrace_append hprefix tailTrace_152630
  have hstable : (prefixWord ++ tailWord_152630).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_152630).length < 2 ^ (prefixWord ++ tailWord_152630).sum := by decide
  have hdescent : baseEnd_152630 < baseStart_152630 := by decide
  rcases family_descends (prefixWord ++ tailWord_152630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_152660 : List Nat := [2, 4, 1, 1, 1, 1, 3, 4, 2, 3]
def baseStart_152660 : Nat := 118140960795 + 152660 * 2 ^ 59
def prefixEnd_152660 : Nat := 4983230072969 + 3 ^ 40 * 152660 * 2
def baseEnd_152660 : Nat := 52258637810318633831957

theorem tailTrace_152660 : CollatzResearch.WordTrace tailWord_152660 prefixEnd_152660 52258637810318633831957 := by
  unfold tailWord_152660
  simp only [CollatzResearch.WordTrace]
  refine ⟨2783983813473183548695717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3711978417964244731594289 2783983813473183548695717)
  ·
    refine ⟨521996965026221915380447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2783983813473183548695717 521996965026221915380447)
    ·
      refine ⟨782995447539332873070671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 521996965026221915380447 782995447539332873070671)
      ·
        refine ⟨1174493171308999309606007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 782995447539332873070671 1174493171308999309606007)
        ·
          refine ⟨1761739756963498964409011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1174493171308999309606007 1761739756963498964409011)
          ·
            refine ⟨2642609635445248446613517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1761739756963498964409011 2642609635445248446613517)
            ·
              refine ⟨990978613291968167480069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2642609635445248446613517 990978613291968167480069)
              ·
                refine ⟨185808489992244031402513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 990978613291968167480069 185808489992244031402513)
                ·
                  refine ⟨139356367494183023551885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 185808489992244031402513 139356367494183023551885)
                  ·
                    refine ⟨52258637810318633831957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 139356367494183023551885 52258637810318633831957)
                    ·
                      rfl

theorem cell22_152660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 3, 4, 2, 3].length) (baseStart_152660 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_152660 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_152660 prefixEnd_152660 := by exact prefixLift 152660
  have htrace : WordTrace (prefixWord ++ tailWord_152660) baseStart_152660 baseEnd_152660 := by
    simpa [prefixWord, tailWord_152660, baseEnd_152660] using wordTrace_append hprefix tailTrace_152660
  have hstable : (prefixWord ++ tailWord_152660).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_152660).length < 2 ^ (prefixWord ++ tailWord_152660).sum := by decide
  have hdescent : baseEnd_152660 < baseStart_152660 := by decide
  rcases family_descends (prefixWord ++ tailWord_152660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_152722 : List Nat := [3, 2, 3, 1, 1, 3, 2, 1, 3, 3]
def baseStart_152722 : Nat := 118140960795 + 152722 * 2 ^ 59
def prefixEnd_152722 : Nat := 4983230072969 + 3 ^ 40 * 152722 * 2
def baseEnd_152722 : Nat := 52279861677371138781767

theorem tailTrace_152722 : CollatzResearch.WordTrace tailWord_152722 prefixEnd_152722 52279861677371138781767 := by
  unfold tailWord_152722
  simp only [CollatzResearch.WordTrace]
  refine ⟨1392557238180437921537105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3713485968481167790765613 1392557238180437921537105)
  ·
    refine ⟨1044417928635328441152829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1392557238180437921537105 1044417928635328441152829)
    ·
      refine ⟨391656723238248165432311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1044417928635328441152829 391656723238248165432311)
      ·
        refine ⟨587485084857372248148467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 391656723238248165432311 587485084857372248148467)
        ·
          refine ⟨881227627286058372222701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 587485084857372248148467 881227627286058372222701)
          ·
            refine ⟨330460360232271889583513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 881227627286058372222701 330460360232271889583513)
            ·
              refine ⟨247845270174203917187635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 330460360232271889583513 247845270174203917187635)
              ·
                refine ⟨371767905261305875781453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 247845270174203917187635 371767905261305875781453)
                ·
                  refine ⟨139412964472989703418045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 371767905261305875781453 139412964472989703418045)
                  ·
                    refine ⟨52279861677371138781767, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 139412964472989703418045 52279861677371138781767)
                    ·
                      rfl

theorem cell22_152722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 3, 2, 1, 3, 3].length) (baseStart_152722 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_152722 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_152722 prefixEnd_152722 := by exact prefixLift 152722
  have htrace : WordTrace (prefixWord ++ tailWord_152722) baseStart_152722 baseEnd_152722 := by
    simpa [prefixWord, tailWord_152722, baseEnd_152722] using wordTrace_append hprefix tailTrace_152722
  have hstable : (prefixWord ++ tailWord_152722).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_152722).length < 2 ^ (prefixWord ++ tailWord_152722).sum := by decide
  have hdescent : baseEnd_152722 < baseStart_152722 := by decide
  rcases family_descends (prefixWord ++ tailWord_152722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_152731 : List Nat := [1, 1, 1, 1, 1, 1, 2, 3, 1, 10]
def baseStart_152731 : Nat := 118140960795 + 152731 * 2 ^ 59
def prefixEnd_152731 : Nat := 4983230072969 + 3 ^ 40 * 152731 * 2
def baseEnd_152731 : Nat := 52282942561298115306739

theorem tailTrace_152731 : CollatzResearch.WordTrace tailWord_152731 prefixEnd_152731 52282942561298115306739 := by
  unfold tailWord_152731
  simp only [CollatzResearch.WordTrace]
  refine ⟨5570557209689146223226047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3713704806459430815484031 5570557209689146223226047)
  ·
    refine ⟨8355835814533719334839071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5570557209689146223226047 8355835814533719334839071)
    ·
      refine ⟨12533753721800579002258607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8355835814533719334839071 12533753721800579002258607)
      ·
        refine ⟨18800630582700868503387911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12533753721800579002258607 18800630582700868503387911)
        ·
          refine ⟨28200945874051302755081867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18800630582700868503387911 28200945874051302755081867)
          ·
            refine ⟨42301418811076954132622801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28200945874051302755081867 42301418811076954132622801)
            ·
              refine ⟨31726064108307715599467101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42301418811076954132622801 31726064108307715599467101)
              ·
                refine ⟨11897274040615393349800163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31726064108307715599467101 11897274040615393349800163)
                ·
                  refine ⟨17845911060923090024700245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11897274040615393349800163 17845911060923090024700245)
                  ·
                    refine ⟨52282942561298115306739, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 17845911060923090024700245 52282942561298115306739)
                    ·
                      rfl

theorem cell22_152731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 1, 10].length) (baseStart_152731 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_152731 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_152731 prefixEnd_152731 := by exact prefixLift 152731
  have htrace : WordTrace (prefixWord ++ tailWord_152731) baseStart_152731 baseEnd_152731 := by
    simpa [prefixWord, tailWord_152731, baseEnd_152731] using wordTrace_append hprefix tailTrace_152731
  have hstable : (prefixWord ++ tailWord_152731).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_152731).length < 2 ^ (prefixWord ++ tailWord_152731).sum := by decide
  have hdescent : baseEnd_152731 < baseStart_152731 := by decide
  rcases family_descends (prefixWord ++ tailWord_152731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_152733 : List Nat := [1, 4, 2, 1, 1, 2, 1, 3, 2, 5]
def baseStart_152733 : Nat := 118140960795 + 152733 * 2 ^ 59
def prefixEnd_152733 : Nat := 4983230072969 + 3 ^ 40 * 152733 * 2
def baseEnd_152733 : Nat := 52283627202170776756733

theorem tailTrace_152733 : CollatzResearch.WordTrace tailWord_152733 prefixEnd_152733 52283627202170776756733 := by
  unfold tailWord_152733
  simp only [CollatzResearch.WordTrace]
  refine ⟨5570630155681900564798853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3713753437121267043199235 5570630155681900564798853)
  ·
    refine ⟨1044493154190356355899785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5570630155681900564798853 1044493154190356355899785)
    ·
      refine ⟨783369865642767266924839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1044493154190356355899785 783369865642767266924839)
      ·
        refine ⟨1175054798464150900387259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 783369865642767266924839 1175054798464150900387259)
        ·
          refine ⟨1762582197696226350580889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1175054798464150900387259 1762582197696226350580889)
          ·
            refine ⟨1321936648272169762935667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1762582197696226350580889 1321936648272169762935667)
            ·
              refine ⟨1982904972408254644403501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1321936648272169762935667 1982904972408254644403501)
              ·
                refine ⟨743589364653095491651313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1982904972408254644403501 743589364653095491651313)
                ·
                  refine ⟨557692023489821618738485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 743589364653095491651313 557692023489821618738485)
                  ·
                    refine ⟨52283627202170776756733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 557692023489821618738485 52283627202170776756733)
                    ·
                      rfl

theorem cell22_152733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 1, 3, 2, 5].length) (baseStart_152733 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_152733 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_152733 prefixEnd_152733 := by exact prefixLift 152733
  have htrace : WordTrace (prefixWord ++ tailWord_152733) baseStart_152733 baseEnd_152733 := by
    simpa [prefixWord, tailWord_152733, baseEnd_152733] using wordTrace_append hprefix tailTrace_152733
  have hstable : (prefixWord ++ tailWord_152733).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_152733).length < 2 ^ (prefixWord ++ tailWord_152733).sum := by decide
  have hdescent : baseEnd_152733 < baseStart_152733 := by decide
  rcases family_descends (prefixWord ++ tailWord_152733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_152765 : List Nat := [1, 4, 1, 2, 1, 1, 4, 3, 1, 4]
def baseStart_152765 : Nat := 118140960795 + 152765 * 2 ^ 59
def prefixEnd_152765 : Nat := 4983230072969 + 3 ^ 40 * 152765 * 2
def baseEnd_152765 : Nat := 52294581456133359956635

theorem tailTrace_152765 : CollatzResearch.WordTrace tailWord_152765 prefixEnd_152765 52294581456133359956635 := by
  unfold tailWord_152765
  simp only [CollatzResearch.WordTrace]
  refine ⟨5571797291565970029963749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3714531527710646686642499 5571797291565970029963749)
  ·
    refine ⟨1044711992168619380618203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5571797291565970029963749 1044711992168619380618203)
    ·
      refine ⟨1567067988252929070927305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1044711992168619380618203 1567067988252929070927305)
      ·
        refine ⟨1175300991189696803195479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1567067988252929070927305 1175300991189696803195479)
        ·
          refine ⟨1762951486784545204793219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1175300991189696803195479 1762951486784545204793219)
          ·
            refine ⟨2644427230176817807189829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1762951486784545204793219 2644427230176817807189829)
            ·
              refine ⟨495830105658153338848093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2644427230176817807189829 495830105658153338848093)
              ·
                refine ⟨185936289621807502068035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 495830105658153338848093 185936289621807502068035)
                ·
                  refine ⟨278904434432711253102053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 185936289621807502068035 278904434432711253102053)
                  ·
                    refine ⟨52294581456133359956635, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 278904434432711253102053 52294581456133359956635)
                    ·
                      rfl

theorem cell22_152765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 4, 3, 1, 4].length) (baseStart_152765 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_152765 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_152765 prefixEnd_152765 := by exact prefixLift 152765
  have htrace : WordTrace (prefixWord ++ tailWord_152765) baseStart_152765 baseEnd_152765 := by
    simpa [prefixWord, tailWord_152765, baseEnd_152765] using wordTrace_append hprefix tailTrace_152765
  have hstable : (prefixWord ++ tailWord_152765).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_152765).length < 2 ^ (prefixWord ++ tailWord_152765).sum := by decide
  have hdescent : baseEnd_152765 < baseStart_152765 := by decide
  rcases family_descends (prefixWord ++ tailWord_152765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_152793 : List Nat := [1, 2, 1, 2, 3, 1, 1, 1, 6, 4]
def baseStart_152793 : Nat := 118140960795 + 152793 * 2 ^ 59
def prefixEnd_152793 : Nat := 4983230072969 + 3 ^ 40 * 152793 * 2
def baseEnd_152793 : Nat := 52304166428350620256549

theorem tailTrace_152793 : CollatzResearch.WordTrace tailWord_152793 prefixEnd_152793 52304166428350620256549 := by
  unfold tailWord_152793
  simp only [CollatzResearch.WordTrace]
  refine ⟨5572818535464530811983033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3715212356976353874655355 5572818535464530811983033)
  ·
    refine ⟨4179613901598398108987275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5572818535464530811983033 4179613901598398108987275)
    ·
      refine ⟨6269420852397597163480913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4179613901598398108987275 6269420852397597163480913)
      ·
        refine ⟨4702065639298197872610685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6269420852397597163480913 4702065639298197872610685)
        ·
          refine ⟨1763274614736824202229007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4702065639298197872610685 1763274614736824202229007)
          ·
            refine ⟨2644911922105236303343511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1763274614736824202229007 2644911922105236303343511)
            ·
              refine ⟨3967367883157854455015267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2644911922105236303343511 3967367883157854455015267)
              ·
                refine ⟨5951051824736781682522901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3967367883157854455015267 5951051824736781682522901)
                ·
                  refine ⟨278955554284536641368261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5951051824736781682522901 278955554284536641368261)
                  ·
                    refine ⟨52304166428350620256549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 278955554284536641368261 52304166428350620256549)
                    ·
                      rfl

theorem cell22_152793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 1, 6, 4].length) (baseStart_152793 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_152793 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_152793 prefixEnd_152793 := by exact prefixLift 152793
  have htrace : WordTrace (prefixWord ++ tailWord_152793) baseStart_152793 baseEnd_152793 := by
    simpa [prefixWord, tailWord_152793, baseEnd_152793] using wordTrace_append hprefix tailTrace_152793
  have hstable : (prefixWord ++ tailWord_152793).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_152793).length < 2 ^ (prefixWord ++ tailWord_152793).sum := by decide
  have hdescent : baseEnd_152793 < baseStart_152793 := by decide
  rcases family_descends (prefixWord ++ tailWord_152793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_152808 : List Nat := [2, 1, 4, 1, 2, 1, 1, 10]
def baseStart_152808 : Nat := 118140960795 + 152808 * 2 ^ 59
def prefixEnd_152808 : Nat := 4983230072969 + 3 ^ 40 * 152808 * 2
def baseEnd_152808 : Nat := 5812144581655064570167

theorem tailTrace_152808 : CollatzResearch.WordTrace tailWord_152808 prefixEnd_152808 5812144581655064570167 := by
  unfold tailWord_152808
  simp only [CollatzResearch.WordTrace]
  refine ⟨2786682815205094186889539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3715577086940125582519385 2786682815205094186889539)
  ·
    refine ⟨4180024222807641280334309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2786682815205094186889539 4180024222807641280334309)
    ·
      refine ⟨783754541776432740062683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4180024222807641280334309 783754541776432740062683)
      ·
        refine ⟨1175631812664649110094025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 783754541776432740062683 1175631812664649110094025)
        ·
          refine ⟨881723859498486832570519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1175631812664649110094025 881723859498486832570519)
          ·
            refine ⟨1322585789247730248855779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 881723859498486832570519 1322585789247730248855779)
            ·
              refine ⟨1983878683871595373283669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1322585789247730248855779 1983878683871595373283669)
              ·
                refine ⟨5812144581655064570167, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 1983878683871595373283669 5812144581655064570167)
                ·
                  rfl

theorem cell22_152808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 1, 10].length) (baseStart_152808 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_152808 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_152808 prefixEnd_152808 := by exact prefixLift 152808
  have htrace : WordTrace (prefixWord ++ tailWord_152808) baseStart_152808 baseEnd_152808 := by
    simpa [prefixWord, tailWord_152808, baseEnd_152808] using wordTrace_append hprefix tailTrace_152808
  have hstable : (prefixWord ++ tailWord_152808).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_152808).length < 2 ^ (prefixWord ++ tailWord_152808).sum := by decide
  have hdescent : baseEnd_152808 < baseStart_152808 := by decide
  rcases family_descends (prefixWord ++ tailWord_152808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_152810 : List Nat := [3, 1, 3, 1, 1, 3, 1, 3, 2, 4]
def baseStart_152810 : Nat := 118140960795 + 152810 * 2 ^ 59
def prefixEnd_152810 : Nat := 4983230072969 + 3 ^ 40 * 152810 * 2
def baseEnd_152810 : Nat := 52309985875768242581497

theorem tailTrace_152810 : CollatzResearch.WordTrace tailWord_152810 prefixEnd_152810 52309985875768242581497 := by
  unfold tailWord_152810
  simp only [CollatzResearch.WordTrace]
  refine ⟨1393359644100735678837971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3715625717601961810234589 1393359644100735678837971)
  ·
    refine ⟨2090039466151103518256957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1393359644100735678837971 2090039466151103518256957)
    ·
      refine ⟨783764799806663819346359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2090039466151103518256957 783764799806663819346359)
      ·
        refine ⟨1175647199709995729019539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 783764799806663819346359 1175647199709995729019539)
        ·
          refine ⟨1763470799564993593529309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1175647199709995729019539 1763470799564993593529309)
          ·
            refine ⟨661301549836872597573491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1763470799564993593529309 661301549836872597573491)
            ·
              refine ⟨991952324755308896360237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 661301549836872597573491 991952324755308896360237)
              ·
                refine ⟨371982121783240836135089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 991952324755308896360237 371982121783240836135089)
                ·
                  refine ⟨278986591337430627101317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 371982121783240836135089 278986591337430627101317)
                  ·
                    refine ⟨52309985875768242581497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 278986591337430627101317 52309985875768242581497)
                    ·
                      rfl

theorem cell22_152810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 1, 3, 2, 4].length) (baseStart_152810 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_152810 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_152810 prefixEnd_152810 := by exact prefixLift 152810
  have htrace : WordTrace (prefixWord ++ tailWord_152810) baseStart_152810 baseEnd_152810 := by
    simpa [prefixWord, tailWord_152810, baseEnd_152810] using wordTrace_append hprefix tailTrace_152810
  have hstable : (prefixWord ++ tailWord_152810).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_152810).length < 2 ^ (prefixWord ++ tailWord_152810).sum := by decide
  have hdescent : baseEnd_152810 < baseStart_152810 := by decide
  rcases family_descends (prefixWord ++ tailWord_152810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_152853 : List Nat := [1, 3, 2, 1, 2, 1, 1, 2, 9]
def baseStart_152853 : Nat := 118140960795 + 152853 * 2 ^ 59
def prefixEnd_152853 : Nat := 4983230072969 + 3 ^ 40 * 152853 * 2
def baseEnd_152853 : Nat := 17441568551510154585455

theorem tailTrace_152853 : CollatzResearch.WordTrace tailWord_152853 prefixEnd_152853 17441568551510154585455 := by
  unfold tailWord_152853
  simp only [CollatzResearch.WordTrace]
  refine ⟨5575006915247161059167213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3716671276831440706111475 5575006915247161059167213)
  ·
    refine ⟨2090627593217685397187705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5575006915247161059167213 2090627593217685397187705)
    ·
      refine ⟨1567970694913264047890779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2090627593217685397187705 1567970694913264047890779)
      ·
        refine ⟨2351956042369896071836169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1567970694913264047890779 2351956042369896071836169)
        ·
          refine ⟨1763967031777422053877127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2351956042369896071836169 1763967031777422053877127)
          ·
            refine ⟨2645950547666133080815691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1763967031777422053877127 2645950547666133080815691)
            ·
              refine ⟨3968925821499199621223537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2645950547666133080815691 3968925821499199621223537)
              ·
                refine ⟨2976694366124399715917653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3968925821499199621223537 2976694366124399715917653)
                ·
                  refine ⟨17441568551510154585455, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 2976694366124399715917653 17441568551510154585455)
                  ·
                    rfl

theorem cell22_152853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 2, 9].length) (baseStart_152853 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_152853 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_152853 prefixEnd_152853 := by exact prefixLift 152853
  have htrace : WordTrace (prefixWord ++ tailWord_152853) baseStart_152853 baseEnd_152853 := by
    simpa [prefixWord, tailWord_152853, baseEnd_152853] using wordTrace_append hprefix tailTrace_152853
  have hstable : (prefixWord ++ tailWord_152853).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_152853).length < 2 ^ (prefixWord ++ tailWord_152853).sum := by decide
  have hdescent : baseEnd_152853 < baseStart_152853 := by decide
  rcases family_descends (prefixWord ++ tailWord_152853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_152885 : List Nat := [1, 3, 3, 1, 2, 2, 1, 2, 2, 5]
def baseStart_152885 : Nat := 118140960795 + 152885 * 2 ^ 59
def prefixEnd_152885 : Nat := 4983230072969 + 3 ^ 40 * 152885 * 2
def baseEnd_152885 : Nat := 52335659908493046956267

theorem tailTrace_152885 : CollatzResearch.WordTrace tailWord_152885 prefixEnd_152885 52335659908493046956267 := by
  unfold tailWord_152885
  simp only [CollatzResearch.WordTrace]
  refine ⟨5576174051131230524332109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3717449367420820349554739 5576174051131230524332109)
  ·
    refine ⟨2091065269174211446624541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5576174051131230524332109 2091065269174211446624541)
    ·
      refine ⟨784149475940329292484203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2091065269174211446624541 784149475940329292484203)
      ·
        refine ⟨1176224213910493938726305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 784149475940329292484203 1176224213910493938726305)
        ·
          refine ⟨882168160432870454044729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1176224213910493938726305 882168160432870454044729)
          ·
            refine ⟨661626120324652840533547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 882168160432870454044729 661626120324652840533547)
            ·
              refine ⟨992439180486979260800321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 661626120324652840533547 992439180486979260800321)
              ·
                refine ⟨744329385365234445600241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 992439180486979260800321 744329385365234445600241)
                ·
                  refine ⟨558247039023925834200181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 744329385365234445600241 558247039023925834200181)
                  ·
                    refine ⟨52335659908493046956267, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 558247039023925834200181 52335659908493046956267)
                    ·
                      rfl

theorem cell22_152885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 1, 2, 2, 5].length) (baseStart_152885 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_152885 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_152885 prefixEnd_152885 := by exact prefixLift 152885
  have htrace : WordTrace (prefixWord ++ tailWord_152885) baseStart_152885 baseEnd_152885 := by
    simpa [prefixWord, tailWord_152885, baseEnd_152885] using wordTrace_append hprefix tailTrace_152885
  have hstable : (prefixWord ++ tailWord_152885).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_152885).length < 2 ^ (prefixWord ++ tailWord_152885).sum := by decide
  have hdescent : baseEnd_152885 < baseStart_152885 := by decide
  rcases family_descends (prefixWord ++ tailWord_152885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_152917 : List Nat := [1, 3, 2, 2, 3, 1, 1, 4, 1, 4]
def baseStart_152917 : Nat := 118140960795 + 152917 * 2 ^ 59
def prefixEnd_152917 : Nat := 4983230072969 + 3 ^ 40 * 152917 * 2
def baseEnd_152917 : Nat := 52346614162455630156169

theorem tailTrace_152917 : CollatzResearch.WordTrace tailWord_152917 prefixEnd_152917 52346614162455630156169 := by
  unfold tailWord_152917
  simp only [CollatzResearch.WordTrace]
  refine ⟨5577341187015299989497005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3718227458010199992998003 5577341187015299989497005)
  ·
    refine ⟨2091502945130737496061377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5577341187015299989497005 2091502945130737496061377)
    ·
      refine ⟨1568627208848053122046033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2091502945130737496061377 1568627208848053122046033)
      ·
        refine ⟨1176470406636039841534525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1568627208848053122046033 1176470406636039841534525)
        ·
          refine ⟨441176402488514940575447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1176470406636039841534525 441176402488514940575447)
          ·
            refine ⟨661764603732772410863171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 441176402488514940575447 661764603732772410863171)
            ·
              refine ⟨992646905599158616294757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 661764603732772410863171 992646905599158616294757)
              ·
                refine ⟨186121294799842240555267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 992646905599158616294757 186121294799842240555267)
                ·
                  refine ⟨279181942199763360832901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 186121294799842240555267 279181942199763360832901)
                  ·
                    refine ⟨52346614162455630156169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 279181942199763360832901 52346614162455630156169)
                    ·
                      rfl

theorem cell22_152917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 1, 4, 1, 4].length) (baseStart_152917 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_152917 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_152917 prefixEnd_152917 := by exact prefixLift 152917
  have htrace : WordTrace (prefixWord ++ tailWord_152917) baseStart_152917 baseEnd_152917 := by
    simpa [prefixWord, tailWord_152917, baseEnd_152917] using wordTrace_append hprefix tailTrace_152917
  have hstable : (prefixWord ++ tailWord_152917).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_152917).length < 2 ^ (prefixWord ++ tailWord_152917).sum := by decide
  have hdescent : baseEnd_152917 < baseStart_152917 := by decide
  rcases family_descends (prefixWord ++ tailWord_152917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_152945 : List Nat := [1, 2, 2, 2, 1, 2, 3, 1, 4, 4]
def baseStart_152945 : Nat := 118140960795 + 152945 * 2 ^ 59
def prefixEnd_152945 : Nat := 4983230072969 + 3 ^ 40 * 152945 * 2
def baseEnd_152945 : Nat := 52356199134672890456083

theorem tailTrace_152945 : CollatzResearch.WordTrace tailWord_152945 prefixEnd_152945 52356199134672890456083 := by
  unfold tailWord_152945
  simp only [CollatzResearch.WordTrace]
  refine ⟨5578362430913860771516289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3718908287275907181010859 5578362430913860771516289)
  ·
    refine ⟨4183771823185395578637217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5578362430913860771516289 4183771823185395578637217)
    ·
      refine ⟨3137828867389046683977913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4183771823185395578637217 3137828867389046683977913)
      ·
        refine ⟨2353371650541785012983435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3137828867389046683977913 2353371650541785012983435)
        ·
          refine ⟨3530057475812677519475153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2353371650541785012983435 3530057475812677519475153)
          ·
            refine ⟨2647543106859508139606365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3530057475812677519475153 2647543106859508139606365)
            ·
              refine ⟨992828665072315552352387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2647543106859508139606365 992828665072315552352387)
              ·
                refine ⟨1489242997608473328528581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 992828665072315552352387 1489242997608473328528581)
                ·
                  refine ⟨279233062051588749099109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1489242997608473328528581 279233062051588749099109)
                  ·
                    refine ⟨52356199134672890456083, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 279233062051588749099109 52356199134672890456083)
                    ·
                      rfl

theorem cell22_152945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 3, 1, 4, 4].length) (baseStart_152945 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_152945 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_152945 prefixEnd_152945 := by exact prefixLift 152945
  have htrace : WordTrace (prefixWord ++ tailWord_152945) baseStart_152945 baseEnd_152945 := by
    simpa [prefixWord, tailWord_152945, baseEnd_152945] using wordTrace_append hprefix tailTrace_152945
  have hstable : (prefixWord ++ tailWord_152945).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_152945).length < 2 ^ (prefixWord ++ tailWord_152945).sum := by decide
  have hdescent : baseEnd_152945 < baseStart_152945 := by decide
  rcases family_descends (prefixWord ++ tailWord_152945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_152949 : List Nat := [1, 3, 4, 1, 3, 2, 1, 1, 6]
def baseStart_152949 : Nat := 118140960795 + 152949 * 2 ^ 59
def prefixEnd_152949 : Nat := 4983230072969 + 3 ^ 40 * 152949 * 2
def baseEnd_152949 : Nat := 17452522805472737785357

theorem tailTrace_152949 : CollatzResearch.WordTrace tailWord_152949 prefixEnd_152949 17452522805472737785357 := by
  unfold tailWord_152949
  simp only [CollatzResearch.WordTrace]
  refine ⟨5578508322899369454661901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3719005548599579636441267 5578508322899369454661901)
  ·
    refine ⟨2091940621087263545498213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5578508322899369454661901 2091940621087263545498213)
    ·
      refine ⟨392238866453861914780915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2091940621087263545498213 392238866453861914780915)
      ·
        refine ⟨588358299680792872171373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 392238866453861914780915 588358299680792872171373)
        ·
          refine ⟨220634362380297327064265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 588358299680792872171373 220634362380297327064265)
          ·
            refine ⟨165475771785222995298199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 220634362380297327064265 165475771785222995298199)
            ·
              refine ⟨248213657677834492947299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 165475771785222995298199 248213657677834492947299)
              ·
                refine ⟨372320486516751739420949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 248213657677834492947299 372320486516751739420949)
                ·
                  refine ⟨17452522805472737785357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 372320486516751739420949 17452522805472737785357)
                  ·
                    rfl

theorem cell22_152949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 2, 1, 1, 6].length) (baseStart_152949 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_152949 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_152949 prefixEnd_152949 := by exact prefixLift 152949
  have htrace : WordTrace (prefixWord ++ tailWord_152949) baseStart_152949 baseEnd_152949 := by
    simpa [prefixWord, tailWord_152949, baseEnd_152949] using wordTrace_append hprefix tailTrace_152949
  have hstable : (prefixWord ++ tailWord_152949).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_152949).length < 2 ^ (prefixWord ++ tailWord_152949).sum := by decide
  have hdescent : baseEnd_152949 < baseStart_152949 := by decide
  rcases family_descends (prefixWord ++ tailWord_152949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_152964 : List Nat := [2, 3, 2, 1, 1, 4, 1, 3, 2, 3]
def baseStart_152964 : Nat := 118140960795 + 152964 * 2 ^ 59
def prefixEnd_152964 : Nat := 4983230072969 + 3 ^ 40 * 152964 * 2
def baseEnd_152964 : Nat := 52362703222963174231025

theorem tailTrace_152964 : CollatzResearch.WordTrace tailWord_152964 prefixEnd_152964 52362703222963174231025 := by
  unfold tailWord_152964
  simp only [CollatzResearch.WordTrace]
  refine ⟨2789527708922513508228973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3719370278563351344305297 2789527708922513508228973)
  ·
    refine ⟨1046072890845942565585865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2789527708922513508228973 1046072890845942565585865)
    ·
      refine ⟨784554668134456924189399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1046072890845942565585865 784554668134456924189399)
      ·
        refine ⟨1176832002201685386284099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 784554668134456924189399 1176832002201685386284099)
        ·
          refine ⟨1765248003302528079426149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1176832002201685386284099 1765248003302528079426149)
          ·
            refine ⟨330984000619224014892403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1765248003302528079426149 330984000619224014892403)
            ·
              refine ⟨496476000928836022338605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 330984000619224014892403 496476000928836022338605)
              ·
                refine ⟨186178500348313508376977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 496476000928836022338605 186178500348313508376977)
                ·
                  refine ⟨139633875261235131282733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 186178500348313508376977 139633875261235131282733)
                  ·
                    refine ⟨52362703222963174231025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 139633875261235131282733 52362703222963174231025)
                    ·
                      rfl

theorem cell22_152964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 4, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 4, 1, 3, 2, 3].length) (baseStart_152964 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_152964 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_152964 prefixEnd_152964 := by exact prefixLift 152964
  have htrace : WordTrace (prefixWord ++ tailWord_152964) baseStart_152964 baseEnd_152964 := by
    simpa [prefixWord, tailWord_152964, baseEnd_152964] using wordTrace_append hprefix tailTrace_152964
  have hstable : (prefixWord ++ tailWord_152964).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_152964).length < 2 ^ (prefixWord ++ tailWord_152964).sum := by decide
  have hdescent : baseEnd_152964 < baseStart_152964 := by decide
  rcases family_descends (prefixWord ++ tailWord_152964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_153000 : List Nat := [2, 1, 6, 1, 3, 1, 2, 2, 4]
def baseStart_153000 : Nat := 118140960795 + 153000 * 2 ^ 59
def prefixEnd_153000 : Nat := 4983230072969 + 3 ^ 40 * 153000 * 2
def baseEnd_153000 : Nat := 17458342252890360110305

theorem tailTrace_153000 : CollatzResearch.WordTrace tailWord_153000 prefixEnd_153000 17458342252890360110305 := by
  unfold tailWord_153000
  simp only [CollatzResearch.WordTrace]
  refine ⟨2790184222857302582384227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3720245630476403443178969 2790184222857302582384227)
  ·
    refine ⟨4185276334285953873576341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2790184222857302582384227 4185276334285953873576341)
    ·
      refine ⟨196184828169654087823891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 4185276334285953873576341 196184828169654087823891)
      ·
        refine ⟨294277242254481131735837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 196184828169654087823891 294277242254481131735837)
        ·
          refine ⟨110353965845430424400939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 294277242254481131735837 110353965845430424400939)
          ·
            refine ⟨165530948768145636601409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 110353965845430424400939 165530948768145636601409)
            ·
              refine ⟨124148211576109227451057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 165530948768145636601409 124148211576109227451057)
              ·
                refine ⟨93111158682081920588293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 124148211576109227451057 93111158682081920588293)
                ·
                  refine ⟨17458342252890360110305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 93111158682081920588293 17458342252890360110305)
                  ·
                    rfl

theorem cell22_153000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 3, 1, 2, 2, 4].length) (baseStart_153000 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_153000 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_153000 prefixEnd_153000 := by exact prefixLift 153000
  have htrace : WordTrace (prefixWord ++ tailWord_153000) baseStart_153000 baseEnd_153000 := by
    simpa [prefixWord, tailWord_153000, baseEnd_153000] using wordTrace_append hprefix tailTrace_153000
  have hstable : (prefixWord ++ tailWord_153000).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_153000).length < 2 ^ (prefixWord ++ tailWord_153000).sum := by decide
  have hdescent : baseEnd_153000 < baseStart_153000 := by decide
  rcases family_descends (prefixWord ++ tailWord_153000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_153094 : List Nat := [6, 2, 1, 1, 2, 2, 1, 3, 1, 3]
def baseStart_153094 : Nat := 118140960795 + 153094 * 2 ^ 59
def prefixEnd_153094 : Nat := 4983230072969 + 3 ^ 40 * 153094 * 2
def baseEnd_153094 : Nat := 52407204879686168480627

theorem tailTrace_153094 : CollatzResearch.WordTrace tailWord_153094 prefixEnd_153094 52407204879686168480627 := by
  unfold tailWord_153094
  simp only [CollatzResearch.WordTrace]
  refine ⟨174493653355439350584073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 3722531271582706145793557 174493653355439350584073)
  ·
    refine ⟨130870240016579512938055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 174493653355439350584073 130870240016579512938055)
    ·
      refine ⟨196305360024869269407083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 130870240016579512938055 196305360024869269407083)
      ·
        refine ⟨294458040037303904110625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 196305360024869269407083 294458040037303904110625)
        ·
          refine ⟨220843530027977928082969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 294458040037303904110625 220843530027977928082969)
          ·
            refine ⟨165632647520983446062227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 220843530027977928082969 165632647520983446062227)
            ·
              refine ⟨248448971281475169093341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 165632647520983446062227 248448971281475169093341)
              ·
                refine ⟨93168364230553188410003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 248448971281475169093341 93168364230553188410003)
                ·
                  refine ⟨139752546345829782615005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 93168364230553188410003 139752546345829782615005)
                  ·
                    refine ⟨52407204879686168480627, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 139752546345829782615005 52407204879686168480627)
                    ·
                      rfl

theorem cell22_153094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 2, 1, 3, 1, 3].length) (baseStart_153094 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_153094 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_153094 prefixEnd_153094 := by exact prefixLift 153094
  have htrace : WordTrace (prefixWord ++ tailWord_153094) baseStart_153094 baseEnd_153094 := by
    simpa [prefixWord, tailWord_153094, baseEnd_153094] using wordTrace_append hprefix tailTrace_153094
  have hstable : (prefixWord ++ tailWord_153094).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_153094).length < 2 ^ (prefixWord ++ tailWord_153094).sum := by decide
  have hdescent : baseEnd_153094 < baseStart_153094 := by decide
  rcases family_descends (prefixWord ++ tailWord_153094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_153097 : List Nat := [1, 2, 1, 1, 3, 1, 4, 3, 2, 4]
def baseStart_153097 : Nat := 118140960795 + 153097 * 2 ^ 59
def prefixEnd_153097 : Nat := 4983230072969 + 3 ^ 40 * 153097 * 2
def baseEnd_153097 : Nat := 52408231840995160655617

theorem tailTrace_153097 : CollatzResearch.WordTrace tailWord_153097 prefixEnd_153097 52408231840995160655617 := by
  unfold tailWord_153097
  simp only [CollatzResearch.WordTrace]
  refine ⟨5583906326363190731049545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3722604217575460487366363 5583906326363190731049545)
  ·
    refine ⟨4187929744772393048287159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5583906326363190731049545 4187929744772393048287159)
    ·
      refine ⟨6281894617158589572430739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4187929744772393048287159 6281894617158589572430739)
      ·
        refine ⟨9422841925737884358646109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6281894617158589572430739 9422841925737884358646109)
        ·
          refine ⟨3533565722151706634492291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9422841925737884358646109 3533565722151706634492291)
          ·
            refine ⟨5300348583227559951738437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3533565722151706634492291 5300348583227559951738437)
            ·
              refine ⟨993815359355167490950957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5300348583227559951738437 993815359355167490950957)
              ·
                refine ⟨372680759758187809106609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 993815359355167490950957 372680759758187809106609)
                ·
                  refine ⟨279510569818640856829957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 372680759758187809106609 279510569818640856829957)
                  ·
                    refine ⟨52408231840995160655617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 279510569818640856829957 52408231840995160655617)
                    ·
                      rfl

theorem cell22_153097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 4, 3, 2, 4].length) (baseStart_153097 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_153097 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_153097 prefixEnd_153097 := by exact prefixLift 153097
  have htrace : WordTrace (prefixWord ++ tailWord_153097) baseStart_153097 baseEnd_153097 := by
    simpa [prefixWord, tailWord_153097, baseEnd_153097] using wordTrace_append hprefix tailTrace_153097
  have hstable : (prefixWord ++ tailWord_153097).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_153097).length < 2 ^ (prefixWord ++ tailWord_153097).sum := by decide
  have hdescent : baseEnd_153097 < baseStart_153097 := by decide
  rcases family_descends (prefixWord ++ tailWord_153097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_153189 : List Nat := [1, 3, 1, 3, 3, 2, 1, 1, 2, 5]
def baseStart_153189 : Nat := 118140960795 + 153189 * 2 ^ 59
def prefixEnd_153189 : Nat := 4983230072969 + 3 ^ 40 * 153189 * 2
def baseEnd_153189 : Nat := 52439725321137587355335

theorem tailTrace_153189 : CollatzResearch.WordTrace tailWord_153189 prefixEnd_153189 52439725321137587355335 := by
  unfold tailWord_153189
  simp only [CollatzResearch.WordTrace]
  refine ⟨5587261842029890443398621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3724841228019926962265747 5587261842029890443398621)
  ·
    refine ⟨2095223190761208916274483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5587261842029890443398621 2095223190761208916274483)
    ·
      refine ⟨3142834786141813374411725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2095223190761208916274483 3142834786141813374411725)
      ·
        refine ⟨1178563044803180015404397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3142834786141813374411725 1178563044803180015404397)
        ·
          refine ⟨441961141801192505776649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1178563044803180015404397 441961141801192505776649)
          ·
            refine ⟨331470856350894379332487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 441961141801192505776649 331470856350894379332487)
            ·
              refine ⟨497206284526341568998731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 331470856350894379332487 497206284526341568998731)
              ·
                refine ⟨745809426789512353498097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 497206284526341568998731 745809426789512353498097)
                ·
                  refine ⟨559357070092134265123573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 745809426789512353498097 559357070092134265123573)
                  ·
                    refine ⟨52439725321137587355335, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 559357070092134265123573 52439725321137587355335)
                    ·
                      rfl

theorem cell22_153189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 2, 1, 1, 2, 5].length) (baseStart_153189 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_153189 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_153189 prefixEnd_153189 := by exact prefixLift 153189
  have htrace : WordTrace (prefixWord ++ tailWord_153189) baseStart_153189 baseEnd_153189 := by
    simpa [prefixWord, tailWord_153189, baseEnd_153189] using wordTrace_append hprefix tailTrace_153189
  have hstable : (prefixWord ++ tailWord_153189).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_153189).length < 2 ^ (prefixWord ++ tailWord_153189).sum := by decide
  have hdescent : baseEnd_153189 < baseStart_153189 := by decide
  rcases family_descends (prefixWord ++ tailWord_153189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_153249 : List Nat := [1, 2, 3, 3, 2, 1, 1, 2, 1, 6]
def baseStart_153249 : Nat := 118140960795 + 153249 * 2 ^ 59
def prefixEnd_153249 : Nat := 4983230072969 + 3 ^ 40 * 153249 * 2
def baseEnd_153249 : Nat := 52460264547317430855151

theorem tailTrace_153249 : CollatzResearch.WordTrace tailWord_153249 prefixEnd_153249 52460264547317430855151 := by
  unfold tailWord_153249
  simp only [CollatzResearch.WordTrace]
  refine ⟨5589450221812520690582801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3726300147875013793721867 5589450221812520690582801)
  ·
    refine ⟨4192087666359390517937101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5589450221812520690582801 4192087666359390517937101)
    ·
      refine ⟨1572032874884771444226413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4192087666359390517937101 1572032874884771444226413)
      ·
        refine ⟨589512328081789291584905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1572032874884771444226413 589512328081789291584905)
        ·
          refine ⟨442134246061341968688679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 589512328081789291584905 442134246061341968688679)
          ·
            refine ⟨663201369092012953033019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 442134246061341968688679 663201369092012953033019)
            ·
              refine ⟨994802053638019429549529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 663201369092012953033019 994802053638019429549529)
              ·
                refine ⟨746101540228514572162147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 994802053638019429549529 746101540228514572162147)
                ·
                  refine ⟨1119152310342771858243221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 746101540228514572162147 1119152310342771858243221)
                  ·
                    refine ⟨52460264547317430855151, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1119152310342771858243221 52460264547317430855151)
                    ·
                      rfl

theorem cell22_153249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 1, 2, 1, 6].length) (baseStart_153249 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_153249 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_153249 prefixEnd_153249 := by exact prefixLift 153249
  have htrace : WordTrace (prefixWord ++ tailWord_153249) baseStart_153249 baseEnd_153249 := by
    simpa [prefixWord, tailWord_153249, baseEnd_153249] using wordTrace_append hprefix tailTrace_153249
  have hstable : (prefixWord ++ tailWord_153249).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_153249).length < 2 ^ (prefixWord ++ tailWord_153249).sum := by decide
  have hdescent : baseEnd_153249 < baseStart_153249 := by decide
  rcases family_descends (prefixWord ++ tailWord_153249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_153264 : List Nat := [2, 1, 1, 1, 2, 1, 8, 6]
def baseStart_153264 : Nat := 118140960795 + 153264 * 2 ^ 59
def prefixEnd_153264 : Nat := 4983230072969 + 3 ^ 40 * 153264 * 2
def baseEnd_153264 : Nat := 5829488817095821303345

theorem tailTrace_153264 : CollatzResearch.WordTrace tailWord_153264 prefixEnd_153264 5829488817095821303345 := by
  unfold tailWord_153264
  simp only [CollatzResearch.WordTrace]
  refine ⟨2794998658379089126189423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3726664877838785501585897 2794998658379089126189423)
  ·
    refine ⟨4192497987568633689284135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2794998658379089126189423 4192497987568633689284135)
    ·
      refine ⟨6288746981352950533926203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4192497987568633689284135 6288746981352950533926203)
      ·
        refine ⟨9433120472029425800889305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6288746981352950533926203 9433120472029425800889305)
        ·
          refine ⟨7074840354022069350666979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9433120472029425800889305 7074840354022069350666979)
          ·
            refine ⟨10612260531033104026000469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7074840354022069350666979 10612260531033104026000469)
            ·
              refine ⟨124362428098044187804693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 10612260531033104026000469 124362428098044187804693)
              ·
                refine ⟨5829488817095821303345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 124362428098044187804693 5829488817095821303345)
                ·
                  rfl

theorem cell22_153264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 8, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 8, 6].length) (baseStart_153264 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_153264 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_153264 prefixEnd_153264 := by exact prefixLift 153264
  have htrace : WordTrace (prefixWord ++ tailWord_153264) baseStart_153264 baseEnd_153264 := by
    simpa [prefixWord, tailWord_153264, baseEnd_153264] using wordTrace_append hprefix tailTrace_153264
  have hstable : (prefixWord ++ tailWord_153264).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_153264).length < 2 ^ (prefixWord ++ tailWord_153264).sum := by decide
  have hdescent : baseEnd_153264 < baseStart_153264 := by decide
  rcases family_descends (prefixWord ++ tailWord_153264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_153270 : List Nat := [5, 1, 3, 1, 1, 1, 3, 3, 4]
def baseStart_153270 : Nat := 118140960795 + 153270 * 2 ^ 59
def prefixEnd_153270 : Nat := 4983230072969 + 3 ^ 40 * 153270 * 2
def baseEnd_153270 : Nat := 17489151092160125360029

theorem tailTrace_153270 : CollatzResearch.WordTrace tailWord_153270 prefixEnd_153270 17489151092160125360029 := by
  unfold tailWord_153270
  simp only [CollatzResearch.WordTrace]
  refine ⟨349388509671027579818579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 3726810769824294184731509 349388509671027579818579)
  ·
    refine ⟨524082764506541369727869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 349388509671027579818579 524082764506541369727869)
    ·
      refine ⟨196531036689953013647951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 524082764506541369727869 196531036689953013647951)
      ·
        refine ⟨294796555034929520471927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 196531036689953013647951 294796555034929520471927)
        ·
          refine ⟨442194832552394280707891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 294796555034929520471927 442194832552394280707891)
          ·
            refine ⟨663292248828591421061837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 442194832552394280707891 663292248828591421061837)
            ·
              refine ⟨248734593310721782898189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 663292248828591421061837 248734593310721782898189)
              ·
                refine ⟨93275472491520668586821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 248734593310721782898189 93275472491520668586821)
                ·
                  refine ⟨17489151092160125360029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 93275472491520668586821 17489151092160125360029)
                  ·
                    rfl

theorem cell22_153270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 3, 3, 4].length) (baseStart_153270 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_153270 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_153270 prefixEnd_153270 := by exact prefixLift 153270
  have htrace : WordTrace (prefixWord ++ tailWord_153270) baseStart_153270 baseEnd_153270 := by
    simpa [prefixWord, tailWord_153270, baseEnd_153270] using wordTrace_append hprefix tailTrace_153270
  have hstable : (prefixWord ++ tailWord_153270).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_153270).length < 2 ^ (prefixWord ++ tailWord_153270).sum := by decide
  have hdescent : baseEnd_153270 < baseStart_153270 := by decide
  rcases family_descends (prefixWord ++ tailWord_153270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_153294 : List Nat := [4, 1, 1, 1, 3, 1, 2, 1, 2, 6]
def baseStart_153294 : Nat := 118140960795 + 153294 * 2 ^ 59
def prefixEnd_153294 : Nat := 4983230072969 + 3 ^ 40 * 153294 * 2
def baseEnd_153294 : Nat := 52475668966952313480013

theorem tailTrace_153294 : CollatzResearch.WordTrace tailWord_153294 prefixEnd_153294 52475668966952313480013 := by
  unfold tailWord_153294
  simp only [CollatzResearch.WordTrace]
  refine ⟨698886438331186671996367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3727394337766328917313957 698886438331186671996367)
  ·
    refine ⟨1048329657496780007994551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 698886438331186671996367 1048329657496780007994551)
    ·
      refine ⟨1572494486245170011991827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1048329657496780007994551 1572494486245170011991827)
      ·
        refine ⟨2358741729367755017987741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1572494486245170011991827 2358741729367755017987741)
        ·
          refine ⟨884528148512908131745403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2358741729367755017987741 884528148512908131745403)
          ·
            refine ⟨1326792222769362197618105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 884528148512908131745403 1326792222769362197618105)
            ·
              refine ⟨995094167077021648213579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1326792222769362197618105 995094167077021648213579)
              ·
                refine ⟨1492641250615532472320369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 995094167077021648213579 1492641250615532472320369)
                ·
                  refine ⟨1119480937961649354240277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1492641250615532472320369 1119480937961649354240277)
                  ·
                    refine ⟨52475668966952313480013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1119480937961649354240277 52475668966952313480013)
                    ·
                      rfl

theorem cell22_153294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 2, 1, 2, 6].length) (baseStart_153294 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_153294 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_153294 prefixEnd_153294 := by exact prefixLift 153294
  have htrace : WordTrace (prefixWord ++ tailWord_153294) baseStart_153294 baseEnd_153294 := by
    simpa [prefixWord, tailWord_153294, baseEnd_153294] using wordTrace_append hprefix tailTrace_153294
  have hstable : (prefixWord ++ tailWord_153294).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_153294).length < 2 ^ (prefixWord ++ tailWord_153294).sum := by decide
  have hdescent : baseEnd_153294 < baseStart_153294 := by decide
  rcases family_descends (prefixWord ++ tailWord_153294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_153302 : List Nat := [5, 2, 1, 3, 1, 1, 1, 3, 2, 3]
def baseStart_153302 : Nat := 118140960795 + 153302 * 2 ^ 59
def prefixEnd_153302 : Nat := 4983230072969 + 3 ^ 40 * 153302 * 2
def baseEnd_153302 : Nat := 52478407530442959279989

theorem tailTrace_153302 : CollatzResearch.WordTrace tailWord_153302 prefixEnd_153302 52478407530442959279989 := by
  unfold tailWord_153302
  simp only [CollatzResearch.WordTrace]
  refine ⟨349461455663781921391385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 3727588860413673828174773 349461455663781921391385)
  ·
    refine ⟨262096091747836441043539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 349461455663781921391385 262096091747836441043539)
    ·
      refine ⟨393144137621754661565309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 262096091747836441043539 393144137621754661565309)
      ·
        refine ⟨147429051608157998086991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 393144137621754661565309 147429051608157998086991)
        ·
          refine ⟨221143577412236997130487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 147429051608157998086991 221143577412236997130487)
          ·
            refine ⟨331715366118355495695731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 221143577412236997130487 331715366118355495695731)
            ·
              refine ⟨497573049177533243543597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 331715366118355495695731 497573049177533243543597)
              ·
                refine ⟨186589893441574966328849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 497573049177533243543597 186589893441574966328849)
                ·
                  refine ⟨139942420081181224746637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 186589893441574966328849 139942420081181224746637)
                  ·
                    refine ⟨52478407530442959279989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 139942420081181224746637 52478407530442959279989)
                    ·
                      rfl

theorem cell22_153302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 1, 1, 3, 2, 3].length) (baseStart_153302 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_153302 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_153302 prefixEnd_153302 := by exact prefixLift 153302
  have htrace : WordTrace (prefixWord ++ tailWord_153302) baseStart_153302 baseEnd_153302 := by
    simpa [prefixWord, tailWord_153302, baseEnd_153302] using wordTrace_append hprefix tailTrace_153302
  have hstable : (prefixWord ++ tailWord_153302).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_153302).length < 2 ^ (prefixWord ++ tailWord_153302).sum := by decide
  have hdescent : baseEnd_153302 < baseStart_153302 := by decide
  rcases family_descends (prefixWord ++ tailWord_153302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_153388 : List Nat := [2, 2, 1, 1, 1, 6, 2, 3, 4]
def baseStart_153388 : Nat := 118140960795 + 153388 * 2 ^ 59
def prefixEnd_153388 : Nat := 4983230072969 + 3 ^ 40 * 153388 * 2
def baseEnd_153388 : Nat := 17502615695989133876575

theorem tailTrace_153388 : CollatzResearch.WordTrace tailWord_153388 prefixEnd_153388 17502615695989133876575 := by
  unfold tailWord_153388
  simp only [CollatzResearch.WordTrace]
  refine ⟨2797259984154473714946409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3729679978872631619928545 2797259984154473714946409)
  ·
    refine ⟨2097944988115855286209807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2797259984154473714946409 2097944988115855286209807)
    ·
      refine ⟨3146917482173782929314711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2097944988115855286209807 3146917482173782929314711)
      ·
        refine ⟨4720376223260674393972067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3146917482173782929314711 4720376223260674393972067)
        ·
          refine ⟨7080564334891011590958101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4720376223260674393972067 7080564334891011590958101)
          ·
            refine ⟨331901453198016168326161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 7080564334891011590958101 331901453198016168326161)
            ·
              refine ⟨248926089898512126244621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 331901453198016168326161 248926089898512126244621)
              ·
                refine ⟨93347283711942047341733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 248926089898512126244621 93347283711942047341733)
                ·
                  refine ⟨17502615695989133876575, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 93347283711942047341733 17502615695989133876575)
                  ·
                    rfl

theorem cell22_153388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 6, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 6, 2, 3, 4].length) (baseStart_153388 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_153388 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_153388 prefixEnd_153388 := by exact prefixLift 153388
  have htrace : WordTrace (prefixWord ++ tailWord_153388) baseStart_153388 baseEnd_153388 := by
    simpa [prefixWord, tailWord_153388, baseEnd_153388] using wordTrace_append hprefix tailTrace_153388
  have hstable : (prefixWord ++ tailWord_153388).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_153388).length < 2 ^ (prefixWord ++ tailWord_153388).sum := by decide
  have hdescent : baseEnd_153388 < baseStart_153388 := by decide
  rcases family_descends (prefixWord ++ tailWord_153388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_153390 : List Nat := [4, 1, 3, 2, 2, 1, 1, 3, 1, 4]
def baseStart_153390 : Nat := 118140960795 + 153390 * 2 ^ 59
def prefixEnd_153390 : Nat := 4983230072969 + 3 ^ 40 * 153390 * 2
def baseEnd_153390 : Nat := 52508531728840063079719

theorem tailTrace_153390 : CollatzResearch.WordTrace tailWord_153390 prefixEnd_153390 52508531728840063079719 := by
  unfold tailWord_153390
  simp only [CollatzResearch.WordTrace]
  refine ⟨699324114287712721433203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3729728609534467847643749 699324114287712721433203)
  ·
    refine ⟨1048986171431569082149805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 699324114287712721433203 1048986171431569082149805)
    ·
      refine ⟨393369814286838405806177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1048986171431569082149805 393369814286838405806177)
      ·
        refine ⟨295027360715128804354633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 393369814286838405806177 295027360715128804354633)
        ·
          refine ⟨221270520536346603265975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 295027360715128804354633 221270520536346603265975)
          ·
            refine ⟨331905780804519904898963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 221270520536346603265975 331905780804519904898963)
            ·
              refine ⟨497858671206779857348445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 331905780804519904898963 497858671206779857348445)
              ·
                refine ⟨186697001702542446505667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 497858671206779857348445 186697001702542446505667)
                ·
                  refine ⟨280045502553813669758501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 186697001702542446505667 280045502553813669758501)
                  ·
                    refine ⟨52508531728840063079719, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 280045502553813669758501 52508531728840063079719)
                    ·
                      rfl

theorem cell22_153390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 1, 1, 3, 1, 4].length) (baseStart_153390 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_153390 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_153390 prefixEnd_153390 := by exact prefixLift 153390
  have htrace : WordTrace (prefixWord ++ tailWord_153390) baseStart_153390 baseEnd_153390 := by
    simpa [prefixWord, tailWord_153390, baseEnd_153390] using wordTrace_append hprefix tailTrace_153390
  have hstable : (prefixWord ++ tailWord_153390).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_153390).length < 2 ^ (prefixWord ++ tailWord_153390).sum := by decide
  have hdescent : baseEnd_153390 < baseStart_153390 := by decide
  rcases family_descends (prefixWord ++ tailWord_153390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_153420 : List Nat := [2, 2, 1, 3, 5, 1, 1, 1, 1, 5]
def baseStart_153420 : Nat := 118140960795 + 153420 * 2 ^ 59
def prefixEnd_153420 : Nat := 4983230072969 + 3 ^ 40 * 153420 * 2
def baseEnd_153420 : Nat := 52518801341929984829627

theorem tailTrace_153420 : CollatzResearch.WordTrace tailWord_153420 prefixEnd_153420 52518801341929984829627 := by
  unfold tailWord_153420
  simp only [CollatzResearch.WordTrace]
  refine ⟨2797843552096508447528857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3730458069462011263371809 2797843552096508447528857)
  ·
    refine ⟨2098382664072381335646643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2797843552096508447528857 2098382664072381335646643)
    ·
      refine ⟨3147573996108572003469965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2098382664072381335646643 3147573996108572003469965)
      ·
        refine ⟨1180340248540714501301237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3147573996108572003469965 1180340248540714501301237)
        ·
          refine ⟨110656898300691984496991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 1180340248540714501301237 110656898300691984496991)
          ·
            refine ⟨165985347451037976745487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 110656898300691984496991 165985347451037976745487)
            ·
              refine ⟨248978021176556965118231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 165985347451037976745487 248978021176556965118231)
              ·
                refine ⟨373467031764835447677347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 248978021176556965118231 373467031764835447677347)
                ·
                  refine ⟨560200547647253171516021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 373467031764835447677347 560200547647253171516021)
                  ·
                    refine ⟨52518801341929984829627, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 560200547647253171516021 52518801341929984829627)
                    ·
                      rfl

theorem cell22_153420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 5, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 5, 1, 1, 1, 1, 5].length) (baseStart_153420 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_153420 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_153420 prefixEnd_153420 := by exact prefixLift 153420
  have htrace : WordTrace (prefixWord ++ tailWord_153420) baseStart_153420 baseEnd_153420 := by
    simpa [prefixWord, tailWord_153420, baseEnd_153420] using wordTrace_append hprefix tailTrace_153420
  have hstable : (prefixWord ++ tailWord_153420).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_153420).length < 2 ^ (prefixWord ++ tailWord_153420).sum := by decide
  have hdescent : baseEnd_153420 < baseStart_153420 := by decide
  rcases family_descends (prefixWord ++ tailWord_153420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_153450 : List Nat := [3, 1, 3, 4, 2, 1, 8]
def baseStart_153450 : Nat := 118140960795 + 153450 * 2 ^ 59
def prefixEnd_153450 : Nat := 4983230072969 + 3 ^ 40 * 153450 * 2
def baseEnd_153450 : Nat := 1945521146482218762205

theorem tailTrace_153450 : CollatzResearch.WordTrace tailWord_153450 prefixEnd_153450 1945521146482218762205 := by
  unfold tailWord_153450
  simp only [CollatzResearch.WordTrace]
  refine ⟨1399195323521083004662451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3731187529389554679099869 1399195323521083004662451)
  ·
    refine ⟨2098792985281624506993677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1399195323521083004662451 2098792985281624506993677)
    ·
      refine ⟨787047369480609190122629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2098792985281624506993677 787047369480609190122629)
      ·
        refine ⟨147571381777614223147993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 787047369480609190122629 147571381777614223147993)
        ·
          refine ⟨110678536333210667360995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 147571381777614223147993 110678536333210667360995)
          ·
            refine ⟨166017804499816001041493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 110678536333210667360995 166017804499816001041493)
            ·
              refine ⟨1945521146482218762205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 166017804499816001041493 1945521146482218762205)
              ·
                rfl

theorem cell22_153450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 2, 1, 8].length) (baseStart_153450 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_153450 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_153450 prefixEnd_153450 := by exact prefixLift 153450
  have htrace : WordTrace (prefixWord ++ tailWord_153450) baseStart_153450 baseEnd_153450 := by
    simpa [prefixWord, tailWord_153450, baseEnd_153450] using wordTrace_append hprefix tailTrace_153450
  have hstable : (prefixWord ++ tailWord_153450).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_153450).length < 2 ^ (prefixWord ++ tailWord_153450).sum := by decide
  have hdescent : baseEnd_153450 < baseStart_153450 := by decide
  rcases family_descends (prefixWord ++ tailWord_153450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_153461 : List Nat := [1, 3, 4, 1, 1, 1, 1, 3, 7]
def baseStart_153461 : Nat := 118140960795 + 153461 * 2 ^ 59
def prefixEnd_153461 : Nat := 4983230072969 + 3 ^ 40 * 153461 * 2
def baseEnd_153461 : Nat := 17510945493273181518167

theorem tailTrace_153461 : CollatzResearch.WordTrace tailWord_153461 prefixEnd_153461 17510945493273181518167 := by
  unfold tailWord_153461
  simp only [CollatzResearch.WordTrace]
  refine ⟨5597182497044480897300237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3731454998029653931533491 5597182497044480897300237)
  ·
    refine ⟨2098943436391680336487589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5597182497044480897300237 2098943436391680336487589)
    ·
      refine ⟨393551894323440063091423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2098943436391680336487589 393551894323440063091423)
      ·
        refine ⟨590327841485160094637135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 393551894323440063091423 590327841485160094637135)
        ·
          refine ⟨885491762227740141955703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 590327841485160094637135 885491762227740141955703)
          ·
            refine ⟨1328237643341610212933555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 885491762227740141955703 1328237643341610212933555)
            ·
              refine ⟨1992356465012415319400333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1328237643341610212933555 1992356465012415319400333)
              ·
                refine ⟨747133674379655744775125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1992356465012415319400333 747133674379655744775125)
                ·
                  refine ⟨17510945493273181518167, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 747133674379655744775125 17510945493273181518167)
                  ·
                    rfl

theorem cell22_153461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 1, 3, 7].length) (baseStart_153461 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_153461 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_153461 prefixEnd_153461 := by exact prefixLift 153461
  have htrace : WordTrace (prefixWord ++ tailWord_153461) baseStart_153461 baseEnd_153461 := by
    simpa [prefixWord, tailWord_153461, baseEnd_153461] using wordTrace_append hprefix tailTrace_153461
  have hstable : (prefixWord ++ tailWord_153461).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_153461).length < 2 ^ (prefixWord ++ tailWord_153461).sum := by decide
  have hdescent : baseEnd_153461 < baseStart_153461 := by decide
  rcases family_descends (prefixWord ++ tailWord_153461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_153476 : List Nat := [2, 3, 2, 1, 1, 1, 2, 3, 2, 5]
def baseStart_153476 : Nat := 118140960795 + 153476 * 2 ^ 59
def prefixEnd_153476 : Nat := 4983230072969 + 3 ^ 40 * 153476 * 2
def baseEnd_153476 : Nat := 52537971286364505429455

theorem tailTrace_153476 : CollatzResearch.WordTrace tailWord_153476 prefixEnd_153476 52537971286364505429455 := by
  unfold tailWord_153476
  simp only [CollatzResearch.WordTrace]
  refine ⟨2798864795995069229548141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3731819727993425639397521 2798864795995069229548141)
  ·
    refine ⟨1049574298498150961080553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2798864795995069229548141 1049574298498150961080553)
    ·
      refine ⟨787180723873613220810415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1049574298498150961080553 787180723873613220810415)
      ·
        refine ⟨1180771085810419831215623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 787180723873613220810415 1180771085810419831215623)
        ·
          refine ⟨1771156628715629746823435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1180771085810419831215623 1771156628715629746823435)
          ·
            refine ⟨2656734943073444620235153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1771156628715629746823435 2656734943073444620235153)
            ·
              refine ⟨1992551207305083465176365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2656734943073444620235153 1992551207305083465176365)
              ·
                refine ⟨747206702739406299441137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1992551207305083465176365 747206702739406299441137)
                ·
                  refine ⟨560405027054554724580853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 747206702739406299441137 560405027054554724580853)
                  ·
                    refine ⟨52537971286364505429455, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 560405027054554724580853 52537971286364505429455)
                    ·
                      rfl

theorem cell22_153476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 2, 3, 2, 5].length) (baseStart_153476 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_153476 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_153476 prefixEnd_153476 := by exact prefixLift 153476
  have htrace : WordTrace (prefixWord ++ tailWord_153476) baseStart_153476 baseEnd_153476 := by
    simpa [prefixWord, tailWord_153476, baseEnd_153476] using wordTrace_append hprefix tailTrace_153476
  have hstable : (prefixWord ++ tailWord_153476).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_153476).length < 2 ^ (prefixWord ++ tailWord_153476).sum := by decide
  have hdescent : baseEnd_153476 < baseStart_153476 := by decide
  rcases family_descends (prefixWord ++ tailWord_153476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_153512 : List Nat := [2, 1, 6, 2, 1, 1, 2, 2, 5]
def baseStart_153512 : Nat := 118140960795 + 153512 * 2 ^ 59
def prefixEnd_153512 : Nat := 4983230072969 + 3 ^ 40 * 153512 * 2
def baseEnd_153512 : Nat := 17516764940690803843115

theorem tailTrace_153512 : CollatzResearch.WordTrace tailWord_153512 prefixEnd_153512 17516764940690803843115 := by
  unfold tailWord_153512
  simp only [CollatzResearch.WordTrace]
  refine ⟨2799521309929858303703395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3732695079906477738271193 2799521309929858303703395)
  ·
    refine ⟨4199281964894787455555093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2799521309929858303703395 4199281964894787455555093)
    ·
      refine ⟨196841342104443161979145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 4199281964894787455555093 196841342104443161979145)
      ·
        refine ⟨147631006578332371484359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 196841342104443161979145 147631006578332371484359)
        ·
          refine ⟨221446509867498557226539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 147631006578332371484359 221446509867498557226539)
          ·
            refine ⟨332169764801247835839809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 221446509867498557226539 332169764801247835839809)
            ·
              refine ⟨249127323600935876879857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 332169764801247835839809 249127323600935876879857)
              ·
                refine ⟨186845492700701907659893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 249127323600935876879857 186845492700701907659893)
                ·
                  refine ⟨17516764940690803843115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 186845492700701907659893 17516764940690803843115)
                  ·
                    rfl

theorem cell22_153512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 1, 2, 2, 5].length) (baseStart_153512 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_153512 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_153512 prefixEnd_153512 := by exact prefixLift 153512
  have htrace : WordTrace (prefixWord ++ tailWord_153512) baseStart_153512 baseEnd_153512 := by
    simpa [prefixWord, tailWord_153512, baseEnd_153512] using wordTrace_append hprefix tailTrace_153512
  have hstable : (prefixWord ++ tailWord_153512).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_153512).length < 2 ^ (prefixWord ++ tailWord_153512).sum := by decide
  have hdescent : baseEnd_153512 < baseStart_153512 := by decide
  rcases family_descends (prefixWord ++ tailWord_153512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_153523 : List Nat := [1, 1, 1, 2, 3, 1, 5, 4, 4]
def baseStart_153523 : Nat := 118140960795 + 153523 * 2 ^ 59
def prefixEnd_153523 : Nat := 4983230072969 + 3 ^ 40 * 153523 * 2
def baseEnd_153523 : Nat := 17518020115624016501437

theorem tailTrace_153523 : CollatzResearch.WordTrace tailWord_153523 prefixEnd_153523 17518020115624016501437 := by
  unfold tailWord_153523
  simp only [CollatzResearch.WordTrace]
  refine ⟨5599443822819865486057223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3732962548546576990704815 5599443822819865486057223)
  ·
    refine ⟨8399165734229798229085835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5599443822819865486057223 8399165734229798229085835)
    ·
      refine ⟨12598748601344697343628753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8399165734229798229085835 12598748601344697343628753)
      ·
        refine ⟨9449061451008523007721565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12598748601344697343628753 9449061451008523007721565)
        ·
          refine ⟨3543398044128196127895587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9449061451008523007721565 3543398044128196127895587)
          ·
            refine ⟨5315097066192294191843381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3543398044128196127895587 5315097066192294191843381)
            ·
              refine ⟨498290349955527580485317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 5315097066192294191843381 498290349955527580485317)
              ·
                refine ⟨93429440616661421340997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 498290349955527580485317 93429440616661421340997)
                ·
                  refine ⟨17518020115624016501437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 93429440616661421340997 17518020115624016501437)
                  ·
                    rfl

theorem cell22_153523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 5, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 5, 4, 4].length) (baseStart_153523 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_153523 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_153523 prefixEnd_153523 := by exact prefixLift 153523
  have htrace : WordTrace (prefixWord ++ tailWord_153523) baseStart_153523 baseEnd_153523 := by
    simpa [prefixWord, tailWord_153523, baseEnd_153523] using wordTrace_append hprefix tailTrace_153523
  have hstable : (prefixWord ++ tailWord_153523).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_153523).length < 2 ^ (prefixWord ++ tailWord_153523).sum := by decide
  have hdescent : baseEnd_153523 < baseStart_153523 := by decide
  rcases family_descends (prefixWord ++ tailWord_153523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_153536 : List Nat := [2, 1, 1, 2, 3, 2, 2, 2, 1, 6]
def baseStart_153536 : Nat := 118140960795 + 153536 * 2 ^ 59
def prefixEnd_153536 : Nat := 4983230072969 + 3 ^ 40 * 153536 * 2
def baseEnd_153536 : Nat := 52558510512544348929271

theorem tailTrace_153536 : CollatzResearch.WordTrace tailWord_153536 prefixEnd_153536 52558510512544348929271 := by
  unfold tailWord_153536
  simp only [CollatzResearch.WordTrace]
  refine ⟨2799958985886384353140231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3733278647848512470853641 2799958985886384353140231)
  ·
    refine ⟨4199938478829576529710347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2799958985886384353140231 4199938478829576529710347)
    ·
      refine ⟨6299907718244364794565521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4199938478829576529710347 6299907718244364794565521)
      ·
        refine ⟨4724930788683273595924141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6299907718244364794565521 4724930788683273595924141)
        ·
          refine ⟨1771849045756227598471553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4724930788683273595924141 1771849045756227598471553)
          ·
            refine ⟨1328886784317170698853665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1771849045756227598471553 1328886784317170698853665)
            ·
              refine ⟨996665088237878024140249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1328886784317170698853665 996665088237878024140249)
              ·
                refine ⟨747498816178408518105187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 996665088237878024140249 747498816178408518105187)
                ·
                  refine ⟨1121248224267612777157781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 747498816178408518105187 1121248224267612777157781)
                  ·
                    refine ⟨52558510512544348929271, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1121248224267612777157781 52558510512544348929271)
                    ·
                      rfl

theorem cell22_153536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 2, 2, 1, 6].length) (baseStart_153536 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_153536 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_153536 prefixEnd_153536 := by exact prefixLift 153536
  have htrace : WordTrace (prefixWord ++ tailWord_153536) baseStart_153536 baseEnd_153536 := by
    simpa [prefixWord, tailWord_153536, baseEnd_153536] using wordTrace_append hprefix tailTrace_153536
  have hstable : (prefixWord ++ tailWord_153536).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_153536).length < 2 ^ (prefixWord ++ tailWord_153536).sum := by decide
  have hdescent : baseEnd_153536 < baseStart_153536 := by decide
  rcases family_descends (prefixWord ++ tailWord_153536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_153634 : List Nat := [3, 3, 1, 1, 1, 2, 5, 2, 1, 3]
def baseStart_153634 : Nat := 118140960795 + 153634 * 2 ^ 59
def prefixEnd_153634 : Nat := 4983230072969 + 3 ^ 40 * 153634 * 2
def baseEnd_153634 : Nat := 52592057915304759978971

theorem tailTrace_153634 : CollatzResearch.WordTrace tailWord_153634 prefixEnd_153634 52592057915304759978971 := by
  unfold tailWord_153634
  simp only [CollatzResearch.WordTrace]
  refine ⟨1400873081354432860836989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3735661550278487628898637 1400873081354432860836989)
  ·
    refine ⟨525327405507912322813871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1400873081354432860836989 525327405507912322813871)
    ·
      refine ⟨787991108261868484220807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 525327405507912322813871 787991108261868484220807)
      ·
        refine ⟨1181986662392802726331211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 787991108261868484220807 1181986662392802726331211)
        ·
          refine ⟨1772979993589204089496817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1181986662392802726331211 1772979993589204089496817)
          ·
            refine ⟨1329734995191903067122613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1772979993589204089496817 1329734995191903067122613)
            ·
              refine ⟨124662655799240912542745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1329734995191903067122613 124662655799240912542745)
              ·
                refine ⟨93496991849430684407059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 124662655799240912542745 93496991849430684407059)
                ·
                  refine ⟨140245487774146026610589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 93496991849430684407059 140245487774146026610589)
                  ·
                    refine ⟨52592057915304759978971, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 140245487774146026610589 52592057915304759978971)
                    ·
                      rfl

theorem cell22_153634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 5, 2, 1, 3].length) (baseStart_153634 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_153634 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_153634 prefixEnd_153634 := by exact prefixLift 153634
  have htrace : WordTrace (prefixWord ++ tailWord_153634) baseStart_153634 baseEnd_153634 := by
    simpa [prefixWord, tailWord_153634, baseEnd_153634] using wordTrace_append hprefix tailTrace_153634
  have hstable : (prefixWord ++ tailWord_153634).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_153634).length < 2 ^ (prefixWord ++ tailWord_153634).sum := by decide
  have hdescent : baseEnd_153634 < baseStart_153634 := by decide
  rcases family_descends (prefixWord ++ tailWord_153634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_153673 : List Nat := [1, 2, 1, 1, 2, 2, 5, 2, 1, 5]
def baseStart_153673 : Nat := 118140960795 + 153673 * 2 ^ 59
def prefixEnd_153673 : Nat := 4983230072969 + 3 ^ 40 * 153673 * 2
def baseEnd_153673 : Nat := 52605408412321658253851

theorem tailTrace_153673 : CollatzResearch.WordTrace tailWord_153673 prefixEnd_153673 52605408412321658253851 := by
  unfold tailWord_153673
  simp only [CollatzResearch.WordTrace]
  refine ⟨5604914772276441104017673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3736609848184294069345115 5604914772276441104017673)
  ·
    refine ⟨4203686079207330828013255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5604914772276441104017673 4203686079207330828013255)
    ·
      refine ⟨6305529118810996242019883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4203686079207330828013255 6305529118810996242019883)
      ·
        refine ⟨9458293678216494363029825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6305529118810996242019883 9458293678216494363029825)
        ·
          refine ⟨7093720258662370772272369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9458293678216494363029825 7093720258662370772272369)
          ·
            refine ⟨5320290193996778079204277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7093720258662370772272369 5320290193996778079204277)
            ·
              refine ⟨498777205687197944925401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 5320290193996778079204277 498777205687197944925401)
              ·
                refine ⟨374082904265398458694051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 498777205687197944925401 374082904265398458694051)
                ·
                  refine ⟨561124356398097688041077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 374082904265398458694051 561124356398097688041077)
                  ·
                    refine ⟨52605408412321658253851, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 561124356398097688041077 52605408412321658253851)
                    ·
                      rfl

theorem cell22_153673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 5, 2, 1, 5].length) (baseStart_153673 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_153673 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_153673 prefixEnd_153673 := by exact prefixLift 153673
  have htrace : WordTrace (prefixWord ++ tailWord_153673) baseStart_153673 baseEnd_153673 := by
    simpa [prefixWord, tailWord_153673, baseEnd_153673] using wordTrace_append hprefix tailTrace_153673
  have hstable : (prefixWord ++ tailWord_153673).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_153673).length < 2 ^ (prefixWord ++ tailWord_153673).sum := by decide
  have hdescent : baseEnd_153673 < baseStart_153673 := by decide
  rcases family_descends (prefixWord ++ tailWord_153673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_153692 : List Nat := [2, 2, 4, 1, 1, 3, 1, 4, 4]
def baseStart_153692 : Nat := 118140960795 + 153692 * 2 ^ 59
def prefixEnd_153692 : Nat := 4983230072969 + 3 ^ 40 * 153692 * 2
def baseEnd_153692 : Nat := 17537304166870647342931

theorem tailTrace_153692 : CollatzResearch.WordTrace tailWord_153692 prefixEnd_153692 17537304166870647342931 := by
  unfold tailWord_153692
  simp only [CollatzResearch.WordTrace]
  refine ⟨2802803879603803674479665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3737071839471738232639553 2802803879603803674479665)
  ·
    refine ⟨2102102909702852755859749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2802803879603803674479665 2102102909702852755859749)
    ·
      refine ⟨394144295569284891723703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2102102909702852755859749 394144295569284891723703)
      ·
        refine ⟨591216443353927337585555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 394144295569284891723703 591216443353927337585555)
        ·
          refine ⟨886824665030891006378333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 591216443353927337585555 886824665030891006378333)
          ·
            refine ⟨332559249386584127391875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 886824665030891006378333 332559249386584127391875)
            ·
              refine ⟨498838874079876191087813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 332559249386584127391875 498838874079876191087813)
              ·
                refine ⟨93532288889976785828965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 498838874079876191087813 93532288889976785828965)
                ·
                  refine ⟨17537304166870647342931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 93532288889976785828965 17537304166870647342931)
                  ·
                    rfl

theorem cell22_153692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 3, 1, 4, 4].length) (baseStart_153692 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_153692 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_153692 prefixEnd_153692 := by exact prefixLift 153692
  have htrace : WordTrace (prefixWord ++ tailWord_153692) baseStart_153692 baseEnd_153692 := by
    simpa [prefixWord, tailWord_153692, baseEnd_153692] using wordTrace_append hprefix tailTrace_153692
  have hstable : (prefixWord ++ tailWord_153692).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_153692).length < 2 ^ (prefixWord ++ tailWord_153692).sum := by decide
  have hdescent : baseEnd_153692 < baseStart_153692 := by decide
  rcases family_descends (prefixWord ++ tailWord_153692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_153825 : List Nat := [1, 2, 3, 1, 3, 1, 2, 3, 1, 5]
def baseStart_153825 : Nat := 118140960795 + 153825 * 2 ^ 59
def prefixEnd_153825 : Nat := 4983230072969 + 3 ^ 40 * 153825 * 2
def baseEnd_153825 : Nat := 52657441118643928453385

theorem tailTrace_153825 : CollatzResearch.WordTrace tailWord_153825 prefixEnd_153825 52657441118643928453385 := by
  unfold tailWord_153825
  simp only [CollatzResearch.WordTrace]
  refine ⟨5610458667725771063550929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3740305778483847375700619 5610458667725771063550929)
  ·
    refine ⟨4207844000794328297663197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5610458667725771063550929 4207844000794328297663197)
    ·
      refine ⟨1577941500297873111623699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4207844000794328297663197 1577941500297873111623699)
      ·
        refine ⟨2366912250446809667435549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1577941500297873111623699 2366912250446809667435549)
        ·
          refine ⟨887592093917553625288331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2366912250446809667435549 887592093917553625288331)
          ·
            refine ⟨1331388140876330437932497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 887592093917553625288331 1331388140876330437932497)
            ·
              refine ⟨998541105657247828449373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1331388140876330437932497 998541105657247828449373)
              ·
                refine ⟨374452914621467935668515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 998541105657247828449373 374452914621467935668515)
                ·
                  refine ⟨561679371932201903502773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 374452914621467935668515 561679371932201903502773)
                  ·
                    refine ⟨52657441118643928453385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 561679371932201903502773 52657441118643928453385)
                    ·
                      rfl

theorem cell22_153825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 2, 3, 1, 5].length) (baseStart_153825 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_153825 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_153825 prefixEnd_153825 := by exact prefixLift 153825
  have htrace : WordTrace (prefixWord ++ tailWord_153825) baseStart_153825 baseEnd_153825 := by
    simpa [prefixWord, tailWord_153825, baseEnd_153825] using wordTrace_append hprefix tailTrace_153825
  have hstable : (prefixWord ++ tailWord_153825).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_153825).length < 2 ^ (prefixWord ++ tailWord_153825).sum := by decide
  have hdescent : baseEnd_153825 < baseStart_153825 := by decide
  rcases family_descends (prefixWord ++ tailWord_153825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_153829 : List Nat := [1, 3, 1, 4, 2, 3, 1, 2, 1, 4]
def baseStart_153829 : Nat := 118140960795 + 153829 * 2 ^ 59
def prefixEnd_153829 : Nat := 4983230072969 + 3 ^ 40 * 153829 * 2
def baseEnd_153829 : Nat := 52658810400389251353373

theorem tailTrace_153829 : CollatzResearch.WordTrace tailWord_153829 prefixEnd_153829 52658810400389251353373 := by
  unfold tailWord_153829
  simp only [CollatzResearch.WordTrace]
  refine ⟨5610604559711279746696541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3740403039807519831131027 5610604559711279746696541)
  ·
    refine ⟨2103976709891729905011203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5610604559711279746696541 2103976709891729905011203)
    ·
      refine ⟨3155965064837594857516805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2103976709891729905011203 3155965064837594857516805)
      ·
        refine ⟨591743449657049035784401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3155965064837594857516805 591743449657049035784401)
        ·
          refine ⟨443807587242786776838301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 591743449657049035784401 443807587242786776838301)
          ·
            refine ⟨166427845216045041314363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 443807587242786776838301 166427845216045041314363)
            ·
              refine ⟨249641767824067561971545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 166427845216045041314363 249641767824067561971545)
              ·
                refine ⟨187231325868050671478659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 249641767824067561971545 187231325868050671478659)
                ·
                  refine ⟨280846988802076007217989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 187231325868050671478659 280846988802076007217989)
                  ·
                    refine ⟨52658810400389251353373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 280846988802076007217989 52658810400389251353373)
                    ·
                      rfl

theorem cell22_153829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 3, 1, 2, 1, 4].length) (baseStart_153829 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_153829 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_153829 prefixEnd_153829 := by exact prefixLift 153829
  have htrace : WordTrace (prefixWord ++ tailWord_153829) baseStart_153829 baseEnd_153829 := by
    simpa [prefixWord, tailWord_153829, baseEnd_153829] using wordTrace_append hprefix tailTrace_153829
  have hstable : (prefixWord ++ tailWord_153829).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_153829).length < 2 ^ (prefixWord ++ tailWord_153829).sum := by decide
  have hdescent : baseEnd_153829 < baseStart_153829 := by decide
  rcases family_descends (prefixWord ++ tailWord_153829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_153842 : List Nat := [3, 2, 1, 3, 2, 2, 1, 2, 1, 5]
def baseStart_153842 : Nat := 118140960795 + 153842 * 2 ^ 59
def prefixEnd_153842 : Nat := 4983230072969 + 3 ^ 40 * 153842 * 2
def baseEnd_153842 : Nat := 52663260566061550778333

theorem tailTrace_153842 : CollatzResearch.WordTrace tailWord_153842 prefixEnd_153842 52663260566061550778333 := by
  unfold tailWord_153842
  simp only [CollatzResearch.WordTrace]
  refine ⟨1402769677166045741729945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3740719139109455311279853 1402769677166045741729945)
  ·
    refine ⟨1052077257874534306297459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1402769677166045741729945 1052077257874534306297459)
    ·
      refine ⟨1578115886811801459446189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1052077257874534306297459 1578115886811801459446189)
      ·
        refine ⟨591793457554425547292321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1578115886811801459446189 591793457554425547292321)
        ·
          refine ⟨443845093165819160469241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 591793457554425547292321 443845093165819160469241)
          ·
            refine ⟨332883819874364370351931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 443845093165819160469241 332883819874364370351931)
            ·
              refine ⟨499325729811546555527897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 332883819874364370351931 499325729811546555527897)
              ·
                refine ⟨374494297358659916645923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 499325729811546555527897 374494297358659916645923)
                ·
                  refine ⟨561741446037989874968885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 374494297358659916645923 561741446037989874968885)
                  ·
                    refine ⟨52663260566061550778333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 561741446037989874968885 52663260566061550778333)
                    ·
                      rfl

theorem cell22_153842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 2, 1, 2, 1, 5].length) (baseStart_153842 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_153842 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_153842 prefixEnd_153842 := by exact prefixLift 153842
  have htrace : WordTrace (prefixWord ++ tailWord_153842) baseStart_153842 baseEnd_153842 := by
    simpa [prefixWord, tailWord_153842, baseEnd_153842] using wordTrace_append hprefix tailTrace_153842
  have hstable : (prefixWord ++ tailWord_153842).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_153842).length < 2 ^ (prefixWord ++ tailWord_153842).sum := by decide
  have hdescent : baseEnd_153842 < baseStart_153842 := by decide
  rcases family_descends (prefixWord ++ tailWord_153842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_153887 : List Nat := [1, 1, 2, 4, 3, 1, 1, 1, 5, 3]
def baseStart_153887 : Nat := 118140960795 + 153887 * 2 ^ 59
def prefixEnd_153887 : Nat := 4983230072969 + 3 ^ 40 * 153887 * 2
def baseEnd_153887 : Nat := 52678664985696433403195

theorem tailTrace_153887 : CollatzResearch.WordTrace tailWord_153887 prefixEnd_153887 52678664985696433403195 := by
  unfold tailWord_153887
  simp only [CollatzResearch.WordTrace]
  refine ⟨5612719993501155652307915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3741813329000770434871943 5612719993501155652307915)
  ·
    refine ⟨8419079990251733478461873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5612719993501155652307915 8419079990251733478461873)
    ·
      refine ⟨6314309992688800108846405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8419079990251733478461873 6314309992688800108846405)
      ·
        refine ⟨1183933123629150020408701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6314309992688800108846405 1183933123629150020408701)
        ·
          refine ⟨443974921360931257653263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1183933123629150020408701 443974921360931257653263)
          ·
            refine ⟨665962382041396886479895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 443974921360931257653263 665962382041396886479895)
            ·
              refine ⟨998943573062095329719843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 665962382041396886479895 998943573062095329719843)
              ·
                refine ⟨1498415359593142994579765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 998943573062095329719843 1498415359593142994579765)
                ·
                  refine ⟨140476439961857155741853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1498415359593142994579765 140476439961857155741853)
                  ·
                    refine ⟨52678664985696433403195, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 140476439961857155741853 52678664985696433403195)
                    ·
                      rfl

theorem cell22_153887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 1, 1, 5, 3].length) (baseStart_153887 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_153887 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_153887 prefixEnd_153887 := by exact prefixLift 153887
  have htrace : WordTrace (prefixWord ++ tailWord_153887) baseStart_153887 baseEnd_153887 := by
    simpa [prefixWord, tailWord_153887, baseEnd_153887] using wordTrace_append hprefix tailTrace_153887
  have hstable : (prefixWord ++ tailWord_153887).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_153887).length < 2 ^ (prefixWord ++ tailWord_153887).sum := by decide
  have hdescent : baseEnd_153887 < baseStart_153887 := by decide
  rcases family_descends (prefixWord ++ tailWord_153887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_153921 : List Nat := [1, 2, 5, 2, 2, 1, 2, 1, 3, 3]
def baseStart_153921 : Nat := 118140960795 + 153921 * 2 ^ 59
def prefixEnd_153921 : Nat := 4983230072969 + 3 ^ 40 * 153921 * 2
def baseEnd_153921 : Nat := 52690303880531678053091

theorem tailTrace_153921 : CollatzResearch.WordTrace tailWord_153921 prefixEnd_153921 52690303880531678053091 := by
  unfold tailWord_153921
  simp only [CollatzResearch.WordTrace]
  refine ⟨5613960075377979459045617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3742640050251986306030411 5613960075377979459045617)
  ·
    refine ⟨4210470056533484594284213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5613960075377979459045617 4210470056533484594284213)
    ·
      refine ⟨394731567800014180714145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 4210470056533484594284213 394731567800014180714145)
      ·
        refine ⟨296048675850010635535609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 394731567800014180714145 296048675850010635535609)
        ·
          refine ⟨222036506887507976651707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 296048675850010635535609 222036506887507976651707)
          ·
            refine ⟨333054760331261964977561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 222036506887507976651707 333054760331261964977561)
            ·
              refine ⟨249791070248446473733171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 333054760331261964977561 249791070248446473733171)
              ·
                refine ⟨374686605372669710599757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 249791070248446473733171 374686605372669710599757)
                ·
                  refine ⟨140507477014751141474909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 374686605372669710599757 140507477014751141474909)
                  ·
                    refine ⟨52690303880531678053091, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 140507477014751141474909 52690303880531678053091)
                    ·
                      rfl

theorem cell22_153921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 1, 2, 1, 3, 3].length) (baseStart_153921 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_153921 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_153921 prefixEnd_153921 := by exact prefixLift 153921
  have htrace : WordTrace (prefixWord ++ tailWord_153921) baseStart_153921 baseEnd_153921 := by
    simpa [prefixWord, tailWord_153921, baseEnd_153921] using wordTrace_append hprefix tailTrace_153921
  have hstable : (prefixWord ++ tailWord_153921).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_153921).length < 2 ^ (prefixWord ++ tailWord_153921).sum := by decide
  have hdescent : baseEnd_153921 < baseStart_153921 := by decide
  rcases family_descends (prefixWord ++ tailWord_153921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_153975 : List Nat := [1, 1, 3, 1, 1, 2, 2, 2, 3, 6]
def baseStart_153975 : Nat := 118140960795 + 153975 * 2 ^ 59
def prefixEnd_153975 : Nat := 4983230072969 + 3 ^ 40 * 153975 * 2
def baseEnd_153975 : Nat := 52708789184093537202925

theorem tailTrace_153975 : CollatzResearch.WordTrace tailWord_153975 prefixEnd_153975 52708789184093537202925 := by
  unfold tailWord_153975
  simp only [CollatzResearch.WordTrace]
  refine ⟨5615929617182346681511379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3743953078121564454340919 5615929617182346681511379)
  ·
    refine ⟨8423894425773520022267069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5615929617182346681511379 8423894425773520022267069)
    ·
      refine ⟨3158960409665070008350151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8423894425773520022267069 3158960409665070008350151)
      ·
        refine ⟨4738440614497605012525227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3158960409665070008350151 4738440614497605012525227)
        ·
          refine ⟨7107660921746407518787841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4738440614497605012525227 7107660921746407518787841)
          ·
            refine ⟨5330745691309805639090881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7107660921746407518787841 5330745691309805639090881)
            ·
              refine ⟨3998059268482354229318161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5330745691309805639090881 3998059268482354229318161)
              ·
                refine ⟨2998544451361765671988621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3998059268482354229318161 2998544451361765671988621)
                ·
                  refine ⟨1124454169260662126995733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2998544451361765671988621 1124454169260662126995733)
                  ·
                    refine ⟨52708789184093537202925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1124454169260662126995733 52708789184093537202925)
                    ·
                      rfl

theorem cell22_153975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 2, 3, 6].length) (baseStart_153975 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_153975 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_153975 prefixEnd_153975 := by exact prefixLift 153975
  have htrace : WordTrace (prefixWord ++ tailWord_153975) baseStart_153975 baseEnd_153975 := by
    simpa [prefixWord, tailWord_153975, baseEnd_153975] using wordTrace_append hprefix tailTrace_153975
  have hstable : (prefixWord ++ tailWord_153975).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_153975).length < 2 ^ (prefixWord ++ tailWord_153975).sum := by decide
  have hdescent : baseEnd_153975 < baseStart_153975 := by decide
  rcases family_descends (prefixWord ++ tailWord_153975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_153992 : List Nat := [2, 1, 3, 3, 1, 1, 1, 2, 4, 4]
def baseStart_153992 : Nat := 118140960795 + 153992 * 2 ^ 59
def prefixEnd_153992 : Nat := 4983230072969 + 3 ^ 40 * 153992 * 2
def baseEnd_153992 : Nat := 52714608631511159527873

theorem tailTrace_153992 : CollatzResearch.WordTrace tailWord_153992 prefixEnd_153992 52714608631511159527873 := by
  unfold tailWord_153992
  simp only [CollatzResearch.WordTrace]
  refine ⟨2808274829060379292440115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3744366438747172389920153 2808274829060379292440115)
  ·
    refine ⟨4212412243590568938660173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2808274829060379292440115 4212412243590568938660173)
    ·
      refine ⟨1579654591346463351997565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4212412243590568938660173 1579654591346463351997565)
      ·
        refine ⟨592370471754923756999087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1579654591346463351997565 592370471754923756999087)
        ·
          refine ⟨888555707632385635498631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 592370471754923756999087 888555707632385635498631)
          ·
            refine ⟨1332833561448578453247947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 888555707632385635498631 1332833561448578453247947)
            ·
              refine ⟨1999250342172867679871921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1332833561448578453247947 1999250342172867679871921)
              ·
                refine ⟨1499437756629650759903941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1999250342172867679871921 1499437756629650759903941)
                ·
                  refine ⟨281144579368059517481989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1499437756629650759903941 281144579368059517481989)
                  ·
                    refine ⟨52714608631511159527873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 281144579368059517481989 52714608631511159527873)
                    ·
                      rfl

theorem cell22_153992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 1, 2, 4, 4].length) (baseStart_153992 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_153992 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_153992 prefixEnd_153992 := by exact prefixLift 153992
  have htrace : WordTrace (prefixWord ++ tailWord_153992) baseStart_153992 baseEnd_153992 := by
    simpa [prefixWord, tailWord_153992, baseEnd_153992] using wordTrace_append hprefix tailTrace_153992
  have hstable : (prefixWord ++ tailWord_153992).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_153992).length < 2 ^ (prefixWord ++ tailWord_153992).sum := by decide
  have hdescent : baseEnd_153992 < baseStart_153992 := by decide
  rcases family_descends (prefixWord ++ tailWord_153992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_154116 : List Nat := [2, 3, 2, 3, 1, 1, 1, 4, 1, 4]
def baseStart_154116 : Nat := 118140960795 + 154116 * 2 ^ 59
def prefixEnd_154116 : Nat := 4983230072969 + 3 ^ 40 * 154116 * 2
def baseEnd_154116 : Nat := 52757056365616169427493

theorem tailTrace_154116 : CollatzResearch.WordTrace tailWord_154116 prefixEnd_154116 52757056365616169427493 := by
  unfold tailWord_154116
  simp only [CollatzResearch.WordTrace]
  refine ⟨2810536154835763881197101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3747381539781018508262801 2810536154835763881197101)
  ·
    refine ⟨1053951058063411455448913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2810536154835763881197101 1053951058063411455448913)
    ·
      refine ⟨790463293547558591586685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1053951058063411455448913 790463293547558591586685)
      ·
        refine ⟨296423735080334471845007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 790463293547558591586685 296423735080334471845007)
        ·
          refine ⟨444635602620501707767511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 296423735080334471845007 444635602620501707767511)
          ·
            refine ⟨666953403930752561651267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 444635602620501707767511 666953403930752561651267)
            ·
              refine ⟨1000430105896128842476901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 666953403930752561651267 1000430105896128842476901)
              ·
                refine ⟨187580644855524157964419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1000430105896128842476901 187580644855524157964419)
                ·
                  refine ⟨281370967283286236946629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 187580644855524157964419 281370967283286236946629)
                  ·
                    refine ⟨52757056365616169427493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 281370967283286236946629 52757056365616169427493)
                    ·
                      rfl

theorem cell22_154116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 1, 4, 1, 4].length) (baseStart_154116 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_154116 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_154116 prefixEnd_154116 := by exact prefixLift 154116
  have htrace : WordTrace (prefixWord ++ tailWord_154116) baseStart_154116 baseEnd_154116 := by
    simpa [prefixWord, tailWord_154116, baseEnd_154116] using wordTrace_append hprefix tailTrace_154116
  have hstable : (prefixWord ++ tailWord_154116).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_154116).length < 2 ^ (prefixWord ++ tailWord_154116).sum := by decide
  have hdescent : baseEnd_154116 < baseStart_154116 := by decide
  rcases family_descends (prefixWord ++ tailWord_154116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_154146 : List Nat := [3, 3, 1, 1, 1, 1, 1, 6, 2, 3]
def baseStart_154146 : Nat := 118140960795 + 154146 * 2 ^ 59
def prefixEnd_154146 : Nat := 4983230072969 + 3 ^ 40 * 154146 * 2
def baseEnd_154146 : Nat := 52767325978706091177401

theorem tailTrace_154146 : CollatzResearch.WordTrace tailWord_154146 prefixEnd_154146 52767325978706091177401 := by
  unfold tailWord_154146
  simp only [CollatzResearch.WordTrace]
  refine ⟨1405541624890710721496573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3748110999708561923990861 1405541624890710721496573)
  ·
    refine ⟨527078109334016520561215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1405541624890710721496573 527078109334016520561215)
    ·
      refine ⟨790617164001024780841823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 527078109334016520561215 790617164001024780841823)
      ·
        refine ⟨1185925746001537171262735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 790617164001024780841823 1185925746001537171262735)
        ·
          refine ⟨1778888619002305756894103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1185925746001537171262735 1778888619002305756894103)
          ·
            refine ⟨2668332928503458635341155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1778888619002305756894103 2668332928503458635341155)
            ·
              refine ⟨4002499392755187953011733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2668332928503458635341155 4002499392755187953011733)
              ·
                refine ⟨187617159035399435297425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 4002499392755187953011733 187617159035399435297425)
                ·
                  refine ⟨140712869276549576473069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 187617159035399435297425 140712869276549576473069)
                  ·
                    refine ⟨52767325978706091177401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 140712869276549576473069 52767325978706091177401)
                    ·
                      rfl

theorem cell22_154146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 6, 2, 3].length) (baseStart_154146 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_154146 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_154146 prefixEnd_154146 := by exact prefixLift 154146
  have htrace : WordTrace (prefixWord ++ tailWord_154146) baseStart_154146 baseEnd_154146 := by
    simpa [prefixWord, tailWord_154146, baseEnd_154146] using wordTrace_append hprefix tailTrace_154146
  have hstable : (prefixWord ++ tailWord_154146).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_154146).length < 2 ^ (prefixWord ++ tailWord_154146).sum := by decide
  have hdescent : baseEnd_154146 < baseStart_154146 := by decide
  rcases family_descends (prefixWord ++ tailWord_154146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_154148 : List Nat := [2, 3, 1, 5, 1, 2, 1, 1, 6]
def baseStart_154148 : Nat := 118140960795 + 154148 * 2 ^ 59
def prefixEnd_154148 : Nat := 4983230072969 + 3 ^ 40 * 154148 * 2
def baseEnd_154148 : Nat := 17589336873192917542465

theorem tailTrace_154148 : CollatzResearch.WordTrace tailWord_154148 prefixEnd_154148 17589336873192917542465 := by
  unfold tailWord_154148
  simp only [CollatzResearch.WordTrace]
  refine ⟨2811119722777798613779549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3748159630370398151706065 2811119722777798613779549)
  ·
    refine ⟨1054169896041674480167331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2811119722777798613779549 1054169896041674480167331)
    ·
      refine ⟨1581254844062511720250997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1054169896041674480167331 1581254844062511720250997)
      ·
        refine ⟨148242641630860473773531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 1581254844062511720250997 148242641630860473773531)
        ·
          refine ⟨222363962446290710660297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 148242641630860473773531 222363962446290710660297)
          ·
            refine ⟨166772971834718032995223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 222363962446290710660297 166772971834718032995223)
            ·
              refine ⟨250159457752077049492835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 166772971834718032995223 250159457752077049492835)
              ·
                refine ⟨375239186628115574239253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 250159457752077049492835 375239186628115574239253)
                ·
                  refine ⟨17589336873192917542465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 375239186628115574239253 17589336873192917542465)
                  ·
                    rfl

theorem cell22_154148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 2, 1, 1, 6].length) (baseStart_154148 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_154148 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_154148 prefixEnd_154148 := by exact prefixLift 154148
  have htrace : WordTrace (prefixWord ++ tailWord_154148) baseStart_154148 baseEnd_154148 := by
    simpa [prefixWord, tailWord_154148, baseEnd_154148] using wordTrace_append hprefix tailTrace_154148
  have hstable : (prefixWord ++ tailWord_154148).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_154148).length < 2 ^ (prefixWord ++ tailWord_154148).sum := by decide
  have hdescent : baseEnd_154148 < baseStart_154148 := by decide
  rcases family_descends (prefixWord ++ tailWord_154148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_154180 : List Nat := [2, 3, 5, 1, 1, 1, 1, 2, 1, 5]
def baseStart_154180 : Nat := 118140960795 + 154180 * 2 ^ 59
def prefixEnd_154180 : Nat := 4983230072969 + 3 ^ 40 * 154180 * 2
def baseEnd_154180 : Nat := 52778964873541335827297

theorem tailTrace_154180 : CollatzResearch.WordTrace tailWord_154180 prefixEnd_154180 52778964873541335827297 := by
  unfold tailWord_154180
  simp only [CollatzResearch.WordTrace]
  refine ⟨2811703290719833346361997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3748937720959777795149329 2811703290719833346361997)
  ·
    refine ⟨1054388734019937504885749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2811703290719833346361997 1054388734019937504885749)
    ·
      refine ⟨98848943814369141083039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 1054388734019937504885749 98848943814369141083039)
      ·
        refine ⟨148273415721553711624559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98848943814369141083039 148273415721553711624559)
        ·
          refine ⟨222410123582330567436839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 148273415721553711624559 222410123582330567436839)
          ·
            refine ⟨333615185373495851155259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 222410123582330567436839 333615185373495851155259)
            ·
              refine ⟨500422778060243776732889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 333615185373495851155259 500422778060243776732889)
              ·
                refine ⟨375317083545182832549667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 500422778060243776732889 375317083545182832549667)
                ·
                  refine ⟨562975625317774248824501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 375317083545182832549667 562975625317774248824501)
                  ·
                    refine ⟨52778964873541335827297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 562975625317774248824501 52778964873541335827297)
                    ·
                      rfl

theorem cell22_154180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 1, 1, 2, 1, 5].length) (baseStart_154180 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_154180 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_154180 prefixEnd_154180 := by exact prefixLift 154180
  have htrace : WordTrace (prefixWord ++ tailWord_154180) baseStart_154180 baseEnd_154180 := by
    simpa [prefixWord, tailWord_154180, baseEnd_154180] using wordTrace_append hprefix tailTrace_154180
  have hstable : (prefixWord ++ tailWord_154180).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_154180).length < 2 ^ (prefixWord ++ tailWord_154180).sum := by decide
  have hdescent : baseEnd_154180 < baseStart_154180 := by decide
  rcases family_descends (prefixWord ++ tailWord_154180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_154187 : List Nat := [1, 1, 1, 1, 3, 1, 4, 1, 9]
def baseStart_154187 : Nat := 118140960795 + 154187 * 2 ^ 59
def prefixEnd_154187 : Nat := 4983230072969 + 3 ^ 40 * 154187 * 2
def baseEnd_154187 : Nat := 17593787038865216967425

theorem tailTrace_154187 : CollatzResearch.WordTrace tailWord_154187 prefixEnd_154187 17593787038865216967425 := by
  unfold tailWord_154187
  simp only [CollatzResearch.WordTrace]
  refine ⟨5623661892414306888228815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3749107928276204592152543 5623661892414306888228815)
  ·
    refine ⟨8435492838621460332343223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5623661892414306888228815 8435492838621460332343223)
    ·
      refine ⟨12653239257932190498514835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8435492838621460332343223 12653239257932190498514835)
      ·
        refine ⟨18979858886898285747772253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12653239257932190498514835 18979858886898285747772253)
        ·
          refine ⟨7117447082586857155414595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18979858886898285747772253 7117447082586857155414595)
          ·
            refine ⟨10676170623880285733121893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7117447082586857155414595 10676170623880285733121893)
            ·
              refine ⟨2001781991977553574960355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10676170623880285733121893 2001781991977553574960355)
              ·
                refine ⟨3002672987966330362440533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2001781991977553574960355 3002672987966330362440533)
                ·
                  refine ⟨17593787038865216967425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 3002672987966330362440533 17593787038865216967425)
                  ·
                    rfl

theorem cell22_154187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 4, 1, 9].length) (baseStart_154187 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_154187 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_154187 prefixEnd_154187 := by exact prefixLift 154187
  have htrace : WordTrace (prefixWord ++ tailWord_154187) baseStart_154187 baseEnd_154187 := by
    simpa [prefixWord, tailWord_154187, baseEnd_154187] using wordTrace_append hprefix tailTrace_154187
  have hstable : (prefixWord ++ tailWord_154187).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_154187).length < 2 ^ (prefixWord ++ tailWord_154187).sum := by decide
  have hdescent : baseEnd_154187 < baseStart_154187 := by decide
  rcases family_descends (prefixWord ++ tailWord_154187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_154210 : List Nat := [3, 3, 2, 3, 2, 1, 1, 7]
def baseStart_154210 : Nat := 118140960795 + 154210 * 2 ^ 59
def prefixEnd_154210 : Nat := 4983230072969 + 3 ^ 40 * 154210 * 2
def baseEnd_154210 : Nat := 5865470498514584175245

theorem tailTrace_154210 : CollatzResearch.WordTrace tailWord_154210 prefixEnd_154210 5865470498514584175245 := by
  unfold tailWord_154210
  simp only [CollatzResearch.WordTrace]
  refine ⟨1406125192832745454079021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3749667180887321210877389 1406125192832745454079021)
  ·
    refine ⟨527296947312279545279633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1406125192832745454079021 527296947312279545279633)
    ·
      refine ⟨395472710484209658959725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 527296947312279545279633 395472710484209658959725)
      ·
        refine ⟨148302266431578622109897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 395472710484209658959725 148302266431578622109897)
        ·
          refine ⟨111226699823683966582423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 148302266431578622109897 111226699823683966582423)
          ·
            refine ⟨166840049735525949873635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 111226699823683966582423 166840049735525949873635)
            ·
              refine ⟨250260074603288924810453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 166840049735525949873635 250260074603288924810453)
              ·
                refine ⟨5865470498514584175245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 250260074603288924810453 5865470498514584175245)
                ·
                  rfl

theorem cell22_154210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 2, 1, 1, 7].length) (baseStart_154210 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_154210 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_154210 prefixEnd_154210 := by exact prefixLift 154210
  have htrace : WordTrace (prefixWord ++ tailWord_154210) baseStart_154210 baseEnd_154210 := by
    simpa [prefixWord, tailWord_154210, baseEnd_154210] using wordTrace_append hprefix tailTrace_154210
  have hstable : (prefixWord ++ tailWord_154210).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_154210).length < 2 ^ (prefixWord ++ tailWord_154210).sum := by decide
  have hdescent : baseEnd_154210 < baseStart_154210 := by decide
  rcases family_descends (prefixWord ++ tailWord_154210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_154221 : List Nat := [1, 5, 1, 1, 3, 1, 2, 3, 5]
def baseStart_154221 : Nat := 118140960795 + 154221 * 2 ^ 59
def prefixEnd_154221 : Nat := 4983230072969 + 3 ^ 40 * 154221 * 2
def baseEnd_154221 : Nat := 17597666670476965184057

theorem tailTrace_154221 : CollatzResearch.WordTrace tailWord_154221 prefixEnd_154221 17597666670476965184057 := by
  unfold tailWord_154221
  simp only [CollatzResearch.WordTrace]
  refine ⟨5624901974291130694966517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3749934649527420463311011 5624901974291130694966517)
  ·
    refine ⟨527334560089793502653111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 5624901974291130694966517 527334560089793502653111)
    ·
      refine ⟨791001840134690253979667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 527334560089793502653111 791001840134690253979667)
      ·
        refine ⟨1186502760202035380969501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 791001840134690253979667 1186502760202035380969501)
        ·
          refine ⟨444938535075763267863563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1186502760202035380969501 444938535075763267863563)
          ·
            refine ⟨667407802613644901795345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 444938535075763267863563 667407802613644901795345)
            ·
              refine ⟨500555851960233676346509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 667407802613644901795345 500555851960233676346509)
              ·
                refine ⟨187708444485087628629941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 500555851960233676346509 187708444485087628629941)
                ·
                  refine ⟨17597666670476965184057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 187708444485087628629941 17597666670476965184057)
                  ·
                    rfl

theorem cell22_154221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 2, 3, 5].length) (baseStart_154221 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_154221 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_154221 prefixEnd_154221 := by exact prefixLift 154221
  have htrace : WordTrace (prefixWord ++ tailWord_154221) baseStart_154221 baseEnd_154221 := by
    simpa [prefixWord, tailWord_154221, baseEnd_154221] using wordTrace_append hprefix tailTrace_154221
  have hstable : (prefixWord ++ tailWord_154221).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_154221).length < 2 ^ (prefixWord ++ tailWord_154221).sum := by decide
  have hdescent : baseEnd_154221 < baseStart_154221 := by decide
  rcases family_descends (prefixWord ++ tailWord_154221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_154317 : List Nat := [1, 6, 2, 1, 3, 1, 1, 1, 6]
def baseStart_154317 : Nat := 118140960795 + 154317 * 2 ^ 59
def prefixEnd_154317 : Nat := 4983230072969 + 3 ^ 40 * 154317 * 2
def baseEnd_154317 : Nat := 17608620924439548383959

theorem tailTrace_154317 : CollatzResearch.WordTrace tailWord_154317 prefixEnd_154317 17608620924439548383959 := by
  unfold tailWord_154317
  simp only [CollatzResearch.WordTrace]
  refine ⟨5628403381943339090461205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3752268921295559393640803 5628403381943339090461205)
  ·
    refine ⟨263831408528594019865369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 5628403381943339090461205 263831408528594019865369)
    ·
      refine ⟨197873556396445514899027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 263831408528594019865369 197873556396445514899027)
      ·
        refine ⟨296810334594668272348541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 197873556396445514899027 296810334594668272348541)
        ·
          refine ⟨111303875473000602130703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 296810334594668272348541 111303875473000602130703)
          ·
            refine ⟨166955813209500903196055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 111303875473000602130703 166955813209500903196055)
            ·
              refine ⟨250433719814251354794083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 166955813209500903196055 250433719814251354794083)
              ·
                refine ⟨375650579721377032191125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 250433719814251354794083 375650579721377032191125)
                ·
                  refine ⟨17608620924439548383959, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 375650579721377032191125 17608620924439548383959)
                  ·
                    rfl

theorem cell22_154317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 3, 1, 1, 1, 6].length) (baseStart_154317 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_154317 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_154317 prefixEnd_154317 := by exact prefixLift 154317
  have htrace : WordTrace (prefixWord ++ tailWord_154317) baseStart_154317 baseEnd_154317 := by
    simpa [prefixWord, tailWord_154317, baseEnd_154317] using wordTrace_append hprefix tailTrace_154317
  have hstable : (prefixWord ++ tailWord_154317).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_154317).length < 2 ^ (prefixWord ++ tailWord_154317).sum := by decide
  have hdescent : baseEnd_154317 < baseStart_154317 := by decide
  rcases family_descends (prefixWord ++ tailWord_154317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_154332 : List Nat := [2, 2, 5, 1, 1, 1, 4, 1, 2, 3]
def baseStart_154332 : Nat := 118140960795 + 154332 * 2 ^ 59
def prefixEnd_154332 : Nat := 4983230072969 + 3 ^ 40 * 154332 * 2
def baseEnd_154332 : Nat := 52830997579863606026831

theorem tailTrace_154332 : CollatzResearch.WordTrace tailWord_154332 prefixEnd_154332 52830997579863606026831 := by
  unfold tailWord_154332
  simp only [CollatzResearch.WordTrace]
  refine ⟨2814475238444498326128625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3752633651259331101504833 2814475238444498326128625)
  ·
    refine ⟨2110856428833373744596469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2814475238444498326128625 2110856428833373744596469)
    ·
      refine ⟨197892790203128788555919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 2110856428833373744596469 197892790203128788555919)
      ·
        refine ⟨296839185304693182833879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 197892790203128788555919 296839185304693182833879)
        ·
          refine ⟨445258777957039774250819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 296839185304693182833879 445258777957039774250819)
          ·
            refine ⟨667888166935559661376229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 445258777957039774250819 667888166935559661376229)
            ·
              refine ⟨125229031300417436508043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 667888166935559661376229 125229031300417436508043)
              ·
                refine ⟨187843546950626154762065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 125229031300417436508043 187843546950626154762065)
                ·
                  refine ⟨140882660212969616071549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 187843546950626154762065 140882660212969616071549)
                  ·
                    refine ⟨52830997579863606026831, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 140882660212969616071549 52830997579863606026831)
                    ·
                      rfl

theorem cell22_154332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 4, 1, 2, 3].length) (baseStart_154332 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_154332 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_154332 prefixEnd_154332 := by exact prefixLift 154332
  have htrace : WordTrace (prefixWord ++ tailWord_154332) baseStart_154332 baseEnd_154332 := by
    simpa [prefixWord, tailWord_154332, baseEnd_154332] using wordTrace_append hprefix tailTrace_154332
  have hstable : (prefixWord ++ tailWord_154332).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_154332).length < 2 ^ (prefixWord ++ tailWord_154332).sum := by decide
  have hdescent : baseEnd_154332 < baseStart_154332 := by decide
  rcases family_descends (prefixWord ++ tailWord_154332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_154401 : List Nat := [1, 2, 3, 2, 1, 2, 3, 2, 6]
def baseStart_154401 : Nat := 118140960795 + 154401 * 2 ^ 59
def prefixEnd_154401 : Nat := 4983230072969 + 3 ^ 40 * 154401 * 2
def baseEnd_154401 : Nat := 17618205896656808683873

theorem tailTrace_154401 : CollatzResearch.WordTrace tailWord_154401 prefixEnd_154401 17618205896656808683873 := by
  unfold tailWord_154401
  simp only [CollatzResearch.WordTrace]
  refine ⟨5631467113639021436519057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3754311409092680957679371 5631467113639021436519057)
  ·
    refine ⟨4223600335229266077389293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5631467113639021436519057 4223600335229266077389293)
    ·
      refine ⟨1583850125710974779020985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4223600335229266077389293 1583850125710974779020985)
      ·
        refine ⟨1187887594283231084265739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1583850125710974779020985 1187887594283231084265739)
        ·
          refine ⟨1781831391424846626398609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1187887594283231084265739 1781831391424846626398609)
          ·
            refine ⟨1336373543568634969798957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1781831391424846626398609 1336373543568634969798957)
            ·
              refine ⟨501140078838238113674609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1336373543568634969798957 501140078838238113674609)
              ·
                refine ⟨375855059128678585255957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 501140078838238113674609 375855059128678585255957)
                ·
                  refine ⟨17618205896656808683873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 375855059128678585255957 17618205896656808683873)
                  ·
                    rfl

theorem cell22_154401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 3, 2, 6].length) (baseStart_154401 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_154401 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_154401 prefixEnd_154401 := by exact prefixLift 154401
  have htrace : WordTrace (prefixWord ++ tailWord_154401) baseStart_154401 baseEnd_154401 := by
    simpa [prefixWord, tailWord_154401, baseEnd_154401] using wordTrace_append hprefix tailTrace_154401
  have hstable : (prefixWord ++ tailWord_154401).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_154401).length < 2 ^ (prefixWord ++ tailWord_154401).sum := by decide
  have hdescent : baseEnd_154401 < baseStart_154401 := by decide
  rcases family_descends (prefixWord ++ tailWord_154401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_154491 : List Nat := [1, 1, 1, 1, 1, 5, 4, 1, 7]
def baseStart_154491 : Nat := 118140960795 + 154491 * 2 ^ 59
def prefixEnd_154491 : Nat := 4983230072969 + 3 ^ 40 * 154491 * 2
def baseEnd_154491 : Nat := 17628475509746730433781

theorem tailTrace_154491 : CollatzResearch.WordTrace tailWord_154491 prefixEnd_154491 17628475509746730433781 := by
  unfold tailWord_154491
  simp only [CollatzResearch.WordTrace]
  refine ⟨5634749683312966807295327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3756499788875311204863551 5634749683312966807295327)
  ·
    refine ⟨8452124524969450210942991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5634749683312966807295327 8452124524969450210942991)
    ·
      refine ⟨12678186787454175316414487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8452124524969450210942991 12678186787454175316414487)
      ·
        refine ⟨19017280181181262974621731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12678186787454175316414487 19017280181181262974621731)
        ·
          refine ⟨28525920271771894461932597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19017280181181262974621731 28525920271771894461932597)
          ·
            refine ⟨2674305025478615105806181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 28525920271771894461932597 2674305025478615105806181)
            ·
              refine ⟨501432192277240332338659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2674305025478615105806181 501432192277240332338659)
              ·
                refine ⟨752148288415860498507989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 501432192277240332338659 752148288415860498507989)
                ·
                  refine ⟨17628475509746730433781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 752148288415860498507989 17628475509746730433781)
                  ·
                    rfl

theorem cell22_154491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 4, 1, 7].length) (baseStart_154491 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_154491 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_154491 prefixEnd_154491 := by exact prefixLift 154491
  have htrace : WordTrace (prefixWord ++ tailWord_154491) baseStart_154491 baseEnd_154491 := by
    simpa [prefixWord, tailWord_154491, baseEnd_154491] using wordTrace_append hprefix tailTrace_154491
  have hstable : (prefixWord ++ tailWord_154491).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_154491).length < 2 ^ (prefixWord ++ tailWord_154491).sum := by decide
  have hdescent : baseEnd_154491 < baseStart_154491 := by decide
  rcases family_descends (prefixWord ++ tailWord_154491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_154495 : List Nat := [1, 1, 2, 2, 1, 1, 4, 6, 1, 3]
def baseStart_154495 : Nat := 118140960795 + 154495 * 2 ^ 59
def prefixEnd_154495 : Nat := 4983230072969 + 3 ^ 40 * 154495 * 2
def baseEnd_154495 : Nat := 52886795810985514201331

theorem tailTrace_154495 : CollatzResearch.WordTrace tailWord_154495 prefixEnd_154495 52886795810985514201331 := by
  unfold tailWord_154495
  simp only [CollatzResearch.WordTrace]
  refine ⟨5634895575298475490440939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3756597050198983660293959 5634895575298475490440939)
  ·
    refine ⟨8452343362947713235661409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5634895575298475490440939 8452343362947713235661409)
    ·
      refine ⟨6339257522210784926746057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8452343362947713235661409 6339257522210784926746057)
      ·
        refine ⟨4754443141658088695059543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6339257522210784926746057 4754443141658088695059543)
        ·
          refine ⟨7131664712487133042589315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4754443141658088695059543 7131664712487133042589315)
          ·
            refine ⟨10697497068730699563883973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7131664712487133042589315 10697497068730699563883973)
            ·
              refine ⟨2005780700387006168228245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10697497068730699563883973 2005780700387006168228245)
              ·
                refine ⟨94020970330640914135699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2005780700387006168228245 94020970330640914135699)
                ·
                  refine ⟨141031455495961371203549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 94020970330640914135699 141031455495961371203549)
                  ·
                    refine ⟨52886795810985514201331, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 141031455495961371203549 52886795810985514201331)
                    ·
                      rfl

theorem cell22_154495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 4, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 4, 6, 1, 3].length) (baseStart_154495 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_154495 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_154495 prefixEnd_154495 := by exact prefixLift 154495
  have htrace : WordTrace (prefixWord ++ tailWord_154495) baseStart_154495 baseEnd_154495 := by
    simpa [prefixWord, tailWord_154495, baseEnd_154495] using wordTrace_append hprefix tailTrace_154495
  have hstable : (prefixWord ++ tailWord_154495).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_154495).length < 2 ^ (prefixWord ++ tailWord_154495).sum := by decide
  have hdescent : baseEnd_154495 < baseStart_154495 := by decide
  rcases family_descends (prefixWord ++ tailWord_154495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_154583 : List Nat := [1, 1, 3, 2, 1, 1, 2, 5, 2, 4]
def baseStart_154583 : Nat := 118140960795 + 154583 * 2 ^ 59
def prefixEnd_154583 : Nat := 4983230072969 + 3 ^ 40 * 154583 * 2
def baseEnd_154583 : Nat := 52916920009382618001061

theorem tailTrace_154583 : CollatzResearch.WordTrace tailWord_154583 prefixEnd_154583 52916920009382618001061 := by
  unfold tailWord_154583
  simp only [CollatzResearch.WordTrace]
  refine ⟨5638105198979666519644403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3758736799319777679762935 5638105198979666519644403)
  ·
    refine ⟨8457157798469499779466605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5638105198979666519644403 8457157798469499779466605)
    ·
      refine ⟨3171434174426062417299977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8457157798469499779466605 3171434174426062417299977)
      ·
        refine ⟨2378575630819546812974983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3171434174426062417299977 2378575630819546812974983)
        ·
          refine ⟨3567863446229320219462475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2378575630819546812974983 3567863446229320219462475)
          ·
            refine ⟨5351795169343980329193713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3567863446229320219462475 5351795169343980329193713)
            ·
              refine ⟨4013846377007985246895285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5351795169343980329193713 4013846377007985246895285)
              ·
                refine ⟨376298097844498616896433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4013846377007985246895285 376298097844498616896433)
                ·
                  refine ⟨282223573383373962672325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 376298097844498616896433 282223573383373962672325)
                  ·
                    refine ⟨52916920009382618001061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 282223573383373962672325 52916920009382618001061)
                    ·
                      rfl

theorem cell22_154583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 5, 2, 4].length) (baseStart_154583 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_154583 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_154583 prefixEnd_154583 := by exact prefixLift 154583
  have htrace : WordTrace (prefixWord ++ tailWord_154583) baseStart_154583 baseEnd_154583 := by
    simpa [prefixWord, tailWord_154583, baseEnd_154583] using wordTrace_append hprefix tailTrace_154583
  have hstable : (prefixWord ++ tailWord_154583).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_154583).length < 2 ^ (prefixWord ++ tailWord_154583).sum := by decide
  have hdescent : baseEnd_154583 < baseStart_154583 := by decide
  rcases family_descends (prefixWord ++ tailWord_154583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_154589 : List Nat := [1, 4, 3, 1, 2, 3, 2, 1, 1, 4]
def baseStart_154589 : Nat := 118140960795 + 154589 * 2 ^ 59
def prefixEnd_154589 : Nat := 4983230072969 + 3 ^ 40 * 154589 * 2
def baseEnd_154589 : Nat := 52918973932000602351043

theorem tailTrace_154589 : CollatzResearch.WordTrace tailWord_154589 prefixEnd_154589 52918973932000602351043 := by
  unfold tailWord_154589
  simp only [CollatzResearch.WordTrace]
  refine ⟨5638324036957929544362821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3758882691305286362908547 5638324036957929544362821)
  ·
    refine ⟨1057185756929611789568029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5638324036957929544362821 1057185756929611789568029)
    ·
      refine ⟨396444658848604421088011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1057185756929611789568029 396444658848604421088011)
      ·
        refine ⟨594666988272906631632017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 396444658848604421088011 594666988272906631632017)
        ·
          refine ⟨446000241204679973724013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 594666988272906631632017 446000241204679973724013)
          ·
            refine ⟨167250090451754990146505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 446000241204679973724013 167250090451754990146505)
            ·
              refine ⟨125437567838816242609879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 167250090451754990146505 125437567838816242609879)
              ·
                refine ⟨188156351758224363914819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 125437567838816242609879 188156351758224363914819)
                ·
                  refine ⟨282234527637336545872229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 188156351758224363914819 282234527637336545872229)
                  ·
                    refine ⟨52918973932000602351043, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 282234527637336545872229 52918973932000602351043)
                    ·
                      rfl

theorem cell22_154589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 3, 2, 1, 1, 4].length) (baseStart_154589 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_154589 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_154589 prefixEnd_154589 := by exact prefixLift 154589
  have htrace : WordTrace (prefixWord ++ tailWord_154589) baseStart_154589 baseEnd_154589 := by
    simpa [prefixWord, tailWord_154589, baseEnd_154589] using wordTrace_append hprefix tailTrace_154589
  have hstable : (prefixWord ++ tailWord_154589).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_154589).length < 2 ^ (prefixWord ++ tailWord_154589).sum := by decide
  have hdescent : baseEnd_154589 < baseStart_154589 := by decide
  rcases family_descends (prefixWord ++ tailWord_154589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_154602 : List Nat := [3, 1, 3, 1, 2, 2, 3, 2, 2, 3]
def baseStart_154602 : Nat := 118140960795 + 154602 * 2 ^ 59
def prefixEnd_154602 : Nat := 4983230072969 + 3 ^ 40 * 154602 * 2
def baseEnd_154602 : Nat := 52923424097672901776003

theorem tailTrace_154602 : CollatzResearch.WordTrace tailWord_154602 prefixEnd_154602 52923424097672901776003 := by
  unfold tailWord_154602
  simp only [CollatzResearch.WordTrace]
  refine ⟨1409699546477708191146515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3759198790607221843057373 1409699546477708191146515)
  ·
    refine ⟨2114549319716562286719773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1409699546477708191146515 2114549319716562286719773)
    ·
      refine ⟨792955994893710857519915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2114549319716562286719773 792955994893710857519915)
      ·
        refine ⟨1189433992340566286279873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 792955994893710857519915 1189433992340566286279873)
        ·
          refine ⟨892075494255424714709905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1189433992340566286279873 892075494255424714709905)
          ·
            refine ⟨669056620691568536032429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 892075494255424714709905 669056620691568536032429)
            ·
              refine ⟨250896232759338201012161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 669056620691568536032429 250896232759338201012161)
              ·
                refine ⟨188172174569503650759121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 250896232759338201012161 188172174569503650759121)
                ·
                  refine ⟨141129130927127738069341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 188172174569503650759121 141129130927127738069341)
                  ·
                    refine ⟨52923424097672901776003, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 141129130927127738069341 52923424097672901776003)
                    ·
                      rfl

theorem cell22_154602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 3, 2, 2, 3].length) (baseStart_154602 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_154602 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_154602 prefixEnd_154602 := by exact prefixLift 154602
  have htrace : WordTrace (prefixWord ++ tailWord_154602) baseStart_154602 baseEnd_154602 := by
    simpa [prefixWord, tailWord_154602, baseEnd_154602] using wordTrace_append hprefix tailTrace_154602
  have hstable : (prefixWord ++ tailWord_154602).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_154602).length < 2 ^ (prefixWord ++ tailWord_154602).sum := by decide
  have hdescent : baseEnd_154602 < baseStart_154602 := by decide
  rcases family_descends (prefixWord ++ tailWord_154602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_154660 : List Nat := [2, 3, 1, 4, 1, 1, 2, 1, 7]
def baseStart_154660 : Nat := 118140960795 + 154660 * 2 ^ 59
def prefixEnd_154660 : Nat := 4983230072969 + 3 ^ 40 * 154660 * 2
def baseEnd_154660 : Nat := 17647759560993361275275

theorem tailTrace_154660 : CollatzResearch.WordTrace tailWord_154660 prefixEnd_154660 17647759560993361275275 := by
  unfold tailWord_154660
  simp only [CollatzResearch.WordTrace]
  refine ⟨2820456809850354335098717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3760609079800472446798289 2820456809850354335098717)
  ·
    refine ⟨1057671303693882875662019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2820456809850354335098717 1057671303693882875662019)
    ·
      refine ⟨1586506955540824313493029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1057671303693882875662019 1586506955540824313493029)
      ·
        refine ⟨297470054163904558779943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1586506955540824313493029 297470054163904558779943)
        ·
          refine ⟨446205081245856838169915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 297470054163904558779943 446205081245856838169915)
          ·
            refine ⟨669307621868785257254873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 446205081245856838169915 669307621868785257254873)
            ·
              refine ⟨501980716401588942941155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 669307621868785257254873 501980716401588942941155)
              ·
                refine ⟨752971074602383414411733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 501980716401588942941155 752971074602383414411733)
                ·
                  refine ⟨17647759560993361275275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 752971074602383414411733 17647759560993361275275)
                  ·
                    rfl

theorem cell22_154660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 2, 1, 7].length) (baseStart_154660 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_154660 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_154660 prefixEnd_154660 := by exact prefixLift 154660
  have htrace : WordTrace (prefixWord ++ tailWord_154660) baseStart_154660 baseEnd_154660 := by
    simpa [prefixWord, tailWord_154660, baseEnd_154660] using wordTrace_append hprefix tailTrace_154660
  have hstable : (prefixWord ++ tailWord_154660).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_154660).length < 2 ^ (prefixWord ++ tailWord_154660).sum := by decide
  have hdescent : baseEnd_154660 < baseStart_154660 := by decide
  rcases family_descends (prefixWord ++ tailWord_154660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_154688 : List Nat := [2, 1, 1, 2, 2, 3, 2, 1, 8]
def baseStart_154688 : Nat := 118140960795 + 154688 * 2 ^ 59
def prefixEnd_154688 : Nat := 4983230072969 + 3 ^ 40 * 154688 * 2
def baseEnd_154688 : Nat := 17650954551732448041913

theorem tailTrace_154688 : CollatzResearch.WordTrace tailWord_154688 prefixEnd_154688 17650954551732448041913 := by
  unfold tailWord_154688
  simp only [CollatzResearch.WordTrace]
  refine ⟨2820967431799634726108359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3761289909066179634811145 2820967431799634726108359)
  ·
    refine ⟨4231451147699452089162539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2820967431799634726108359 4231451147699452089162539)
    ·
      refine ⟨6347176721549178133743809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4231451147699452089162539 6347176721549178133743809)
      ·
        refine ⟨4760382541161883600307857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6347176721549178133743809 4760382541161883600307857)
        ·
          refine ⟨3570286905871412700230893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4760382541161883600307857 3570286905871412700230893)
          ·
            refine ⟨1338857589701779762586585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3570286905871412700230893 1338857589701779762586585)
            ·
              refine ⟨1004143192276334821939939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1338857589701779762586585 1004143192276334821939939)
              ·
                refine ⟨1506214788414502232909909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1004143192276334821939939 1506214788414502232909909)
                ·
                  refine ⟨17650954551732448041913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 1506214788414502232909909 17650954551732448041913)
                  ·
                    rfl

theorem cell22_154688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 2, 1, 8].length) (baseStart_154688 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_154688 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_154688 prefixEnd_154688 := by exact prefixLift 154688
  have htrace : WordTrace (prefixWord ++ tailWord_154688) baseStart_154688 baseEnd_154688 := by
    simpa [prefixWord, tailWord_154688, baseEnd_154688] using wordTrace_append hprefix tailTrace_154688
  have hstable : (prefixWord ++ tailWord_154688).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_154688).length < 2 ^ (prefixWord ++ tailWord_154688).sum := by decide
  have hdescent : baseEnd_154688 < baseStart_154688 := by decide
  rcases family_descends (prefixWord ++ tailWord_154688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_154859 : List Nat := [1, 1, 1, 1, 2, 8, 1, 2, 1, 4]
def baseStart_154859 : Nat := 118140960795 + 154859 * 2 ^ 59
def prefixEnd_154859 : Nat := 4983230072969 + 3 ^ 40 * 154859 * 2
def baseEnd_154859 : Nat := 53011400449809898100215

theorem tailTrace_154859 : CollatzResearch.WordTrace tailWord_154859 prefixEnd_154859 53011400449809898100215 := by
  unfold tailWord_154859
  simp only [CollatzResearch.WordTrace]
  refine ⟨5648171745979765656691631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3765447830653177104461087 5648171745979765656691631)
  ·
    refine ⟨8472257618969648485037447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5648171745979765656691631 8472257618969648485037447)
    ·
      refine ⟨12708386428454472727556171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8472257618969648485037447 12708386428454472727556171)
      ·
        refine ⟨19062579642681709091334257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12708386428454472727556171 19062579642681709091334257)
        ·
          refine ⟨14296934732011281818500693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19062579642681709091334257 14296934732011281818500693)
          ·
            refine ⟨167542203890757208810555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 14296934732011281818500693 167542203890757208810555)
            ·
              refine ⟨251313305836135813215833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 167542203890757208810555 251313305836135813215833)
              ·
                refine ⟨188484979377101859911875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 251313305836135813215833 188484979377101859911875)
                ·
                  refine ⟨282727469065652789867813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 188484979377101859911875 282727469065652789867813)
                  ·
                    refine ⟨53011400449809898100215, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 282727469065652789867813 53011400449809898100215)
                    ·
                      rfl

theorem cell22_154859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 8, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 8, 1, 2, 1, 4].length) (baseStart_154859 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_154859 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_154859 prefixEnd_154859 := by exact prefixLift 154859
  have htrace : WordTrace (prefixWord ++ tailWord_154859) baseStart_154859 baseEnd_154859 := by
    simpa [prefixWord, tailWord_154859, baseEnd_154859] using wordTrace_append hprefix tailTrace_154859
  have hstable : (prefixWord ++ tailWord_154859).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_154859).length < 2 ^ (prefixWord ++ tailWord_154859).sum := by decide
  have hdescent : baseEnd_154859 < baseStart_154859 := by decide
  rcases family_descends (prefixWord ++ tailWord_154859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_154876 : List Nat := [2, 2, 2, 1, 5, 1, 3, 1, 1, 4]
def baseStart_154876 : Nat := 118140960795 + 154876 * 2 ^ 59
def prefixEnd_154876 : Nat := 4983230072969 + 3 ^ 40 * 154876 * 2
def baseEnd_154876 : Nat := 53017219897227520425163

theorem tailTrace_154876 : CollatzResearch.WordTrace tailWord_154876 prefixEnd_154876 53017219897227520425163 := by
  unfold tailWord_154876
  simp only [CollatzResearch.WordTrace]
  refine ⟨2824395893459088780030241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3765861191278785040040321 2824395893459088780030241)
  ·
    refine ⟨2118296920094316585022681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2824395893459088780030241 2118296920094316585022681)
    ·
      refine ⟨1588722690070737438767011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2118296920094316585022681 1588722690070737438767011)
      ·
        refine ⟨2383084035106106158150517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1588722690070737438767011 2383084035106106158150517)
        ·
          refine ⟨223414128291197452326611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 2383084035106106158150517 223414128291197452326611)
          ·
            refine ⟨335121192436796178489917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 223414128291197452326611 335121192436796178489917)
            ·
              refine ⟨125670447163798566933719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 335121192436796178489917 125670447163798566933719)
              ·
                refine ⟨188505670745697850400579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 125670447163798566933719 188505670745697850400579)
                ·
                  refine ⟨282758506118546775600869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 188505670745697850400579 282758506118546775600869)
                  ·
                    refine ⟨53017219897227520425163, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 282758506118546775600869 53017219897227520425163)
                    ·
                      rfl

theorem cell22_154876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 1, 3, 1, 1, 4].length) (baseStart_154876 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_154876 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_154876 prefixEnd_154876 := by exact prefixLift 154876
  have htrace : WordTrace (prefixWord ++ tailWord_154876) baseStart_154876 baseEnd_154876 := by
    simpa [prefixWord, tailWord_154876, baseEnd_154876] using wordTrace_append hprefix tailTrace_154876
  have hstable : (prefixWord ++ tailWord_154876).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_154876).length < 2 ^ (prefixWord ++ tailWord_154876).sum := by decide
  have hdescent : baseEnd_154876 < baseStart_154876 := by decide
  rcases family_descends (prefixWord ++ tailWord_154876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_154889 : List Nat := [1, 2, 1, 1, 3, 3, 4, 2, 2, 3]
def baseStart_154889 : Nat := 118140960795 + 154889 * 2 ^ 59
def prefixEnd_154889 : Nat := 4983230072969 + 3 ^ 40 * 154889 * 2
def baseEnd_154889 : Nat := 53021670062899819850123

theorem tailTrace_154889 : CollatzResearch.WordTrace tailWord_154889 prefixEnd_154889 53021670062899819850123 := by
  unfold tailWord_154889
  simp only [CollatzResearch.WordTrace]
  refine ⟨5649265935871080780283721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3766177290580720520189147 5649265935871080780283721)
  ·
    refine ⟨4236949451903310585212791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5649265935871080780283721 4236949451903310585212791)
    ·
      refine ⟨6355424177854965877819187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4236949451903310585212791 6355424177854965877819187)
      ·
        refine ⟨9533136266782448816728781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6355424177854965877819187 9533136266782448816728781)
        ·
          refine ⟨3574926100043418306273293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9533136266782448816728781 3574926100043418306273293)
          ·
            refine ⟨1340597287516281864852485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3574926100043418306273293 1340597287516281864852485)
            ·
              refine ⟨251361991409302849659841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1340597287516281864852485 251361991409302849659841)
              ·
                refine ⟨188521493556977137244881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 251361991409302849659841 188521493556977137244881)
                ·
                  refine ⟨141391120167732852933661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 188521493556977137244881 141391120167732852933661)
                  ·
                    refine ⟨53021670062899819850123, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 141391120167732852933661 53021670062899819850123)
                    ·
                      rfl

theorem cell22_154889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 4, 2, 2, 3].length) (baseStart_154889 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_154889 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_154889 prefixEnd_154889 := by exact prefixLift 154889
  have htrace : WordTrace (prefixWord ++ tailWord_154889) baseStart_154889 baseEnd_154889 := by
    simpa [prefixWord, tailWord_154889, baseEnd_154889] using wordTrace_append hprefix tailTrace_154889
  have hstable : (prefixWord ++ tailWord_154889).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_154889).length < 2 ^ (prefixWord ++ tailWord_154889).sum := by decide
  have hdescent : baseEnd_154889 < baseStart_154889 := by decide
  rcases family_descends (prefixWord ++ tailWord_154889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_154891 : List Nat := [1, 1, 1, 1, 5, 5, 2, 2, 4]
def baseStart_154891 : Nat := 118140960795 + 154891 * 2 ^ 59
def prefixEnd_154891 : Nat := 4983230072969 + 3 ^ 40 * 154891 * 2
def baseEnd_154891 : Nat := 17674118234590827100039

theorem tailTrace_154891 : CollatzResearch.WordTrace tailWord_154891 prefixEnd_154891 17674118234590827100039 := by
  unfold tailWord_154891
  simp only [CollatzResearch.WordTrace]
  refine ⟨5649338881863835121856527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3766225921242556747904351 5649338881863835121856527)
  ·
    refine ⟨8474008322795752682784791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5649338881863835121856527 8474008322795752682784791)
    ·
      refine ⟨12711012484193629024177187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8474008322795752682784791 12711012484193629024177187)
      ·
        refine ⟨19066518726290443536265781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12711012484193629024177187 19066518726290443536265781)
        ·
          refine ⟨1787486130589729081524917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 19066518726290443536265781 1787486130589729081524917)
          ·
            refine ⟨167576824742787101392961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1787486130589729081524917 167576824742787101392961)
            ·
              refine ⟨125682618557090326044721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 167576824742787101392961 125682618557090326044721)
              ·
                refine ⟨94261963917817744533541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 125682618557090326044721 94261963917817744533541)
                ·
                  refine ⟨17674118234590827100039, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 94261963917817744533541 17674118234590827100039)
                  ·
                    rfl

theorem cell22_154891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 5, 2, 2, 4].length) (baseStart_154891 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_154891 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_154891 prefixEnd_154891 := by exact prefixLift 154891
  have htrace : WordTrace (prefixWord ++ tailWord_154891) baseStart_154891 baseEnd_154891 := by
    simpa [prefixWord, tailWord_154891, baseEnd_154891] using wordTrace_append hprefix tailTrace_154891
  have hstable : (prefixWord ++ tailWord_154891).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_154891).length < 2 ^ (prefixWord ++ tailWord_154891).sum := by decide
  have hdescent : baseEnd_154891 < baseStart_154891 := by decide
  rcases family_descends (prefixWord ++ tailWord_154891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_154951 : List Nat := [1, 1, 4, 1, 2, 3, 2, 4, 1, 3]
def baseStart_154951 : Nat := 118140960795 + 154951 * 2 ^ 59
def prefixEnd_154951 : Nat := 4983230072969 + 3 ^ 40 * 154951 * 2
def baseEnd_154951 : Nat := 53042893929952324799933

theorem tailTrace_154951 : CollatzResearch.WordTrace tailWord_154951 prefixEnd_154951 53042893929952324799933 := by
  unfold tailWord_154951
  simp only [CollatzResearch.WordTrace]
  refine ⟨5651527261646465369040707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3767684841097643579360471 5651527261646465369040707)
  ·
    refine ⟨8477290892469698053561061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5651527261646465369040707 8477290892469698053561061)
    ·
      refine ⟨1589492042338068385042699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8477290892469698053561061 1589492042338068385042699)
      ·
        refine ⟨2384238063507102577564049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1589492042338068385042699 2384238063507102577564049)
        ·
          refine ⟨1788178547630326933173037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2384238063507102577564049 1788178547630326933173037)
          ·
            refine ⟨670566955361372599939889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1788178547630326933173037 670566955361372599939889)
            ·
              refine ⟨502925216521029449954917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 670566955361372599939889 502925216521029449954917)
              ·
                refine ⟨94298478097693021866547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 502925216521029449954917 94298478097693021866547)
                ·
                  refine ⟨141447717146539532799821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 94298478097693021866547 141447717146539532799821)
                  ·
                    refine ⟨53042893929952324799933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 141447717146539532799821 53042893929952324799933)
                    ·
                      rfl

theorem cell22_154951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 2, 4, 1, 3].length) (baseStart_154951 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_154951 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_154951 prefixEnd_154951 := by exact prefixLift 154951
  have htrace : WordTrace (prefixWord ++ tailWord_154951) baseStart_154951 baseEnd_154951 := by
    simpa [prefixWord, tailWord_154951, baseEnd_154951] using wordTrace_append hprefix tailTrace_154951
  have hstable : (prefixWord ++ tailWord_154951).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_154951).length < 2 ^ (prefixWord ++ tailWord_154951).sum := by decide
  have hdescent : baseEnd_154951 < baseStart_154951 := by decide
  rcases family_descends (prefixWord ++ tailWord_154951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_154977 : List Nat := [1, 2, 3, 1, 1, 1, 1, 5, 3, 4]
def baseStart_154977 : Nat := 118140960795 + 154977 * 2 ^ 59
def prefixEnd_154977 : Nat := 4983230072969 + 3 ^ 40 * 154977 * 2
def baseEnd_154977 : Nat := 53051794261296923649853

theorem tailTrace_154977 : CollatzResearch.WordTrace tailWord_154977 prefixEnd_154977 53051794261296923649853 := by
  unfold tailWord_154977
  simp only [CollatzResearch.WordTrace]
  refine ⟨5652475559552271809487185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3768317039701514539658123 5652475559552271809487185)
  ·
    refine ⟨4239356669664203857115389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5652475559552271809487185 4239356669664203857115389)
    ·
      refine ⟨1589758751124076446418271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4239356669664203857115389 1589758751124076446418271)
      ·
        refine ⟨2384638126686114669627407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1589758751124076446418271 2384638126686114669627407)
        ·
          refine ⟨3576957190029172004441111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2384638126686114669627407 3576957190029172004441111)
          ·
            refine ⟨5365435785043758006661667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3576957190029172004441111 5365435785043758006661667)
            ·
              refine ⟨8048153677565637009992501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5365435785043758006661667 8048153677565637009992501)
              ·
                refine ⟨754514407271778469686797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8048153677565637009992501 754514407271778469686797)
                ·
                  refine ⟨282942902726916926132549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 754514407271778469686797 282942902726916926132549)
                  ·
                    refine ⟨53051794261296923649853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 282942902726916926132549 53051794261296923649853)
                    ·
                      rfl

theorem cell22_154977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 5, 3, 4].length) (baseStart_154977 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_154977 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_154977 prefixEnd_154977 := by exact prefixLift 154977
  have htrace : WordTrace (prefixWord ++ tailWord_154977) baseStart_154977 baseEnd_154977 := by
    simpa [prefixWord, tailWord_154977, baseEnd_154977] using wordTrace_append hprefix tailTrace_154977
  have hstable : (prefixWord ++ tailWord_154977).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_154977).length < 2 ^ (prefixWord ++ tailWord_154977).sum := by decide
  have hdescent : baseEnd_154977 < baseStart_154977 := by decide
  rcases family_descends (prefixWord ++ tailWord_154977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_154994 : List Nat := [3, 2, 1, 2, 1, 2, 1, 5, 1, 4]
def baseStart_154994 : Nat := 118140960795 + 154994 * 2 ^ 59
def prefixEnd_154994 : Nat := 4983230072969 + 3 ^ 40 * 154994 * 2
def baseEnd_154994 : Nat := 53057613708714545974801

theorem tailTrace_154994 : CollatzResearch.WordTrace tailWord_154994 prefixEnd_154994 53057613708714545974801 := by
  unfold tailWord_154994
  simp only [CollatzResearch.WordTrace]
  refine ⟨1413273900122670928214009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3768730400327122475237357 1413273900122670928214009)
  ·
    refine ⟨1059955425092003196160507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1413273900122670928214009 1059955425092003196160507)
    ·
      refine ⟨1589933137638004794240761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1059955425092003196160507 1589933137638004794240761)
      ·
        refine ⟨1192449853228503595680571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1589933137638004794240761 1192449853228503595680571)
        ·
          refine ⟨1788674779842755393520857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1192449853228503595680571 1788674779842755393520857)
          ·
            refine ⟨1341506084882066545140643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1788674779842755393520857 1341506084882066545140643)
            ·
              refine ⟨2012259127323099817710965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1341506084882066545140643 2012259127323099817710965)
              ·
                refine ⟨188649293186540607910403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2012259127323099817710965 188649293186540607910403)
                ·
                  refine ⟨282973939779810911865605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 188649293186540607910403 282973939779810911865605)
                  ·
                    refine ⟨53057613708714545974801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 282973939779810911865605 53057613708714545974801)
                    ·
                      rfl

theorem cell22_154994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 1, 5, 1, 4].length) (baseStart_154994 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_154994 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_154994 prefixEnd_154994 := by exact prefixLift 154994
  have htrace : WordTrace (prefixWord ++ tailWord_154994) baseStart_154994 baseEnd_154994 := by
    simpa [prefixWord, tailWord_154994, baseEnd_154994] using wordTrace_append hprefix tailTrace_154994
  have hstable : (prefixWord ++ tailWord_154994).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_154994).length < 2 ^ (prefixWord ++ tailWord_154994).sum := by decide
  have hdescent : baseEnd_154994 < baseStart_154994 := by decide
  rcases family_descends (prefixWord ++ tailWord_154994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_155028 : List Nat := [2, 4, 2, 1, 2, 3, 1, 2, 1, 4]
def baseStart_155028 : Nat := 118140960795 + 155028 * 2 ^ 59
def prefixEnd_155028 : Nat := 4983230072969 + 3 ^ 40 * 155028 * 2
def baseEnd_155028 : Nat := 53069252603549790624697

theorem tailTrace_155028 : CollatzResearch.WordTrace tailWord_155028 prefixEnd_155028 53069252603549790624697 := by
  unfold tailWord_155028
  simp only [CollatzResearch.WordTrace]
  refine ⟨2827167841183753759796869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3769557121578338346395825 2827167841183753759796869)
  ·
    refine ⟨530093970221953829961913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2827167841183753759796869 530093970221953829961913)
    ·
      refine ⟨397570477666465372471435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 530093970221953829961913 397570477666465372471435)
      ·
        refine ⟨596355716499698058707153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 397570477666465372471435 596355716499698058707153)
        ·
          refine ⟨447266787374773544030365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 596355716499698058707153 447266787374773544030365)
          ·
            refine ⟨167725045265540079011387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 447266787374773544030365 167725045265540079011387)
            ·
              refine ⟨251587567898310118517081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 167725045265540079011387 251587567898310118517081)
              ·
                refine ⟨188690675923732588887811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 251587567898310118517081 188690675923732588887811)
                ·
                  refine ⟨283036013885598883331717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 188690675923732588887811 283036013885598883331717)
                  ·
                    refine ⟨53069252603549790624697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 283036013885598883331717 53069252603549790624697)
                    ·
                      rfl

theorem cell22_155028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 3, 1, 2, 1, 4].length) (baseStart_155028 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_155028 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_155028 prefixEnd_155028 := by exact prefixLift 155028
  have htrace : WordTrace (prefixWord ++ tailWord_155028) baseStart_155028 baseEnd_155028 := by
    simpa [prefixWord, tailWord_155028, baseEnd_155028] using wordTrace_append hprefix tailTrace_155028
  have hstable : (prefixWord ++ tailWord_155028).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_155028).length < 2 ^ (prefixWord ++ tailWord_155028).sum := by decide
  have hdescent : baseEnd_155028 < baseStart_155028 := by decide
  rcases family_descends (prefixWord ++ tailWord_155028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_155039 : List Nat := [1, 1, 2, 5, 1, 2, 1, 3, 2, 4]
def baseStart_155039 : Nat := 118140960795 + 155039 * 2 ^ 59
def prefixEnd_155039 : Nat := 4983230072969 + 3 ^ 40 * 155039 * 2
def baseEnd_155039 : Nat := 53073018128349428599663

theorem tailTrace_155039 : CollatzResearch.WordTrace tailWord_155039 prefixEnd_155039 53073018128349428599663 := by
  unfold tailWord_155039
  simp only [CollatzResearch.WordTrace]
  refine ⟨5654736885327656398244171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3769824590218437598829447 5654736885327656398244171)
  ·
    refine ⟨8482105327991484597366257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5654736885327656398244171 8482105327991484597366257)
    ·
      refine ⟨6361578995993613448024693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8482105327991484597366257 6361578995993613448024693)
      ·
        refine ⟨596398030874401260752315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 6361578995993613448024693 596398030874401260752315)
        ·
          refine ⟨894597046311601891128473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 596398030874401260752315 894597046311601891128473)
          ·
            refine ⟨670947784733701418346355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 894597046311601891128473 670947784733701418346355)
            ·
              refine ⟨1006421677100552127519533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 670947784733701418346355 1006421677100552127519533)
              ·
                refine ⟨377408128912707047819825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1006421677100552127519533 377408128912707047819825)
                ·
                  refine ⟨283056096684530285864869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 377408128912707047819825 283056096684530285864869)
                  ·
                    refine ⟨53073018128349428599663, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 283056096684530285864869 53073018128349428599663)
                    ·
                      rfl

theorem cell22_155039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 1, 3, 2, 4].length) (baseStart_155039 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_155039 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_155039 prefixEnd_155039 := by exact prefixLift 155039
  have htrace : WordTrace (prefixWord ++ tailWord_155039) baseStart_155039 baseEnd_155039 := by
    simpa [prefixWord, tailWord_155039, baseEnd_155039] using wordTrace_append hprefix tailTrace_155039
  have hstable : (prefixWord ++ tailWord_155039).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_155039).length < 2 ^ (prefixWord ++ tailWord_155039).sum := by decide
  have hdescent : baseEnd_155039 < baseStart_155039 := by decide
  rcases family_descends (prefixWord ++ tailWord_155039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_155103 : List Nat := [1, 1, 2, 3, 3, 1, 4, 3, 1, 3]
def baseStart_155103 : Nat := 118140960795 + 155103 * 2 ^ 59
def prefixEnd_155103 : Nat := 4983230072969 + 3 ^ 40 * 155103 * 2
def baseEnd_155103 : Nat := 53094926636274594999467

theorem tailTrace_155103 : CollatzResearch.WordTrace tailWord_155103 prefixEnd_155103 53094926636274594999467 := by
  unfold tailWord_155103
  simp only [CollatzResearch.WordTrace]
  refine ⟨5657071157095795328573963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3771380771397196885715975 5657071157095795328573963)
  ·
    refine ⟨8485606735643692992860945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5657071157095795328573963 8485606735643692992860945)
    ·
      refine ⟨6364205051732769744645709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8485606735643692992860945 6364205051732769744645709)
      ·
        refine ⟨2386576894399788654242141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6364205051732769744645709 2386576894399788654242141)
        ·
          refine ⟨894966335399920745340803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2386576894399788654242141 894966335399920745340803)
          ·
            refine ⟨1342449503099881118011205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 894966335399920745340803 1342449503099881118011205)
            ·
              refine ⟨251709281831227709627101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1342449503099881118011205 251709281831227709627101)
              ·
                refine ⟨94390980686710391110163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 251709281831227709627101 94390980686710391110163)
                ·
                  refine ⟨141586471030065586665245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 94390980686710391110163 141586471030065586665245)
                  ·
                    refine ⟨53094926636274594999467, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 141586471030065586665245 53094926636274594999467)
                    ·
                      rfl

theorem cell22_155103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 4, 3, 1, 3].length) (baseStart_155103 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_155103 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_155103 prefixEnd_155103 := by exact prefixLift 155103
  have htrace : WordTrace (prefixWord ++ tailWord_155103) baseStart_155103 baseEnd_155103 := by
    simpa [prefixWord, tailWord_155103, baseEnd_155103] using wordTrace_append hprefix tailTrace_155103
  have hstable : (prefixWord ++ tailWord_155103).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_155103).length < 2 ^ (prefixWord ++ tailWord_155103).sum := by decide
  have hdescent : baseEnd_155103 < baseStart_155103 := by decide
  rcases family_descends (prefixWord ++ tailWord_155103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_155144 : List Nat := [2, 1, 3, 2, 1, 1, 4, 2, 6]
def baseStart_155144 : Nat := 118140960795 + 155144 * 2 ^ 59
def prefixEnd_155144 : Nat := 4983230072969 + 3 ^ 40 * 155144 * 2
def baseEnd_155144 : Nat := 17702987258054718241447

theorem tailTrace_155144 : CollatzResearch.WordTrace tailWord_155144 prefixEnd_155144 17702987258054718241447 := by
  unfold tailWord_155144
  simp only [CollatzResearch.WordTrace]
  refine ⟨2829283274973629665408243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3772377699964839553877657 2829283274973629665408243)
  ·
    refine ⟨4243924912460444498112365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2829283274973629665408243 4243924912460444498112365)
    ·
      refine ⟨1591471842172666686792137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4243924912460444498112365 1591471842172666686792137)
      ·
        refine ⟨1193603881629500015094103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1591471842172666686792137 1193603881629500015094103)
        ·
          refine ⟨1790405822444250022641155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1193603881629500015094103 1790405822444250022641155)
          ·
            refine ⟨2685608733666375033961733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1790405822444250022641155 2685608733666375033961733)
            ·
              refine ⟨503551637562445318867825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2685608733666375033961733 503551637562445318867825)
              ·
                refine ⟨377663728171833989150869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 503551637562445318867825 377663728171833989150869)
                ·
                  refine ⟨17702987258054718241447, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 377663728171833989150869 17702987258054718241447)
                  ·
                    rfl

theorem cell22_155144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 4, 2, 6].length) (baseStart_155144 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_155144 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_155144 prefixEnd_155144 := by exact prefixLift 155144
  have htrace : WordTrace (prefixWord ++ tailWord_155144) baseStart_155144 baseEnd_155144 := by
    simpa [prefixWord, tailWord_155144, baseEnd_155144] using wordTrace_append hprefix tailTrace_155144
  have hstable : (prefixWord ++ tailWord_155144).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_155144).length < 2 ^ (prefixWord ++ tailWord_155144).sum := by decide
  have hdescent : baseEnd_155144 < baseStart_155144 := by decide
  rcases family_descends (prefixWord ++ tailWord_155144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_155146 : List Nat := [3, 1, 2, 2, 2, 2, 1, 4, 1, 4]
def baseStart_155146 : Nat := 118140960795 + 155146 * 2 ^ 59
def prefixEnd_155146 : Nat := 4983230072969 + 3 ^ 40 * 155146 * 2
def baseEnd_155146 : Nat := 53109646415036816174335

theorem tailTrace_155146 : CollatzResearch.WordTrace tailWord_155146 prefixEnd_155146 53109646415036816174335 := by
  unfold tailWord_155146
  simp only [CollatzResearch.WordTrace]
  refine ⟨1414659873985003418097323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3772426330626675781592861 1414659873985003418097323)
  ·
    refine ⟨2121989810977505127145985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1414659873985003418097323 2121989810977505127145985)
    ·
      refine ⟨1591492358233128845359489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2121989810977505127145985 1591492358233128845359489)
      ·
        refine ⟨1193619268674846634019617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1591492358233128845359489 1193619268674846634019617)
        ·
          refine ⟨895214451506134975514713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1193619268674846634019617 895214451506134975514713)
          ·
            refine ⟨671410838629601231636035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 895214451506134975514713 671410838629601231636035)
            ·
              refine ⟨1007116257944401847454053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 671410838629601231636035 1007116257944401847454053)
              ·
                refine ⟨188834298364575346397635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1007116257944401847454053 188834298364575346397635)
                ·
                  refine ⟨283251447546863019596453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 188834298364575346397635 283251447546863019596453)
                  ·
                    refine ⟨53109646415036816174335, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 283251447546863019596453 53109646415036816174335)
                    ·
                      rfl

theorem cell22_155146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 1, 4, 1, 4].length) (baseStart_155146 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_155146 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_155146 prefixEnd_155146 := by exact prefixLift 155146
  have htrace : WordTrace (prefixWord ++ tailWord_155146) baseStart_155146 baseEnd_155146 := by
    simpa [prefixWord, tailWord_155146, baseEnd_155146] using wordTrace_append hprefix tailTrace_155146
  have hstable : (prefixWord ++ tailWord_155146).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_155146).length < 2 ^ (prefixWord ++ tailWord_155146).sum := by decide
  have hdescent : baseEnd_155146 < baseStart_155146 := by decide
  rcases family_descends (prefixWord ++ tailWord_155146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_155189 : List Nat := [1, 3, 3, 1, 1, 3, 1, 9]
def baseStart_155189 : Nat := 118140960795 + 155189 * 2 ^ 59
def prefixEnd_155189 : Nat := 4983230072969 + 3 ^ 40 * 155189 * 2
def baseEnd_155189 : Nat := 5902707354866559705467

theorem tailTrace_155189 : CollatzResearch.WordTrace tailWord_155189 prefixEnd_155189 5902707354866559705467 := by
  unfold tailWord_155189
  simp only [CollatzResearch.WordTrace]
  refine ⟨5660207834784232016204621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3773471889856154677469747 5660207834784232016204621)
  ·
    refine ⟨2122577938044087006076733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5660207834784232016204621 2122577938044087006076733)
    ·
      refine ⟨795966726766532627278775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2122577938044087006076733 795966726766532627278775)
      ·
        refine ⟨1193950090149798940918163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 795966726766532627278775 1193950090149798940918163)
        ·
          refine ⟨1790925135224698411377245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1193950090149798940918163 1790925135224698411377245)
          ·
            refine ⟨671596925709261904266467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1790925135224698411377245 671596925709261904266467)
            ·
              refine ⟨1007395388563892856399701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 671596925709261904266467 1007395388563892856399701)
              ·
                refine ⟨5902707354866559705467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 1007395388563892856399701 5902707354866559705467)
                ·
                  rfl

theorem cell22_155189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 1, 9].length) (baseStart_155189 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_155189 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_155189 prefixEnd_155189 := by exact prefixLift 155189
  have htrace : WordTrace (prefixWord ++ tailWord_155189) baseStart_155189 baseEnd_155189 := by
    simpa [prefixWord, tailWord_155189, baseEnd_155189] using wordTrace_append hprefix tailTrace_155189
  have hstable : (prefixWord ++ tailWord_155189).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_155189).length < 2 ^ (prefixWord ++ tailWord_155189).sum := by decide
  have hdescent : baseEnd_155189 < baseStart_155189 := by decide
  rcases family_descends (prefixWord ++ tailWord_155189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_155193 : List Nat := [1, 2, 1, 5, 1, 3, 1, 3, 2, 3]
def baseStart_155193 : Nat := 118140960795 + 155193 * 2 ^ 59
def prefixEnd_155193 : Nat := 4983230072969 + 3 ^ 40 * 155193 * 2
def baseEnd_155193 : Nat := 53125735475544360249191

theorem tailTrace_155193 : CollatzResearch.WordTrace tailWord_155193 prefixEnd_155193 53125735475544360249191 := by
  unfold tailWord_155193
  simp only [CollatzResearch.WordTrace]
  refine ⟨5660353726769740699350233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3773569151179827132900155 5660353726769740699350233)
  ·
    refine ⟨4245265295077305524512675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5660353726769740699350233 4245265295077305524512675)
    ·
      refine ⟨6367897942615958286769013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4245265295077305524512675 6367897942615958286769013)
      ·
        refine ⟨596990432120246089384595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 6367897942615958286769013 596990432120246089384595)
        ·
          refine ⟨895485648180369134076893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 596990432120246089384595 895485648180369134076893)
          ·
            refine ⟨335807118067638425278835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 895485648180369134076893 335807118067638425278835)
            ·
              refine ⟨503710677101457637918253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 335807118067638425278835 503710677101457637918253)
              ·
                refine ⟨188891503913046614219345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 503710677101457637918253 188891503913046614219345)
                ·
                  refine ⟨141668627934784960664509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 188891503913046614219345 141668627934784960664509)
                  ·
                    refine ⟨53125735475544360249191, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 141668627934784960664509 53125735475544360249191)
                    ·
                      rfl

theorem cell22_155193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 3, 1, 3, 2, 3].length) (baseStart_155193 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_155193 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_155193 prefixEnd_155193 := by exact prefixLift 155193
  have htrace : WordTrace (prefixWord ++ tailWord_155193) baseStart_155193 baseEnd_155193 := by
    simpa [prefixWord, tailWord_155193, baseEnd_155193] using wordTrace_append hprefix tailTrace_155193
  have hstable : (prefixWord ++ tailWord_155193).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_155193).length < 2 ^ (prefixWord ++ tailWord_155193).sum := by decide
  have hdescent : baseEnd_155193 < baseStart_155193 := by decide
  rcases family_descends (prefixWord ++ tailWord_155193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_155229 : List Nat := [1, 4, 4, 2, 1, 2, 2, 2, 4]
def baseStart_155229 : Nat := 118140960795 + 155229 * 2 ^ 59
def prefixEnd_155229 : Nat := 4983230072969 + 3 ^ 40 * 155229 * 2
def baseEnd_155229 : Nat := 17712686337084088783027

theorem tailTrace_155229 : CollatzResearch.WordTrace tailWord_155229 prefixEnd_155229 17712686337084088783027 := by
  unfold tailWord_155229
  simp only [CollatzResearch.WordTrace]
  refine ⟨5661666754639318847660741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3774444503092879231773827 5661666754639318847660741)
  ·
    refine ⟨1061562516494872283936389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5661666754639318847660741 1061562516494872283936389)
    ·
      refine ⟨199042971842788553238073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1061562516494872283936389 199042971842788553238073)
      ·
        refine ⟨149282228882091414928555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 199042971842788553238073 149282228882091414928555)
        ·
          refine ⟨223923343323137122392833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 149282228882091414928555 223923343323137122392833)
          ·
            refine ⟨167942507492352841794625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 223923343323137122392833 167942507492352841794625)
            ·
              refine ⟨125956880619264631345969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 167942507492352841794625 125956880619264631345969)
              ·
                refine ⟨94467660464448473509477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 125956880619264631345969 94467660464448473509477)
                ·
                  refine ⟨17712686337084088783027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 94467660464448473509477 17712686337084088783027)
                  ·
                    rfl

theorem cell22_155229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 2, 2, 2, 4].length) (baseStart_155229 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_155229 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_155229 prefixEnd_155229 := by exact prefixLift 155229
  have htrace : WordTrace (prefixWord ++ tailWord_155229) baseStart_155229 baseEnd_155229 := by
    simpa [prefixWord, tailWord_155229, baseEnd_155229] using wordTrace_append hprefix tailTrace_155229
  have hstable : (prefixWord ++ tailWord_155229).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_155229).length < 2 ^ (prefixWord ++ tailWord_155229).sum := by decide
  have hdescent : baseEnd_155229 < baseStart_155229 := by decide
  rcases family_descends (prefixWord ++ tailWord_155229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_155296 : List Nat := [2, 1, 1, 4, 3, 1, 1, 3, 6]
def baseStart_155296 : Nat := 118140960795 + 155296 * 2 ^ 59
def prefixEnd_155296 : Nat := 4983230072969 + 3 ^ 40 * 155296 * 2
def baseEnd_155296 : Nat := 17720331493495474974625

theorem tailTrace_155296 : CollatzResearch.WordTrace tailWord_155296 prefixEnd_155296 17720331493495474974625 := by
  unfold tailWord_155296
  simp only [CollatzResearch.WordTrace]
  refine ⟨2832055222698294645174871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3776073630264392860233161 2832055222698294645174871)
  ·
    refine ⟨4248082834047441967762307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2832055222698294645174871 4248082834047441967762307)
    ·
      refine ⟨6372124251071162951643461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4248082834047441967762307 6372124251071162951643461)
      ·
        refine ⟨1194773297075843053433149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6372124251071162951643461 1194773297075843053433149)
        ·
          refine ⟨448039986403441145037431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1194773297075843053433149 448039986403441145037431)
          ·
            refine ⟨672059979605161717556147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 448039986403441145037431 672059979605161717556147)
            ·
              refine ⟨1008089969407742576334221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 672059979605161717556147 1008089969407742576334221)
              ·
                refine ⟨378033738527903466125333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1008089969407742576334221 378033738527903466125333)
                ·
                  refine ⟨17720331493495474974625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 378033738527903466125333 17720331493495474974625)
                  ·
                    rfl

theorem cell22_155296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 1, 3, 6].length) (baseStart_155296 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_155296 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_155296 prefixEnd_155296 := by exact prefixLift 155296
  have htrace : WordTrace (prefixWord ++ tailWord_155296) baseStart_155296 baseEnd_155296 := by
    simpa [prefixWord, tailWord_155296, baseEnd_155296] using wordTrace_append hprefix tailTrace_155296
  have hstable : (prefixWord ++ tailWord_155296).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_155296).length < 2 ^ (prefixWord ++ tailWord_155296).sum := by decide
  have hdescent : baseEnd_155296 < baseStart_155296 := by decide
  rcases family_descends (prefixWord ++ tailWord_155296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_155398 : List Nat := [6, 2, 2, 1, 1, 1, 1, 4, 4]
def baseStart_155398 : Nat := 118140960795 + 155398 * 2 ^ 59
def prefixEnd_155398 : Nat := 4983230072969 + 3 ^ 40 * 155398 * 2
def baseEnd_155398 : Nat := 17731970388330719624521

theorem tailTrace_155398 : CollatzResearch.WordTrace tailWord_155398 prefixEnd_155398 17731970388330719624521 := by
  unfold tailWord_155398
  simp only [CollatzResearch.WordTrace]
  refine ⟨177119709094595647205089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 3778553794018040473708565 177119709094595647205089)
  ·
    refine ⟨132839781820946735403817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 177119709094595647205089 132839781820946735403817)
    ·
      refine ⟨99629836365710051552863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 132839781820946735403817 99629836365710051552863)
      ·
        refine ⟨149444754548565077329295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99629836365710051552863 149444754548565077329295)
        ·
          refine ⟨224167131822847615993943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 149444754548565077329295 224167131822847615993943)
          ·
            refine ⟨336250697734271423990915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 224167131822847615993943 336250697734271423990915)
            ·
              refine ⟨504376046601407135986373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 336250697734271423990915 504376046601407135986373)
              ·
                refine ⟨94570508737763837997445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 504376046601407135986373 94570508737763837997445)
                ·
                  refine ⟨17731970388330719624521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 94570508737763837997445 17731970388330719624521)
                  ·
                    rfl

theorem cell22_155398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 1, 1, 4, 4].length) (baseStart_155398 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_155398 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_155398 prefixEnd_155398 := by exact prefixLift 155398
  have htrace : WordTrace (prefixWord ++ tailWord_155398) baseStart_155398 baseEnd_155398 := by
    simpa [prefixWord, tailWord_155398, baseEnd_155398] using wordTrace_append hprefix tailTrace_155398
  have hstable : (prefixWord ++ tailWord_155398).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_155398).length < 2 ^ (prefixWord ++ tailWord_155398).sum := by decide
  have hdescent : baseEnd_155398 < baseStart_155398 := by decide
  rcases family_descends (prefixWord ++ tailWord_155398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_155401 : List Nat := [1, 2, 1, 1, 3, 2, 1, 4, 2, 5]
def baseStart_155401 : Nat := 118140960795 + 155401 * 2 ^ 59
def prefixEnd_155401 : Nat := 4983230072969 + 3 ^ 40 * 155401 * 2
def baseEnd_155401 : Nat := 53196938126301151048553

theorem tailTrace_155401 : CollatzResearch.WordTrace tailWord_155401 prefixEnd_155401 53196938126301151048553 := by
  unfold tailWord_155401
  simp only [CollatzResearch.WordTrace]
  refine ⟨5667940110016192222922057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3778626740010794815281371 5667940110016192222922057)
  ·
    refine ⟨4250955082512144167191543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5667940110016192222922057 4250955082512144167191543)
    ·
      refine ⟨6376432623768216250787315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4250955082512144167191543 6376432623768216250787315)
      ·
        refine ⟨9564648935652324376180973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6376432623768216250787315 9564648935652324376180973)
        ·
          refine ⟨3586743350869621641067865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9564648935652324376180973 3586743350869621641067865)
          ·
            refine ⟨2690057513152216230800899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3586743350869621641067865 2690057513152216230800899)
            ·
              refine ⟨4035086269728324346201349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2690057513152216230800899 4035086269728324346201349)
              ·
                refine ⟨756578675574060814912753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4035086269728324346201349 756578675574060814912753)
                ·
                  refine ⟨567434006680545611184565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 756578675574060814912753 567434006680545611184565)
                  ·
                    refine ⟨53196938126301151048553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 567434006680545611184565 53196938126301151048553)
                    ·
                      rfl

theorem cell22_155401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 4, 2, 5].length) (baseStart_155401 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_155401 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_155401 prefixEnd_155401 := by exact prefixLift 155401
  have htrace : WordTrace (prefixWord ++ tailWord_155401) baseStart_155401 baseEnd_155401 := by
    simpa [prefixWord, tailWord_155401, baseEnd_155401] using wordTrace_append hprefix tailTrace_155401
  have hstable : (prefixWord ++ tailWord_155401).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_155401).length < 2 ^ (prefixWord ++ tailWord_155401).sum := by decide
  have hdescent : baseEnd_155401 < baseStart_155401 := by decide
  rcases family_descends (prefixWord ++ tailWord_155401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_155418 : List Nat := [3, 1, 1, 3, 2, 3, 1, 1, 2, 5]
def baseStart_155418 : Nat := 118140960795 + 155418 * 2 ^ 59
def prefixEnd_155418 : Nat := 4983230072969 + 3 ^ 40 * 155418 * 2
def baseEnd_155418 : Nat := 53202757573718773373501

theorem tailTrace_155418 : CollatzResearch.WordTrace tailWord_155418 prefixEnd_155418 53202757573718773373501 := by
  unfold tailWord_155418
  simp only [CollatzResearch.WordTrace]
  refine ⟨1417140037738651031572727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3779040100636402750860605 1417140037738651031572727)
  ·
    refine ⟨2125710056607976547359091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1417140037738651031572727 2125710056607976547359091)
    ·
      refine ⟨3188565084911964821038637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2125710056607976547359091 3188565084911964821038637)
      ·
        refine ⟨1195711906841986807889489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3188565084911964821038637 1195711906841986807889489)
        ·
          refine ⟨896783930131490105917117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1195711906841986807889489 896783930131490105917117)
          ·
            refine ⟨336293973799308789718919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 896783930131490105917117 336293973799308789718919)
            ·
              refine ⟨504440960698963184578379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 336293973799308789718919 504440960698963184578379)
              ·
                refine ⟨756661441048444776867569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 504440960698963184578379 756661441048444776867569)
                ·
                  refine ⟨567496080786333582650677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 756661441048444776867569 567496080786333582650677)
                  ·
                    refine ⟨53202757573718773373501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 567496080786333582650677 53202757573718773373501)
                    ·
                      rfl

theorem cell22_155418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 3, 1, 1, 2, 5].length) (baseStart_155418 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_155418 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_155418 prefixEnd_155418 := by exact prefixLift 155418
  have htrace : WordTrace (prefixWord ++ tailWord_155418) baseStart_155418 baseEnd_155418 := by
    simpa [prefixWord, tailWord_155418, baseEnd_155418] using wordTrace_append hprefix tailTrace_155418
  have hstable : (prefixWord ++ tailWord_155418).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_155418).length < 2 ^ (prefixWord ++ tailWord_155418).sum := by decide
  have hdescent : baseEnd_155418 < baseStart_155418 := by decide
  rcases family_descends (prefixWord ++ tailWord_155418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_155450 : List Nat := [3, 1, 1, 1, 5, 2, 1, 3, 1, 4]
def baseStart_155450 : Nat := 118140960795 + 155450 * 2 ^ 59
def prefixEnd_155450 : Nat := 4983230072969 + 3 ^ 40 * 155450 * 2
def baseEnd_155450 : Nat := 53213711827681356573403

theorem tailTrace_155450 : CollatzResearch.WordTrace tailWord_155450 prefixEnd_155450 53213711827681356573403 := by
  unfold tailWord_155450
  simp only [CollatzResearch.WordTrace]
  refine ⟨1417431821709668397863951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3779818191225782394303869 1417431821709668397863951)
  ·
    refine ⟨2126147732564502596795927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1417431821709668397863951 2126147732564502596795927)
    ·
      refine ⟨3189221598846753895193891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2126147732564502596795927 3189221598846753895193891)
      ·
        refine ⟨4783832398270130842790837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3189221598846753895193891 4783832398270130842790837)
        ·
          refine ⟨448484287337824766511641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 4783832398270130842790837 448484287337824766511641)
          ·
            refine ⟨336363215503368574883731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 448484287337824766511641 336363215503368574883731)
            ·
              refine ⟨504544823255052862325597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 336363215503368574883731 504544823255052862325597)
              ·
                refine ⟨189204308720644823372099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 504544823255052862325597 189204308720644823372099)
                ·
                  refine ⟨283806463080967235058149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 189204308720644823372099 283806463080967235058149)
                  ·
                    refine ⟨53213711827681356573403, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 283806463080967235058149 53213711827681356573403)
                    ·
                      rfl

theorem cell22_155450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 2, 1, 3, 1, 4].length) (baseStart_155450 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_155450 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_155450 prefixEnd_155450 := by exact prefixLift 155450
  have htrace : WordTrace (prefixWord ++ tailWord_155450) baseStart_155450 baseEnd_155450 := by
    simpa [prefixWord, tailWord_155450, baseEnd_155450] using wordTrace_append hprefix tailTrace_155450
  have hstable : (prefixWord ++ tailWord_155450).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_155450).length < 2 ^ (prefixWord ++ tailWord_155450).sum := by decide
  have hdescent : baseEnd_155450 < baseStart_155450 := by decide
  rcases family_descends (prefixWord ++ tailWord_155450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_155583 : List Nat := [1, 1, 2, 2, 2, 1, 4, 3, 6]
def baseStart_155583 : Nat := 118140960795 + 155583 * 2 ^ 59
def prefixEnd_155583 : Nat := 4983230072969 + 3 ^ 40 * 155583 * 2
def baseEnd_155583 : Nat := 17753080148571114332665

theorem tailTrace_155583 : CollatzResearch.WordTrace tailWord_155583 prefixEnd_155583 17753080148571114332665 := by
  unfold tailWord_155583
  simp only [CollatzResearch.WordTrace]
  refine ⟨5674578195356837306047403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3783052130237891537364935 5674578195356837306047403)
  ·
    refine ⟨8511867293035255959071105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5674578195356837306047403 8511867293035255959071105)
    ·
      refine ⟨6383900469776441969303329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8511867293035255959071105 6383900469776441969303329)
      ·
        refine ⟨4787925352332331476977497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6383900469776441969303329 4787925352332331476977497)
        ·
          refine ⟨3590944014249248607733123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4787925352332331476977497 3590944014249248607733123)
          ·
            refine ⟨5386416021373872911599685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3590944014249248607733123 5386416021373872911599685)
            ·
              refine ⟨1009953004007601170924941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5386416021373872911599685 1009953004007601170924941)
              ·
                refine ⟨378732376502850439096853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1009953004007601170924941 378732376502850439096853)
                ·
                  refine ⟨17753080148571114332665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 378732376502850439096853 17753080148571114332665)
                  ·
                    rfl

theorem cell22_155583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 4, 3, 6].length) (baseStart_155583 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_155583 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_155583 prefixEnd_155583 := by exact prefixLift 155583
  have htrace : WordTrace (prefixWord ++ tailWord_155583) baseStart_155583 baseEnd_155583 := by
    simpa [prefixWord, tailWord_155583, baseEnd_155583] using wordTrace_append hprefix tailTrace_155583
  have hstable : (prefixWord ++ tailWord_155583).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_155583).length < 2 ^ (prefixWord ++ tailWord_155583).sum := by decide
  have hdescent : baseEnd_155583 < baseStart_155583 := by decide
  rcases family_descends (prefixWord ++ tailWord_155583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_155615 : List Nat := [1, 1, 2, 3, 4, 1, 2, 2, 1, 5]
def baseStart_155615 : Nat := 118140960795 + 155615 * 2 ^ 59
def prefixEnd_155615 : Nat := 4983230072969 + 3 ^ 40 * 155615 * 2
def baseEnd_155615 : Nat := 53270194699675926197897

theorem tailTrace_155615 : CollatzResearch.WordTrace tailWord_155615 prefixEnd_155615 53270194699675926197897 := by
  unfold tailWord_155615
  simp only [CollatzResearch.WordTrace]
  refine ⟨5675745331240906771212299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3783830220827271180808199 5675745331240906771212299)
  ·
    refine ⟨8513617996861360156818449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5675745331240906771212299 8513617996861360156818449)
    ·
      refine ⟨6385213497646020117613837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8513617996861360156818449 6385213497646020117613837)
      ·
        refine ⟨2394455061617257544105189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6385213497646020117613837 2394455061617257544105189)
        ·
          refine ⟨448960324053235789519723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2394455061617257544105189 448960324053235789519723)
          ·
            refine ⟨673440486079853684279585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 448960324053235789519723 673440486079853684279585)
            ·
              refine ⟨505080364559890263209689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 673440486079853684279585 505080364559890263209689)
              ·
                refine ⟨378810273419917697407267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 505080364559890263209689 378810273419917697407267)
                ·
                  refine ⟨568215410129876546110901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 378810273419917697407267 568215410129876546110901)
                  ·
                    refine ⟨53270194699675926197897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 568215410129876546110901 53270194699675926197897)
                    ·
                      rfl

theorem cell22_155615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 2, 2, 1, 5].length) (baseStart_155615 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_155615 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_155615 prefixEnd_155615 := by exact prefixLift 155615
  have htrace : WordTrace (prefixWord ++ tailWord_155615) baseStart_155615 baseEnd_155615 := by
    simpa [prefixWord, tailWord_155615, baseEnd_155615] using wordTrace_append hprefix tailTrace_155615
  have hstable : (prefixWord ++ tailWord_155615).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_155615).length < 2 ^ (prefixWord ++ tailWord_155615).sum := by decide
  have hdescent : baseEnd_155615 < baseStart_155615 := by decide
  rcases family_descends (prefixWord ++ tailWord_155615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_155619 : List Nat := [1, 1, 1, 6, 1, 4, 2, 1, 1, 4]
def baseStart_155619 : Nat := 118140960795 + 155619 * 2 ^ 59
def prefixEnd_155619 : Nat := 4983230072969 + 3 ^ 40 * 155619 * 2
def baseEnd_155619 : Nat := 53271563981421249097885

theorem tailTrace_155619 : CollatzResearch.WordTrace tailWord_155619 prefixEnd_155619 53271563981421249097885 := by
  unfold tailWord_155619
  simp only [CollatzResearch.WordTrace]
  refine ⟨5675891223226415454357911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3783927482150943636238607 5675891223226415454357911)
  ·
    refine ⟨8513836834839623181536867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5675891223226415454357911 8513836834839623181536867)
    ·
      refine ⟨12770755252259434772305301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8513836834839623181536867 12770755252259434772305301)
      ·
        refine ⟨598629152449661004951811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 12770755252259434772305301 598629152449661004951811)
        ·
          refine ⟨897943728674491507427717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 598629152449661004951811 897943728674491507427717)
          ·
            refine ⟨168364449126467157642697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 897943728674491507427717 168364449126467157642697)
            ·
              refine ⟨126273336844850368232023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 168364449126467157642697 126273336844850368232023)
              ·
                refine ⟨189410005267275552348035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 126273336844850368232023 189410005267275552348035)
                ·
                  refine ⟨284115007900913328522053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 189410005267275552348035 284115007900913328522053)
                  ·
                    refine ⟨53271563981421249097885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 284115007900913328522053 53271563981421249097885)
                    ·
                      rfl

theorem cell22_155619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 4, 2, 1, 1, 4].length) (baseStart_155619 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_155619 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_155619 prefixEnd_155619 := by exact prefixLift 155619
  have htrace : WordTrace (prefixWord ++ tailWord_155619) baseStart_155619 baseEnd_155619 := by
    simpa [prefixWord, tailWord_155619, baseEnd_155619] using wordTrace_append hprefix tailTrace_155619
  have hstable : (prefixWord ++ tailWord_155619).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_155619).length < 2 ^ (prefixWord ++ tailWord_155619).sum := by decide
  have hdescent : baseEnd_155619 < baseStart_155619 := by decide
  rcases family_descends (prefixWord ++ tailWord_155619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_155632 : List Nat := [2, 1, 1, 1, 3, 2, 5, 2, 2, 3]
def baseStart_155632 : Nat := 118140960795 + 155632 * 2 ^ 59
def prefixEnd_155632 : Nat := 4983230072969 + 3 ^ 40 * 155632 * 2
def baseEnd_155632 : Nat := 53276014147093548522845

theorem tailTrace_155632 : CollatzResearch.WordTrace tailWord_155632 prefixEnd_155632 53276014147093548522845 := by
  unfold tailWord_155632
  simp only [CollatzResearch.WordTrace]
  refine ⟨2838182686089659337290575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3784243581452879116387433 2838182686089659337290575)
  ·
    refine ⟨4257274029134489005935863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2838182686089659337290575 4257274029134489005935863)
    ·
      refine ⟨6385911043701733508903795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4257274029134489005935863 6385911043701733508903795)
      ·
        refine ⟨9578866565552600263355693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6385911043701733508903795 9578866565552600263355693)
        ·
          refine ⟨3592074962082225098758385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9578866565552600263355693 3592074962082225098758385)
          ·
            refine ⟨2694056221561668824068789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3592074962082225098758385 2694056221561668824068789)
            ·
              refine ⟨252567770771406452256449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2694056221561668824068789 252567770771406452256449)
              ·
                refine ⟨189425828078554839192337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 252567770771406452256449 189425828078554839192337)
                ·
                  refine ⟨142069371058916129394253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 189425828078554839192337 142069371058916129394253)
                  ·
                    refine ⟨53276014147093548522845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 142069371058916129394253 53276014147093548522845)
                    ·
                      rfl

theorem cell22_155632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 5, 2, 2, 3].length) (baseStart_155632 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_155632 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_155632 prefixEnd_155632 := by exact prefixLift 155632
  have htrace : WordTrace (prefixWord ++ tailWord_155632) baseStart_155632 baseEnd_155632 := by
    simpa [prefixWord, tailWord_155632, baseEnd_155632] using wordTrace_append hprefix tailTrace_155632
  have hstable : (prefixWord ++ tailWord_155632).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_155632).length < 2 ^ (prefixWord ++ tailWord_155632).sum := by decide
  have hdescent : baseEnd_155632 < baseStart_155632 := by decide
  rcases family_descends (prefixWord ++ tailWord_155632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_155649 : List Nat := [1, 2, 4, 1, 2, 1, 5, 1, 2, 3]
def baseStart_155649 : Nat := 118140960795 + 155649 * 2 ^ 59
def prefixEnd_155649 : Nat := 4983230072969 + 3 ^ 40 * 155649 * 2
def baseEnd_155649 : Nat := 53281833594511170847793

theorem tailTrace_155649 : CollatzResearch.WordTrace tailWord_155649 prefixEnd_155649 53281833594511170847793 := by
  unfold tailWord_155649
  simp only [CollatzResearch.WordTrace]
  refine ⟨5676985413117730577950001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3784656942078487051966667 5676985413117730577950001)
  ·
    refine ⟨4257739059838297933462501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5676985413117730577950001 4257739059838297933462501)
    ·
      refine ⟨798326073719680862524219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4257739059838297933462501 798326073719680862524219)
      ·
        refine ⟨1197489110579521293786329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 798326073719680862524219 1197489110579521293786329)
        ·
          refine ⟨898116832934640970339747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1197489110579521293786329 898116832934640970339747)
          ·
            refine ⟨1347175249401961455509621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 898116832934640970339747 1347175249401961455509621)
            ·
              refine ⟨126297679631433886454027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1347175249401961455509621 126297679631433886454027)
              ·
                refine ⟨189446519447150829681041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 126297679631433886454027 189446519447150829681041)
                ·
                  refine ⟨142084889585363122260781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 189446519447150829681041 142084889585363122260781)
                  ·
                    refine ⟨53281833594511170847793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 142084889585363122260781 53281833594511170847793)
                    ·
                      rfl

theorem cell22_155649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 5, 1, 2, 3].length) (baseStart_155649 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_155649 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_155649 prefixEnd_155649 := by exact prefixLift 155649
  have htrace : WordTrace (prefixWord ++ tailWord_155649) baseStart_155649 baseEnd_155649 := by
    simpa [prefixWord, tailWord_155649, baseEnd_155649] using wordTrace_append hprefix tailTrace_155649
  have hstable : (prefixWord ++ tailWord_155649).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_155649).length < 2 ^ (prefixWord ++ tailWord_155649).sum := by decide
  have hdescent : baseEnd_155649 < baseStart_155649 := by decide
  rcases family_descends (prefixWord ++ tailWord_155649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_155668 : List Nat := [2, 4, 3, 2, 1, 2, 1, 3, 4]
def baseStart_155668 : Nat := 118140960795 + 155668 * 2 ^ 59
def prefixEnd_155668 : Nat := 4983230072969 + 3 ^ 40 * 155668 * 2
def baseEnd_155668 : Nat := 17762779227600484874245

theorem tailTrace_155668 : CollatzResearch.WordTrace tailWord_155668 prefixEnd_155668 17762779227600484874245 := by
  unfold tailWord_155668
  simp only [CollatzResearch.WordTrace]
  refine ⟨2838839200024448411445829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3785118933365931215261105 2838839200024448411445829)
  ·
    refine ⟨532282350004584077146093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2838839200024448411445829 532282350004584077146093)
    ·
      refine ⟨199605881251719028929785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 532282350004584077146093 199605881251719028929785)
      ·
        refine ⟨149704410938789271697339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 199605881251719028929785 149704410938789271697339)
        ·
          refine ⟨224556616408183907546009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 149704410938789271697339 224556616408183907546009)
          ·
            refine ⟨168417462306137930659507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 224556616408183907546009 168417462306137930659507)
            ·
              refine ⟨252626193459206895989261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 168417462306137930659507 252626193459206895989261)
              ·
                refine ⟨94734822547202585995973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 252626193459206895989261 94734822547202585995973)
                ·
                  refine ⟨17762779227600484874245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 94734822547202585995973 17762779227600484874245)
                  ·
                    rfl

theorem cell22_155668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 2, 1, 3, 4].length) (baseStart_155668 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_155668 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_155668 prefixEnd_155668 := by exact prefixLift 155668
  have htrace : WordTrace (prefixWord ++ tailWord_155668) baseStart_155668 baseEnd_155668 := by
    simpa [prefixWord, tailWord_155668, baseEnd_155668] using wordTrace_append hprefix tailTrace_155668
  have hstable : (prefixWord ++ tailWord_155668).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_155668).length < 2 ^ (prefixWord ++ tailWord_155668).sum := by decide
  have hdescent : baseEnd_155668 < baseStart_155668 := by decide
  rcases family_descends (prefixWord ++ tailWord_155668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_155694 : List Nat := [4, 1, 3, 1, 1, 2, 3, 1, 3, 3]
def baseStart_155694 : Nat := 118140960795 + 155694 * 2 ^ 59
def prefixEnd_155694 : Nat := 4983230072969 + 3 ^ 40 * 155694 * 2
def baseEnd_155694 : Nat := 53297238014146053472655

theorem tailTrace_155694 : CollatzResearch.WordTrace tailWord_155694 prefixEnd_155694 53297238014146053472655 := by
  unfold tailWord_155694
  simp only [CollatzResearch.WordTrace]
  refine ⟨709828337244337907917267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3785751131969802175558757 709828337244337907917267)
  ·
    refine ⟨1064742505866506861875901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 709828337244337907917267 1064742505866506861875901)
    ·
      refine ⟨399278439699940073203463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1064742505866506861875901 399278439699940073203463)
      ·
        refine ⟨598917659549910109805195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 399278439699940073203463 598917659549910109805195)
        ·
          refine ⟨898376489324865164707793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 598917659549910109805195 898376489324865164707793)
          ·
            refine ⟨673782366993648873530845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 898376489324865164707793 673782366993648873530845)
            ·
              refine ⟨252668387622618327574067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 673782366993648873530845 252668387622618327574067)
              ·
                refine ⟨379002581433927491361101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 252668387622618327574067 379002581433927491361101)
                ·
                  refine ⟨142125968037722809260413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 379002581433927491361101 142125968037722809260413)
                  ·
                    refine ⟨53297238014146053472655, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 142125968037722809260413 53297238014146053472655)
                    ·
                      rfl

theorem cell22_155694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 3, 1, 3, 3].length) (baseStart_155694 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_155694 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_155694 prefixEnd_155694 := by exact prefixLift 155694
  have htrace : WordTrace (prefixWord ++ tailWord_155694) baseStart_155694 baseEnd_155694 := by
    simpa [prefixWord, tailWord_155694, baseEnd_155694] using wordTrace_append hprefix tailTrace_155694
  have hstable : (prefixWord ++ tailWord_155694).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_155694).length < 2 ^ (prefixWord ++ tailWord_155694).sum := by decide
  have hdescent : baseEnd_155694 < baseStart_155694 := by decide
  rcases family_descends (prefixWord ++ tailWord_155694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_155700 : List Nat := [2, 5, 1, 2, 3, 1, 2, 1, 2, 3]
def baseStart_155700 : Nat := 118140960795 + 155700 * 2 ^ 59
def prefixEnd_155700 : Nat := 4983230072969 + 3 ^ 40 * 155700 * 2
def baseEnd_155700 : Nat := 53299291936764037822637

theorem tailTrace_155700 : CollatzResearch.WordTrace tailWord_155700 prefixEnd_155700 53299291936764037822637 := by
  unfold tailWord_155700
  simp only [CollatzResearch.WordTrace]
  refine ⟨2839422767966483144028277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3785897023955310858704369 2839422767966483144028277)
  ·
    refine ⟨266195884496857794752651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 2839422767966483144028277 266195884496857794752651)
    ·
      refine ⟨399293826745286692128977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 266195884496857794752651 399293826745286692128977)
      ·
        refine ⟨299470370058965019096733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 399293826745286692128977 299470370058965019096733)
        ·
          refine ⟨112301388772111882161275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 299470370058965019096733 112301388772111882161275)
          ·
            refine ⟨168452083158167823241913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 112301388772111882161275 168452083158167823241913)
            ·
              refine ⟨126339062368625867431435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 168452083158167823241913 126339062368625867431435)
              ·
                refine ⟨189508593552938801147153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 126339062368625867431435 189508593552938801147153)
                ·
                  refine ⟨142131445164704100860365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 189508593552938801147153 142131445164704100860365)
                  ·
                    refine ⟨53299291936764037822637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 142131445164704100860365 53299291936764037822637)
                    ·
                      rfl

theorem cell22_155700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 3, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 3, 1, 2, 1, 2, 3].length) (baseStart_155700 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_155700 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_155700 prefixEnd_155700 := by exact prefixLift 155700
  have htrace : WordTrace (prefixWord ++ tailWord_155700) baseStart_155700 baseEnd_155700 := by
    simpa [prefixWord, tailWord_155700, baseEnd_155700] using wordTrace_append hprefix tailTrace_155700
  have hstable : (prefixWord ++ tailWord_155700).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_155700).length < 2 ^ (prefixWord ++ tailWord_155700).sum := by decide
  have hdescent : baseEnd_155700 < baseStart_155700 := by decide
  rcases family_descends (prefixWord ++ tailWord_155700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_155767 : List Nat := [1, 1, 3, 1, 1, 6, 2, 1, 1, 5]
def baseStart_155767 : Nat := 118140960795 + 155767 * 2 ^ 59
def prefixEnd_155767 : Nat := 4983230072969 + 3 ^ 40 * 155767 * 2
def baseEnd_155767 : Nat := 53322227405998196397431

theorem tailTrace_155767 : CollatzResearch.WordTrace tailWord_155767 prefixEnd_155767 53322227405998196397431 := by
  unfold tailWord_155767
  simp only [CollatzResearch.WordTrace]
  refine ⟨5681289226690236730745555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3787526151126824487163703 5681289226690236730745555)
  ·
    refine ⟨8521933840035355096118333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5681289226690236730745555 8521933840035355096118333)
    ·
      refine ⟨3195725190013258161044375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8521933840035355096118333 3195725190013258161044375)
      ·
        refine ⟨4793587785019887241566563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3195725190013258161044375 4793587785019887241566563)
        ·
          refine ⟨7190381677529830862349845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4793587785019887241566563 7190381677529830862349845)
          ·
            refine ⟨337049141134210821672649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 7190381677529830862349845 337049141134210821672649)
            ·
              refine ⟨252786855850658116254487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 337049141134210821672649 252786855850658116254487)
              ·
                refine ⟨379180283775987174381731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 252786855850658116254487 379180283775987174381731)
                ·
                  refine ⟨568770425663980761572597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 379180283775987174381731 568770425663980761572597)
                  ·
                    refine ⟨53322227405998196397431, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 568770425663980761572597 53322227405998196397431)
                    ·
                      rfl

theorem cell22_155767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 6, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 6, 2, 1, 1, 5].length) (baseStart_155767 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_155767 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_155767 prefixEnd_155767 := by exact prefixLift 155767
  have htrace : WordTrace (prefixWord ++ tailWord_155767) baseStart_155767 baseEnd_155767 := by
    simpa [prefixWord, tailWord_155767, baseEnd_155767] using wordTrace_append hprefix tailTrace_155767
  have hstable : (prefixWord ++ tailWord_155767).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_155767).length < 2 ^ (prefixWord ++ tailWord_155767).sum := by decide
  have hdescent : baseEnd_155767 < baseStart_155767 := by decide
  rcases family_descends (prefixWord ++ tailWord_155767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_155818 : List Nat := [3, 1, 5, 1, 3, 1, 1, 1, 1, 5]
def baseStart_155818 : Nat := 118140960795 + 155818 * 2 ^ 59
def prefixEnd_155818 : Nat := 4983230072969 + 3 ^ 40 * 155818 * 2
def baseEnd_155818 : Nat := 53339685748251063372275

theorem tailTrace_155818 : CollatzResearch.WordTrace tailWord_155818 prefixEnd_155818 53339685748251063372275 := by
  unfold tailWord_155818
  simp only [CollatzResearch.WordTrace]
  refine ⟨1420787337376368110213027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3788766233003648293901405 1420787337376368110213027)
  ·
    refine ⟨2131181006064552165319541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1420787337376368110213027 2131181006064552165319541)
    ·
      refine ⟨199798219318551765498707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 2131181006064552165319541 199798219318551765498707)
      ·
        refine ⟨299697328977827648248061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 199798219318551765498707 299697328977827648248061)
        ·
          refine ⟨112386498366685368093023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 299697328977827648248061 112386498366685368093023)
          ·
            refine ⟨168579747550028052139535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 112386498366685368093023 168579747550028052139535)
            ·
              refine ⟨252869621325042078209303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 168579747550028052139535 252869621325042078209303)
              ·
                refine ⟨379304431987563117313955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 252869621325042078209303 379304431987563117313955)
                ·
                  refine ⟨568956647981344675970933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 379304431987563117313955 568956647981344675970933)
                  ·
                    refine ⟨53339685748251063372275, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 568956647981344675970933 53339685748251063372275)
                    ·
                      rfl

theorem cell22_155818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 3, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 3, 1, 1, 1, 1, 5].length) (baseStart_155818 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_155818 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_155818 prefixEnd_155818 := by exact prefixLift 155818
  have htrace : WordTrace (prefixWord ++ tailWord_155818) baseStart_155818 baseEnd_155818 := by
    simpa [prefixWord, tailWord_155818, baseEnd_155818] using wordTrace_append hprefix tailTrace_155818
  have hstable : (prefixWord ++ tailWord_155818).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_155818).length < 2 ^ (prefixWord ++ tailWord_155818).sum := by decide
  have hdescent : baseEnd_155818 < baseStart_155818 := by decide
  rcases family_descends (prefixWord ++ tailWord_155818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_155872 : List Nat := [2, 1, 1, 3, 1, 3, 2, 2, 3, 4]
def baseStart_155872 : Nat := 118140960795 + 155872 * 2 ^ 59
def prefixEnd_155872 : Nat := 4983230072969 + 3 ^ 40 * 155872 * 2
def baseEnd_155872 : Nat := 53358171051812922522109

theorem tailTrace_155872 : CollatzResearch.WordTrace tailWord_155872 prefixEnd_155872 53358171051812922522109 := by
  unfold tailWord_155872
  simp only [CollatzResearch.WordTrace]
  refine ⟨2842559445654919831658935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3790079260873226442211913 2842559445654919831658935)
  ·
    refine ⟨4263839168482379747488403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2842559445654919831658935 4263839168482379747488403)
    ·
      refine ⟨6395758752723569621232605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4263839168482379747488403 6395758752723569621232605)
      ·
        refine ⟨2398409532271338607962227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6395758752723569621232605 2398409532271338607962227)
        ·
          refine ⟨3597614298407007911943341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2398409532271338607962227 3597614298407007911943341)
          ·
            refine ⟨1349105361902627966978753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3597614298407007911943341 1349105361902627966978753)
            ·
              refine ⟨1011829021426970975234065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1349105361902627966978753 1011829021426970975234065)
              ·
                refine ⟨758871766070228231425549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1011829021426970975234065 758871766070228231425549)
                ·
                  refine ⟨284576912276335586784581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 758871766070228231425549 284576912276335586784581)
                  ·
                    refine ⟨53358171051812922522109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 284576912276335586784581 53358171051812922522109)
                    ·
                      rfl

theorem cell22_155872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 2, 2, 3, 4].length) (baseStart_155872 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_155872 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_155872 prefixEnd_155872 := by exact prefixLift 155872
  have htrace : WordTrace (prefixWord ++ tailWord_155872) baseStart_155872 baseEnd_155872 := by
    simpa [prefixWord, tailWord_155872, baseEnd_155872] using wordTrace_append hprefix tailTrace_155872
  have hstable : (prefixWord ++ tailWord_155872).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_155872).length < 2 ^ (prefixWord ++ tailWord_155872).sum := by decide
  have hdescent : baseEnd_155872 < baseStart_155872 := by decide
  rcases family_descends (prefixWord ++ tailWord_155872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_155889 : List Nat := [1, 2, 2, 2, 2, 1, 5, 2, 1, 4]
def baseStart_155889 : Nat := 118140960795 + 155889 * 2 ^ 59
def prefixEnd_155889 : Nat := 4983230072969 + 3 ^ 40 * 155889 * 2
def baseEnd_155889 : Nat := 53363990499230544847057

theorem tailTrace_155889 : CollatzResearch.WordTrace tailWord_155889 prefixEnd_155889 53363990499230544847057 := by
  unfold tailWord_155889
  simp only [CollatzResearch.WordTrace]
  refine ⟨5685738932248251566686721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3790492621498834377791147 5685738932248251566686721)
  ·
    refine ⟨4264304199186188675015041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5685738932248251566686721 4264304199186188675015041)
    ·
      refine ⟨3198228149389641506261281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4264304199186188675015041 3198228149389641506261281)
      ·
        refine ⟨2398671112042231129695961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3198228149389641506261281 2398671112042231129695961)
        ·
          refine ⟨1799003334031673347271971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2398671112042231129695961 1799003334031673347271971)
          ·
            refine ⟨2698505001047510020907957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1799003334031673347271971 2698505001047510020907957)
            ·
              refine ⟨252984843848204064460121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2698505001047510020907957 252984843848204064460121)
              ·
                refine ⟨189738632886153048345091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 252984843848204064460121 189738632886153048345091)
                ·
                  refine ⟨284607949329229572517637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 189738632886153048345091 284607949329229572517637)
                  ·
                    refine ⟨53363990499230544847057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 284607949329229572517637 53363990499230544847057)
                    ·
                      rfl

theorem cell22_155889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 5, 2, 1, 4].length) (baseStart_155889 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_155889 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_155889 prefixEnd_155889 := by exact prefixLift 155889
  have htrace : WordTrace (prefixWord ++ tailWord_155889) baseStart_155889 baseEnd_155889 := by
    simpa [prefixWord, tailWord_155889, baseEnd_155889] using wordTrace_append hprefix tailTrace_155889
  have hstable : (prefixWord ++ tailWord_155889).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_155889).length < 2 ^ (prefixWord ++ tailWord_155889).sum := by decide
  have hdescent : baseEnd_155889 < baseStart_155889 := by decide
  rcases family_descends (prefixWord ++ tailWord_155889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_155921 : List Nat := [1, 2, 2, 1, 1, 5, 4, 2, 4]
def baseStart_155921 : Nat := 118140960795 + 155921 * 2 ^ 59
def prefixEnd_155921 : Nat := 4983230072969 + 3 ^ 40 * 155921 * 2
def baseEnd_155921 : Nat := 17791648251064376015653

theorem tailTrace_155921 : CollatzResearch.WordTrace tailWord_155921 prefixEnd_155921 17791648251064376015653 := by
  unfold tailWord_155921
  simp only [CollatzResearch.WordTrace]
  refine ⟨5686906068132321031851617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3791270712088214021234411 5686906068132321031851617)
  ·
    refine ⟨4265179551099240773888713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5686906068132321031851617 4265179551099240773888713)
    ·
      refine ⟨3198884663324430580416535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4265179551099240773888713 3198884663324430580416535)
      ·
        refine ⟨4798326994986645870624803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3198884663324430580416535 4798326994986645870624803)
        ·
          refine ⟨7197490492479968805937205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4798326994986645870624803 7197490492479968805937205)
          ·
            refine ⟨674764733669997075556613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 7197490492479968805937205 674764733669997075556613)
            ·
              refine ⟨126518387563124451666865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 674764733669997075556613 126518387563124451666865)
              ·
                refine ⟨94888790672343338750149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 126518387563124451666865 94888790672343338750149)
                ·
                  refine ⟨17791648251064376015653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 94888790672343338750149 17791648251064376015653)
                  ·
                    rfl

theorem cell22_155921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 4, 2, 4].length) (baseStart_155921 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_155921 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_155921 prefixEnd_155921 := by exact prefixLift 155921
  have htrace : WordTrace (prefixWord ++ tailWord_155921) baseStart_155921 baseEnd_155921 := by
    simpa [prefixWord, tailWord_155921, baseEnd_155921] using wordTrace_append hprefix tailTrace_155921
  have hstable : (prefixWord ++ tailWord_155921).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_155921).length < 2 ^ (prefixWord ++ tailWord_155921).sum := by decide
  have hdescent : baseEnd_155921 < baseStart_155921 := by decide
  rcases family_descends (prefixWord ++ tailWord_155921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_155936 : List Nat := [2, 1, 1, 5, 2, 1, 2, 3, 2, 3]
def baseStart_155936 : Nat := 118140960795 + 155936 * 2 ^ 59
def prefixEnd_155936 : Nat := 4983230072969 + 3 ^ 40 * 155936 * 2
def baseEnd_155936 : Nat := 53380079559738088921913

theorem tailTrace_155936 : CollatzResearch.WordTrace tailWord_155936 prefixEnd_155936 53380079559738088921913 := by
  unfold tailWord_155936
  simp only [CollatzResearch.WordTrace]
  refine ⟨2843726581538989296823831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3791635442051985729098441 2843726581538989296823831)
  ·
    refine ⟨4265589872308483945235747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2843726581538989296823831 4265589872308483945235747)
    ·
      refine ⟨6398384808462725917853621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4265589872308483945235747 6398384808462725917853621)
      ·
        refine ⟨599848575793380554798777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 6398384808462725917853621 599848575793380554798777)
        ·
          refine ⟨449886431845035416099083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 599848575793380554798777 449886431845035416099083)
          ·
            refine ⟨674829647767553124148625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 449886431845035416099083 674829647767553124148625)
            ·
              refine ⟨506122235825664843111469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 674829647767553124148625 506122235825664843111469)
              ·
                refine ⟨189795838434624316166801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 506122235825664843111469 189795838434624316166801)
                ·
                  refine ⟨142346878825968237125101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 189795838434624316166801 142346878825968237125101)
                  ·
                    refine ⟨53380079559738088921913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 142346878825968237125101 53380079559738088921913)
                    ·
                      rfl

theorem cell22_155936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 2, 3, 2, 3].length) (baseStart_155936 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_155936 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_155936 prefixEnd_155936 := by exact prefixLift 155936
  have htrace : WordTrace (prefixWord ++ tailWord_155936) baseStart_155936 baseEnd_155936 := by
    simpa [prefixWord, tailWord_155936, baseEnd_155936] using wordTrace_append hprefix tailTrace_155936
  have hstable : (prefixWord ++ tailWord_155936).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_155936).length < 2 ^ (prefixWord ++ tailWord_155936).sum := by decide
  have hdescent : baseEnd_155936 < baseStart_155936 := by decide
  rcases family_descends (prefixWord ++ tailWord_155936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_155964 : List Nat := [2, 2, 2, 2, 1, 2, 1, 2, 5, 3]
def baseStart_155964 : Nat := 118140960795 + 155964 * 2 ^ 59
def prefixEnd_155964 : Nat := 4983230072969 + 3 ^ 40 * 155964 * 2
def baseEnd_155964 : Nat := 53389664531955349221827

theorem tailTrace_155964 : CollatzResearch.WordTrace tailWord_155964 prefixEnd_155964 53389664531955349221827 := by
  unfold tailWord_155964
  simp only [CollatzResearch.WordTrace]
  refine ⟨2844237203488269687833473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3792316271317692917111297 2844237203488269687833473)
  ·
    refine ⟨2133177902616202265875105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2844237203488269687833473 2133177902616202265875105)
    ·
      refine ⟨1599883426962151699406329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2133177902616202265875105 1599883426962151699406329)
      ·
        refine ⟨1199912570221613774554747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1599883426962151699406329 1199912570221613774554747)
        ·
          refine ⟨1799868855332420661832121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1199912570221613774554747 1799868855332420661832121)
          ·
            refine ⟨1349901641499315496374091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1799868855332420661832121 1349901641499315496374091)
            ·
              refine ⟨2024852462248973244561137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1349901641499315496374091 2024852462248973244561137)
              ·
                refine ⟨1518639346686729933420853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2024852462248973244561137 1518639346686729933420853)
                ·
                  refine ⟨142372438751880931258205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1518639346686729933420853 142372438751880931258205)
                  ·
                    refine ⟨53389664531955349221827, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 142372438751880931258205 53389664531955349221827)
                    ·
                      rfl

theorem cell22_155964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 1, 2, 5, 3].length) (baseStart_155964 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_155964 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_155964 prefixEnd_155964 := by exact prefixLift 155964
  have htrace : WordTrace (prefixWord ++ tailWord_155964) baseStart_155964 baseEnd_155964 := by
    simpa [prefixWord, tailWord_155964, baseEnd_155964] using wordTrace_append hprefix tailTrace_155964
  have hstable : (prefixWord ++ tailWord_155964).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_155964).length < 2 ^ (prefixWord ++ tailWord_155964).sum := by decide
  have hdescent : baseEnd_155964 < baseStart_155964 := by decide
  rcases family_descends (prefixWord ++ tailWord_155964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_155992 : List Nat := [2, 1, 2, 2, 1, 1, 2, 3, 1, 7]
def baseStart_155992 : Nat := 118140960795 + 155992 * 2 ^ 59
def prefixEnd_155992 : Nat := 4983230072969 + 3 ^ 40 * 155992 * 2
def baseEnd_155992 : Nat := 53399249504172609521741

theorem tailTrace_155992 : CollatzResearch.WordTrace tailWord_155992 prefixEnd_155992 53399249504172609521741 := by
  unfold tailWord_155992
  simp only [CollatzResearch.WordTrace]
  refine ⟨2844747825437550078843115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3792997100583400105124153 2844747825437550078843115)
  ·
    refine ⟨4267121738156325118264673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2844747825437550078843115 4267121738156325118264673)
    ·
      refine ⟨3200341303617243838698505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4267121738156325118264673 3200341303617243838698505)
      ·
        refine ⟨2400255977712932879023879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3200341303617243838698505 2400255977712932879023879)
        ·
          refine ⟨3600383966569399318535819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2400255977712932879023879 3600383966569399318535819)
          ·
            refine ⟨5400575949854098977803729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3600383966569399318535819 5400575949854098977803729)
            ·
              refine ⟨4050431962390574233352797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5400575949854098977803729 4050431962390574233352797)
              ·
                refine ⟨1518911985896465337507299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4050431962390574233352797 1518911985896465337507299)
                ·
                  refine ⟨2278367978844698006260949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1518911985896465337507299 2278367978844698006260949)
                  ·
                    refine ⟨53399249504172609521741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 2278367978844698006260949 53399249504172609521741)
                    ·
                      rfl

theorem cell22_155992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 3, 1, 7].length) (baseStart_155992 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_155992 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_155992 prefixEnd_155992 := by exact prefixLift 155992
  have htrace : WordTrace (prefixWord ++ tailWord_155992) baseStart_155992 baseEnd_155992 := by
    simpa [prefixWord, tailWord_155992, baseEnd_155992] using wordTrace_append hprefix tailTrace_155992
  have hstable : (prefixWord ++ tailWord_155992).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_155992).length < 2 ^ (prefixWord ++ tailWord_155992).sum := by decide
  have hdescent : baseEnd_155992 < baseStart_155992 := by decide
  rcases family_descends (prefixWord ++ tailWord_155992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_156058 : List Nat := [3, 1, 1, 4, 1, 4, 1, 2, 1, 4]
def baseStart_156058 : Nat := 118140960795 + 156058 * 2 ^ 59
def prefixEnd_156058 : Nat := 4983230072969 + 3 ^ 40 * 156058 * 2
def baseEnd_156058 : Nat := 53421842652970437371539

theorem tailTrace_156058 : CollatzResearch.WordTrace tailWord_156058 prefixEnd_156058 53421842652970437371539 := by
  unfold tailWord_156058
  simp only [CollatzResearch.WordTrace]
  refine ⟨1422975717158998357397207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3794601912423995619725885 1422975717158998357397207)
  ·
    refine ⟨2134463575738497536095811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1422975717158998357397207 2134463575738497536095811)
    ·
      refine ⟨3201695363607746304143717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2134463575738497536095811 3201695363607746304143717)
      ·
        refine ⟨600317880676452432026947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3201695363607746304143717 600317880676452432026947)
        ·
          refine ⟨900476821014678648040421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 600317880676452432026947 900476821014678648040421)
          ·
            refine ⟨168839403940252246507579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 900476821014678648040421 168839403940252246507579)
            ·
              refine ⟨253259105910378369761369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 168839403940252246507579 253259105910378369761369)
              ·
                refine ⟨189944329432783777321027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 253259105910378369761369 189944329432783777321027)
                ·
                  refine ⟨284916494149175665981541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 189944329432783777321027 284916494149175665981541)
                  ·
                    refine ⟨53421842652970437371539, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 284916494149175665981541 53421842652970437371539)
                    ·
                      rfl

theorem cell22_156058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 4, 1, 2, 1, 4].length) (baseStart_156058 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_156058 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_156058 prefixEnd_156058 := by exact prefixLift 156058
  have htrace : WordTrace (prefixWord ++ tailWord_156058) baseStart_156058 baseEnd_156058 := by
    simpa [prefixWord, tailWord_156058, baseEnd_156058] using wordTrace_append hprefix tailTrace_156058
  have hstable : (prefixWord ++ tailWord_156058).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_156058).length < 2 ^ (prefixWord ++ tailWord_156058).sum := by decide
  have hdescent : baseEnd_156058 < baseStart_156058 := by decide
  rcases family_descends (prefixWord ++ tailWord_156058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_156071 : List Nat := [1, 1, 6, 1, 1, 3, 1, 2, 1, 5]
def baseStart_156071 : Nat := 118140960795 + 156071 * 2 ^ 59
def prefixEnd_156071 : Nat := 4983230072969 + 3 ^ 40 * 156071 * 2
def baseEnd_156071 : Nat := 53426292818642736796499

theorem tailTrace_156071 : CollatzResearch.WordTrace tailWord_156071 prefixEnd_156071 53426292818642736796499 := by
  unfold tailWord_156071
  simp only [CollatzResearch.WordTrace]
  refine ⟨5692377017588896649812067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3794918011725931099874711 5692377017588896649812067)
  ·
    refine ⟨8538565526383344974718101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5692377017588896649812067 8538565526383344974718101)
    ·
      refine ⟨400245259049219295689911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 8538565526383344974718101 400245259049219295689911)
      ·
        refine ⟨600367888573828943534867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 400245259049219295689911 600367888573828943534867)
        ·
          refine ⟨900551832860743415302301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 600367888573828943534867 900551832860743415302301)
          ·
            refine ⟨337706937322778780738363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 900551832860743415302301 337706937322778780738363)
            ·
              refine ⟨506560405984168171107545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 337706937322778780738363 506560405984168171107545)
              ·
                refine ⟨379920304488126128330659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 506560405984168171107545 379920304488126128330659)
                ·
                  refine ⟨569880456732189192495989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 379920304488126128330659 569880456732189192495989)
                  ·
                    refine ⟨53426292818642736796499, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 569880456732189192495989 53426292818642736796499)
                    ·
                      rfl

theorem cell22_156071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 3, 1, 2, 1, 5].length) (baseStart_156071 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_156071 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_156071 prefixEnd_156071 := by exact prefixLift 156071
  have htrace : WordTrace (prefixWord ++ tailWord_156071) baseStart_156071 baseEnd_156071 := by
    simpa [prefixWord, tailWord_156071, baseEnd_156071] using wordTrace_append hprefix tailTrace_156071
  have hstable : (prefixWord ++ tailWord_156071).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_156071).length < 2 ^ (prefixWord ++ tailWord_156071).sum := by decide
  have hdescent : baseEnd_156071 < baseStart_156071 := by decide
  rcases family_descends (prefixWord ++ tailWord_156071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_156118 : List Nat := [5, 2, 1, 1, 1, 1, 5, 6]
def baseStart_156118 : Nat := 118140960795 + 156118 * 2 ^ 59
def prefixEnd_156118 : Nat := 4983230072969 + 3 ^ 40 * 156118 * 2
def baseEnd_156118 : Nat := 5938042431016697874595

theorem tailTrace_156118 : CollatzResearch.WordTrace tailWord_156118 prefixEnd_156118 5938042431016697874595 := by
  unfold tailWord_156118
  simp only [CollatzResearch.WordTrace]
  refine ⟨355880703026163979798313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 3796060832279082451182005 355880703026163979798313)
  ·
    refine ⟨266910527269622984848735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 355880703026163979798313 266910527269622984848735)
    ·
      refine ⟨400365790904434477273103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 266910527269622984848735 400365790904434477273103)
      ·
        refine ⟨600548686356651715909655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 400365790904434477273103 600548686356651715909655)
        ·
          refine ⟨900823029534977573864483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 600548686356651715909655 900823029534977573864483)
          ·
            refine ⟨1351234544302466360796725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 900823029534977573864483 1351234544302466360796725)
            ·
              refine ⟨126678238528356221324693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1351234544302466360796725 126678238528356221324693)
              ·
                refine ⟨5938042431016697874595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 126678238528356221324693 5938042431016697874595)
                ·
                  rfl

theorem cell22_156118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 5, 6].length) (baseStart_156118 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_156118 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_156118 prefixEnd_156118 := by exact prefixLift 156118
  have htrace : WordTrace (prefixWord ++ tailWord_156118) baseStart_156118 baseEnd_156118 := by
    simpa [prefixWord, tailWord_156118, baseEnd_156118] using wordTrace_append hprefix tailTrace_156118
  have hstable : (prefixWord ++ tailWord_156118).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_156118).length < 2 ^ (prefixWord ++ tailWord_156118).sum := by decide
  have hdescent : baseEnd_156118 < baseStart_156118 := by decide
  rcases family_descends (prefixWord ++ tailWord_156118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_156129 : List Nat := [1, 2, 3, 1, 2, 2, 2, 2, 7]
def baseStart_156129 : Nat := 118140960795 + 156129 * 2 ^ 59
def prefixEnd_156129 : Nat := 4983230072969 + 3 ^ 40 * 156129 * 2
def baseEnd_156129 : Nat := 17815382467983306282107

theorem tailTrace_156129 : CollatzResearch.WordTrace tailWord_156129 prefixEnd_156129 17815382467983306282107 := by
  unfold tailWord_156129
  simp only [CollatzResearch.WordTrace]
  refine ⟨5694492451378772555423441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3796328300919181703615627 5694492451378772555423441)
  ·
    refine ⟨4270869338534079416567581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5694492451378772555423441 4270869338534079416567581)
    ·
      refine ⟨1601576001950279781212843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4270869338534079416567581 1601576001950279781212843)
      ·
        refine ⟨2402364002925419671819265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1601576001950279781212843 2402364002925419671819265)
        ·
          refine ⟨1801773002194064753864449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2402364002925419671819265 1801773002194064753864449)
          ·
            refine ⟨1351329751645548565398337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1801773002194064753864449 1351329751645548565398337)
            ·
              refine ⟨1013497313734161424048753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1351329751645548565398337 1013497313734161424048753)
              ·
                refine ⟨760122985300621068036565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1013497313734161424048753 760122985300621068036565)
                ·
                  refine ⟨17815382467983306282107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 760122985300621068036565 17815382467983306282107)
                  ·
                    rfl

theorem cell22_156129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 2, 2, 7].length) (baseStart_156129 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_156129 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_156129 prefixEnd_156129 := by exact prefixLift 156129
  have htrace : WordTrace (prefixWord ++ tailWord_156129) baseStart_156129 baseEnd_156129 := by
    simpa [prefixWord, tailWord_156129, baseEnd_156129] using wordTrace_append hprefix tailTrace_156129
  have hstable : (prefixWord ++ tailWord_156129).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_156129).length < 2 ^ (prefixWord ++ tailWord_156129).sum := by decide
  have hdescent : baseEnd_156129 < baseStart_156129 := by decide
  rcases family_descends (prefixWord ++ tailWord_156129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_156144 : List Nat := [2, 1, 1, 1, 3, 3, 1, 1, 4, 5]
def baseStart_156144 : Nat := 118140960795 + 156144 * 2 ^ 59
def prefixEnd_156144 : Nat := 4983230072969 + 3 ^ 40 * 156144 * 2
def baseEnd_156144 : Nat := 53451282210494879721275

theorem tailTrace_156144 : CollatzResearch.WordTrace tailWord_156144 prefixEnd_156144 53451282210494879721275 := by
  unfold tailWord_156144
  simp only [CollatzResearch.WordTrace]
  refine ⟨2847519773162215058609743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3796693030882953411479657 2847519773162215058609743)
  ·
    refine ⟨4271279659743322587914615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2847519773162215058609743 4271279659743322587914615)
    ·
      refine ⟨6406919489614983881871923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4271279659743322587914615 6406919489614983881871923)
      ·
        refine ⟨9610379234422475822807885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6406919489614983881871923 9610379234422475822807885)
        ·
          refine ⟨3603892212908428433552957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9610379234422475822807885 3603892212908428433552957)
          ·
            refine ⟨1351459579840660662582359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3603892212908428433552957 1351459579840660662582359)
            ·
              refine ⟨2027189369760990993873539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1351459579840660662582359 2027189369760990993873539)
              ·
                refine ⟨3040784054641486490810309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2027189369760990993873539 3040784054641486490810309)
                ·
                  refine ⟨570147010245278717026933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3040784054641486490810309 570147010245278717026933)
                  ·
                    refine ⟨53451282210494879721275, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 570147010245278717026933 53451282210494879721275)
                    ·
                      rfl

theorem cell22_156144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 1, 1, 4, 5].length) (baseStart_156144 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_156144 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_156144 prefixEnd_156144 := by exact prefixLift 156144
  have htrace : WordTrace (prefixWord ++ tailWord_156144) baseStart_156144 baseEnd_156144 := by
    simpa [prefixWord, tailWord_156144, baseEnd_156144] using wordTrace_append hprefix tailTrace_156144
  have hstable : (prefixWord ++ tailWord_156144).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_156144).length < 2 ^ (prefixWord ++ tailWord_156144).sum := by decide
  have hdescent : baseEnd_156144 < baseStart_156144 := by decide
  rcases family_descends (prefixWord ++ tailWord_156144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_156150 : List Nat := [5, 1, 1, 1, 2, 1, 1, 6, 1, 3]
def baseStart_156150 : Nat := 118140960795 + 156150 * 2 ^ 59
def prefixEnd_156150 : Nat := 4983230072969 + 3 ^ 40 * 156150 * 2
def baseEnd_156150 : Nat := 53453336133112864071257

theorem tailTrace_156150 : CollatzResearch.WordTrace tailWord_156150 prefixEnd_156150 53453336133112864071257 := by
  unfold tailWord_156150
  simp only [CollatzResearch.WordTrace]
  refine ⟨355953649018918321371119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 3796838922868462094625269 355953649018918321371119)
  ·
    refine ⟨533930473528377482056679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 355953649018918321371119 533930473528377482056679)
    ·
      refine ⟨800895710292566223085019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 533930473528377482056679 800895710292566223085019)
      ·
        refine ⟨1201343565438849334627529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 800895710292566223085019 1201343565438849334627529)
        ·
          refine ⟨901007674079137000970647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1201343565438849334627529 901007674079137000970647)
          ·
            refine ⟨1351511511118705501455971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 901007674079137000970647 1351511511118705501455971)
            ·
              refine ⟨2027267266678058252183957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1351511511118705501455971 2027267266678058252183957)
              ·
                refine ⟨95028153125533980571123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2027267266678058252183957 95028153125533980571123)
                ·
                  refine ⟨142542229688300970856685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 95028153125533980571123 142542229688300970856685)
                  ·
                    refine ⟨53453336133112864071257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 142542229688300970856685 53453336133112864071257)
                    ·
                      rfl

theorem cell22_156150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 1, 6, 1, 3].length) (baseStart_156150 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_156150 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_156150 prefixEnd_156150 := by exact prefixLift 156150
  have htrace : WordTrace (prefixWord ++ tailWord_156150) baseStart_156150 baseEnd_156150 := by
    simpa [prefixWord, tailWord_156150, baseEnd_156150] using wordTrace_append hprefix tailTrace_156150
  have hstable : (prefixWord ++ tailWord_156150).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_156150).length < 2 ^ (prefixWord ++ tailWord_156150).sum := by decide
  have hdescent : baseEnd_156150 < baseStart_156150 := by decide
  rcases family_descends (prefixWord ++ tailWord_156150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_156161 : List Nat := [1, 2, 4, 1, 3, 1, 2, 1, 2, 5]
def baseStart_156161 : Nat := 118140960795 + 156161 * 2 ^ 59
def prefixEnd_156161 : Nat := 4983230072969 + 3 ^ 40 * 156161 * 2
def baseEnd_156161 : Nat := 53457101657912502046223

theorem tailTrace_156161 : CollatzResearch.WordTrace tailWord_156161 prefixEnd_156161 53457101657912502046223 := by
  unfold tailWord_156161
  simp only [CollatzResearch.WordTrace]
  refine ⟨5695659587262842020588337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3797106391508561347058891 5695659587262842020588337)
  ·
    refine ⟨4271744690447131515441253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5695659587262842020588337 4271744690447131515441253)
    ·
      refine ⟨800952129458837159145235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4271744690447131515441253 800952129458837159145235)
      ·
        refine ⟨1201428194188255738717853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 800952129458837159145235 1201428194188255738717853)
        ·
          refine ⟨450535572820595902019195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1201428194188255738717853 450535572820595902019195)
          ·
            refine ⟨675803359230893853028793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 450535572820595902019195 675803359230893853028793)
            ·
              refine ⟨506852519423170389771595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 675803359230893853028793 506852519423170389771595)
              ·
                refine ⟨760278779134755584657393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 506852519423170389771595 760278779134755584657393)
                ·
                  refine ⟨570209084351066688493045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 760278779134755584657393 570209084351066688493045)
                  ·
                    refine ⟨53457101657912502046223, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 570209084351066688493045 53457101657912502046223)
                    ·
                      rfl

theorem cell22_156161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 2, 1, 2, 5].length) (baseStart_156161 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_156161 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_156161 prefixEnd_156161 := by exact prefixLift 156161
  have htrace : WordTrace (prefixWord ++ tailWord_156161) baseStart_156161 baseEnd_156161 := by
    simpa [prefixWord, tailWord_156161, baseEnd_156161] using wordTrace_append hprefix tailTrace_156161
  have hstable : (prefixWord ++ tailWord_156161).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_156161).length < 2 ^ (prefixWord ++ tailWord_156161).sum := by decide
  have hdescent : baseEnd_156161 < baseStart_156161 := by decide
  rcases family_descends (prefixWord ++ tailWord_156161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_156223 : List Nat := [1, 1, 2, 2, 3, 2, 3, 3, 2, 3]
def baseStart_156223 : Nat := 118140960795 + 156223 * 2 ^ 59
def prefixEnd_156223 : Nat := 4983230072969 + 3 ^ 40 * 156223 * 2
def baseEnd_156223 : Nat := 53478325524965006996033

theorem tailTrace_156223 : CollatzResearch.WordTrace tailWord_156223 prefixEnd_156223 53478325524965006996033 := by
  unfold tailWord_156223
  simp only [CollatzResearch.WordTrace]
  refine ⟨5697920913038226609345323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3798613942025484406230215 5697920913038226609345323)
  ·
    refine ⟨8546881369557339914017985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5697920913038226609345323 8546881369557339914017985)
    ·
      refine ⟨6410161027168004935513489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8546881369557339914017985 6410161027168004935513489)
      ·
        refine ⟨4807620770376003701635117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6410161027168004935513489 4807620770376003701635117)
        ·
          refine ⟨1802857788891001388113169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4807620770376003701635117 1802857788891001388113169)
          ·
            refine ⟨1352143341668251041084877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1802857788891001388113169 1352143341668251041084877)
            ·
              refine ⟨507053753125594140406829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1352143341668251041084877 507053753125594140406829)
              ·
                refine ⟨190145157422097802652561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 507053753125594140406829 190145157422097802652561)
                ·
                  refine ⟨142608868066573351989421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 190145157422097802652561 142608868066573351989421)
                  ·
                    refine ⟨53478325524965006996033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 142608868066573351989421 53478325524965006996033)
                    ·
                      rfl

theorem cell22_156223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 3, 3, 2, 3].length) (baseStart_156223 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_156223 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_156223 prefixEnd_156223 := by exact prefixLift 156223
  have htrace : WordTrace (prefixWord ++ tailWord_156223) baseStart_156223 baseEnd_156223 := by
    simpa [prefixWord, tailWord_156223, baseEnd_156223] using wordTrace_append hprefix tailTrace_156223
  have hstable : (prefixWord ++ tailWord_156223).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_156223).length < 2 ^ (prefixWord ++ tailWord_156223).sum := by decide
  have hdescent : baseEnd_156223 < baseStart_156223 := by decide
  rcases family_descends (prefixWord ++ tailWord_156223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_156266 : List Nat := [3, 1, 3, 2, 1, 1, 1, 1, 1, 8]
def baseStart_156266 : Nat := 118140960795 + 156266 * 2 ^ 59
def prefixEnd_156266 : Nat := 4983230072969 + 3 ^ 40 * 156266 * 2
def baseEnd_156266 : Nat := 53493045303727228170901

theorem tailTrace_156266 : CollatzResearch.WordTrace tailWord_156266 prefixEnd_156266 53493045303727228170901 := by
  unfold tailWord_156266
  simp only [CollatzResearch.WordTrace]
  refine ⟨1424872312970611238290163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3799659501254963302107101 1424872312970611238290163)
  ·
    refine ⟨2137308469455916857435245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1424872312970611238290163 2137308469455916857435245)
    ·
      refine ⟨801490676045968821538217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2137308469455916857435245 801490676045968821538217)
      ·
        refine ⟨601118007034476616153663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 801490676045968821538217 601118007034476616153663)
        ·
          refine ⟨901677010551714924230495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 601118007034476616153663 901677010551714924230495)
          ·
            refine ⟨1352515515827572386345743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 901677010551714924230495 1352515515827572386345743)
            ·
              refine ⟨2028773273741358579518615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1352515515827572386345743 2028773273741358579518615)
              ·
                refine ⟨3043159910612037869277923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2028773273741358579518615 3043159910612037869277923)
                ·
                  refine ⟨4564739865918056803916885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3043159910612037869277923 4564739865918056803916885)
                  ·
                    refine ⟨53493045303727228170901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 4564739865918056803916885 53493045303727228170901)
                    ·
                      rfl

theorem cell22_156266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 1, 1, 1, 8].length) (baseStart_156266 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_156266 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_156266 prefixEnd_156266 := by exact prefixLift 156266
  have htrace : WordTrace (prefixWord ++ tailWord_156266) baseStart_156266 baseEnd_156266 := by
    simpa [prefixWord, tailWord_156266, baseEnd_156266] using wordTrace_append hprefix tailTrace_156266
  have hstable : (prefixWord ++ tailWord_156266).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_156266).length < 2 ^ (prefixWord ++ tailWord_156266).sum := by decide
  have hdescent : baseEnd_156266 < baseStart_156266 := by decide
  rcases family_descends (prefixWord ++ tailWord_156266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_156285 : List Nat := [1, 4, 1, 1, 5, 1, 1, 2, 3, 3]
def baseStart_156285 : Nat := 118140960795 + 156285 * 2 ^ 59
def prefixEnd_156285 : Nat := 4983230072969 + 3 ^ 40 * 156285 * 2
def baseEnd_156285 : Nat := 53499549392017511945843

theorem tailTrace_156285 : CollatzResearch.WordTrace tailWord_156285 prefixEnd_156285 53499549392017511945843 := by
  unfold tailWord_156285
  simp only [CollatzResearch.WordTrace]
  refine ⟨5700182238813611198102309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3800121492542407465401539 5700182238813611198102309)
  ·
    refine ⟨1068784169777552099644183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5700182238813611198102309 1068784169777552099644183)
    ·
      refine ⟨1603176254666328149466275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1068784169777552099644183 1603176254666328149466275)
      ·
        refine ⟨2404764381999492224199413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1603176254666328149466275 2404764381999492224199413)
        ·
          refine ⟨225446660812452396018695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 2404764381999492224199413 225446660812452396018695)
          ·
            refine ⟨338169991218678594028043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 225446660812452396018695 338169991218678594028043)
            ·
              refine ⟨507254986828017891042065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 338169991218678594028043 507254986828017891042065)
              ·
                refine ⟨380441240121013418281549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 507254986828017891042065 380441240121013418281549)
                ·
                  refine ⟨142665465045380031855581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 380441240121013418281549 142665465045380031855581)
                  ·
                    refine ⟨53499549392017511945843, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 142665465045380031855581 53499549392017511945843)
                    ·
                      rfl

theorem cell22_156285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 1, 1, 2, 3, 3].length) (baseStart_156285 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_156285 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_156285 prefixEnd_156285 := by exact prefixLift 156285
  have htrace : WordTrace (prefixWord ++ tailWord_156285) baseStart_156285 baseEnd_156285 := by
    simpa [prefixWord, tailWord_156285, baseEnd_156285] using wordTrace_append hprefix tailTrace_156285
  have hstable : (prefixWord ++ tailWord_156285).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_156285).length < 2 ^ (prefixWord ++ tailWord_156285).sum := by decide
  have hdescent : baseEnd_156285 < baseStart_156285 := by decide
  rcases family_descends (prefixWord ++ tailWord_156285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_156302 : List Nat := [4, 1, 1, 3, 1, 1, 4, 3, 1, 3]
def baseStart_156302 : Nat := 118140960795 + 156302 * 2 ^ 59
def prefixEnd_156302 : Nat := 4983230072969 + 3 ^ 40 * 156302 * 2
def baseEnd_156302 : Nat := 53505368839435134270791

theorem tailTrace_156302 : CollatzResearch.WordTrace tailWord_156302 prefixEnd_156302 53505368839435134270791 := by
  unfold tailWord_156302
  simp only [CollatzResearch.WordTrace]
  refine ⟨712600284969002887683895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3800534853168015400980773 712600284969002887683895)
  ·
    refine ⟨1068900427453504331525843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 712600284969002887683895 1068900427453504331525843)
    ·
      refine ⟨1603350641180256497288765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1068900427453504331525843 1603350641180256497288765)
      ·
        refine ⟨601256490442596186483287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1603350641180256497288765 601256490442596186483287)
        ·
          refine ⟨901884735663894279724931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 601256490442596186483287 901884735663894279724931)
          ·
            refine ⟨1352827103495841419587397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 901884735663894279724931 1352827103495841419587397)
            ·
              refine ⟨253655081905470266172637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1352827103495841419587397 253655081905470266172637)
              ·
                refine ⟨95120655714551349814739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 253655081905470266172637 95120655714551349814739)
                ·
                  refine ⟨142680983571827024722109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 95120655714551349814739 142680983571827024722109)
                  ·
                    refine ⟨53505368839435134270791, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 142680983571827024722109 53505368839435134270791)
                    ·
                      rfl

theorem cell22_156302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 4, 3, 1, 3].length) (baseStart_156302 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_156302 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_156302 prefixEnd_156302 := by exact prefixLift 156302
  have htrace : WordTrace (prefixWord ++ tailWord_156302) baseStart_156302 baseEnd_156302 := by
    simpa [prefixWord, tailWord_156302, baseEnd_156302] using wordTrace_append hprefix tailTrace_156302
  have hstable : (prefixWord ++ tailWord_156302).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_156302).length < 2 ^ (prefixWord ++ tailWord_156302).sum := by decide
  have hdescent : baseEnd_156302 < baseStart_156302 := by decide
  rcases family_descends (prefixWord ++ tailWord_156302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_156353 : List Nat := [1, 2, 6, 2, 2, 1, 1, 3, 1, 3]
def baseStart_156353 : Nat := 118140960795 + 156353 * 2 ^ 59
def prefixEnd_156353 : Nat := 4983230072969 + 3 ^ 40 * 156353 * 2
def baseEnd_156353 : Nat := 53522827181688001245635

theorem tailTrace_156353 : CollatzResearch.WordTrace tailWord_156353 prefixEnd_156353 53522827181688001245635 := by
  unfold tailWord_156353
  simp only [CollatzResearch.WordTrace]
  refine ⟨5702662402567258811577713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3801774935044839207718475 5702662402567258811577713)
  ·
    refine ⟨4276996801925444108683285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5702662402567258811577713 4276996801925444108683285)
    ·
      refine ⟨200484225090255192594529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 4276996801925444108683285 200484225090255192594529)
      ·
        refine ⟨150363168817691394445897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 200484225090255192594529 150363168817691394445897)
        ·
          refine ⟨112772376613268545834423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 150363168817691394445897 112772376613268545834423)
          ·
            refine ⟨169158564919902818751635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 112772376613268545834423 169158564919902818751635)
            ·
              refine ⟨253737847379854228127453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 169158564919902818751635 253737847379854228127453)
              ·
                refine ⟨95151692767445335547795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 253737847379854228127453 95151692767445335547795)
                ·
                  refine ⟨142727539151168003321693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 95151692767445335547795 142727539151168003321693)
                  ·
                    refine ⟨53522827181688001245635, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 142727539151168003321693 53522827181688001245635)
                    ·
                      rfl

theorem cell22_156353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 2, 1, 1, 3, 1, 3].length) (baseStart_156353 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_156353 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_156353 prefixEnd_156353 := by exact prefixLift 156353
  have htrace : WordTrace (prefixWord ++ tailWord_156353) baseStart_156353 baseEnd_156353 := by
    simpa [prefixWord, tailWord_156353, baseEnd_156353] using wordTrace_append hprefix tailTrace_156353
  have hstable : (prefixWord ++ tailWord_156353).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_156353).length < 2 ^ (prefixWord ++ tailWord_156353).sum := by decide
  have hdescent : baseEnd_156353 < baseStart_156353 := by decide
  rcases family_descends (prefixWord ++ tailWord_156353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_156360 : List Nat := [2, 1, 3, 1, 2, 3, 3, 3, 4]
def baseStart_156360 : Nat := 118140960795 + 156360 * 2 ^ 59
def prefixEnd_156360 : Nat := 4983230072969 + 3 ^ 40 * 156360 * 2
def baseEnd_156360 : Nat := 17841741141580772106871

theorem tailTrace_156360 : CollatzResearch.WordTrace tailWord_156360 prefixEnd_156360 17841741141580772106871 := by
  unfold tailWord_156360
  simp only [CollatzResearch.WordTrace]
  refine ⟨2851458856770949503541267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3801945142361266004721689 2851458856770949503541267)
  ·
    refine ⟨4277188285156424255311901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2851458856770949503541267 4277188285156424255311901)
    ·
      refine ⟨1603945606933659095741963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4277188285156424255311901 1603945606933659095741963)
      ·
        refine ⟨2405918410400488643612945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1603945606933659095741963 2405918410400488643612945)
        ·
          refine ⟨1804438807800366482709709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2405918410400488643612945 1804438807800366482709709)
          ·
            refine ⟨676664552925137431016141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1804438807800366482709709 676664552925137431016141)
            ·
              refine ⟨253749207346926536631053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 676664552925137431016141 253749207346926536631053)
              ·
                refine ⟨95155952755097451236645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 253749207346926536631053 95155952755097451236645)
                ·
                  refine ⟨17841741141580772106871, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 95155952755097451236645 17841741141580772106871)
                  ·
                    rfl

theorem cell22_156360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 3, 3, 4].length) (baseStart_156360 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_156360 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_156360 prefixEnd_156360 := by exact prefixLift 156360
  have htrace : WordTrace (prefixWord ++ tailWord_156360) baseStart_156360 baseEnd_156360 := by
    simpa [prefixWord, tailWord_156360, baseEnd_156360] using wordTrace_append hprefix tailTrace_156360
  have hstable : (prefixWord ++ tailWord_156360).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_156360).length < 2 ^ (prefixWord ++ tailWord_156360).sum := by decide
  have hdescent : baseEnd_156360 < baseStart_156360 := by decide
  rcases family_descends (prefixWord ++ tailWord_156360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_156388 : List Nat := [2, 3, 1, 1, 1, 5, 2, 7]
def baseStart_156388 : Nat := 118140960795 + 156388 * 2 ^ 59
def prefixEnd_156388 : Nat := 4983230072969 + 3 ^ 40 * 156388 * 2
def baseEnd_156388 : Nat := 5948312044106619624503

theorem tailTrace_156388 : CollatzResearch.WordTrace tailWord_156388 prefixEnd_156388 5948312044106619624503 := by
  unfold tailWord_156388
  simp only [CollatzResearch.WordTrace]
  refine ⟨2851969478720229894550909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3802625971626973192734545 2851969478720229894550909)
  ·
    refine ⟨1069488554520086210456591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2851969478720229894550909 1069488554520086210456591)
    ·
      refine ⟨1604232831780129315684887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1069488554520086210456591 1604232831780129315684887)
      ·
        refine ⟨2406349247670193973527331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1604232831780129315684887 2406349247670193973527331)
        ·
          refine ⟨3609523871505290960290997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2406349247670193973527331 3609523871505290960290997)
          ·
            refine ⟨338392862953621027527281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 3609523871505290960290997 338392862953621027527281)
            ·
              refine ⟨253794647215215770645461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 338392862953621027527281 253794647215215770645461)
              ·
                refine ⟨5948312044106619624503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 253794647215215770645461 5948312044106619624503)
                ·
                  rfl

theorem cell22_156388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 5, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 5, 2, 7].length) (baseStart_156388 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_156388 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_156388 prefixEnd_156388 := by exact prefixLift 156388
  have htrace : WordTrace (prefixWord ++ tailWord_156388) baseStart_156388 baseEnd_156388 := by
    simpa [prefixWord, tailWord_156388, baseEnd_156388] using wordTrace_append hprefix tailTrace_156388
  have hstable : (prefixWord ++ tailWord_156388).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_156388).length < 2 ^ (prefixWord ++ tailWord_156388).sum := by decide
  have hdescent : baseEnd_156388 < baseStart_156388 := by decide
  rcases family_descends (prefixWord ++ tailWord_156388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_156392 : List Nat := [2, 1, 4, 1, 4, 1, 1, 3, 2, 3]
def baseStart_156392 : Nat := 118140960795 + 156392 * 2 ^ 59
def prefixEnd_156392 : Nat := 4983230072969 + 3 ^ 40 * 156392 * 2
def baseEnd_156392 : Nat := 53536177678704899520515

theorem tailTrace_156392 : CollatzResearch.WordTrace tailWord_156392 prefixEnd_156392 53536177678704899520515 := by
  unfold tailWord_156392
  simp only [CollatzResearch.WordTrace]
  refine ⟨2852042424712984236123715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3802723232950645648164953 2852042424712984236123715)
  ·
    refine ⟨4278063637069476354185573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2852042424712984236123715 4278063637069476354185573)
    ·
      refine ⟨802136931950526816409795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4278063637069476354185573 802136931950526816409795)
      ·
        refine ⟨1203205397925790224614693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 802136931950526816409795 1203205397925790224614693)
        ·
          refine ⟨225601012111085667115255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1203205397925790224614693 225601012111085667115255)
          ·
            refine ⟨338401518166628500672883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 225601012111085667115255 338401518166628500672883)
            ·
              refine ⟨507602277249942751009325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 338401518166628500672883 507602277249942751009325)
              ·
                refine ⟨190350853968728531628497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 507602277249942751009325 190350853968728531628497)
                ·
                  refine ⟨142763140476546398721373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 190350853968728531628497 142763140476546398721373)
                  ·
                    refine ⟨53536177678704899520515, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 142763140476546398721373 53536177678704899520515)
                    ·
                      rfl

theorem cell22_156392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 1, 1, 3, 2, 3].length) (baseStart_156392 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_156392 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_156392 prefixEnd_156392 := by exact prefixLift 156392
  have htrace : WordTrace (prefixWord ++ tailWord_156392) baseStart_156392 baseEnd_156392 := by
    simpa [prefixWord, tailWord_156392, baseEnd_156392] using wordTrace_append hprefix tailTrace_156392
  have hstable : (prefixWord ++ tailWord_156392).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_156392).length < 2 ^ (prefixWord ++ tailWord_156392).sum := by decide
  have hdescent : baseEnd_156392 < baseStart_156392 := by decide
  rcases family_descends (prefixWord ++ tailWord_156392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_156403 : List Nat := [1, 1, 1, 2, 2, 3, 1, 3, 5, 3]
def baseStart_156403 : Nat := 118140960795 + 156403 * 2 ^ 59
def prefixEnd_156403 : Nat := 4983230072969 + 3 ^ 40 * 156403 * 2
def baseEnd_156403 : Nat := 53539943203504537495481

theorem tailTrace_156403 : CollatzResearch.WordTrace tailWord_156403 prefixEnd_156403 53539943203504537495481 := by
  unfold tailWord_156403
  simp only [CollatzResearch.WordTrace]
  refine ⟨5704486052386117350897863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3802990701590744900598575 5704486052386117350897863)
  ·
    refine ⟨8556729078579176026346795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5704486052386117350897863 8556729078579176026346795)
    ·
      refine ⟨12835093617868764039520193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8556729078579176026346795 12835093617868764039520193)
      ·
        refine ⟨9626320213401573029640145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12835093617868764039520193 9626320213401573029640145)
        ·
          refine ⟨7219740160051179772230109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9626320213401573029640145 7219740160051179772230109)
          ·
            refine ⟨2707402560019192414586291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7219740160051179772230109 2707402560019192414586291)
            ·
              refine ⟨4061103840028788621879437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2707402560019192414586291 4061103840028788621879437)
              ·
                refine ⟨1522913940010795733204789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4061103840028788621879437 1522913940010795733204789)
                ·
                  refine ⟨142773181876012099987949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1522913940010795733204789 142773181876012099987949)
                  ·
                    refine ⟨53539943203504537495481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 142773181876012099987949 53539943203504537495481)
                    ·
                      rfl

theorem cell22_156403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 3, 5, 3].length) (baseStart_156403 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_156403 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_156403 prefixEnd_156403 := by exact prefixLift 156403
  have htrace : WordTrace (prefixWord ++ tailWord_156403) baseStart_156403 baseEnd_156403 := by
    simpa [prefixWord, tailWord_156403, baseEnd_156403] using wordTrace_append hprefix tailTrace_156403
  have hstable : (prefixWord ++ tailWord_156403).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_156403).length < 2 ^ (prefixWord ++ tailWord_156403).sum := by decide
  have hdescent : baseEnd_156403 < baseStart_156403 := by decide
  rcases family_descends (prefixWord ++ tailWord_156403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_156422 : List Nat := [6, 2, 2, 12]
def baseStart_156422 : Nat := 118140960795 + 156422 * 2 ^ 59
def prefixEnd_156422 : Nat := 4983230072969 + 3 ^ 40 * 156422 * 2
def baseEnd_156422 : Nat := 73451916723998383087

theorem tailTrace_156422 : CollatzResearch.WordTrace tailWord_156422 prefixEnd_156422 73451916723998383087 := by
  unfold tailWord_156422
  simp only [CollatzResearch.WordTrace]
  refine ⟨178286844978665112369985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 3803452692878189063893013 178286844978665112369985)
  ·
    refine ⟨133715133733998834277489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 178286844978665112369985 133715133733998834277489)
    ·
      refine ⟨100286350300499125708117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 133715133733998834277489 100286350300499125708117)
      ·
        refine ⟨73451916723998383087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 12 100286350300499125708117 73451916723998383087)
        ·
          rfl

theorem cell22_156422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 12].length) (baseStart_156422 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_156422 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_156422 prefixEnd_156422 := by exact prefixLift 156422
  have htrace : WordTrace (prefixWord ++ tailWord_156422) baseStart_156422 baseEnd_156422 := by
    simpa [prefixWord, tailWord_156422, baseEnd_156422] using wordTrace_append hprefix tailTrace_156422
  have hstable : (prefixWord ++ tailWord_156422).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_156422).length < 2 ^ (prefixWord ++ tailWord_156422).sum := by decide
  have hdescent : baseEnd_156422 < baseStart_156422 := by decide
  rcases family_descends (prefixWord ++ tailWord_156422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_156433 : List Nat := [1, 2, 2, 1, 1, 3, 3, 4, 5]
def baseStart_156433 : Nat := 118140960795 + 156433 * 2 ^ 59
def prefixEnd_156433 : Nat := 4983230072969 + 3 ^ 40 * 156433 * 2
def baseEnd_156433 : Nat := 17850070938864819748463

theorem tailTrace_156433 : CollatzResearch.WordTrace tailWord_156433 prefixEnd_156433 17850070938864819748463 := by
  unfold tailWord_156433
  simp only [CollatzResearch.WordTrace]
  refine ⟨5705580242277432474489953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3803720161518288316326635 5705580242277432474489953)
  ·
    refine ⟨4279185181708074355867465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5705580242277432474489953 4279185181708074355867465)
    ·
      refine ⟨3209388886281055766900599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4279185181708074355867465 3209388886281055766900599)
      ·
        refine ⟨4814083329421583650350899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3209388886281055766900599 4814083329421583650350899)
        ·
          refine ⟨7221124994132375475526349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4814083329421583650350899 7221124994132375475526349)
          ·
            refine ⟨2707921872799640803322381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7221124994132375475526349 2707921872799640803322381)
            ·
              refine ⟨1015470702299865301245893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2707921872799640803322381 1015470702299865301245893)
              ·
                refine ⟨190400756681224743983605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1015470702299865301245893 190400756681224743983605)
                ·
                  refine ⟨17850070938864819748463, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 190400756681224743983605 17850070938864819748463)
                  ·
                    rfl

theorem cell22_156433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 3, 4, 5].length) (baseStart_156433 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_156433 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_156433 prefixEnd_156433 := by exact prefixLift 156433
  have htrace : WordTrace (prefixWord ++ tailWord_156433) baseStart_156433 baseEnd_156433 := by
    simpa [prefixWord, tailWord_156433, baseEnd_156433] using wordTrace_append hprefix tailTrace_156433
  have hstable : (prefixWord ++ tailWord_156433).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_156433).length < 2 ^ (prefixWord ++ tailWord_156433).sum := by decide
  have hdescent : baseEnd_156433 < baseStart_156433 := by decide
  rcases family_descends (prefixWord ++ tailWord_156433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_156437 : List Nat := [1, 3, 2, 1, 2, 2, 3, 4, 1, 3]
def baseStart_156437 : Nat := 118140960795 + 156437 * 2 ^ 59
def prefixEnd_156437 : Nat := 4983230072969 + 3 ^ 40 * 156437 * 2
def baseEnd_156437 : Nat := 53551582098339782145377

theorem tailTrace_156437 : CollatzResearch.WordTrace tailWord_156437 prefixEnd_156437 53551582098339782145377 := by
  unfold tailWord_156437
  simp only [CollatzResearch.WordTrace]
  refine ⟨5705726134262941157635565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3803817422841960771757043 5705726134262941157635565)
  ·
    refine ⟨2139647300348602934113337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5705726134262941157635565 2139647300348602934113337)
    ·
      refine ⟨1604735475261452200585003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2139647300348602934113337 1604735475261452200585003)
      ·
        refine ⟨2407103212892178300877505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1604735475261452200585003 2407103212892178300877505)
        ·
          refine ⟨1805327409669133725658129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2407103212892178300877505 1805327409669133725658129)
          ·
            refine ⟨1353995557251850294243597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1805327409669133725658129 1353995557251850294243597)
            ·
              refine ⟨507748333969443860341349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1353995557251850294243597 507748333969443860341349)
              ·
                refine ⟨95202812619270723814003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 507748333969443860341349 95202812619270723814003)
                ·
                  refine ⟨142804218928906085721005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 95202812619270723814003 142804218928906085721005)
                  ·
                    refine ⟨53551582098339782145377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 142804218928906085721005 53551582098339782145377)
                    ·
                      rfl

theorem cell22_156437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 3, 4, 1, 3].length) (baseStart_156437 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_156437 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_156437 prefixEnd_156437 := by exact prefixLift 156437
  have htrace : WordTrace (prefixWord ++ tailWord_156437) baseStart_156437 baseEnd_156437 := by
    simpa [prefixWord, tailWord_156437, baseEnd_156437] using wordTrace_append hprefix tailTrace_156437
  have hstable : (prefixWord ++ tailWord_156437).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_156437).length < 2 ^ (prefixWord ++ tailWord_156437).sum := by decide
  have hdescent : baseEnd_156437 < baseStart_156437 := by decide
  rcases family_descends (prefixWord ++ tailWord_156437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_156448 : List Nat := [2, 1, 1, 5, 1, 2, 1, 1, 1, 7]
def baseStart_156448 : Nat := 118140960795 + 156448 * 2 ^ 59
def prefixEnd_156448 : Nat := 4983230072969 + 3 ^ 40 * 156448 * 2
def baseEnd_156448 : Nat := 53555347623139420120343

theorem tailTrace_156448 : CollatzResearch.WordTrace tailWord_156448 prefixEnd_156448 53555347623139420120343 := by
  unfold tailWord_156448
  simp only [CollatzResearch.WordTrace]
  refine ⟨2853063668611545018142999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3804084891482060024190665 2853063668611545018142999)
  ·
    refine ⟨4279595502917317527214499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2853063668611545018142999 4279595502917317527214499)
    ·
      refine ⟨6419393254375976290821749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4279595502917317527214499 6419393254375976290821749)
      ·
        refine ⟨601818117597747777264539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 6419393254375976290821749 601818117597747777264539)
        ·
          refine ⟨902727176396621665896809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 601818117597747777264539 902727176396621665896809)
          ·
            refine ⟨677045382297466249422607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 902727176396621665896809 677045382297466249422607)
            ·
              refine ⟨1015568073446199374133911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 677045382297466249422607 1015568073446199374133911)
              ·
                refine ⟨1523352110169299061200867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1015568073446199374133911 1523352110169299061200867)
                ·
                  refine ⟨2285028165253948591801301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1523352110169299061200867 2285028165253948591801301)
                  ·
                    refine ⟨53555347623139420120343, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 2285028165253948591801301 53555347623139420120343)
                    ·
                      rfl

theorem cell22_156448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 1, 1, 1, 7].length) (baseStart_156448 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_156448 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_156448 prefixEnd_156448 := by exact prefixLift 156448
  have htrace : WordTrace (prefixWord ++ tailWord_156448) baseStart_156448 baseEnd_156448 := by
    simpa [prefixWord, tailWord_156448, baseEnd_156448] using wordTrace_append hprefix tailTrace_156448
  have hstable : (prefixWord ++ tailWord_156448).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_156448).length < 2 ^ (prefixWord ++ tailWord_156448).sum := by decide
  have hdescent : baseEnd_156448 < baseStart_156448 := by decide
  rcases family_descends (prefixWord ++ tailWord_156448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_156450 : List Nat := [3, 3, 1, 1, 2, 2, 2, 3, 5]
def baseStart_156450 : Nat := 118140960795 + 156450 * 2 ^ 59
def prefixEnd_156450 : Nat := 4983230072969 + 3 ^ 40 * 156450 * 2
def baseEnd_156450 : Nat := 17852010754670693856779

theorem tailTrace_156450 : CollatzResearch.WordTrace tailWord_156450 prefixEnd_156450 17852010754670693856779 := by
  unfold tailWord_156450
  simp only [CollatzResearch.WordTrace]
  refine ⟨1426550070803961094464701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3804133522143896251905869 1426550070803961094464701)
  ·
    refine ⟨534956276551485410424263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1426550070803961094464701 534956276551485410424263)
    ·
      refine ⟨802434414827228115636395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 534956276551485410424263 802434414827228115636395)
      ·
        refine ⟨1203651622240842173454593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 802434414827228115636395 1203651622240842173454593)
        ·
          refine ⟨902738716680631630090945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1203651622240842173454593 902738716680631630090945)
          ·
            refine ⟨677054037510473722568209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 902738716680631630090945 677054037510473722568209)
            ·
              refine ⟨507790528132855291926157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 677054037510473722568209 507790528132855291926157)
              ·
                refine ⟨190421448049820734472309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 507790528132855291926157 190421448049820734472309)
                ·
                  refine ⟨17852010754670693856779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 190421448049820734472309 17852010754670693856779)
                  ·
                    rfl

theorem cell22_156450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 2, 3, 5].length) (baseStart_156450 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_156450 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_156450 prefixEnd_156450 := by exact prefixLift 156450
  have htrace : WordTrace (prefixWord ++ tailWord_156450) baseStart_156450 baseEnd_156450 := by
    simpa [prefixWord, tailWord_156450, baseEnd_156450] using wordTrace_append hprefix tailTrace_156450
  have hstable : (prefixWord ++ tailWord_156450).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_156450).length < 2 ^ (prefixWord ++ tailWord_156450).sum := by decide
  have hdescent : baseEnd_156450 < baseStart_156450 := by decide
  rcases family_descends (prefixWord ++ tailWord_156450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_156514 : List Nat := [3, 3, 2, 1, 3, 1, 2, 2, 1, 4]
def baseStart_156514 : Nat := 118140960795 + 156514 * 2 ^ 59
def prefixEnd_156514 : Nat := 4983230072969 + 3 ^ 40 * 156514 * 2
def baseEnd_156514 : Nat := 53577940771937247970141

theorem tailTrace_156514 : CollatzResearch.WordTrace tailWord_156514 prefixEnd_156514 53577940771937247970141 := by
  unfold tailWord_156514
  simp only [CollatzResearch.WordTrace]
  refine ⟨1427133638745995827047149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3805689703322655538792397 1427133638745995827047149)
  ·
    refine ⟨535175114529748435142681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1427133638745995827047149 535175114529748435142681)
    ·
      refine ⟨401381335897311326357011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 535175114529748435142681 401381335897311326357011)
      ·
        refine ⟨602072003845966989535517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 401381335897311326357011 602072003845966989535517)
        ·
          refine ⟨225777001442237621075819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 602072003845966989535517 225777001442237621075819)
          ·
            refine ⟨338665502163356431613729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 225777001442237621075819 338665502163356431613729)
            ·
              refine ⟨253999126622517323710297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 338665502163356431613729 253999126622517323710297)
              ·
                refine ⟨190499344966887992782723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 253999126622517323710297 190499344966887992782723)
                ·
                  refine ⟨285749017450331989174085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 190499344966887992782723 285749017450331989174085)
                  ·
                    refine ⟨53577940771937247970141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 285749017450331989174085 53577940771937247970141)
                    ·
                      rfl

theorem cell22_156514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 1, 2, 2, 1, 4].length) (baseStart_156514 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_156514 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_156514 prefixEnd_156514 := by exact prefixLift 156514
  have htrace : WordTrace (prefixWord ++ tailWord_156514) baseStart_156514 baseEnd_156514 := by
    simpa [prefixWord, tailWord_156514, baseEnd_156514] using wordTrace_append hprefix tailTrace_156514
  have hstable : (prefixWord ++ tailWord_156514).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_156514).length < 2 ^ (prefixWord ++ tailWord_156514).sum := by decide
  have hdescent : baseEnd_156514 < baseStart_156514 := by decide
  rcases family_descends (prefixWord ++ tailWord_156514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_156525 : List Nat := [1, 5, 1, 1, 1, 1, 1, 5, 2, 4]
def baseStart_156525 : Nat := 118140960795 + 156525 * 2 ^ 59
def prefixEnd_156525 : Nat := 4983230072969 + 3 ^ 40 * 156525 * 2
def baseEnd_156525 : Nat := 53581706296736885945107

theorem tailTrace_156525 : CollatzResearch.WordTrace tailWord_156525 prefixEnd_156525 53581706296736885945107 := by
  unfold tailWord_156525
  simp only [CollatzResearch.WordTrace]
  refine ⟨5708935757944132186839029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3805957171962754791226019 5708935757944132186839029)
  ·
    refine ⟨535212727307262392516159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 5708935757944132186839029 535212727307262392516159)
    ·
      refine ⟨802819090960893588774239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 535212727307262392516159 802819090960893588774239)
      ·
        refine ⟨1204228636441340383161359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 802819090960893588774239 1204228636441340383161359)
        ·
          refine ⟨1806342954662010574742039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1204228636441340383161359 1806342954662010574742039)
          ·
            refine ⟨2709514431993015862113059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1806342954662010574742039 2709514431993015862113059)
            ·
              refine ⟨4064271647989523793169589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2709514431993015862113059 4064271647989523793169589)
              ·
                refine ⟨381025466999017855609649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4064271647989523793169589 381025466999017855609649)
                ·
                  refine ⟨285769100249263391707237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 381025466999017855609649 285769100249263391707237)
                  ·
                    refine ⟨53581706296736885945107, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 285769100249263391707237 53581706296736885945107)
                    ·
                      rfl

theorem cell22_156525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 5, 2, 4].length) (baseStart_156525 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_156525 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_156525 prefixEnd_156525 := by exact prefixLift 156525
  have htrace : WordTrace (prefixWord ++ tailWord_156525) baseStart_156525 baseEnd_156525 := by
    simpa [prefixWord, tailWord_156525, baseEnd_156525] using wordTrace_append hprefix tailTrace_156525
  have hstable : (prefixWord ++ tailWord_156525).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_156525).length < 2 ^ (prefixWord ++ tailWord_156525).sum := by decide
  have hdescent : baseEnd_156525 < baseStart_156525 := by decide
  rcases family_descends (prefixWord ++ tailWord_156525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_156546 : List Nat := [3, 4, 2, 2, 1, 2, 1, 1, 6]
def baseStart_156546 : Nat := 118140960795 + 156546 * 2 ^ 59
def prefixEnd_156546 : Nat := 4983230072969 + 3 ^ 40 * 156546 * 2
def baseEnd_156546 : Nat := 17862965008633277056681

theorem tailTrace_156546 : CollatzResearch.WordTrace tailWord_156546 prefixEnd_156546 17862965008633277056681 := by
  unfold tailWord_156546
  simp only [CollatzResearch.WordTrace]
  refine ⟨1427425422717013193338373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3806467793912035182235661 1427425422717013193338373)
  ·
    refine ⟨267642266759439973750945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1427425422717013193338373 267642266759439973750945)
    ·
      refine ⟨200731700069579980313209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 267642266759439973750945 200731700069579980313209)
      ·
        refine ⟨150548775052184985234907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 200731700069579980313209 150548775052184985234907)
        ·
          refine ⟨225823162578277477852361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 150548775052184985234907 225823162578277477852361)
          ·
            refine ⟨169367371933708108389271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 225823162578277477852361 169367371933708108389271)
            ·
              refine ⟨254051057900562162583907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 169367371933708108389271 254051057900562162583907)
              ·
                refine ⟨381076586850843243875861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 254051057900562162583907 381076586850843243875861)
                ·
                  refine ⟨17862965008633277056681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 381076586850843243875861 17862965008633277056681)
                  ·
                    rfl

theorem cell22_156546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 2, 1, 1, 6].length) (baseStart_156546 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_156546 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_156546 prefixEnd_156546 := by exact prefixLift 156546
  have htrace : WordTrace (prefixWord ++ tailWord_156546) baseStart_156546 baseEnd_156546 := by
    simpa [prefixWord, tailWord_156546, baseEnd_156546] using wordTrace_append hprefix tailTrace_156546
  have hstable : (prefixWord ++ tailWord_156546).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_156546).length < 2 ^ (prefixWord ++ tailWord_156546).sum := by decide
  have hdescent : baseEnd_156546 < baseStart_156546 := by decide
  rcases family_descends (prefixWord ++ tailWord_156546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_156615 : List Nat := [1, 1, 4, 1, 1, 2, 3, 2, 3, 4]
def baseStart_156615 : Nat := 118140960795 + 156615 * 2 ^ 59
def prefixEnd_156615 : Nat := 4983230072969 + 3 ^ 40 * 156615 * 2
def baseEnd_156615 : Nat := 53612515136006651194831

theorem tailTrace_156615 : CollatzResearch.WordTrace tailWord_156615 prefixEnd_156615 53612515136006651194831 := by
  unfold tailWord_156615
  simp only [CollatzResearch.WordTrace]
  refine ⟨5712218327618077557615299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3808145551745385038410199 5712218327618077557615299)
  ·
    refine ⟨8568327491427116336422949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5712218327618077557615299 8568327491427116336422949)
    ·
      refine ⟨1606561404642584313079303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8568327491427116336422949 1606561404642584313079303)
      ·
        refine ⟨2409842106963876469618955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1606561404642584313079303 2409842106963876469618955)
        ·
          refine ⟨3614763160445814704428433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2409842106963876469618955 3614763160445814704428433)
          ·
            refine ⟨2711072370334361028321325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3614763160445814704428433 2711072370334361028321325)
            ·
              refine ⟨1016652138875385385620497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2711072370334361028321325 1016652138875385385620497)
              ·
                refine ⟨762489104156539039215373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1016652138875385385620497 762489104156539039215373)
                ·
                  refine ⟨285933414058702139705765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 762489104156539039215373 285933414058702139705765)
                  ·
                    refine ⟨53612515136006651194831, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 285933414058702139705765 53612515136006651194831)
                    ·
                      rfl

theorem cell22_156615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 3, 2, 3, 4].length) (baseStart_156615 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_156615 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_156615 prefixEnd_156615 := by exact prefixLift 156615
  have htrace : WordTrace (prefixWord ++ tailWord_156615) baseStart_156615 baseEnd_156615 := by
    simpa [prefixWord, tailWord_156615, baseEnd_156615] using wordTrace_append hprefix tailTrace_156615
  have hstable : (prefixWord ++ tailWord_156615).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_156615).length < 2 ^ (prefixWord ++ tailWord_156615).sum := by decide
  have hdescent : baseEnd_156615 < baseStart_156615 := by decide
  rcases family_descends (prefixWord ++ tailWord_156615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_156720 : List Nat := [2, 1, 1, 1, 2, 4, 1, 3, 7]
def baseStart_156720 : Nat := 118140960795 + 156720 * 2 ^ 59
def prefixEnd_156720 : Nat := 4983230072969 + 3 ^ 40 * 156720 * 2
def baseEnd_156720 : Nat := 17882819593940459106503

theorem tailTrace_156720 : CollatzResearch.WordTrace tailWord_156720 prefixEnd_156720 17882819593940459106503 := by
  unfold tailWord_156720
  simp only [CollatzResearch.WordTrace]
  refine ⟨2858023996118840245093807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3810698661491786993458409 2858023996118840245093807)
  ·
    refine ⟨4287035994178260367640711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2858023996118840245093807 4287035994178260367640711)
    ·
      refine ⟨6430553991267390551461067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4287035994178260367640711 6430553991267390551461067)
      ·
        refine ⟨9645830986901085827191601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6430553991267390551461067 9645830986901085827191601)
        ·
          refine ⟨7234373240175814370393701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9645830986901085827191601 7234373240175814370393701)
          ·
            refine ⟨1356444982532965194448819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7234373240175814370393701 1356444982532965194448819)
            ·
              refine ⟨2034667473799447791673229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1356444982532965194448819 2034667473799447791673229)
              ·
                refine ⟨763000302674792921877461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2034667473799447791673229 763000302674792921877461)
                ·
                  refine ⟨17882819593940459106503, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 763000302674792921877461 17882819593940459106503)
                  ·
                    rfl

theorem cell22_156720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 1, 3, 7].length) (baseStart_156720 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_156720 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_156720 prefixEnd_156720 := by exact prefixLift 156720
  have htrace : WordTrace (prefixWord ++ tailWord_156720) baseStart_156720 baseEnd_156720 := by
    simpa [prefixWord, tailWord_156720, baseEnd_156720] using wordTrace_append hprefix tailTrace_156720
  have hstable : (prefixWord ++ tailWord_156720).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_156720).length < 2 ^ (prefixWord ++ tailWord_156720).sum := by decide
  have hdescent : baseEnd_156720 < baseStart_156720 := by decide
  rcases family_descends (prefixWord ++ tailWord_156720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_156735 : List Nat := [1, 1, 2, 2, 3, 1, 1, 3, 1, 7]
def baseStart_156735 : Nat := 118140960795 + 156735 * 2 ^ 59
def prefixEnd_156735 : Nat := 4983230072969 + 3 ^ 40 * 156735 * 2
def baseEnd_156735 : Nat := 53653593588366338194463

theorem tailTrace_156735 : CollatzResearch.WordTrace tailWord_156735 prefixEnd_156735 53653593588366338194463 := by
  unfold tailWord_156735
  simp only [CollatzResearch.WordTrace]
  refine ⟨5716595087183338051983659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3811063391455558701322439 5716595087183338051983659)
  ·
    refine ⟨8574892630775007077975489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5716595087183338051983659 8574892630775007077975489)
    ·
      refine ⟨6431169473081255308481617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8574892630775007077975489 6431169473081255308481617)
      ·
        refine ⟨4823377104810941481361213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6431169473081255308481617 4823377104810941481361213)
        ·
          refine ⟨1808766414304103055510455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4823377104810941481361213 1808766414304103055510455)
          ·
            refine ⟨2713149621456154583265683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1808766414304103055510455 2713149621456154583265683)
            ·
              refine ⟨4069724432184231874898525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2713149621456154583265683 4069724432184231874898525)
              ·
                refine ⟨1526146662069086953086947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4069724432184231874898525 1526146662069086953086947)
                ·
                  refine ⟨2289219993103630429630421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1526146662069086953086947 2289219993103630429630421)
                  ·
                    refine ⟨53653593588366338194463, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 2289219993103630429630421 53653593588366338194463)
                    ·
                      rfl

theorem cell22_156735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 3, 1, 7].length) (baseStart_156735 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_156735 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_156735 prefixEnd_156735 := by exact prefixLift 156735
  have htrace : WordTrace (prefixWord ++ tailWord_156735) baseStart_156735 baseEnd_156735 := by
    simpa [prefixWord, tailWord_156735, baseEnd_156735] using wordTrace_append hprefix tailTrace_156735
  have hstable : (prefixWord ++ tailWord_156735).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_156735).length < 2 ^ (prefixWord ++ tailWord_156735).sum := by decide
  have hdescent : baseEnd_156735 < baseStart_156735 := by decide
  rcases family_descends (prefixWord ++ tailWord_156735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_156814 : List Nat := [4, 1, 1, 3, 2, 1, 2, 2, 1, 5]
def baseStart_156814 : Nat := 118140960795 + 156814 * 2 ^ 59
def prefixEnd_156814 : Nat := 4983230072969 + 3 ^ 40 * 156814 * 2
def baseEnd_156814 : Nat := 53680636902836465469221

theorem tailTrace_156814 : CollatzResearch.WordTrace tailWord_156814 prefixEnd_156814 53680636902836465469221 := by
  unfold tailWord_156814
  simp only [CollatzResearch.WordTrace]
  refine ⟨714934556737141818013687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3812984302598089696072997 714934556737141818013687)
  ·
    refine ⟨1072401835105712727020531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 714934556737141818013687 1072401835105712727020531)
    ·
      refine ⟨1608602752658569090530797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1072401835105712727020531 1608602752658569090530797)
      ·
        refine ⟨603226032246963408949049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1608602752658569090530797 603226032246963408949049)
        ·
          refine ⟨452419524185222556711787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 603226032246963408949049 452419524185222556711787)
          ·
            refine ⟨678629286277833835067681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 452419524185222556711787 678629286277833835067681)
            ·
              refine ⟨508971964708375376300761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 678629286277833835067681 508971964708375376300761)
              ·
                refine ⟨381728973531281532225571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 508971964708375376300761 381728973531281532225571)
                ·
                  refine ⟨572593460296922298338357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 381728973531281532225571 572593460296922298338357)
                  ·
                    refine ⟨53680636902836465469221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 572593460296922298338357 53680636902836465469221)
                    ·
                      rfl

theorem cell22_156814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 2, 2, 1, 5].length) (baseStart_156814 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_156814 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_156814 prefixEnd_156814 := by exact prefixLift 156814
  have htrace : WordTrace (prefixWord ++ tailWord_156814) baseStart_156814 baseEnd_156814 := by
    simpa [prefixWord, tailWord_156814, baseEnd_156814] using wordTrace_append hprefix tailTrace_156814
  have hstable : (prefixWord ++ tailWord_156814).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_156814).length < 2 ^ (prefixWord ++ tailWord_156814).sum := by decide
  have hdescent : baseEnd_156814 < baseStart_156814 := by decide
  rcases family_descends (prefixWord ++ tailWord_156814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_156818 : List Nat := [3, 2, 3, 1, 1, 4, 2, 1, 1, 4]
def baseStart_156818 : Nat := 118140960795 + 156818 * 2 ^ 59
def prefixEnd_156818 : Nat := 4983230072969 + 3 ^ 40 * 156818 * 2
def baseEnd_156818 : Nat := 53682006184581788369209

theorem tailTrace_156818 : CollatzResearch.WordTrace tailWord_156818 prefixEnd_156818 53682006184581788369209 := by
  unfold tailWord_156818
  simp only [CollatzResearch.WordTrace]
  refine ⟨1429905586470660806813777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3813081563921762151503405 1429905586470660806813777)
  ·
    refine ⟨1072429189852995605110333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1429905586470660806813777 1072429189852995605110333)
    ·
      refine ⟨402160946194873351916375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1072429189852995605110333 402160946194873351916375)
      ·
        refine ⟨603241419292310027874563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 402160946194873351916375 603241419292310027874563)
        ·
          refine ⟨904862128938465041811845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 603241419292310027874563 904862128938465041811845)
          ·
            refine ⟨169661649175962195339721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 904862128938465041811845 169661649175962195339721)
            ·
              refine ⟨127246236881971646504791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 169661649175962195339721 127246236881971646504791)
              ·
                refine ⟨190869355322957469757187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 127246236881971646504791 190869355322957469757187)
                ·
                  refine ⟨286304032984436204635781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 190869355322957469757187 286304032984436204635781)
                  ·
                    refine ⟨53682006184581788369209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 286304032984436204635781 53682006184581788369209)
                    ·
                      rfl

theorem cell22_156818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 4, 2, 1, 1, 4].length) (baseStart_156818 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_156818 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_156818 prefixEnd_156818 := by exact prefixLift 156818
  have htrace : WordTrace (prefixWord ++ tailWord_156818) baseStart_156818 baseEnd_156818 := by
    simpa [prefixWord, tailWord_156818, baseEnd_156818] using wordTrace_append hprefix tailTrace_156818
  have hstable : (prefixWord ++ tailWord_156818).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_156818).length < 2 ^ (prefixWord ++ tailWord_156818).sum := by decide
  have hdescent : baseEnd_156818 < baseStart_156818 := by decide
  rcases family_descends (prefixWord ++ tailWord_156818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_156831 : List Nat := [1, 1, 2, 6, 2, 1, 1, 1, 4, 3]
def baseStart_156831 : Nat := 118140960795 + 156831 * 2 ^ 59
def prefixEnd_156831 : Nat := 4983230072969 + 3 ^ 40 * 156831 * 2
def baseEnd_156831 : Nat := 53686456350254087794169

theorem tailTrace_156831 : CollatzResearch.WordTrace tailWord_156831 prefixEnd_156831 53686456350254087794169 := by
  unfold tailWord_156831
  simp only [CollatzResearch.WordTrace]
  refine ⟨5720096494835546447478347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3813397663223697631652231 5720096494835546447478347)
  ·
    refine ⟨8580144742253319671217521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5720096494835546447478347 8580144742253319671217521)
    ·
      refine ⟨6435108556689989753413141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8580144742253319671217521 6435108556689989753413141)
      ·
        refine ⟨301645713594843269691241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 6435108556689989753413141 301645713594843269691241)
        ·
          refine ⟨226234285196132452268431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 301645713594843269691241 226234285196132452268431)
          ·
            refine ⟨339351427794198678402647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 226234285196132452268431 339351427794198678402647)
            ·
              refine ⟨509027141691298017603971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 339351427794198678402647 509027141691298017603971)
              ·
                refine ⟨763540712536947026405957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 509027141691298017603971 763540712536947026405957)
                ·
                  refine ⟨143163883600677567451117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 763540712536947026405957 143163883600677567451117)
                  ·
                    refine ⟨53686456350254087794169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 143163883600677567451117 53686456350254087794169)
                    ·
                      rfl

theorem cell22_156831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 1, 1, 1, 4, 3].length) (baseStart_156831 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_156831 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_156831 prefixEnd_156831 := by exact prefixLift 156831
  have htrace : WordTrace (prefixWord ++ tailWord_156831) baseStart_156831 baseEnd_156831 := by
    simpa [prefixWord, tailWord_156831, baseEnd_156831] using wordTrace_append hprefix tailTrace_156831
  have hstable : (prefixWord ++ tailWord_156831).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_156831).length < 2 ^ (prefixWord ++ tailWord_156831).sum := by decide
  have hdescent : baseEnd_156831 < baseStart_156831 := by decide
  rcases family_descends (prefixWord ++ tailWord_156831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_156872 : List Nat := [2, 1, 3, 1, 2, 1, 3, 2, 7]
def baseStart_156872 : Nat := 118140960795 + 156872 * 2 ^ 59
def prefixEnd_156872 : Nat := 4983230072969 + 3 ^ 40 * 156872 * 2
def baseEnd_156872 : Nat := 17900163829381215839681

theorem tailTrace_156872 : CollatzResearch.WordTrace tailWord_156872 prefixEnd_156872 17900163829381215839681 := by
  unfold tailWord_156872
  simp only [CollatzResearch.WordTrace]
  refine ⟨2860795943843505224860435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3814394591791340299813913 2860795943843505224860435)
  ·
    refine ⟨4291193915765257837290653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2860795943843505224860435 4291193915765257837290653)
    ·
      refine ⟨1609197718411971688983995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4291193915765257837290653 1609197718411971688983995)
      ·
        refine ⟨2413796577617957533475993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1609197718411971688983995 2413796577617957533475993)
        ·
          refine ⟨1810347433213468150106995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2413796577617957533475993 1810347433213468150106995)
          ·
            refine ⟨2715521149820202225160493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1810347433213468150106995 2715521149820202225160493)
            ·
              refine ⟨1018320431182575834435185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2715521149820202225160493 1018320431182575834435185)
              ·
                refine ⟨763740323386931875826389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1018320431182575834435185 763740323386931875826389)
                ·
                  refine ⟨17900163829381215839681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 763740323386931875826389 17900163829381215839681)
                  ·
                    rfl

theorem cell22_156872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 3, 2, 7].length) (baseStart_156872 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_156872 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_156872 prefixEnd_156872 := by exact prefixLift 156872
  have htrace : WordTrace (prefixWord ++ tailWord_156872) baseStart_156872 baseEnd_156872 := by
    simpa [prefixWord, tailWord_156872, baseEnd_156872] using wordTrace_append hprefix tailTrace_156872
  have hstable : (prefixWord ++ tailWord_156872).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_156872).length < 2 ^ (prefixWord ++ tailWord_156872).sum := by decide
  have hdescent : baseEnd_156872 < baseStart_156872 := by decide
  rcases family_descends (prefixWord ++ tailWord_156872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_156887 : List Nat := [1, 1, 3, 2, 1, 2, 2, 1, 4, 5]
def baseStart_156887 : Nat := 118140960795 + 156887 * 2 ^ 59
def prefixEnd_156887 : Nat := 4983230072969 + 3 ^ 40 * 156887 * 2
def baseEnd_156887 : Nat := 53705626294688608393997

theorem tailTrace_156887 : CollatzResearch.WordTrace tailWord_156887 prefixEnd_156887 53705626294688608393997 := by
  unfold tailWord_156887
  simp only [CollatzResearch.WordTrace]
  refine ⟨5722138982632668011516915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3814759321755112007677943 5722138982632668011516915)
  ·
    refine ⟨8583208473949002017275373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5722138982632668011516915 8583208473949002017275373)
    ·
      refine ⟨3218703177730875756478265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8583208473949002017275373 3218703177730875756478265)
      ·
        refine ⟨2414027383298156817358699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3218703177730875756478265 2414027383298156817358699)
        ·
          refine ⟨3621041074947235226038049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2414027383298156817358699 3621041074947235226038049)
          ·
            refine ⟨2715780806210426419528537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3621041074947235226038049 2715780806210426419528537)
            ·
              refine ⟨2036835604657819814646403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2715780806210426419528537 2036835604657819814646403)
              ·
                refine ⟨3055253406986729721969605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2036835604657819814646403 3055253406986729721969605)
                ·
                  refine ⟨572860013810011822869301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3055253406986729721969605 572860013810011822869301)
                  ·
                    refine ⟨53705626294688608393997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 572860013810011822869301 53705626294688608393997)
                    ·
                      rfl

theorem cell22_156887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 2, 1, 4, 5].length) (baseStart_156887 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_156887 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_156887 prefixEnd_156887 := by exact prefixLift 156887
  have htrace : WordTrace (prefixWord ++ tailWord_156887) baseStart_156887 baseEnd_156887 := by
    simpa [prefixWord, tailWord_156887, baseEnd_156887] using wordTrace_append hprefix tailTrace_156887
  have hstable : (prefixWord ++ tailWord_156887).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_156887).length < 2 ^ (prefixWord ++ tailWord_156887).sum := by decide
  have hdescent : baseEnd_156887 < baseStart_156887 := by decide
  rcases family_descends (prefixWord ++ tailWord_156887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_156906 : List Nat := [3, 1, 3, 1, 1, 3, 4, 1, 5]
def baseStart_156906 : Nat := 118140960795 + 156906 * 2 ^ 59
def prefixEnd_156906 : Nat := 4983230072969 + 3 ^ 40 * 156906 * 2
def baseEnd_156906 : Nat := 17904043460992964056313

theorem tailTrace_156906 : CollatzResearch.WordTrace tailWord_156906 prefixEnd_156906 17904043460992964056313 := by
  unfold tailWord_156906
  simp only [CollatzResearch.WordTrace]
  refine ⟨1430707992390958564114643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3815221313042556170972381 1430707992390958564114643)
  ·
    refine ⟨2146061988586437846171965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1430707992390958564114643 2146061988586437846171965)
    ·
      refine ⟨804773245719914192314487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2146061988586437846171965 804773245719914192314487)
      ·
        refine ⟨1207159868579871288471731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 804773245719914192314487 1207159868579871288471731)
        ·
          refine ⟨1810739802869806932707597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1207159868579871288471731 1810739802869806932707597)
          ·
            refine ⟨679027426076177599765349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1810739802869806932707597 679027426076177599765349)
            ·
              refine ⟨127317642389283299956003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 679027426076177599765349 127317642389283299956003)
              ·
                refine ⟨190976463583924949934005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 127317642389283299956003 190976463583924949934005)
                ·
                  refine ⟨17904043460992964056313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 190976463583924949934005 17904043460992964056313)
                  ·
                    rfl

theorem cell22_156906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 4, 1, 5].length) (baseStart_156906 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_156906 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_156906 prefixEnd_156906 := by exact prefixLift 156906
  have htrace : WordTrace (prefixWord ++ tailWord_156906) baseStart_156906 baseEnd_156906 := by
    simpa [prefixWord, tailWord_156906, baseEnd_156906] using wordTrace_append hprefix tailTrace_156906
  have hstable : (prefixWord ++ tailWord_156906).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_156906).length < 2 ^ (prefixWord ++ tailWord_156906).sum := by decide
  have hdescent : baseEnd_156906 < baseStart_156906 := by decide
  rcases family_descends (prefixWord ++ tailWord_156906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_156947 : List Nat := [1, 1, 1, 2, 1, 3, 1, 1, 5, 6]
def baseStart_156947 : Nat := 118140960795 + 156947 * 2 ^ 59
def prefixEnd_156947 : Nat := 4983230072969 + 3 ^ 40 * 156947 * 2
def baseEnd_156947 : Nat := 53726165520868451893813

theorem tailTrace_156947 : CollatzResearch.WordTrace tailWord_156947 prefixEnd_156947 53726165520868451893813 := by
  unfold tailWord_156947
  simp only [CollatzResearch.WordTrace]
  refine ⟨5724327362415298258701095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3816218241610198839134063 5724327362415298258701095)
  ·
    refine ⟨8586491043622947388051643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5724327362415298258701095 8586491043622947388051643)
    ·
      refine ⟨12879736565434421082077465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8586491043622947388051643 12879736565434421082077465)
      ·
        refine ⟨9659802424075815811558099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12879736565434421082077465 9659802424075815811558099)
        ·
          refine ⟨14489703636113723717337149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9659802424075815811558099 14489703636113723717337149)
          ·
            refine ⟨5433638863542646394001431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14489703636113723717337149 5433638863542646394001431)
            ·
              refine ⟨8150458295313969591002147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5433638863542646394001431 8150458295313969591002147)
              ·
                refine ⟨12225687442970954386503221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8150458295313969591002147 12225687442970954386503221)
                ·
                  refine ⟨1146158197778526973734677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 12225687442970954386503221 1146158197778526973734677)
                  ·
                    refine ⟨53726165520868451893813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1146158197778526973734677 53726165520868451893813)
                    ·
                      rfl

theorem cell22_156947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 1, 5, 6].length) (baseStart_156947 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_156947 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_156947 prefixEnd_156947 := by exact prefixLift 156947
  have htrace : WordTrace (prefixWord ++ tailWord_156947) baseStart_156947 baseEnd_156947 := by
    simpa [prefixWord, tailWord_156947, baseEnd_156947] using wordTrace_append hprefix tailTrace_156947
  have hstable : (prefixWord ++ tailWord_156947).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_156947).length < 2 ^ (prefixWord ++ tailWord_156947).sum := by decide
  have hdescent : baseEnd_156947 < baseStart_156947 := by decide
  rcases family_descends (prefixWord ++ tailWord_156947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_156951 : List Nat := [1, 1, 3, 4, 1, 1, 3, 4, 4]
def baseStart_156951 : Nat := 118140960795 + 156951 * 2 ^ 59
def prefixEnd_156951 : Nat := 4983230072969 + 3 ^ 40 * 156951 * 2
def baseEnd_156951 : Nat := 17909178267537924931267

theorem tailTrace_156951 : CollatzResearch.WordTrace tailWord_156951 prefixEnd_156951 17909178267537924931267 := by
  unfold tailWord_156951
  simp only [CollatzResearch.WordTrace]
  refine ⟨5724473254400806941846707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3816315502933871294564471 5724473254400806941846707)
  ·
    refine ⟨8586709881601210412770061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5724473254400806941846707 8586709881601210412770061)
    ·
      refine ⟨3220016205600453904788773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8586709881601210412770061 3220016205600453904788773)
      ·
        refine ⟨603753038550085107147895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3220016205600453904788773 603753038550085107147895)
        ·
          refine ⟨905629557825127660721843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 603753038550085107147895 905629557825127660721843)
          ·
            refine ⟨1358444336737691491082765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 905629557825127660721843 1358444336737691491082765)
            ·
              refine ⟨509416626276634309156037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1358444336737691491082765 509416626276634309156037)
              ·
                refine ⟨95515617426868932966757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 509416626276634309156037 95515617426868932966757)
                ·
                  refine ⟨17909178267537924931267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 95515617426868932966757 17909178267537924931267)
                  ·
                    rfl

theorem cell22_156951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 3, 4, 4].length) (baseStart_156951 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_156951 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_156951 prefixEnd_156951 := by exact prefixLift 156951
  have htrace : WordTrace (prefixWord ++ tailWord_156951) baseStart_156951 baseEnd_156951 := by
    simpa [prefixWord, tailWord_156951, baseEnd_156951] using wordTrace_append hprefix tailTrace_156951
  have hstable : (prefixWord ++ tailWord_156951).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_156951).length < 2 ^ (prefixWord ++ tailWord_156951).sum := by decide
  have hdescent : baseEnd_156951 < baseStart_156951 := by decide
  rcases family_descends (prefixWord ++ tailWord_156951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_156964 : List Nat := [2, 3, 1, 3, 1, 1, 2, 2, 1, 6]
def baseStart_156964 : Nat := 118140960795 + 156964 * 2 ^ 59
def prefixEnd_156964 : Nat := 4983230072969 + 3 ^ 40 * 156964 * 2
def baseEnd_156964 : Nat := 53731984968286074218761

theorem tailTrace_156964 : CollatzResearch.WordTrace tailWord_156964 prefixEnd_156964 53731984968286074218761 := by
  unfold tailWord_156964
  simp only [CollatzResearch.WordTrace]
  refine ⟨2862473701676855081034973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3816631602235806774713297 2862473701676855081034973)
  ·
    refine ⟨1073427638128820655388115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2862473701676855081034973 1073427638128820655388115)
    ·
      refine ⟨1610141457193230983082173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1073427638128820655388115 1610141457193230983082173)
      ·
        refine ⟨603803046447461618655815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1610141457193230983082173 603803046447461618655815)
        ·
          refine ⟨905704569671192427983723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 603803046447461618655815 905704569671192427983723)
          ·
            refine ⟨1358556854506788641975585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 905704569671192427983723 1358556854506788641975585)
            ·
              refine ⟨1018917640880091481481689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1358556854506788641975585 1018917640880091481481689)
              ·
                refine ⟨764188230660068611111267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1018917640880091481481689 764188230660068611111267)
                ·
                  refine ⟨1146282345990102916666901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 764188230660068611111267 1146282345990102916666901)
                  ·
                    refine ⟨53731984968286074218761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1146282345990102916666901 53731984968286074218761)
                    ·
                      rfl

theorem cell22_156964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 2, 2, 1, 6].length) (baseStart_156964 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_156964 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_156964 prefixEnd_156964 := by exact prefixLift 156964
  have htrace : WordTrace (prefixWord ++ tailWord_156964) baseStart_156964 baseEnd_156964 := by
    simpa [prefixWord, tailWord_156964, baseEnd_156964] using wordTrace_append hprefix tailTrace_156964
  have hstable : (prefixWord ++ tailWord_156964).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_156964).length < 2 ^ (prefixWord ++ tailWord_156964).sum := by decide
  have hdescent : baseEnd_156964 < baseStart_156964 := by decide
  rcases family_descends (prefixWord ++ tailWord_156964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_156981 : List Nat := [1, 3, 3, 1, 2, 2, 3, 1, 2, 4]
def baseStart_156981 : Nat := 118140960795 + 156981 * 2 ^ 59
def prefixEnd_156981 : Nat := 4983230072969 + 3 ^ 40 * 156981 * 2
def baseEnd_156981 : Nat := 53737804415703696543709

theorem tailTrace_156981 : CollatzResearch.WordTrace tailWord_156981 prefixEnd_156981 53737804415703696543709 := by
  unfold tailWord_156981
  simp only [CollatzResearch.WordTrace]
  refine ⟨5725567444292122065438797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3817044962861414710292531 5725567444292122065438797)
  ·
    refine ⟨2147087791609545774539549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5725567444292122065438797 2147087791609545774539549)
    ·
      refine ⟨805157921853579665452331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2147087791609545774539549 805157921853579665452331)
      ·
        refine ⟨1207736882780369498178497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 805157921853579665452331 1207736882780369498178497)
        ·
          refine ⟨905802662085277123633873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1207736882780369498178497 905802662085277123633873)
          ·
            refine ⟨679351996563957842725405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 905802662085277123633873 679351996563957842725405)
            ·
              refine ⟨254756998711484191022027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 679351996563957842725405 254756998711484191022027)
              ·
                refine ⟨382135498067226286533041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 254756998711484191022027 382135498067226286533041)
                ·
                  refine ⟨286601623550419714899781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 382135498067226286533041 286601623550419714899781)
                  ·
                    refine ⟨53737804415703696543709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 286601623550419714899781 53737804415703696543709)
                    ·
                      rfl

theorem cell22_156981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 3, 1, 2, 4].length) (baseStart_156981 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_156981 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_156981 prefixEnd_156981 := by exact prefixLift 156981
  have htrace : WordTrace (prefixWord ++ tailWord_156981) baseStart_156981 baseEnd_156981 := by
    simpa [prefixWord, tailWord_156981, baseEnd_156981] using wordTrace_append hprefix tailTrace_156981
  have hstable : (prefixWord ++ tailWord_156981).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_156981).length < 2 ^ (prefixWord ++ tailWord_156981).sum := by decide
  have hdescent : baseEnd_156981 < baseStart_156981 := by decide
  rcases family_descends (prefixWord ++ tailWord_156981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_156996 : List Nat := [2, 3, 4, 1, 1, 2, 9]
def baseStart_156996 : Nat := 118140960795 + 156996 * 2 ^ 59
def prefixEnd_156996 : Nat := 4983230072969 + 3 ^ 40 * 156996 * 2
def baseEnd_156996 : Nat := 1990479230453653978469

theorem tailTrace_156996 : CollatzResearch.WordTrace tailWord_156996 prefixEnd_156996 1990479230453653978469 := by
  unfold tailWord_156996
  simp only [CollatzResearch.WordTrace]
  refine ⟨2863057269618889813617421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3817409692825186418156561 2863057269618889813617421)
  ·
    refine ⟨1073646476107083680106533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2863057269618889813617421 1073646476107083680106533)
    ·
      refine ⟨201308714270078190019975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1073646476107083680106533 201308714270078190019975)
      ·
        refine ⟨301963071405117285029963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 201308714270078190019975 301963071405117285029963)
        ·
          refine ⟨452944607107675927544945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 301963071405117285029963 452944607107675927544945)
          ·
            refine ⟨339708455330756945658709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 452944607107675927544945 339708455330756945658709)
            ·
              refine ⟨1990479230453653978469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 339708455330756945658709 1990479230453653978469)
              ·
                rfl

theorem cell22_156996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 2, 9].length) (baseStart_156996 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_156996 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_156996 prefixEnd_156996 := by exact prefixLift 156996
  have htrace : WordTrace (prefixWord ++ tailWord_156996) baseStart_156996 baseEnd_156996 := by
    simpa [prefixWord, tailWord_156996, baseEnd_156996] using wordTrace_append hprefix tailTrace_156996
  have hstable : (prefixWord ++ tailWord_156996).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_156996).length < 2 ^ (prefixWord ++ tailWord_156996).sum := by decide
  have hdescent : baseEnd_156996 < baseStart_156996 := by decide
  rcases family_descends (prefixWord ++ tailWord_156996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_157011 : List Nat := [1, 1, 1, 2, 1, 1, 8, 1, 3, 3]
def baseStart_157011 : Nat := 118140960795 + 157011 * 2 ^ 59
def prefixEnd_157011 : Nat := 4983230072969 + 3 ^ 40 * 157011 * 2
def baseEnd_157011 : Nat := 53748074028793618293617

theorem tailTrace_157011 : CollatzResearch.WordTrace tailWord_157011 prefixEnd_157011 53748074028793618293617 := by
  unfold tailWord_157011
  simp only [CollatzResearch.WordTrace]
  refine ⟨5726661634183437189030887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3817774422788958126020591 5726661634183437189030887)
  ·
    refine ⟨8589992451275155783546331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5726661634183437189030887 8589992451275155783546331)
    ·
      refine ⟨12884988676912733675319497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8589992451275155783546331 12884988676912733675319497)
      ·
        refine ⟨9663741507684550256489623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12884988676912733675319497 9663741507684550256489623)
        ·
          refine ⟨14495612261526825384734435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9663741507684550256489623 14495612261526825384734435)
          ·
            refine ⟨21743418392290238077101653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14495612261526825384734435 21743418392290238077101653)
            ·
              refine ⟨254805684284651227466035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 21743418392290238077101653 254805684284651227466035)
              ·
                refine ⟨382208526426976841199053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 254805684284651227466035 382208526426976841199053)
                ·
                  refine ⟨143328197410116315449645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 382208526426976841199053 143328197410116315449645)
                  ·
                    refine ⟨53748074028793618293617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 143328197410116315449645 53748074028793618293617)
                    ·
                      rfl

theorem cell22_157011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 8, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 8, 1, 3, 3].length) (baseStart_157011 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_157011 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_157011 prefixEnd_157011 := by exact prefixLift 157011
  have htrace : WordTrace (prefixWord ++ tailWord_157011) baseStart_157011 baseEnd_157011 := by
    simpa [prefixWord, tailWord_157011, baseEnd_157011] using wordTrace_append hprefix tailTrace_157011
  have hstable : (prefixWord ++ tailWord_157011).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_157011).length < 2 ^ (prefixWord ++ tailWord_157011).sum := by decide
  have hdescent : baseEnd_157011 < baseStart_157011 := by decide
  rcases family_descends (prefixWord ++ tailWord_157011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_157058 : List Nat := [3, 4, 2, 1, 1, 1, 2, 1, 7]
def baseStart_157058 : Nat := 118140960795 + 157058 * 2 ^ 59
def prefixEnd_157058 : Nat := 4983230072969 + 3 ^ 40 * 157058 * 2
def baseEnd_157058 : Nat := 17921387696433720789491

theorem tailTrace_157058 : CollatzResearch.WordTrace tailWord_157058 prefixEnd_157058 17921387696433720789491 := by
  unfold tailWord_157058
  simp only [CollatzResearch.WordTrace]
  refine ⟨1432093966253291053997957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3818917243342109477327885 1432093966253291053997957)
  ·
    refine ⟨268517618672492072624617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1432093966253291053997957 268517618672492072624617)
    ·
      refine ⟨201388214004369054468463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 268517618672492072624617 201388214004369054468463)
      ·
        refine ⟨302082321006553581702695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 201388214004369054468463 302082321006553581702695)
        ·
          refine ⟨453123481509830372554043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 302082321006553581702695 453123481509830372554043)
          ·
            refine ⟨679685222264745558831065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 453123481509830372554043 679685222264745558831065)
            ·
              refine ⟨509763916698559169123299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 679685222264745558831065 509763916698559169123299)
              ·
                refine ⟨764645875047838753684949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 509763916698559169123299 764645875047838753684949)
                ·
                  refine ⟨17921387696433720789491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 764645875047838753684949 17921387696433720789491)
                  ·
                    rfl

theorem cell22_157058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 2, 1, 7].length) (baseStart_157058 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_157058 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_157058 prefixEnd_157058 := by exact prefixLift 157058
  have htrace : WordTrace (prefixWord ++ tailWord_157058) baseStart_157058 baseEnd_157058 := by
    simpa [prefixWord, tailWord_157058, baseEnd_157058] using wordTrace_append hprefix tailTrace_157058
  have hstable : (prefixWord ++ tailWord_157058).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_157058).length < 2 ^ (prefixWord ++ tailWord_157058).sum := by decide
  have hdescent : baseEnd_157058 < baseStart_157058 := by decide
  rcases family_descends (prefixWord ++ tailWord_157058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_157129 : List Nat := [1, 2, 1, 1, 2, 1, 3, 2, 2, 7]
def baseStart_157129 : Nat := 118140960795 + 157129 * 2 ^ 59
def prefixEnd_157129 : Nat := 4983230072969 + 3 ^ 40 * 157129 * 2
def baseEnd_157129 : Nat := 53788467840280643843255

theorem tailTrace_157129 : CollatzResearch.WordTrace tailWord_157129 prefixEnd_157129 53788467840280643843255 := by
  unfold tailWord_157129
  simp only [CollatzResearch.WordTrace]
  refine ⟨5730965447755943341826441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3820643631837295561217627 5730965447755943341826441)
  ·
    refine ⟨4298224085816957506369831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5730965447755943341826441 4298224085816957506369831)
    ·
      refine ⟨6447336128725436259554747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4298224085816957506369831 6447336128725436259554747)
      ·
        refine ⟨9671004193088154389332121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6447336128725436259554747 9671004193088154389332121)
        ·
          refine ⟨7253253144816115791999091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9671004193088154389332121 7253253144816115791999091)
          ·
            refine ⟨10879879717224173687998637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7253253144816115791999091 10879879717224173687998637)
            ·
              refine ⟨4079954893959065132999489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10879879717224173687998637 4079954893959065132999489)
              ·
                refine ⟨3059966170469298849749617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4079954893959065132999489 3059966170469298849749617)
                ·
                  refine ⟨2294974627851974137312213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3059966170469298849749617 2294974627851974137312213)
                  ·
                    refine ⟨53788467840280643843255, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 2294974627851974137312213 53788467840280643843255)
                    ·
                      rfl

theorem cell22_157129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 2, 2, 7].length) (baseStart_157129 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_157129 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_157129 prefixEnd_157129 := by exact prefixLift 157129
  have htrace : WordTrace (prefixWord ++ tailWord_157129) baseStart_157129 baseEnd_157129 := by
    simpa [prefixWord, tailWord_157129, baseEnd_157129] using wordTrace_append hprefix tailTrace_157129
  have hstable : (prefixWord ++ tailWord_157129).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_157129).length < 2 ^ (prefixWord ++ tailWord_157129).sum := by decide
  have hdescent : baseEnd_157129 < baseStart_157129 := by decide
  rcases family_descends (prefixWord ++ tailWord_157129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_157176 : List Nat := [2, 1, 2, 1, 1, 6, 1, 1, 7]
def baseStart_157176 : Nat := 118140960795 + 157176 * 2 ^ 59
def prefixEnd_157176 : Nat := 4983230072969 + 3 ^ 40 * 157176 * 2
def baseEnd_157176 : Nat := 17934852300262729306037

theorem tailTrace_157176 : CollatzResearch.WordTrace tailWord_157176 prefixEnd_157176 17934852300262729306037 := by
  unfold tailWord_157176
  simp only [CollatzResearch.WordTrace]
  refine ⟨2866339839292835184393691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3821786452390446912524921 2866339839292835184393691)
  ·
    refine ⟨4299509758939252776590537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2866339839292835184393691 4299509758939252776590537)
    ·
      refine ⟨3224632319204439582442903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4299509758939252776590537 3224632319204439582442903)
      ·
        refine ⟨4836948478806659373664355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3224632319204439582442903 4836948478806659373664355)
        ·
          refine ⟨7255422718209989060496533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4836948478806659373664355 7255422718209989060496533)
          ·
            refine ⟨340097939916093237210775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 7255422718209989060496533 340097939916093237210775)
            ·
              refine ⟨510146909874139855816163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 340097939916093237210775 510146909874139855816163)
              ·
                refine ⟨765220364811209783724245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 510146909874139855816163 765220364811209783724245)
                ·
                  refine ⟨17934852300262729306037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 765220364811209783724245 17934852300262729306037)
                  ·
                    rfl

theorem cell22_157176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 6, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 6, 1, 1, 7].length) (baseStart_157176 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_157176 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_157176 prefixEnd_157176 := by exact prefixLift 157176
  have htrace : WordTrace (prefixWord ++ tailWord_157176) baseStart_157176 baseEnd_157176 := by
    simpa [prefixWord, tailWord_157176, baseEnd_157176] using wordTrace_append hprefix tailTrace_157176
  have hstable : (prefixWord ++ tailWord_157176).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_157176).length < 2 ^ (prefixWord ++ tailWord_157176).sum := by decide
  have hdescent : baseEnd_157176 < baseStart_157176 := by decide
  rcases family_descends (prefixWord ++ tailWord_157176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_157180 : List Nat := [2, 2, 2, 1, 2, 1, 4, 4, 1, 3]
def baseStart_157180 : Nat := 118140960795 + 157180 * 2 ^ 59
def prefixEnd_157180 : Nat := 4983230072969 + 3 ^ 40 * 157180 * 2
def baseEnd_157180 : Nat := 53805926182533510818099

theorem tailTrace_157180 : CollatzResearch.WordTrace tailWord_157180 prefixEnd_157180 53805926182533510818099 := by
  unfold tailWord_157180
  simp only [CollatzResearch.WordTrace]
  refine ⟨2866412785285589525966497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3821883713714119367955329 2866412785285589525966497)
  ·
    refine ⟨2149809588964192144474873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2866412785285589525966497 2149809588964192144474873)
    ·
      refine ⟨1612357191723144108356155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2149809588964192144474873 1612357191723144108356155)
      ·
        refine ⟨2418535787584716162534233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1612357191723144108356155 2418535787584716162534233)
        ·
          refine ⟨1813901840688537121900675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2418535787584716162534233 1813901840688537121900675)
          ·
            refine ⟨2720852761032805682851013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1813901840688537121900675 2720852761032805682851013)
            ·
              refine ⟨510159892693651065534565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2720852761032805682851013 510159892693651065534565)
              ·
                refine ⟨95654979880059574787731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 510159892693651065534565 95654979880059574787731)
                ·
                  refine ⟨143482469820089362181597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 95654979880059574787731 143482469820089362181597)
                  ·
                    refine ⟨53805926182533510818099, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 143482469820089362181597 53805926182533510818099)
                    ·
                      rfl

theorem cell22_157180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 4, 4, 1, 3].length) (baseStart_157180 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_157180 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_157180 prefixEnd_157180 := by exact prefixLift 157180
  have htrace : WordTrace (prefixWord ++ tailWord_157180) baseStart_157180 baseEnd_157180 := by
    simpa [prefixWord, tailWord_157180, baseEnd_157180] using wordTrace_append hprefix tailTrace_157180
  have hstable : (prefixWord ++ tailWord_157180).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_157180).length < 2 ^ (prefixWord ++ tailWord_157180).sum := by decide
  have hdescent : baseEnd_157180 < baseStart_157180 := by decide
  rcases family_descends (prefixWord ++ tailWord_157180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_157193 : List Nat := [1, 2, 1, 1, 3, 1, 7, 1, 5]
def baseStart_157193 : Nat := 118140960795 + 157193 * 2 ^ 59
def prefixEnd_157193 : Nat := 4983230072969 + 3 ^ 40 * 157193 * 2
def baseEnd_157193 : Nat := 17936792116068603414353

theorem tailTrace_157193 : CollatzResearch.WordTrace tailWord_157193 prefixEnd_157193 17936792116068603414353 := by
  unfold tailWord_157193
  simp only [CollatzResearch.WordTrace]
  refine ⟨5733299719524082272156233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3822199813016054848104155 5733299719524082272156233)
  ·
    refine ⟨4299974789643061704117175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5733299719524082272156233 4299974789643061704117175)
    ·
      refine ⟨6449962184464592556175763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4299974789643061704117175 6449962184464592556175763)
      ·
        refine ⟨9674943276696888834263645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6449962184464592556175763 9674943276696888834263645)
        ·
          refine ⟨3628103728761333312848867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9674943276696888834263645 3628103728761333312848867)
          ·
            refine ⟨5442155593141999969273301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3628103728761333312848867 5442155593141999969273301)
            ·
              refine ⟨127550521714265624279843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 5442155593141999969273301 127550521714265624279843)
              ·
                refine ⟨191325782571398436419765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 127550521714265624279843 191325782571398436419765)
                ·
                  refine ⟨17936792116068603414353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 191325782571398436419765 17936792116068603414353)
                  ·
                    rfl

theorem cell22_157193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 7, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 7, 1, 5].length) (baseStart_157193 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_157193 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_157193 prefixEnd_157193 := by exact prefixLift 157193
  have htrace : WordTrace (prefixWord ++ tailWord_157193) baseStart_157193 baseEnd_157193 := by
    simpa [prefixWord, tailWord_157193, baseEnd_157193] using wordTrace_append hprefix tailTrace_157193
  have hstable : (prefixWord ++ tailWord_157193).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_157193).length < 2 ^ (prefixWord ++ tailWord_157193).sum := by decide
  have hdescent : baseEnd_157193 < baseStart_157193 := by decide
  rcases family_descends (prefixWord ++ tailWord_157193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_157345 : List Nat := [1, 2, 3, 3, 2, 1, 3, 2, 5]
def baseStart_157345 : Nat := 118140960795 + 157345 * 2 ^ 59
def prefixEnd_157345 : Nat := 4983230072969 + 3 ^ 40 * 157345 * 2
def baseEnd_157345 : Nat := 17954136351509360147531

theorem tailTrace_157345 : CollatzResearch.WordTrace tailWord_157345 prefixEnd_157345 17954136351509360147531 := by
  unfold tailWord_157345
  simp only [CollatzResearch.WordTrace]
  refine ⟨5738843614973412231689489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3825895743315608154459659 5738843614973412231689489)
  ·
    refine ⟨4304132711230059173767117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5738843614973412231689489 4304132711230059173767117)
    ·
      refine ⟨1614049766711272190162669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4304132711230059173767117 1614049766711272190162669)
      ·
        refine ⟨605268662516727071311001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1614049766711272190162669 605268662516727071311001)
        ·
          refine ⟨453951496887545303483251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 605268662516727071311001 453951496887545303483251)
          ·
            refine ⟨680927245331317955224877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 453951496887545303483251 680927245331317955224877)
            ·
              refine ⟨255347716999244233209329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 680927245331317955224877 255347716999244233209329)
              ·
                refine ⟨191510787749433174906997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 255347716999244233209329 191510787749433174906997)
                ·
                  refine ⟨17954136351509360147531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 191510787749433174906997 17954136351509360147531)
                  ·
                    rfl

theorem cell22_157345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 3, 2, 5].length) (baseStart_157345 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_157345 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_157345 prefixEnd_157345 := by exact prefixLift 157345
  have htrace : WordTrace (prefixWord ++ tailWord_157345) baseStart_157345 baseEnd_157345 := by
    simpa [prefixWord, tailWord_157345, baseEnd_157345] using wordTrace_append hprefix tailTrace_157345
  have hstable : (prefixWord ++ tailWord_157345).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_157345).length < 2 ^ (prefixWord ++ tailWord_157345).sum := by decide
  have hdescent : baseEnd_157345 < baseStart_157345 := by decide
  rcases family_descends (prefixWord ++ tailWord_157345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_157373 : List Nat := [1, 4, 1, 2, 1, 2, 1, 4, 6]
def baseStart_157373 : Nat := 118140960795 + 157373 * 2 ^ 59
def prefixEnd_157373 : Nat := 4983230072969 + 3 ^ 40 * 157373 * 2
def baseEnd_157373 : Nat := 17957331342248446914169

theorem tailTrace_157373 : CollatzResearch.WordTrace tailWord_157373 prefixEnd_157373 17957331342248446914169 := by
  unfold tailWord_157373
  simp only [CollatzResearch.WordTrace]
  refine ⟨5739864858871973013708773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3826576572581315342472515 5739864858871973013708773)
  ·
    refine ⟨1076224661038494940070395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5739864858871973013708773 1076224661038494940070395)
    ·
      refine ⟨1614336991557742410105593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1076224661038494940070395 1614336991557742410105593)
      ·
        refine ⟨1210752743668306807579195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1614336991557742410105593 1210752743668306807579195)
        ·
          refine ⟨1816129115502460211368793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1210752743668306807579195 1816129115502460211368793)
          ·
            refine ⟨1362096836626845158526595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1816129115502460211368793 1362096836626845158526595)
            ·
              refine ⟨2043145254940267737789893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1362096836626845158526595 2043145254940267737789893)
              ·
                refine ⟨383089735301300200835605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2043145254940267737789893 383089735301300200835605)
                ·
                  refine ⟨17957331342248446914169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 383089735301300200835605 17957331342248446914169)
                  ·
                    rfl

theorem cell22_157373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 1, 4, 6].length) (baseStart_157373 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_157373 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_157373 prefixEnd_157373 := by exact prefixLift 157373
  have htrace : WordTrace (prefixWord ++ tailWord_157373) baseStart_157373 baseEnd_157373 := by
    simpa [prefixWord, tailWord_157373, baseEnd_157373] using wordTrace_append hprefix tailTrace_157373
  have hstable : (prefixWord ++ tailWord_157373).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_157373).length < 2 ^ (prefixWord ++ tailWord_157373).sum := by decide
  have hdescent : baseEnd_157373 < baseStart_157373 := by decide
  rcases family_descends (prefixWord ++ tailWord_157373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_157375 : List Nat := [1, 1, 2, 2, 2, 3, 4, 2, 1, 4]
def baseStart_157375 : Nat := 118140960795 + 157375 * 2 ^ 59
def prefixEnd_157375 : Nat := 4983230072969 + 3 ^ 40 * 157375 * 2
def baseEnd_157375 : Nat := 53872678667618002192501

theorem tailTrace_157375 : CollatzResearch.WordTrace tailWord_157375 prefixEnd_157375 53872678667618002192501 := by
  unfold tailWord_157375
  simp only [CollatzResearch.WordTrace]
  refine ⟨5739937804864727355281579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3826625203243151570187719 5739937804864727355281579)
  ·
    refine ⟨8609906707297091032922369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5739937804864727355281579 8609906707297091032922369)
    ·
      refine ⟨6457430030472818274691777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8609906707297091032922369 6457430030472818274691777)
      ·
        refine ⟨4843072522854613706018833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6457430030472818274691777 4843072522854613706018833)
        ·
          refine ⟨3632304392140960279514125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4843072522854613706018833 3632304392140960279514125)
          ·
            refine ⟨1362114147052860104817797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3632304392140960279514125 1362114147052860104817797)
            ·
              refine ⟨255396402572411269653337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1362114147052860104817797 255396402572411269653337)
              ·
                refine ⟨191547301929308452240003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 255396402572411269653337 191547301929308452240003)
                ·
                  refine ⟨287320952893962678360005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 191547301929308452240003 287320952893962678360005)
                  ·
                    refine ⟨53872678667618002192501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 287320952893962678360005 53872678667618002192501)
                    ·
                      rfl

theorem cell22_157375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 4, 2, 1, 4].length) (baseStart_157375 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_157375 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_157375 prefixEnd_157375 := by exact prefixLift 157375
  have htrace : WordTrace (prefixWord ++ tailWord_157375) baseStart_157375 baseEnd_157375 := by
    simpa [prefixWord, tailWord_157375, baseEnd_157375] using wordTrace_append hprefix tailTrace_157375
  have hstable : (prefixWord ++ tailWord_157375).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_157375).length < 2 ^ (prefixWord ++ tailWord_157375).sum := by decide
  have hdescent : baseEnd_157375 < baseStart_157375 := by decide
  rcases family_descends (prefixWord ++ tailWord_157375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_157407 : List Nat := [1, 1, 2, 3, 2, 2, 5, 2, 4]
def baseStart_157407 : Nat := 118140960795 + 157407 * 2 ^ 59
def prefixEnd_157407 : Nat := 4983230072969 + 3 ^ 40 * 157407 * 2
def baseEnd_157407 : Nat := 17961210973860195130801

theorem tailTrace_157407 : CollatzResearch.WordTrace tailWord_157407 prefixEnd_157407 17961210973860195130801 := by
  unfold tailWord_157407
  simp only [CollatzResearch.WordTrace]
  refine ⟨5741104940748796820446475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3827403293832531213630983 5741104940748796820446475)
  ·
    refine ⟨8611657411123195230669713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5741104940748796820446475 8611657411123195230669713)
    ·
      refine ⟨6458743058342396423002285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8611657411123195230669713 6458743058342396423002285)
      ·
        refine ⟨2422028646878398658625857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6458743058342396423002285 2422028646878398658625857)
        ·
          refine ⟨1816521485158798993969393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2422028646878398658625857 1816521485158798993969393)
          ·
            refine ⟨1362391113869099245477045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1816521485158798993969393 1362391113869099245477045)
            ·
              refine ⟨127724166925228054263473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1362391113869099245477045 127724166925228054263473)
              ·
                refine ⟨95793125193921040697605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 127724166925228054263473 95793125193921040697605)
                ·
                  refine ⟨17961210973860195130801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 95793125193921040697605 17961210973860195130801)
                  ·
                    rfl

theorem cell22_157407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 5, 2, 4].length) (baseStart_157407 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_157407 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_157407 prefixEnd_157407 := by exact prefixLift 157407
  have htrace : WordTrace (prefixWord ++ tailWord_157407) baseStart_157407 baseEnd_157407 := by
    simpa [prefixWord, tailWord_157407, baseEnd_157407] using wordTrace_append hprefix tailTrace_157407
  have hstable : (prefixWord ++ tailWord_157407).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_157407).length < 2 ^ (prefixWord ++ tailWord_157407).sum := by decide
  have hdescent : baseEnd_157407 < baseStart_157407 := by decide
  rcases family_descends (prefixWord ++ tailWord_157407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_157418 : List Nat := [3, 1, 3, 1, 1, 1, 3, 9]
def baseStart_157418 : Nat := 118140960795 + 157418 * 2 ^ 59
def prefixEnd_157418 : Nat := 4983230072969 + 3 ^ 40 * 157418 * 2
def baseEnd_157418 : Nat := 5987488716264469263041

theorem tailTrace_157418 : CollatzResearch.WordTrace tailWord_157418 prefixEnd_157418 5987488716264469263041 := by
  unfold tailWord_157418
  simp only [CollatzResearch.WordTrace]
  refine ⟨1435376535927236424774227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3827670762472630466064605 1435376535927236424774227)
  ·
    refine ⟨2153064803890854637161341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1435376535927236424774227 2153064803890854637161341)
    ·
      refine ⟨807399301459070488935503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2153064803890854637161341 807399301459070488935503)
      ·
        refine ⟨1211098952188605733403255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 807399301459070488935503 1211098952188605733403255)
        ·
          refine ⟨1816648428282908600104883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1211098952188605733403255 1816648428282908600104883)
          ·
            refine ⟨2724972642424362900157325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1816648428282908600104883 2724972642424362900157325)
            ·
              refine ⟨1021864740909136087558997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2724972642424362900157325 1021864740909136087558997)
              ·
                refine ⟨5987488716264469263041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 1021864740909136087558997 5987488716264469263041)
                ·
                  rfl

theorem cell22_157418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 3, 9].length) (baseStart_157418 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_157418 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_157418 prefixEnd_157418 := by exact prefixLift 157418
  have htrace : WordTrace (prefixWord ++ tailWord_157418) baseStart_157418 baseEnd_157418 := by
    simpa [prefixWord, tailWord_157418, baseEnd_157418] using wordTrace_append hprefix tailTrace_157418
  have hstable : (prefixWord ++ tailWord_157418).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_157418).length < 2 ^ (prefixWord ++ tailWord_157418).sum := by decide
  have hdescent : baseEnd_157418 < baseStart_157418 := by decide
  rcases family_descends (prefixWord ++ tailWord_157418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_157422 : List Nat := [4, 1, 2, 1, 1, 2, 3, 3, 2, 3]
def baseStart_157422 : Nat := 118140960795 + 157422 * 2 ^ 59
def prefixEnd_157422 : Nat := 4983230072969 + 3 ^ 40 * 157422 * 2
def baseEnd_157422 : Nat := 53888767728125546267357

theorem tailTrace_157422 : CollatzResearch.WordTrace tailWord_157422 prefixEnd_157422 53888767728125546267357 := by
  unfold tailWord_157422
  simp only [CollatzResearch.WordTrace]
  refine ⟨717706504461806797780315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3827768023796302921495013 717706504461806797780315)
  ·
    refine ⟨1076559756692710196670473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 717706504461806797780315 1076559756692710196670473)
    ·
      refine ⟨807419817519532647502855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1076559756692710196670473 807419817519532647502855)
      ·
        refine ⟨1211129726279298971254283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 807419817519532647502855 1211129726279298971254283)
        ·
          refine ⟨1816694589418948456881425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1211129726279298971254283 1816694589418948456881425)
          ·
            refine ⟨1362520942064211342661069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1816694589418948456881425 1362520942064211342661069)
            ·
              refine ⟨510945353274079253497901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1362520942064211342661069 510945353274079253497901)
              ·
                refine ⟨191604507477779720061713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 510945353274079253497901 191604507477779720061713)
                ·
                  refine ⟨143703380608334790046285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 191604507477779720061713 143703380608334790046285)
                  ·
                    refine ⟨53888767728125546267357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 143703380608334790046285 53888767728125546267357)
                    ·
                      rfl

theorem cell22_157422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 3, 3, 2, 3].length) (baseStart_157422 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_157422 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_157422 prefixEnd_157422 := by exact prefixLift 157422
  have htrace : WordTrace (prefixWord ++ tailWord_157422) baseStart_157422 baseEnd_157422 := by
    simpa [prefixWord, tailWord_157422, baseEnd_157422] using wordTrace_append hprefix tailTrace_157422
  have hstable : (prefixWord ++ tailWord_157422).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_157422).length < 2 ^ (prefixWord ++ tailWord_157422).sum := by decide
  have hdescent : baseEnd_157422 < baseStart_157422 := by decide
  rcases family_descends (prefixWord ++ tailWord_157422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_157467 : List Nat := [1, 1, 1, 1, 1, 1, 4, 8, 1, 3]
def baseStart_157467 : Nat := 118140960795 + 157467 * 2 ^ 59
def prefixEnd_157467 : Nat := 4983230072969 + 3 ^ 40 * 157467 * 2
def baseEnd_157467 : Nat := 53904172147760428892219

theorem tailTrace_157467 : CollatzResearch.WordTrace tailWord_157467 prefixEnd_157467 53904172147760428892219 := by
  unfold tailWord_157467
  simp only [CollatzResearch.WordTrace]
  refine ⟨5743293320531427067630655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3828862213687618045087103 5743293320531427067630655)
  ·
    refine ⟨8614939980797140601445983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5743293320531427067630655 8614939980797140601445983)
    ·
      refine ⟨12922409971195710902168975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8614939980797140601445983 12922409971195710902168975)
      ·
        refine ⟨19383614956793566353253463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12922409971195710902168975 19383614956793566353253463)
        ·
          refine ⟨29075422435190349529880195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19383614956793566353253463 29075422435190349529880195)
          ·
            refine ⟨43613133652785524294820293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29075422435190349529880195 43613133652785524294820293)
            ·
              refine ⟨8177462559897285805278805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 43613133652785524294820293 8177462559897285805278805)
              ·
                refine ⟨95829639373796318030611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8177462559897285805278805 95829639373796318030611)
                ·
                  refine ⟨143744459060694477045917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 95829639373796318030611 143744459060694477045917)
                  ·
                    refine ⟨53904172147760428892219, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 143744459060694477045917 53904172147760428892219)
                    ·
                      rfl

theorem cell22_157467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 8, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 8, 1, 3].length) (baseStart_157467 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_157467 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_157467 prefixEnd_157467 := by exact prefixLift 157467
  have htrace : WordTrace (prefixWord ++ tailWord_157467) baseStart_157467 baseEnd_157467 := by
    simpa [prefixWord, tailWord_157467, baseEnd_157467] using wordTrace_append hprefix tailTrace_157467
  have hstable : (prefixWord ++ tailWord_157467).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_157467).length < 2 ^ (prefixWord ++ tailWord_157467).sum := by decide
  have hdescent : baseEnd_157467 < baseStart_157467 := by decide
  rcases family_descends (prefixWord ++ tailWord_157467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_157501 : List Nat := [1, 4, 1, 4, 1, 2, 2, 3, 1, 3]
def baseStart_157501 : Nat := 118140960795 + 157501 * 2 ^ 59
def prefixEnd_157501 : Nat := 4983230072969 + 3 ^ 40 * 157501 * 2
def baseEnd_157501 : Nat := 53915811042595673542115

theorem tailTrace_157501 : CollatzResearch.WordTrace tailWord_157501 prefixEnd_157501 53915811042595673542115 := by
  unfold tailWord_157501
  simp only [CollatzResearch.WordTrace]
  refine ⟨5744533402408250874368357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3829688934938833916245571 5744533402408250874368357)
  ·
    refine ⟨1077100012951547038944067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5744533402408250874368357 1077100012951547038944067)
    ·
      refine ⟨1615650019427320558416101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1077100012951547038944067 1615650019427320558416101)
      ·
        refine ⟨302934378642622604703019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1615650019427320558416101 302934378642622604703019)
        ·
          refine ⟨454401567963933907054529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 302934378642622604703019 454401567963933907054529)
          ·
            refine ⟨340801175972950430290897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 454401567963933907054529 340801175972950430290897)
            ·
              refine ⟨255600881979712822718173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 340801175972950430290897 255600881979712822718173)
              ·
                refine ⟨95850330742392308519315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 255600881979712822718173 95850330742392308519315)
                ·
                  refine ⟨143775496113588462778973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 95850330742392308519315 143775496113588462778973)
                  ·
                    refine ⟨53915811042595673542115, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 143775496113588462778973 53915811042595673542115)
                    ·
                      rfl

theorem cell22_157501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 2, 2, 3, 1, 3].length) (baseStart_157501 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_157501 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_157501 prefixEnd_157501 := by exact prefixLift 157501
  have htrace : WordTrace (prefixWord ++ tailWord_157501) baseStart_157501 baseEnd_157501 := by
    simpa [prefixWord, tailWord_157501, baseEnd_157501] using wordTrace_append hprefix tailTrace_157501
  have hstable : (prefixWord ++ tailWord_157501).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_157501).length < 2 ^ (prefixWord ++ tailWord_157501).sum := by decide
  have hdescent : baseEnd_157501 < baseStart_157501 := by decide
  rcases family_descends (prefixWord ++ tailWord_157501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_157523 : List Nat := [1, 1, 1, 2, 1, 1, 3, 1, 2, 9]
def baseStart_157523 : Nat := 118140960795 + 157523 * 2 ^ 59
def prefixEnd_157523 : Nat := 4983230072969 + 3 ^ 40 * 157523 * 2
def baseEnd_157523 : Nat := 53923342092194949492047

theorem tailTrace_157523 : CollatzResearch.WordTrace tailWord_157523 prefixEnd_157523 53923342092194949492047 := by
  unfold tailWord_157523
  simp only [CollatzResearch.WordTrace]
  refine ⟨5745335808328548631669223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3830223872219032421112815 5745335808328548631669223)
  ·
    refine ⟨8618003712492822947503835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5745335808328548631669223 8618003712492822947503835)
    ·
      refine ⟨12927005568739234421255753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8618003712492822947503835 12927005568739234421255753)
      ·
        refine ⟨9695254176554425815941815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12927005568739234421255753 9695254176554425815941815)
        ·
          refine ⟨14542881264831638723912723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9695254176554425815941815 14542881264831638723912723)
          ·
            refine ⟨21814321897247458085869085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14542881264831638723912723 21814321897247458085869085)
            ·
              refine ⟨8180370711467796782200907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21814321897247458085869085 8180370711467796782200907)
              ·
                refine ⟨12270556067201695173301361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8180370711467796782200907 12270556067201695173301361)
                ·
                  refine ⟨9202917050401271379976021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12270556067201695173301361 9202917050401271379976021)
                  ·
                    refine ⟨53923342092194949492047, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 9202917050401271379976021 53923342092194949492047)
                    ·
                      rfl

theorem cell22_157523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 1, 2, 9].length) (baseStart_157523 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_157523 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_157523 prefixEnd_157523 := by exact prefixLift 157523
  have htrace : WordTrace (prefixWord ++ tailWord_157523) baseStart_157523 baseEnd_157523 := by
    simpa [prefixWord, tailWord_157523, baseEnd_157523] using wordTrace_append hprefix tailTrace_157523
  have hstable : (prefixWord ++ tailWord_157523).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_157523).length < 2 ^ (prefixWord ++ tailWord_157523).sum := by decide
  have hdescent : baseEnd_157523 < baseStart_157523 := by decide
  rcases family_descends (prefixWord ++ tailWord_157523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_157525 : List Nat := [1, 3, 2, 2, 2, 2, 1, 3, 6]
def baseStart_157525 : Nat := 118140960795 + 157525 * 2 ^ 59
def prefixEnd_157525 : Nat := 4983230072969 + 3 ^ 40 * 157525 * 2
def baseEnd_157525 : Nat := 17974675577689203647347

theorem tailTrace_157525 : CollatzResearch.WordTrace tailWord_157525 prefixEnd_157525 17974675577689203647347 := by
  unfold tailWord_157525
  simp only [CollatzResearch.WordTrace]
  refine ⟨5745408754321302973242029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3830272502880868648828019 5745408754321302973242029)
  ·
    refine ⟨2154528282870488614965761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5745408754321302973242029 2154528282870488614965761)
    ·
      refine ⟨1615896212152866461224321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2154528282870488614965761 1615896212152866461224321)
      ·
        refine ⟨1211922159114649845918241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1615896212152866461224321 1211922159114649845918241)
        ·
          refine ⟨908941619335987384438681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1211922159114649845918241 908941619335987384438681)
          ·
            refine ⟨681706214501990538329011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 908941619335987384438681 681706214501990538329011)
            ·
              refine ⟨1022559321752985807493517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 681706214501990538329011 1022559321752985807493517)
              ·
                refine ⟨383459745657369677810069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1022559321752985807493517 383459745657369677810069)
                ·
                  refine ⟨17974675577689203647347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 383459745657369677810069 17974675577689203647347)
                  ·
                    rfl

theorem cell22_157525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 1, 3, 6].length) (baseStart_157525 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_157525 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_157525 prefixEnd_157525 := by exact prefixLift 157525
  have htrace : WordTrace (prefixWord ++ tailWord_157525) baseStart_157525 baseEnd_157525 := by
    simpa [prefixWord, tailWord_157525, baseEnd_157525] using wordTrace_append hprefix tailTrace_157525
  have hstable : (prefixWord ++ tailWord_157525).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_157525).length < 2 ^ (prefixWord ++ tailWord_157525).sum := by decide
  have hdescent : baseEnd_157525 < baseStart_157525 := by decide
  rcases family_descends (prefixWord ++ tailWord_157525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_157555 : List Nat := [1, 1, 1, 2, 2, 1, 3, 5, 2, 4]
def baseStart_157555 : Nat := 118140960795 + 157555 * 2 ^ 59
def prefixEnd_157555 : Nat := 4983230072969 + 3 ^ 40 * 157555 * 2
def baseEnd_157555 : Nat := 53934296346157532691949

theorem tailTrace_157555 : CollatzResearch.WordTrace tailWord_157555 prefixEnd_157555 53934296346157532691949 := by
  unfold tailWord_157555
  simp only [CollatzResearch.WordTrace]
  refine ⟨5746502944212618096834119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3831001962808412064556079 5746502944212618096834119)
  ·
    refine ⟨8619754416318927145251179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5746502944212618096834119 8619754416318927145251179)
    ·
      refine ⟨12929631624478390717876769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8619754416318927145251179 12929631624478390717876769)
      ·
        refine ⟨9697223718358793038407577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12929631624478390717876769 9697223718358793038407577)
        ·
          refine ⟨7272917788769094778805683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9697223718358793038407577 7272917788769094778805683)
          ·
            refine ⟨10909376683153642168208525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7272917788769094778805683 10909376683153642168208525)
            ·
              refine ⟨4091016256182615813078197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10909376683153642168208525 4091016256182615813078197)
              ·
                refine ⟨383532774017120232476081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4091016256182615813078197 383532774017120232476081)
                ·
                  refine ⟨287649580512840174357061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 383532774017120232476081 287649580512840174357061)
                  ·
                    refine ⟨53934296346157532691949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 287649580512840174357061 53934296346157532691949)
                    ·
                      rfl

theorem cell22_157555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 5, 2, 4].length) (baseStart_157555 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_157555 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_157555 prefixEnd_157555 := by exact prefixLift 157555
  have htrace : WordTrace (prefixWord ++ tailWord_157555) baseStart_157555 baseEnd_157555 := by
    simpa [prefixWord, tailWord_157555, baseEnd_157555] using wordTrace_append hprefix tailTrace_157555
  have hstable : (prefixWord ++ tailWord_157555).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_157555).length < 2 ^ (prefixWord ++ tailWord_157555).sum := by decide
  have hdescent : baseEnd_157555 < baseStart_157555 := by decide
  rcases family_descends (prefixWord ++ tailWord_157555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_157557 : List Nat := [1, 3, 4, 1, 1, 1, 1, 1, 6, 3]
def baseStart_157557 : Nat := 118140960795 + 157557 * 2 ^ 59
def prefixEnd_157557 : Nat := 4983230072969 + 3 ^ 40 * 157557 * 2
def baseEnd_157557 : Nat := 53934980987030194141943

theorem tailTrace_157557 : CollatzResearch.WordTrace tailWord_157557 prefixEnd_157557 53934980987030194141943 := by
  unfold tailWord_157557
  simp only [CollatzResearch.WordTrace]
  refine ⟨5746575890205372438406925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3831050593470248292271283 5746575890205372438406925)
  ·
    refine ⟨2154965958827014664402597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5746575890205372438406925 2154965958827014664402597)
    ·
      refine ⟨404056117280065249575487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2154965958827014664402597 404056117280065249575487)
      ·
        refine ⟨606084175920097874363231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 404056117280065249575487 606084175920097874363231)
        ·
          refine ⟨909126263880146811544847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 606084175920097874363231 909126263880146811544847)
          ·
            refine ⟨1363689395820220217317271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 909126263880146811544847 1363689395820220217317271)
            ·
              refine ⟨2045534093730330325975907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1363689395820220217317271 2045534093730330325975907)
              ·
                refine ⟨3068301140595495488963861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2045534093730330325975907 3068301140595495488963861)
                ·
                  refine ⟨143826615965413851045181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3068301140595495488963861 143826615965413851045181)
                  ·
                    refine ⟨53934980987030194141943, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 143826615965413851045181 53934980987030194141943)
                    ·
                      rfl

theorem cell22_157557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 1, 1, 6, 3].length) (baseStart_157557 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_157557 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_157557 prefixEnd_157557 := by exact prefixLift 157557
  have htrace : WordTrace (prefixWord ++ tailWord_157557) baseStart_157557 baseEnd_157557 := by
    simpa [prefixWord, tailWord_157557, baseEnd_157557] using wordTrace_append hprefix tailTrace_157557
  have hstable : (prefixWord ++ tailWord_157557).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_157557).length < 2 ^ (prefixWord ++ tailWord_157557).sum := by decide
  have hdescent : baseEnd_157557 < baseStart_157557 := by decide
  rcases family_descends (prefixWord ++ tailWord_157557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_157576 : List Nat := [2, 1, 3, 3, 3, 1, 3, 2, 4]
def baseStart_157576 : Nat := 118140960795 + 157576 * 2 ^ 59
def prefixEnd_157576 : Nat := 4983230072969 + 3 ^ 40 * 157576 * 2
def baseEnd_157576 : Nat := 17980495025106825972295

theorem tailTrace_157576 : CollatzResearch.WordTrace tailWord_157576 prefixEnd_157576 17980495025106825972295 := by
  unfold tailWord_157576
  simp only [CollatzResearch.WordTrace]
  refine ⟨2873634438568269341674291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3831512584757692455565721 2873634438568269341674291)
  ·
    refine ⟨4310451657852404012511437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2873634438568269341674291 4310451657852404012511437)
    ·
      refine ⟨1616419371694651504691789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4310451657852404012511437 1616419371694651504691789)
      ·
        refine ⟨606157264385494314259421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1616419371694651504691789 606157264385494314259421)
        ·
          refine ⟨227308974144560367847283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 606157264385494314259421 227308974144560367847283)
          ·
            refine ⟨340963461216840551770925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 227308974144560367847283 340963461216840551770925)
            ·
              refine ⟨127861297956315206914097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 340963461216840551770925 127861297956315206914097)
              ·
                refine ⟨95895973467236405185573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 127861297956315206914097 95895973467236405185573)
                ·
                  refine ⟨17980495025106825972295, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 95895973467236405185573 17980495025106825972295)
                  ·
                    rfl

theorem cell22_157576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 1, 3, 2, 4].length) (baseStart_157576 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_157576 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_157576 prefixEnd_157576 := by exact prefixLift 157576
  have htrace : WordTrace (prefixWord ++ tailWord_157576) baseStart_157576 baseEnd_157576 := by
    simpa [prefixWord, tailWord_157576, baseEnd_157576] using wordTrace_append hprefix tailTrace_157576
  have hstable : (prefixWord ++ tailWord_157576).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_157576).length < 2 ^ (prefixWord ++ tailWord_157576).sum := by decide
  have hdescent : baseEnd_157576 < baseStart_157576 := by decide
  rcases family_descends (prefixWord ++ tailWord_157576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_157591 : List Nat := [1, 1, 3, 3, 1, 5, 2, 1, 2, 3]
def baseStart_157591 : Nat := 118140960795 + 157591 * 2 ^ 59
def prefixEnd_157591 : Nat := 4983230072969 + 3 ^ 40 * 157591 * 2
def baseEnd_157591 : Nat := 53946619881865438791839

theorem tailTrace_157591 : CollatzResearch.WordTrace tailWord_157591 prefixEnd_157591 53946619881865438791839 := by
  unfold tailWord_157591
  simp only [CollatzResearch.WordTrace]
  refine ⟨5747815972082196245144627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3831877314721464163429751 5747815972082196245144627)
  ·
    refine ⟨8621723958123294367716941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5747815972082196245144627 8621723958123294367716941)
    ·
      refine ⟨3233146484296235387893853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8621723958123294367716941 3233146484296235387893853)
      ·
        refine ⟨1212429931611088270460195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3233146484296235387893853 1212429931611088270460195)
        ·
          refine ⟨1818644897416632405690293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1212429931611088270460195 1818644897416632405690293)
          ·
            refine ⟨170497959132809288033465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1818644897416632405690293 170497959132809288033465)
            ·
              refine ⟨127873469349606966025099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 170497959132809288033465 127873469349606966025099)
              ·
                refine ⟨191810204024410449037649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 127873469349606966025099 191810204024410449037649)
                ·
                  refine ⟨143857653018307836778237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 191810204024410449037649 143857653018307836778237)
                  ·
                    refine ⟨53946619881865438791839, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 143857653018307836778237 53946619881865438791839)
                    ·
                      rfl

theorem cell22_157591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 5, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 5, 2, 1, 2, 3].length) (baseStart_157591 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_157591 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_157591 prefixEnd_157591 := by exact prefixLift 157591
  have htrace : WordTrace (prefixWord ++ tailWord_157591) baseStart_157591 baseEnd_157591 := by
    simpa [prefixWord, tailWord_157591, baseEnd_157591] using wordTrace_append hprefix tailTrace_157591
  have hstable : (prefixWord ++ tailWord_157591).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_157591).length < 2 ^ (prefixWord ++ tailWord_157591).sum := by decide
  have hdescent : baseEnd_157591 < baseStart_157591 := by decide
  rcases family_descends (prefixWord ++ tailWord_157591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_157619 : List Nat := [1, 1, 1, 2, 3, 1, 4, 5, 1, 3]
def baseStart_157619 : Nat := 118140960795 + 157619 * 2 ^ 59
def prefixEnd_157619 : Nat := 4983230072969 + 3 ^ 40 * 157619 * 2
def baseEnd_157619 : Nat := 53956204854082699091753

theorem tailTrace_157619 : CollatzResearch.WordTrace tailWord_157619 prefixEnd_157619 53956204854082699091753 := by
  unfold tailWord_157619
  simp only [CollatzResearch.WordTrace]
  refine ⟨5748837215980757027163911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3832558143987171351442607 5748837215980757027163911)
  ·
    refine ⟨8623255823971135540745867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5748837215980757027163911 8623255823971135540745867)
    ·
      refine ⟨12934883735956703311118801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8623255823971135540745867 12934883735956703311118801)
      ·
        refine ⟨9701162801967527483339101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12934883735956703311118801 9701162801967527483339101)
        ·
          refine ⟨3637936050737822806252163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9701162801967527483339101 3637936050737822806252163)
          ·
            refine ⟨5456904076106734209378245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3637936050737822806252163 5456904076106734209378245)
            ·
              refine ⟨1023169514270012664258421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5456904076106734209378245 1023169514270012664258421)
              ·
                refine ⟨95922141962813687274227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1023169514270012664258421 95922141962813687274227)
                ·
                  refine ⟨143883212944220530911341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 95922141962813687274227 143883212944220530911341)
                  ·
                    refine ⟨53956204854082699091753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 143883212944220530911341 53956204854082699091753)
                    ·
                      rfl

theorem cell22_157619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 4, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 4, 5, 1, 3].length) (baseStart_157619 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_157619 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_157619 prefixEnd_157619 := by exact prefixLift 157619
  have htrace : WordTrace (prefixWord ++ tailWord_157619) baseStart_157619 baseEnd_157619 := by
    simpa [prefixWord, tailWord_157619, baseEnd_157619] using wordTrace_append hprefix tailTrace_157619
  have hstable : (prefixWord ++ tailWord_157619).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_157619).length < 2 ^ (prefixWord ++ tailWord_157619).sum := by decide
  have hdescent : baseEnd_157619 < baseStart_157619 := by decide
  rcases family_descends (prefixWord ++ tailWord_157619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_157632 : List Nat := [2, 1, 1, 2, 3, 2, 4, 2, 5]
def baseStart_157632 : Nat := 118140960795 + 157632 * 2 ^ 59
def prefixEnd_157632 : Nat := 4983230072969 + 3 ^ 40 * 157632 * 2
def baseEnd_157632 : Nat := 17986885006584999505571

theorem tailTrace_157632 : CollatzResearch.WordTrace tailWord_157632 prefixEnd_157632 17986885006584999505571 := by
  unfold tailWord_157632
  simp only [CollatzResearch.WordTrace]
  refine ⟨2874655682466830123693575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3832874243289106831591433 2874655682466830123693575)
  ·
    refine ⟨4311983523700245185540363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2874655682466830123693575 4311983523700245185540363)
    ·
      refine ⟨6467975285550367778310545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4311983523700245185540363 6467975285550367778310545)
      ·
        refine ⟨4850981464162775833732909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6467975285550367778310545 4850981464162775833732909)
        ·
          refine ⟨1819118049061040937649841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4850981464162775833732909 1819118049061040937649841)
          ·
            refine ⟨1364338536795780703237381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1819118049061040937649841 1364338536795780703237381)
            ·
              refine ⟨255813475649208881857009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1364338536795780703237381 255813475649208881857009)
              ·
                refine ⟨191860106736906661392757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 255813475649208881857009 191860106736906661392757)
                ·
                  refine ⟨17986885006584999505571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 191860106736906661392757 17986885006584999505571)
                  ·
                    rfl

theorem cell22_157632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 4, 2, 5].length) (baseStart_157632 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_157632 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_157632 prefixEnd_157632 := by exact prefixLift 157632
  have htrace : WordTrace (prefixWord ++ tailWord_157632) baseStart_157632 baseEnd_157632 := by
    simpa [prefixWord, tailWord_157632, baseEnd_157632] using wordTrace_append hprefix tailTrace_157632
  have hstable : (prefixWord ++ tailWord_157632).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_157632).length < 2 ^ (prefixWord ++ tailWord_157632).sum := by decide
  have hdescent : baseEnd_157632 < baseStart_157632 := by decide
  rcases family_descends (prefixWord ++ tailWord_157632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_157694 : List Nat := [4, 2, 2, 2, 1, 1, 1, 3, 6]
def baseStart_157694 : Nat := 118140960795 + 157694 * 2 ^ 59
def prefixEnd_157694 : Nat := 4983230072969 + 3 ^ 40 * 157694 * 2
def baseEnd_157694 : Nat := 17993959628935834488841

theorem tailTrace_157694 : CollatzResearch.WordTrace tailWord_157694 prefixEnd_157694 17993959628935834488841 := by
  unfold tailWord_157694
  simp only [CollatzResearch.WordTrace]
  refine ⟨718946586338630604518017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3834381793806029890762757 718946586338630604518017)
  ·
    refine ⟨539209939753972953388513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 718946586338630604518017 539209939753972953388513)
    ·
      refine ⟨404407454815479715041385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 539209939753972953388513 404407454815479715041385)
      ·
        refine ⟨303305591111609786281039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 404407454815479715041385 303305591111609786281039)
        ·
          refine ⟨454958386667414679421559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 303305591111609786281039 454958386667414679421559)
          ·
            refine ⟨682437580001122019132339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 454958386667414679421559 682437580001122019132339)
            ·
              refine ⟨1023656370001683028698509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 682437580001122019132339 1023656370001683028698509)
              ·
                refine ⟨383871138750631135761941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1023656370001683028698509 383871138750631135761941)
                ·
                  refine ⟨17993959628935834488841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 383871138750631135761941 17993959628935834488841)
                  ·
                    rfl

theorem cell22_157694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 1, 3, 6].length) (baseStart_157694 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_157694 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_157694 prefixEnd_157694 := by exact prefixLift 157694
  have htrace : WordTrace (prefixWord ++ tailWord_157694) baseStart_157694 baseEnd_157694 := by
    simpa [prefixWord, tailWord_157694, baseEnd_157694] using wordTrace_append hprefix tailTrace_157694
  have hstable : (prefixWord ++ tailWord_157694).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_157694).length < 2 ^ (prefixWord ++ tailWord_157694).sum := by decide
  have hdescent : baseEnd_157694 < baseStart_157694 := by decide
  rcases family_descends (prefixWord ++ tailWord_157694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_157722 : List Nat := [3, 1, 1, 3, 1, 4, 1, 8]
def baseStart_157722 : Nat := 118140960795 + 157722 * 2 ^ 59
def prefixEnd_157722 : Nat := 4983230072969 + 3 ^ 40 * 157722 * 2
def baseEnd_157722 : Nat := 5999051539891640418493

theorem tailTrace_157722 : CollatzResearch.WordTrace tailWord_157722 prefixEnd_157722 5999051539891640418493 := by
  unfold tailWord_157722
  simp only [CollatzResearch.WordTrace]
  refine ⟨1438148483651901404540855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3835062623071737078775613 1438148483651901404540855)
  ·
    refine ⟨2157222725477852106811283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1438148483651901404540855 2157222725477852106811283)
    ·
      refine ⟨3235834088216778160216925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2157222725477852106811283 3235834088216778160216925)
      ·
        refine ⟨1213437783081291810081347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3235834088216778160216925 1213437783081291810081347)
        ·
          refine ⟨1820156674621937715122021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1213437783081291810081347 1820156674621937715122021)
          ·
            refine ⟨341279376491613321585379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1820156674621937715122021 341279376491613321585379)
            ·
              refine ⟨511919064737419982378069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 341279376491613321585379 511919064737419982378069)
              ·
                refine ⟨5999051539891640418493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 511919064737419982378069 5999051539891640418493)
                ·
                  rfl

theorem cell22_157722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 4, 1, 8].length) (baseStart_157722 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_157722 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_157722 prefixEnd_157722 := by exact prefixLift 157722
  have htrace : WordTrace (prefixWord ++ tailWord_157722) baseStart_157722 baseEnd_157722 := by
    simpa [prefixWord, tailWord_157722, baseEnd_157722] using wordTrace_append hprefix tailTrace_157722
  have hstable : (prefixWord ++ tailWord_157722).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_157722).length < 2 ^ (prefixWord ++ tailWord_157722).sum := by decide
  have hdescent : baseEnd_157722 < baseStart_157722 := by decide
  rcases family_descends (prefixWord ++ tailWord_157722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_157829 : List Nat := [1, 3, 1, 1, 5, 2, 1, 2, 6]
def baseStart_157829 : Nat := 118140960795 + 157829 * 2 ^ 59
def prefixEnd_157829 : Nat := 4983230072969 + 3 ^ 40 * 157829 * 2
def baseEnd_157829 : Nat := 18009364048570717113703

theorem tailTrace_157829 : CollatzResearch.WordTrace tailWord_157829 prefixEnd_157829 18009364048570717113703 := by
  unfold tailWord_157829
  simp only [CollatzResearch.WordTrace]
  refine ⟨5756496545219962892308541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3837664363479975261539027 5756496545219962892308541)
  ·
    refine ⟨2158686204457486084615703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5756496545219962892308541 2158686204457486084615703)
    ·
      refine ⟨3238029306686229126923555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2158686204457486084615703 3238029306686229126923555)
      ·
        refine ⟨4857043960029343690385333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3238029306686229126923555 4857043960029343690385333)
        ·
          refine ⟨455347871252750970973625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 4857043960029343690385333 455347871252750970973625)
          ·
            refine ⟨341510903439563228230219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 455347871252750970973625 341510903439563228230219)
            ·
              refine ⟨512266355159344842345329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 341510903439563228230219 512266355159344842345329)
              ·
                refine ⟨384199766369508631758997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 512266355159344842345329 384199766369508631758997)
                ·
                  refine ⟨18009364048570717113703, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 384199766369508631758997 18009364048570717113703)
                  ·
                    rfl

theorem cell22_157829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 2, 1, 2, 6].length) (baseStart_157829 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_157829 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_157829 prefixEnd_157829 := by exact prefixLift 157829
  have htrace : WordTrace (prefixWord ++ tailWord_157829) baseStart_157829 baseEnd_157829 := by
    simpa [prefixWord, tailWord_157829, baseEnd_157829] using wordTrace_append hprefix tailTrace_157829
  have hstable : (prefixWord ++ tailWord_157829).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_157829).length < 2 ^ (prefixWord ++ tailWord_157829).sum := by decide
  have hdescent : baseEnd_157829 < baseStart_157829 := by decide
  rcases family_descends (prefixWord ++ tailWord_157829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_157872 : List Nat := [2, 1, 1, 1, 2, 1, 2, 1, 4, 7]
def baseStart_157872 : Nat := 118140960795 + 157872 * 2 ^ 59
def prefixEnd_157872 : Nat := 4983230072969 + 3 ^ 40 * 157872 * 2
def baseEnd_157872 : Nat := 54042811924474372515977

theorem tailTrace_157872 : CollatzResearch.WordTrace tailWord_157872 prefixEnd_157872 54042811924474372515977 := by
  unfold tailWord_157872
  simp only [CollatzResearch.WordTrace]
  refine ⟨2879032442032090618061935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3838709922709454157415913 2879032442032090618061935)
  ·
    refine ⟨4318548663048135927092903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2879032442032090618061935 4318548663048135927092903)
    ·
      refine ⟨6477822994572203890639355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4318548663048135927092903 6477822994572203890639355)
      ·
        refine ⟨9716734491858305835959033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6477822994572203890639355 9716734491858305835959033)
        ·
          refine ⟨7287550868893729376969275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9716734491858305835959033 7287550868893729376969275)
          ·
            refine ⟨10931326303340594065453913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7287550868893729376969275 10931326303340594065453913)
            ·
              refine ⟨8198494727505445549090435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10931326303340594065453913 8198494727505445549090435)
              ·
                refine ⟨12297742091258168323635653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8198494727505445549090435 12297742091258168323635653)
                ·
                  refine ⟨2305826642110906560681685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12297742091258168323635653 2305826642110906560681685)
                  ·
                    refine ⟨54042811924474372515977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 2305826642110906560681685 54042811924474372515977)
                    ·
                      rfl

theorem cell22_157872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 1, 4, 7].length) (baseStart_157872 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_157872 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_157872 prefixEnd_157872 := by exact prefixLift 157872
  have htrace : WordTrace (prefixWord ++ tailWord_157872) baseStart_157872 baseEnd_157872 := by
    simpa [prefixWord, tailWord_157872, baseEnd_157872] using wordTrace_append hprefix tailTrace_157872
  have hstable : (prefixWord ++ tailWord_157872).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_157872).length < 2 ^ (prefixWord ++ tailWord_157872).sum := by decide
  have hdescent : baseEnd_157872 < baseStart_157872 := by decide
  rcases family_descends (prefixWord ++ tailWord_157872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_157919 : List Nat := [1, 1, 2, 3, 2, 1, 1, 6, 5]
def baseStart_157919 : Nat := 118140960795 + 157919 * 2 ^ 59
def prefixEnd_157919 : Nat := 4983230072969 + 3 ^ 40 * 157919 * 2
def baseEnd_157919 : Nat := 18019633661660638863611

theorem tailTrace_157919 : CollatzResearch.WordTrace tailWord_157919 prefixEnd_157919 18019633661660638863611 := by
  unfold tailWord_157919
  simp only [CollatzResearch.WordTrace]
  refine ⟨5759779114893908263084811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3839852743262605508723207 5759779114893908263084811)
  ·
    refine ⟨8639668672340862394627217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5759779114893908263084811 8639668672340862394627217)
    ·
      refine ⟨6479751504255646795970413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8639668672340862394627217 6479751504255646795970413)
      ·
        refine ⟨2429906814095867548488905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6479751504255646795970413 2429906814095867548488905)
        ·
          refine ⟨1822430110571900661366679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2429906814095867548488905 1822430110571900661366679)
          ·
            refine ⟨2733645165857850992050019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1822430110571900661366679 2733645165857850992050019)
            ·
              refine ⟨4100467748786776488075029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2733645165857850992050019 4100467748786776488075029)
              ·
                refine ⟨192209425724380147878517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 4100467748786776488075029 192209425724380147878517)
                ·
                  refine ⟨18019633661660638863611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 192209425724380147878517 18019633661660638863611)
                  ·
                    rfl

theorem cell22_157919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 6, 5].length) (baseStart_157919 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_157919 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_157919 prefixEnd_157919 := by exact prefixLift 157919
  have htrace : WordTrace (prefixWord ++ tailWord_157919) baseStart_157919 baseEnd_157919 := by
    simpa [prefixWord, tailWord_157919, baseEnd_157919] using wordTrace_append hprefix tailTrace_157919
  have hstable : (prefixWord ++ tailWord_157919).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_157919).length < 2 ^ (prefixWord ++ tailWord_157919).sum := by decide
  have hdescent : baseEnd_157919 < baseStart_157919 := by decide
  rcases family_descends (prefixWord ++ tailWord_157919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_157934 : List Nat := [4, 1, 2, 1, 1, 1, 1, 3, 1, 7]
def baseStart_157934 : Nat := 118140960795 + 157934 * 2 ^ 59
def prefixEnd_157934 : Nat := 4983230072969 + 3 ^ 40 * 157934 * 2
def baseEnd_157934 : Nat := 54064035791526877465787

theorem tailTrace_157934 : CollatzResearch.WordTrace tailWord_157934 prefixEnd_157934 54064035791526877465787 := by
  unfold tailWord_157934
  simp only [CollatzResearch.WordTrace]
  refine ⟨720040776229945728110107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3840217473226377216587237 720040776229945728110107)
  ·
    refine ⟨1080061164344918592165161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 720040776229945728110107 1080061164344918592165161)
    ·
      refine ⟨810045873258688944123871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1080061164344918592165161 810045873258688944123871)
      ·
        refine ⟨1215068809888033416185807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 810045873258688944123871 1215068809888033416185807)
        ·
          refine ⟨1822603214832050124278711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1215068809888033416185807 1822603214832050124278711)
          ·
            refine ⟨2733904822248075186418067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1822603214832050124278711 2733904822248075186418067)
            ·
              refine ⟨4100857233372112779627101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2733904822248075186418067 4100857233372112779627101)
              ·
                refine ⟨1537821462514542292360163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4100857233372112779627101 1537821462514542292360163)
                ·
                  refine ⟨2306732193771813438540245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1537821462514542292360163 2306732193771813438540245)
                  ·
                    refine ⟨54064035791526877465787, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 2306732193771813438540245 54064035791526877465787)
                    ·
                      rfl

theorem cell22_157934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 3, 1, 7].length) (baseStart_157934 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_157934 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_157934 prefixEnd_157934 := by exact prefixLift 157934
  have htrace : WordTrace (prefixWord ++ tailWord_157934) baseStart_157934 baseEnd_157934 := by
    simpa [prefixWord, tailWord_157934, baseEnd_157934] using wordTrace_append hprefix tailTrace_157934
  have hstable : (prefixWord ++ tailWord_157934).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_157934).length < 2 ^ (prefixWord ++ tailWord_157934).sum := by decide
  have hdescent : baseEnd_157934 < baseStart_157934 := by decide
  rcases family_descends (prefixWord ++ tailWord_157934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_158017 : List Nat := [1, 2, 5, 2, 2, 2, 2, 1, 1, 4]
def baseStart_158017 : Nat := 118140960795 + 158017 * 2 ^ 59
def prefixEnd_158017 : Nat := 4983230072969 + 3 ^ 40 * 158017 * 2
def baseEnd_158017 : Nat := 54092448387742327640533

theorem tailTrace_158017 : CollatzResearch.WordTrace tailWord_158017 prefixEnd_158017 54092448387742327640533 := by
  unfold tailWord_158017
  simp only [CollatzResearch.WordTrace]
  refine ⟨5763353468538871000152305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3842235645692580666768203 5763353468538871000152305)
  ·
    refine ⟨4322515101404153250114229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5763353468538871000152305 4322515101404153250114229)
    ·
      refine ⟨405235790756639367198209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 4322515101404153250114229 405235790756639367198209)
      ·
        refine ⟨303926843067479525398657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 405235790756639367198209 303926843067479525398657)
        ·
          refine ⟨227945132300609644048993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 303926843067479525398657 227945132300609644048993)
          ·
            refine ⟨170958849225457233036745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 227945132300609644048993 170958849225457233036745)
            ·
              refine ⟨128219136919092924777559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 170958849225457233036745 128219136919092924777559)
              ·
                refine ⟨192328705378639387166339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 128219136919092924777559 192328705378639387166339)
                ·
                  refine ⟨288493058067959080749509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 192328705378639387166339 288493058067959080749509)
                  ·
                    refine ⟨54092448387742327640533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 288493058067959080749509 54092448387742327640533)
                    ·
                      rfl

theorem cell22_158017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 2, 2, 1, 1, 4].length) (baseStart_158017 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_158017 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_158017 prefixEnd_158017 := by exact prefixLift 158017
  have htrace : WordTrace (prefixWord ++ tailWord_158017) baseStart_158017 baseEnd_158017 := by
    simpa [prefixWord, tailWord_158017, baseEnd_158017] using wordTrace_append hprefix tailTrace_158017
  have hstable : (prefixWord ++ tailWord_158017).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_158017).length < 2 ^ (prefixWord ++ tailWord_158017).sum := by decide
  have hdescent : baseEnd_158017 < baseStart_158017 := by decide
  rcases family_descends (prefixWord ++ tailWord_158017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_158060 : List Nat := [2, 2, 1, 1, 7, 1, 2, 6]
def baseStart_158060 : Nat := 118140960795 + 158060 * 2 ^ 59
def prefixEnd_158060 : Nat := 4983230072969 + 3 ^ 40 * 158060 * 2
def baseEnd_158060 : Nat := 6011907574056060979489

theorem tailTrace_158060 : CollatzResearch.WordTrace tailWord_158060 prefixEnd_158060 6011907574056060979489 := by
  unfold tailWord_158060
  simp only [CollatzResearch.WordTrace]
  refine ⟨2882460903691544671983817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3843281204922059562645089 2882460903691544671983817)
  ·
    refine ⟨2161845677768658503987863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2882460903691544671983817 2161845677768658503987863)
    ·
      refine ⟨3242768516652987755981795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2161845677768658503987863 3242768516652987755981795)
      ·
        refine ⟨4864152774979481633972693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3242768516652987755981795 4864152774979481633972693)
        ·
          refine ⟨114003580663581600796235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 4864152774979481633972693 114003580663581600796235)
          ·
            refine ⟨171005370995372401194353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 114003580663581600796235 171005370995372401194353)
            ·
              refine ⟨128254028246529300895765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 171005370995372401194353 128254028246529300895765)
              ·
                refine ⟨6011907574056060979489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 128254028246529300895765 6011907574056060979489)
                ·
                  rfl

theorem cell22_158060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 7, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 7, 1, 2, 6].length) (baseStart_158060 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_158060 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_158060 prefixEnd_158060 := by exact prefixLift 158060
  have htrace : WordTrace (prefixWord ++ tailWord_158060) baseStart_158060 baseEnd_158060 := by
    simpa [prefixWord, tailWord_158060, baseEnd_158060] using wordTrace_append hprefix tailTrace_158060
  have hstable : (prefixWord ++ tailWord_158060).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_158060).length < 2 ^ (prefixWord ++ tailWord_158060).sum := by decide
  have hdescent : baseEnd_158060 < baseStart_158060 := by decide
  rcases family_descends (prefixWord ++ tailWord_158060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_158075 : List Nat := [1, 1, 1, 1, 1, 7, 3, 3, 1, 3]
def baseStart_158075 : Nat := 118140960795 + 158075 * 2 ^ 59
def prefixEnd_158075 : Nat := 4983230072969 + 3 ^ 40 * 158075 * 2
def baseEnd_158075 : Nat := 54112302973049509690355

theorem tailTrace_158075 : CollatzResearch.WordTrace tailWord_158075 prefixEnd_158075 54112302973049509690355 := by
  unfold tailWord_158075
  simp only [CollatzResearch.WordTrace]
  refine ⟨5765468902328746905763679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3843645934885831270509119 5765468902328746905763679)
  ·
    refine ⟨8648203353493120358645519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5765468902328746905763679 8648203353493120358645519)
    ·
      refine ⟨12972305030239680537968279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8648203353493120358645519 12972305030239680537968279)
      ·
        refine ⟨19458457545359520806952419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12972305030239680537968279 19458457545359520806952419)
        ·
          refine ⟨29187686318039281210428629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19458457545359520806952419 29187686318039281210428629)
          ·
            refine ⟨684086398079045653369421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 29187686318039281210428629 684086398079045653369421)
            ·
              refine ⟨256532399279642120013533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 684086398079045653369421 256532399279642120013533)
              ·
                refine ⟨96199649729865795005075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 256532399279642120013533 96199649729865795005075)
                ·
                  refine ⟨144299474594798692507613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 96199649729865795005075 144299474594798692507613)
                  ·
                    refine ⟨54112302973049509690355, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 144299474594798692507613 54112302973049509690355)
                    ·
                      rfl

theorem cell22_158075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 3, 3, 1, 3].length) (baseStart_158075 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_158075 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_158075 prefixEnd_158075 := by exact prefixLift 158075
  have htrace : WordTrace (prefixWord ++ tailWord_158075) baseStart_158075 baseEnd_158075 := by
    simpa [prefixWord, tailWord_158075, baseEnd_158075] using wordTrace_append hprefix tailTrace_158075
  have hstable : (prefixWord ++ tailWord_158075).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_158075).length < 2 ^ (prefixWord ++ tailWord_158075).sum := by decide
  have hdescent : baseEnd_158075 < baseStart_158075 := by decide
  rcases family_descends (prefixWord ++ tailWord_158075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_158092 : List Nat := [2, 2, 1, 2, 1, 5, 3, 2, 1, 3]
def baseStart_158092 : Nat := 118140960795 + 158092 * 2 ^ 59
def prefixEnd_158092 : Nat := 4983230072969 + 3 ^ 40 * 158092 * 2
def baseEnd_158092 : Nat := 54118122420467132015303

theorem tailTrace_158092 : CollatzResearch.WordTrace tailWord_158092 prefixEnd_158092 54118122420467132015303 := by
  unfold tailWord_158092
  simp only [CollatzResearch.WordTrace]
  refine ⟨2883044471633579404566265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3844059295511439206088353 2883044471633579404566265)
  ·
    refine ⟨2162283353725184553424699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2883044471633579404566265 2162283353725184553424699)
    ·
      refine ⟨3243425030587776830137049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2162283353725184553424699 3243425030587776830137049)
      ·
        refine ⟨2432568772940832622602787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3243425030587776830137049 2432568772940832622602787)
        ·
          refine ⟨3648853159411248933904181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2432568772940832622602787 3648853159411248933904181)
          ·
            refine ⟨342079983694804587553517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 3648853159411248933904181 342079983694804587553517)
            ·
              refine ⟨128279993885551720332569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 342079983694804587553517 128279993885551720332569)
              ·
                refine ⟨96209995414163790249427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 128279993885551720332569 96209995414163790249427)
                ·
                  refine ⟨144314993121245685374141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 96209995414163790249427 144314993121245685374141)
                  ·
                    refine ⟨54118122420467132015303, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 144314993121245685374141 54118122420467132015303)
                    ·
                      rfl

theorem cell22_158092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 5, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 5, 3, 2, 1, 3].length) (baseStart_158092 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_158092 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_158092 prefixEnd_158092 := by exact prefixLift 158092
  have htrace : WordTrace (prefixWord ++ tailWord_158092) baseStart_158092 baseEnd_158092 := by
    simpa [prefixWord, tailWord_158092, baseEnd_158092] using wordTrace_append hprefix tailTrace_158092
  have hstable : (prefixWord ++ tailWord_158092).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_158092).length < 2 ^ (prefixWord ++ tailWord_158092).sum := by decide
  have hdescent : baseEnd_158092 < baseStart_158092 := by decide
  rcases family_descends (prefixWord ++ tailWord_158092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_158101 : List Nat := [1, 3, 2, 1, 1, 2, 1, 4, 3, 4]
def baseStart_158101 : Nat := 118140960795 + 158101 * 2 ^ 59
def prefixEnd_158101 : Nat := 4983230072969 + 3 ^ 40 * 158101 * 2
def baseEnd_158101 : Nat := 54121203304394108540275

theorem tailTrace_158101 : CollatzResearch.WordTrace tailWord_158101 prefixEnd_158101 54121203304394108540275 := by
  unfold tailWord_158101
  simp only [CollatzResearch.WordTrace]
  refine ⟨5766417200234553346210157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3844278133489702230806771 5766417200234553346210157)
  ·
    refine ⟨2162406450087957504828809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5766417200234553346210157 2162406450087957504828809)
    ·
      refine ⟨1621804837565968128621607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2162406450087957504828809 1621804837565968128621607)
      ·
        refine ⟨2432707256348952192932411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1621804837565968128621607 2432707256348952192932411)
        ·
          refine ⟨3649060884523428289398617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2432707256348952192932411 3649060884523428289398617)
          ·
            refine ⟨2736795663392571217048963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3649060884523428289398617 2736795663392571217048963)
            ·
              refine ⟨4105193495088856825573445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2736795663392571217048963 4105193495088856825573445)
              ·
                refine ⟨769723780329160654795021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4105193495088856825573445 769723780329160654795021)
                ·
                  refine ⟨288646417623435245548133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 769723780329160654795021 288646417623435245548133)
                  ·
                    refine ⟨54121203304394108540275, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 288646417623435245548133 54121203304394108540275)
                    ·
                      rfl

theorem cell22_158101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 4, 3, 4].length) (baseStart_158101 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_158101 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_158101 prefixEnd_158101 := by exact prefixLift 158101
  have htrace : WordTrace (prefixWord ++ tailWord_158101) baseStart_158101 baseEnd_158101 := by
    simpa [prefixWord, tailWord_158101, baseEnd_158101] using wordTrace_append hprefix tailTrace_158101
  have hstable : (prefixWord ++ tailWord_158101).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_158101).length < 2 ^ (prefixWord ++ tailWord_158101).sum := by decide
  have hdescent : baseEnd_158101 < baseStart_158101 := by decide
  rcases family_descends (prefixWord ++ tailWord_158101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_158116 : List Nat := [2, 3, 1, 2, 1, 1, 2, 4, 6]
def baseStart_158116 : Nat := 118140960795 + 158116 * 2 ^ 59
def prefixEnd_158116 : Nat := 4983230072969 + 3 ^ 40 * 158116 * 2
def baseEnd_158116 : Nat := 18042112703646356471743

theorem tailTrace_158116 : CollatzResearch.WordTrace tailWord_158116 prefixEnd_158116 18042112703646356471743 := by
  unfold tailWord_158116
  simp only [CollatzResearch.WordTrace]
  refine ⟨2883482147590105454003101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3844642863453473938670801 2883482147590105454003101)
  ·
    refine ⟨1081305805346289545251163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2883482147590105454003101 1081305805346289545251163)
    ·
      refine ⟨1621958708019434317876745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1081305805346289545251163 1621958708019434317876745)
      ·
        refine ⟨1216469031014575738407559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1621958708019434317876745 1216469031014575738407559)
        ·
          refine ⟨1824703546521863607611339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1216469031014575738407559 1824703546521863607611339)
          ·
            refine ⟨2737055319782795411417009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1824703546521863607611339 2737055319782795411417009)
            ·
              refine ⟨2052791489837096558562757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2737055319782795411417009 2052791489837096558562757)
              ·
                refine ⟨384898404344455604730517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2052791489837096558562757 384898404344455604730517)
                ·
                  refine ⟨18042112703646356471743, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 384898404344455604730517 18042112703646356471743)
                  ·
                    rfl

theorem cell22_158116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 2, 4, 6].length) (baseStart_158116 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_158116 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_158116 prefixEnd_158116 := by exact prefixLift 158116
  have htrace : WordTrace (prefixWord ++ tailWord_158116) baseStart_158116 baseEnd_158116 := by
    simpa [prefixWord, tailWord_158116, baseEnd_158116] using wordTrace_append hprefix tailTrace_158116
  have hstable : (prefixWord ++ tailWord_158116).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_158116).length < 2 ^ (prefixWord ++ tailWord_158116).sum := by decide
  have hdescent : baseEnd_158116 < baseStart_158116 := by decide
  rcases family_descends (prefixWord ++ tailWord_158116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_158135 : List Nat := [1, 1, 3, 1, 3, 4, 3, 1, 1, 4]
def baseStart_158135 : Nat := 118140960795 + 158135 * 2 ^ 59
def prefixEnd_158135 : Nat := 4983230072969 + 3 ^ 40 * 158135 * 2
def baseEnd_158135 : Nat := 54132842199229353190171

theorem tailTrace_158135 : CollatzResearch.WordTrace tailWord_158135 prefixEnd_158135 54132842199229353190171 := by
  unfold tailWord_158135
  simp only [CollatzResearch.WordTrace]
  refine ⟨5767657282111377152947859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3845104854740918101965239 5767657282111377152947859)
  ·
    refine ⟨8651485923167065729421789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5767657282111377152947859 8651485923167065729421789)
    ·
      refine ⟨3244307221187649648533171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8651485923167065729421789 3244307221187649648533171)
      ·
        refine ⟨4866460831781474472799757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3244307221187649648533171 4866460831781474472799757)
        ·
          refine ⟨1824922811918052927299909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4866460831781474472799757 1824922811918052927299909)
          ·
            refine ⟨342173027234634923868733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1824922811918052927299909 342173027234634923868733)
            ·
              refine ⟨128314885212988096450775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 342173027234634923868733 128314885212988096450775)
              ·
                refine ⟨192472327819482144676163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 128314885212988096450775 192472327819482144676163)
                ·
                  refine ⟨288708491729223217014245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 192472327819482144676163 288708491729223217014245)
                  ·
                    refine ⟨54132842199229353190171, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 288708491729223217014245 54132842199229353190171)
                    ·
                      rfl

theorem cell22_158135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 4, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 4, 3, 1, 1, 4].length) (baseStart_158135 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_158135 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_158135 prefixEnd_158135 := by exact prefixLift 158135
  have htrace : WordTrace (prefixWord ++ tailWord_158135) baseStart_158135 baseEnd_158135 := by
    simpa [prefixWord, tailWord_158135, baseEnd_158135] using wordTrace_append hprefix tailTrace_158135
  have hstable : (prefixWord ++ tailWord_158135).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_158135).length < 2 ^ (prefixWord ++ tailWord_158135).sum := by decide
  have hdescent : baseEnd_158135 < baseStart_158135 := by decide
  rcases family_descends (prefixWord ++ tailWord_158135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_158165 : List Nat := [1, 3, 2, 3, 1, 2, 2, 3, 2, 3]
def baseStart_158165 : Nat := 118140960795 + 158165 * 2 ^ 59
def prefixEnd_158165 : Nat := 4983230072969 + 3 ^ 40 * 158165 * 2
def baseEnd_158165 : Nat := 54143111812319274940079

theorem tailTrace_158165 : CollatzResearch.WordTrace tailWord_158165 prefixEnd_158165 54143111812319274940079 := by
  unfold tailWord_158165
  simp only [CollatzResearch.WordTrace]
  refine ⟨5768751472002692276539949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3845834314668461517693299 5768751472002692276539949)
  ·
    refine ⟨2163281802001009603702481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5768751472002692276539949 2163281802001009603702481)
    ·
      refine ⟨1622461351500757202776861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2163281802001009603702481 1622461351500757202776861)
      ·
        refine ⟨608423006812783951041323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1622461351500757202776861 608423006812783951041323)
        ·
          refine ⟨912634510219175926561985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 608423006812783951041323 912634510219175926561985)
          ·
            refine ⟨684475882664381944921489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 912634510219175926561985 684475882664381944921489)
            ·
              refine ⟨513356911998286458691117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 684475882664381944921489 513356911998286458691117)
              ·
                refine ⟨192508841999357422009169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 513356911998286458691117 192508841999357422009169)
                ·
                  refine ⟨144381631499518066506877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 192508841999357422009169 144381631499518066506877)
                  ·
                    refine ⟨54143111812319274940079, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 144381631499518066506877 54143111812319274940079)
                    ·
                      rfl

theorem cell22_158165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 2, 3, 2, 3].length) (baseStart_158165 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_158165 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_158165 prefixEnd_158165 := by exact prefixLift 158165
  have htrace : WordTrace (prefixWord ++ tailWord_158165) baseStart_158165 baseEnd_158165 := by
    simpa [prefixWord, tailWord_158165, baseEnd_158165] using wordTrace_append hprefix tailTrace_158165
  have hstable : (prefixWord ++ tailWord_158165).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_158165).length < 2 ^ (prefixWord ++ tailWord_158165).sum := by decide
  have hdescent : baseEnd_158165 < baseStart_158165 := by decide
  rcases family_descends (prefixWord ++ tailWord_158165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_158193 : List Nat := [1, 2, 2, 2, 3, 1, 1, 2, 5, 3]
def baseStart_158193 : Nat := 118140960795 + 158193 * 2 ^ 59
def prefixEnd_158193 : Nat := 4983230072969 + 3 ^ 40 * 158193 * 2
def baseEnd_158193 : Nat := 54152696784536535239993

theorem tailTrace_158193 : CollatzResearch.WordTrace tailWord_158193 prefixEnd_158193 54152696784536535239993 := by
  unfold tailWord_158193
  simp only [CollatzResearch.WordTrace]
  refine ⟨5769772715901253058559233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3846515143934168705706155 5769772715901253058559233)
  ·
    refine ⟨4327329536925939793919425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5769772715901253058559233 4327329536925939793919425)
    ·
      refine ⟨3245497152694454845439569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4327329536925939793919425 3245497152694454845439569)
      ·
        refine ⟨2434122864520841134079677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3245497152694454845439569 2434122864520841134079677)
        ·
          refine ⟨912796074195315425279879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2434122864520841134079677 912796074195315425279879)
          ·
            refine ⟨1369194111292973137919819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 912796074195315425279879 1369194111292973137919819)
            ·
              refine ⟨2053791166939459706879729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1369194111292973137919819 2053791166939459706879729)
              ·
                refine ⟨1540343375204594780159797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2053791166939459706879729 1540343375204594780159797)
                ·
                  refine ⟨144407191425430760639981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1540343375204594780159797 144407191425430760639981)
                  ·
                    refine ⟨54152696784536535239993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 144407191425430760639981 54152696784536535239993)
                    ·
                      rfl

theorem cell22_158193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 1, 2, 5, 3].length) (baseStart_158193 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_158193 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_158193 prefixEnd_158193 := by exact prefixLift 158193
  have htrace : WordTrace (prefixWord ++ tailWord_158193) baseStart_158193 baseEnd_158193 := by
    simpa [prefixWord, tailWord_158193, baseEnd_158193] using wordTrace_append hprefix tailTrace_158193
  have hstable : (prefixWord ++ tailWord_158193).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_158193).length < 2 ^ (prefixWord ++ tailWord_158193).sum := by decide
  have hdescent : baseEnd_158193 < baseStart_158193 := by decide
  rcases family_descends (prefixWord ++ tailWord_158193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_158251 : List Nat := [1, 1, 1, 1, 2, 1, 3, 4, 8]
def baseStart_158251 : Nat := 118140960795 + 158251 * 2 ^ 59
def prefixEnd_158251 : Nat := 4983230072969 + 3 ^ 40 * 158251 * 2
def baseEnd_158251 : Nat := 18057517123281239096605

theorem tailTrace_158251 : CollatzResearch.WordTrace tailWord_158251 prefixEnd_158251 18057517123281239096605 := by
  unfold tailWord_158251
  simp only [CollatzResearch.WordTrace]
  refine ⟨5771888149691128964170607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3847925433127419309447071 5771888149691128964170607)
  ·
    refine ⟨8657832224536693446255911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5771888149691128964170607 8657832224536693446255911)
    ·
      refine ⟨12986748336805040169383867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8657832224536693446255911 12986748336805040169383867)
      ·
        refine ⟨19480122505207560254075801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12986748336805040169383867 19480122505207560254075801)
        ·
          refine ⟨14610091878905670190556851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19480122505207560254075801 14610091878905670190556851)
          ·
            refine ⟨21915137818358505285835277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14610091878905670190556851 21915137818358505285835277)
            ·
              refine ⟨8218176681884439482188229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21915137818358505285835277 8218176681884439482188229)
              ·
                refine ⟨1540908127853332402910293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8218176681884439482188229 1540908127853332402910293)
                ·
                  refine ⟨18057517123281239096605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 1540908127853332402910293 18057517123281239096605)
                  ·
                    rfl

theorem cell22_158251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 4, 8].length) (baseStart_158251 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_158251 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_158251 prefixEnd_158251 := by exact prefixLift 158251
  have htrace : WordTrace (prefixWord ++ tailWord_158251) baseStart_158251 baseEnd_158251 := by
    simpa [prefixWord, tailWord_158251, baseEnd_158251] using wordTrace_append hprefix tailTrace_158251
  have hstable : (prefixWord ++ tailWord_158251).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_158251).length < 2 ^ (prefixWord ++ tailWord_158251).sum := by decide
  have hdescent : baseEnd_158251 < baseStart_158251 := by decide
  rcases family_descends (prefixWord ++ tailWord_158251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_158317 : List Nat := [1, 5, 1, 1, 3, 1, 1, 4, 2, 3]
def baseStart_158317 : Nat := 118140960795 + 158317 * 2 ^ 59
def prefixEnd_158317 : Nat := 4983230072969 + 3 ^ 40 * 158317 * 2
def baseEnd_158317 : Nat := 54195144518641545139613

theorem tailTrace_158317 : CollatzResearch.WordTrace tailWord_158317 prefixEnd_158317 54195144518641545139613 := by
  unfold tailWord_158317
  simp only [CollatzResearch.WordTrace]
  refine ⟨5774295367452022236073205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3849530244968014824048803 5774295367452022236073205)
  ·
    refine ⟨541340190698627084631863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 5774295367452022236073205 541340190698627084631863)
    ·
      refine ⟨812010286047940626947795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 541340190698627084631863 812010286047940626947795)
      ·
        refine ⟨1218015429071910940421693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 812010286047940626947795 1218015429071910940421693)
        ·
          refine ⟨456755785901966602658135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1218015429071910940421693 456755785901966602658135)
          ·
            refine ⟨685133678852949903987203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 456755785901966602658135 685133678852949903987203)
            ·
              refine ⟨1027700518279424855980805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 685133678852949903987203 1027700518279424855980805)
              ·
                refine ⟨192693847177392160496401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1027700518279424855980805 192693847177392160496401)
                ·
                  refine ⟨144520385383044120372301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 192693847177392160496401 144520385383044120372301)
                  ·
                    refine ⟨54195144518641545139613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 144520385383044120372301 54195144518641545139613)
                    ·
                      rfl

theorem cell22_158317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 1, 4, 2, 3].length) (baseStart_158317 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_158317 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_158317 prefixEnd_158317 := by exact prefixLift 158317
  have htrace : WordTrace (prefixWord ++ tailWord_158317) baseStart_158317 baseEnd_158317 := by
    simpa [prefixWord, tailWord_158317, baseEnd_158317] using wordTrace_append hprefix tailTrace_158317
  have hstable : (prefixWord ++ tailWord_158317).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_158317).length < 2 ^ (prefixWord ++ tailWord_158317).sum := by decide
  have hdescent : baseEnd_158317 < baseStart_158317 := by decide
  rcases family_descends (prefixWord ++ tailWord_158317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_158343 : List Nat := [1, 1, 4, 2, 1, 2, 1, 2, 2, 6]
def baseStart_158343 : Nat := 118140960795 + 158343 * 2 ^ 59
def prefixEnd_158343 : Nat := 4983230072969 + 3 ^ 40 * 158343 * 2
def baseEnd_158343 : Nat := 54204044849986143989533

theorem tailTrace_158343 : CollatzResearch.WordTrace tailWord_158343 prefixEnd_158343 54204044849986143989533 := by
  unfold tailWord_158343
  simp only [CollatzResearch.WordTrace]
  refine ⟨5775243665357828676519683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3850162443571885784346455 5775243665357828676519683)
  ·
    refine ⟨8662865498036743014779525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5775243665357828676519683 8662865498036743014779525)
    ·
      refine ⟨1624287280881889315271161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8662865498036743014779525 1624287280881889315271161)
      ·
        refine ⟨1218215460661416986453371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1624287280881889315271161 1218215460661416986453371)
        ·
          refine ⟨1827323190992125479680057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1218215460661416986453371 1827323190992125479680057)
          ·
            refine ⟨1370492393244094109760043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1827323190992125479680057 1370492393244094109760043)
            ·
              refine ⟨2055738589866141164640065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1370492393244094109760043 2055738589866141164640065)
              ·
                refine ⟨1541803942399605873480049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2055738589866141164640065 1541803942399605873480049)
                ·
                  refine ⟨1156352956799704405110037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1541803942399605873480049 1156352956799704405110037)
                  ·
                    refine ⟨54204044849986143989533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1156352956799704405110037 54204044849986143989533)
                    ·
                      rfl

theorem cell22_158343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 1, 2, 2, 6].length) (baseStart_158343 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_158343 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_158343 prefixEnd_158343 := by exact prefixLift 158343
  have htrace : WordTrace (prefixWord ++ tailWord_158343) baseStart_158343 baseEnd_158343 := by
    simpa [prefixWord, tailWord_158343, baseEnd_158343] using wordTrace_append hprefix tailTrace_158343
  have hstable : (prefixWord ++ tailWord_158343).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_158343).length < 2 ^ (prefixWord ++ tailWord_158343).sum := by decide
  have hdescent : baseEnd_158343 < baseStart_158343 := by decide
  rcases family_descends (prefixWord ++ tailWord_158343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_158437 : List Nat := [1, 3, 1, 4, 1, 4, 1, 1, 6]
def baseStart_158437 : Nat := 118140960795 + 158437 * 2 ^ 59
def prefixEnd_158437 : Nat := 4983230072969 + 3 ^ 40 * 158437 * 2
def baseEnd_158437 : Nat := 18078740990333744046415

theorem tailTrace_158437 : CollatzResearch.WordTrace tailWord_158437 prefixEnd_158437 18078740990333744046415 := by
  unfold tailWord_158437
  simp only [CollatzResearch.WordTrace]
  refine ⟨5778672127017282730441565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3852448084678188486961043 5778672127017282730441565)
  ·
    refine ⟨2167002047631481023915587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5778672127017282730441565 2167002047631481023915587)
    ·
      refine ⟨3250503071447221535873381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2167002047631481023915587 3250503071447221535873381)
      ·
        refine ⟨609469325896354037976259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3250503071447221535873381 609469325896354037976259)
        ·
          refine ⟨914203988844531056964389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 609469325896354037976259 914203988844531056964389)
          ·
            refine ⟨171413247908349573180823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 914203988844531056964389 171413247908349573180823)
            ·
              refine ⟨257119871862524359771235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 171413247908349573180823 257119871862524359771235)
              ·
                refine ⟨385679807793786539656853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 257119871862524359771235 385679807793786539656853)
                ·
                  refine ⟨18078740990333744046415, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 385679807793786539656853 18078740990333744046415)
                  ·
                    rfl

theorem cell22_158437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 4, 1, 1, 6].length) (baseStart_158437 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_158437 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_158437 prefixEnd_158437 := by exact prefixLift 158437
  have htrace : WordTrace (prefixWord ++ tailWord_158437) baseStart_158437 baseEnd_158437 := by
    simpa [prefixWord, tailWord_158437, baseEnd_158437] using wordTrace_append hprefix tailTrace_158437
  have hstable : (prefixWord ++ tailWord_158437).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_158437).length < 2 ^ (prefixWord ++ tailWord_158437).sum := by decide
  have hdescent : baseEnd_158437 < baseStart_158437 := by decide
  rcases family_descends (prefixWord ++ tailWord_158437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_158482 : List Nat := [3, 2, 4, 1, 2, 10]
def baseStart_158482 : Nat := 118140960795 + 158482 * 2 ^ 59
def prefixEnd_158482 : Nat := 4983230072969 + 3 ^ 40 * 158482 * 2
def baseEnd_158482 : Nat := 669773177662174256347

theorem tailTrace_158482 : CollatzResearch.WordTrace tailWord_158482 prefixEnd_158482 669773177662174256347 := by
  unfold tailWord_158482
  simp only [CollatzResearch.WordTrace]
  refine ⟨1445078352963563853957425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3853542274569503610553133 1445078352963563853957425)
  ·
    refine ⟨1083808764722672890468069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1445078352963563853957425 1083808764722672890468069)
    ·
      refine ⟨203214143385501166962763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1083808764722672890468069 203214143385501166962763)
      ·
        refine ⟨304821215078251750444145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 203214143385501166962763 304821215078251750444145)
        ·
          refine ⟨228615911308688812833109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 304821215078251750444145 228615911308688812833109)
          ·
            refine ⟨669773177662174256347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 228615911308688812833109 669773177662174256347)
            ·
              rfl

theorem cell22_158482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 10].length) (baseStart_158482 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_158482 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_158482 prefixEnd_158482 := by exact prefixLift 158482
  have htrace : WordTrace (prefixWord ++ tailWord_158482) baseStart_158482 baseEnd_158482 := by
    simpa [prefixWord, tailWord_158482, baseEnd_158482] using wordTrace_append hprefix tailTrace_158482
  have hstable : (prefixWord ++ tailWord_158482).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_158482).length < 2 ^ (prefixWord ++ tailWord_158482).sum := by decide
  have hdescent : baseEnd_158482 < baseStart_158482 := by decide
  rcases family_descends (prefixWord ++ tailWord_158482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_158495 : List Nat := [1, 1, 2, 4, 2, 2, 1, 1, 2, 6]
def baseStart_158495 : Nat := 118140960795 + 158495 * 2 ^ 59
def prefixEnd_158495 : Nat := 4983230072969 + 3 ^ 40 * 158495 * 2
def baseEnd_158495 : Nat := 54256077556308414189067

theorem tailTrace_158495 : CollatzResearch.WordTrace tailWord_158495 prefixEnd_158495 54256077556308414189067 := by
  unfold tailWord_158495
  simp only [CollatzResearch.WordTrace]
  refine ⟨5780787560807158636052939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3853858373871439090701959 5780787560807158636052939)
  ·
    refine ⟨8671181341210737954079409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5780787560807158636052939 8671181341210737954079409)
    ·
      refine ⟨6503386005908053465559557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8671181341210737954079409 6503386005908053465559557)
      ·
        refine ⟨1219384876107760024792417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6503386005908053465559557 1219384876107760024792417)
        ·
          refine ⟨914538657080820018594313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1219384876107760024792417 914538657080820018594313)
          ·
            refine ⟨685903992810615013945735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 914538657080820018594313 685903992810615013945735)
            ·
              refine ⟨1028855989215922520918603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 685903992810615013945735 1028855989215922520918603)
              ·
                refine ⟨1543283983823883781377905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1028855989215922520918603 1543283983823883781377905)
                ·
                  refine ⟨1157462987867912836033429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1543283983823883781377905 1157462987867912836033429)
                  ·
                    refine ⟨54256077556308414189067, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1157462987867912836033429 54256077556308414189067)
                    ·
                      rfl

theorem cell22_158495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 1, 1, 2, 6].length) (baseStart_158495 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_158495 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_158495 prefixEnd_158495 := by exact prefixLift 158495
  have htrace : WordTrace (prefixWord ++ tailWord_158495) baseStart_158495 baseEnd_158495 := by
    simpa [prefixWord, tailWord_158495, baseEnd_158495] using wordTrace_append hprefix tailTrace_158495
  have hstable : (prefixWord ++ tailWord_158495).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_158495).length < 2 ^ (prefixWord ++ tailWord_158495).sum := by decide
  have hdescent : baseEnd_158495 < baseStart_158495 := by decide
  rcases family_descends (prefixWord ++ tailWord_158495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_158497 : List Nat := [1, 2, 3, 2, 1, 2, 2, 3, 3, 3]
def baseStart_158497 : Nat := 118140960795 + 158497 * 2 ^ 59
def prefixEnd_158497 : Nat := 4983230072969 + 3 ^ 40 * 158497 * 2
def baseEnd_158497 : Nat := 54256762197181075639061

theorem tailTrace_158497 : CollatzResearch.WordTrace tailWord_158497 prefixEnd_158497 54256762197181075639061 := by
  unfold tailWord_158497
  simp only [CollatzResearch.WordTrace]
  refine ⟨5780860506799912977625745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3853907004533275318417163 5780860506799912977625745)
  ·
    refine ⟨4335645380099934733219309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5780860506799912977625745 4335645380099934733219309)
    ·
      refine ⟨1625867017537475524957241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4335645380099934733219309 1625867017537475524957241)
      ·
        refine ⟨1219400263153106643717931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1625867017537475524957241 1219400263153106643717931)
        ·
          refine ⟨1829100394729659965576897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1219400263153106643717931 1829100394729659965576897)
          ·
            refine ⟨1371825296047244974182673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1829100394729659965576897 1371825296047244974182673)
            ·
              refine ⟨1028868972035433730637005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1371825296047244974182673 1028868972035433730637005)
              ·
                refine ⟨385825864513287648988877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1028868972035433730637005 385825864513287648988877)
                ·
                  refine ⟨144684699192482868370829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 385825864513287648988877 144684699192482868370829)
                  ·
                    refine ⟨54256762197181075639061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 144684699192482868370829 54256762197181075639061)
                    ·
                      rfl

theorem cell22_158497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 2, 3, 3, 3].length) (baseStart_158497 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_158497 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_158497 prefixEnd_158497 := by exact prefixLift 158497
  have htrace : WordTrace (prefixWord ++ tailWord_158497) baseStart_158497 baseEnd_158497 := by
    simpa [prefixWord, tailWord_158497, baseEnd_158497] using wordTrace_append hprefix tailTrace_158497
  have hstable : (prefixWord ++ tailWord_158497).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_158497).length < 2 ^ (prefixWord ++ tailWord_158497).sum := by decide
  have hdescent : baseEnd_158497 < baseStart_158497 := by decide
  rcases family_descends (prefixWord ++ tailWord_158497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_158518 : List Nat := [5, 1, 2, 2, 3, 1, 1, 1, 2, 4]
def baseStart_158518 : Nat := 118140960795 + 158518 * 2 ^ 59
def prefixEnd_158518 : Nat := 4983230072969 + 3 ^ 40 * 158518 * 2
def baseEnd_158518 : Nat := 54263950926344020863997

theorem tailTrace_158518 : CollatzResearch.WordTrace tailWord_158518 prefixEnd_158518 54263950926344020863997 := by
  unfold tailWord_158518
  simp only [CollatzResearch.WordTrace]
  refine ⟨361351652482739597758763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 3854417626482555709426805 361351652482739597758763)
  ·
    refine ⟨542027478724109396638145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 361351652482739597758763 542027478724109396638145)
    ·
      refine ⟨406520609043082047478609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 542027478724109396638145 406520609043082047478609)
      ·
        refine ⟨304890456782311535608957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 406520609043082047478609 304890456782311535608957)
        ·
          refine ⟨114333921293366825853359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 304890456782311535608957 114333921293366825853359)
          ·
            refine ⟨171500881940050238780039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 114333921293366825853359 171500881940050238780039)
            ·
              refine ⟨257251322910075358170059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 171500881940050238780039 257251322910075358170059)
              ·
                refine ⟨385876984365113037255089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 257251322910075358170059 385876984365113037255089)
                ·
                  refine ⟨289407738273834777941317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 385876984365113037255089 289407738273834777941317)
                  ·
                    refine ⟨54263950926344020863997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 289407738273834777941317 54263950926344020863997)
                    ·
                      rfl

theorem cell22_158518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 3, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 3, 1, 1, 1, 2, 4].length) (baseStart_158518 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_158518 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_158518 prefixEnd_158518 := by exact prefixLift 158518
  have htrace : WordTrace (prefixWord ++ tailWord_158518) baseStart_158518 baseEnd_158518 := by
    simpa [prefixWord, tailWord_158518, baseEnd_158518] using wordTrace_append hprefix tailTrace_158518
  have hstable : (prefixWord ++ tailWord_158518).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_158518).length < 2 ^ (prefixWord ++ tailWord_158518).sum := by decide
  have hdescent : baseEnd_158518 < baseStart_158518 := by decide
  rcases family_descends (prefixWord ++ tailWord_158518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_158587 : List Nat := [1, 1, 1, 1, 1, 5, 3, 2, 4, 3]
def baseStart_158587 : Nat := 118140960795 + 158587 * 2 ^ 59
def prefixEnd_158587 : Nat := 4983230072969 + 3 ^ 40 * 158587 * 2
def baseEnd_158587 : Nat := 54287571036450840888785

theorem tailTrace_158587 : CollatzResearch.WordTrace tailWord_158587 prefixEnd_158587 54287571036450840888785 := by
  unfold tailWord_158587
  simp only [CollatzResearch.WordTrace]
  refine ⟨5784143076473858348402015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3856095384315905565601343 5784143076473858348402015)
  ·
    refine ⟨8676214614710787522603023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5784143076473858348402015 8676214614710787522603023)
    ·
      refine ⟨13014321922066181283904535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8676214614710787522603023 13014321922066181283904535)
      ·
        refine ⟨19521482883099271925856803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13014321922066181283904535 19521482883099271925856803)
        ·
          refine ⟨29282224324648907888785205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19521482883099271925856803 29282224324648907888785205)
          ·
            refine ⟨2745208530435835114573613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 29282224324648907888785205 2745208530435835114573613)
            ·
              refine ⟨1029453198913438167965105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2745208530435835114573613 1029453198913438167965105)
              ·
                refine ⟨772089899185078625973829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1029453198913438167965105 772089899185078625973829)
                ·
                  refine ⟨144766856097202242370093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 772089899185078625973829 144766856097202242370093)
                  ·
                    refine ⟨54287571036450840888785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 144766856097202242370093 54287571036450840888785)
                    ·
                      rfl

theorem cell22_158587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 3, 2, 4, 3].length) (baseStart_158587 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_158587 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_158587 prefixEnd_158587 := by exact prefixLift 158587
  have htrace : WordTrace (prefixWord ++ tailWord_158587) baseStart_158587 baseEnd_158587 := by
    simpa [prefixWord, tailWord_158587, baseEnd_158587] using wordTrace_append hprefix tailTrace_158587
  have hstable : (prefixWord ++ tailWord_158587).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_158587).length < 2 ^ (prefixWord ++ tailWord_158587).sum := by decide
  have hdescent : baseEnd_158587 < baseStart_158587 := by decide
  rcases family_descends (prefixWord ++ tailWord_158587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_158589 : List Nat := [1, 4, 1, 1, 2, 1, 5, 3, 4]
def baseStart_158589 : Nat := 118140960795 + 158589 * 2 ^ 59
def prefixEnd_158589 : Nat := 4983230072969 + 3 ^ 40 * 158589 * 2
def baseEnd_158589 : Nat := 18096085225774500779593

theorem tailTrace_158589 : CollatzResearch.WordTrace tailWord_158589 prefixEnd_158589 18096085225774500779593 := by
  unfold tailWord_158589
  simp only [CollatzResearch.WordTrace]
  refine ⟨5784216022466612689974821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3856144014977741793316547 5784216022466612689974821)
  ·
    refine ⟨1084540504212489879370279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5784216022466612689974821 1084540504212489879370279)
    ·
      refine ⟨1626810756318734819055419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1084540504212489879370279 1626810756318734819055419)
      ·
        refine ⟨2440216134478102228583129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1626810756318734819055419 2440216134478102228583129)
        ·
          refine ⟨1830162100858576671437347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2440216134478102228583129 1830162100858576671437347)
          ·
            refine ⟨2745243151287865007156021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1830162100858576671437347 2745243151287865007156021)
            ·
              refine ⟨257366545433237344420877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2745243151287865007156021 257366545433237344420877)
              ·
                refine ⟨96512454537464004157829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 257366545433237344420877 96512454537464004157829)
                ·
                  refine ⟨18096085225774500779593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 96512454537464004157829 18096085225774500779593)
                  ·
                    rfl

theorem cell22_158589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 5, 3, 4].length) (baseStart_158589 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_158589 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_158589 prefixEnd_158589 := by exact prefixLift 158589
  have htrace : WordTrace (prefixWord ++ tailWord_158589) baseStart_158589 baseEnd_158589 := by
    simpa [prefixWord, tailWord_158589, baseEnd_158589] using wordTrace_append hprefix tailTrace_158589
  have hstable : (prefixWord ++ tailWord_158589).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_158589).length < 2 ^ (prefixWord ++ tailWord_158589).sum := by decide
  have hdescent : baseEnd_158589 < baseStart_158589 := by decide
  rcases family_descends (prefixWord ++ tailWord_158589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_158754 : List Nat := [3, 3, 1, 1, 1, 3, 2, 1, 1, 6]
def baseStart_158754 : Nat := 118140960795 + 158754 * 2 ^ 59
def prefixEnd_158754 : Nat := 4983230072969 + 3 ^ 40 * 158754 * 2
def baseEnd_158754 : Nat := 54344738549318071963273

theorem tailTrace_158754 : CollatzResearch.WordTrace tailWord_158754 prefixEnd_158754 54344738549318071963273 := by
  unfold tailWord_158754
  simp only [CollatzResearch.WordTrace]
  refine ⟨1447558516717211467432829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3860156044579230579820877 1447558516717211467432829)
  ·
    refine ⟨542834443768954300287311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1447558516717211467432829 542834443768954300287311)
    ·
      refine ⟨814251665653431450430967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 542834443768954300287311 814251665653431450430967)
      ·
        refine ⟨1221377498480147175646451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 814251665653431450430967 1221377498480147175646451)
        ·
          refine ⟨1832066247720220763469677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1221377498480147175646451 1832066247720220763469677)
          ·
            refine ⟨687024842895082786301129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1832066247720220763469677 687024842895082786301129)
            ·
              refine ⟨515268632171312089725847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 687024842895082786301129 515268632171312089725847)
              ·
                refine ⟨772902948256968134588771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 515268632171312089725847 772902948256968134588771)
                ·
                  refine ⟨1159354422385452201883157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 772902948256968134588771 1159354422385452201883157)
                  ·
                    refine ⟨54344738549318071963273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1159354422385452201883157 54344738549318071963273)
                    ·
                      rfl

theorem cell22_158754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 2, 1, 1, 6].length) (baseStart_158754 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_158754 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_158754 prefixEnd_158754 := by exact prefixLift 158754
  have htrace : WordTrace (prefixWord ++ tailWord_158754) baseStart_158754 baseEnd_158754 := by
    simpa [prefixWord, tailWord_158754, baseEnd_158754] using wordTrace_append hprefix tailTrace_158754
  have hstable : (prefixWord ++ tailWord_158754).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_158754).length < 2 ^ (prefixWord ++ tailWord_158754).sum := by decide
  have hdescent : baseEnd_158754 < baseStart_158754 := by decide
  rcases family_descends (prefixWord ++ tailWord_158754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_158756 : List Nat := [2, 3, 1, 4, 1, 1, 1, 2, 4, 3]
def baseStart_158756 : Nat := 118140960795 + 158756 * 2 ^ 59
def prefixEnd_158756 : Nat := 4983230072969 + 3 ^ 40 * 158756 * 2
def baseEnd_158756 : Nat := 54345423190190733413267

theorem tailTrace_158756 : CollatzResearch.WordTrace tailWord_158756 prefixEnd_158756 54345423190190733413267 := by
  unfold tailWord_158756
  simp only [CollatzResearch.WordTrace]
  refine ⟨2895153506430800105652061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3860204675241066807536081 2895153506430800105652061)
  ·
    refine ⟨1085682564911550039619523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2895153506430800105652061 1085682564911550039619523)
    ·
      refine ⟨1628523847367325059429285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1085682564911550039619523 1628523847367325059429285)
      ·
        refine ⟨305348221381373448642991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1628523847367325059429285 305348221381373448642991)
        ·
          refine ⟨458022332072060172964487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 305348221381373448642991 458022332072060172964487)
          ·
            refine ⟨687033498108090259446731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 458022332072060172964487 687033498108090259446731)
            ·
              refine ⟨1030550247162135389170097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 687033498108090259446731 1030550247162135389170097)
              ·
                refine ⟨772912685371601541877573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1030550247162135389170097 772912685371601541877573)
                ·
                  refine ⟨144921128507175289102045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 772912685371601541877573 144921128507175289102045)
                  ·
                    refine ⟨54345423190190733413267, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 144921128507175289102045 54345423190190733413267)
                    ·
                      rfl

theorem cell22_158756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 1, 2, 4, 3].length) (baseStart_158756 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_158756 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_158756 prefixEnd_158756 := by exact prefixLift 158756
  have htrace : WordTrace (prefixWord ++ tailWord_158756) baseStart_158756 baseEnd_158756 := by
    simpa [prefixWord, tailWord_158756, baseEnd_158756] using wordTrace_append hprefix tailTrace_158756
  have hstable : (prefixWord ++ tailWord_158756).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_158756).length < 2 ^ (prefixWord ++ tailWord_158756).sum := by decide
  have hdescent : baseEnd_158756 < baseStart_158756 := by decide
  rcases family_descends (prefixWord ++ tailWord_158756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_158790 : List Nat := [6, 1, 1, 1, 1, 3, 1, 3, 2, 3]
def baseStart_158790 : Nat := 118140960795 + 158790 * 2 ^ 59
def prefixEnd_158790 : Nat := 4983230072969 + 3 ^ 40 * 158790 * 2
def baseEnd_158790 : Nat := 54357062085025978063163

theorem tailTrace_158790 : CollatzResearch.WordTrace tailWord_158790 prefixEnd_158790 54357062085025978063163 := by
  unfold tailWord_158790
  simp only [CollatzResearch.WordTrace]
  refine ⟨180985846710575750563807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 3861031396492282678694549 180985846710575750563807)
  ·
    refine ⟨271478770065863625845711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 180985846710575750563807 271478770065863625845711)
    ·
      refine ⟨407218155098795438768567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 271478770065863625845711 407218155098795438768567)
      ·
        refine ⟨610827232648193158152851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 407218155098795438768567 610827232648193158152851)
        ·
          refine ⟨916240848972289737229277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 610827232648193158152851 916240848972289737229277)
          ·
            refine ⟨343590318364608651460979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 916240848972289737229277 343590318364608651460979)
            ·
              refine ⟨515385477546912977191469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 343590318364608651460979 515385477546912977191469)
              ·
                refine ⟨193269554080092366446801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 515385477546912977191469 193269554080092366446801)
                ·
                  refine ⟨144952165560069274835101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 193269554080092366446801 144952165560069274835101)
                  ·
                    refine ⟨54357062085025978063163, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 144952165560069274835101 54357062085025978063163)
                    ·
                      rfl

theorem cell22_158790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 3, 1, 3, 2, 3].length) (baseStart_158790 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_158790 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_158790 prefixEnd_158790 := by exact prefixLift 158790
  have htrace : WordTrace (prefixWord ++ tailWord_158790) baseStart_158790 baseEnd_158790 := by
    simpa [prefixWord, tailWord_158790, baseEnd_158790] using wordTrace_append hprefix tailTrace_158790
  have hstable : (prefixWord ++ tailWord_158790).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_158790).length < 2 ^ (prefixWord ++ tailWord_158790).sum := by decide
  have hdescent : baseEnd_158790 < baseStart_158790 := by decide
  rcases family_descends (prefixWord ++ tailWord_158790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_158844 : List Nat := [2, 2, 2, 1, 1, 3, 1, 1, 5, 4]
def baseStart_158844 : Nat := 118140960795 + 158844 * 2 ^ 59
def prefixEnd_158844 : Nat := 4983230072969 + 3 ^ 40 * 158844 * 2
def baseEnd_158844 : Nat := 54375547388587837212997

theorem tailTrace_158844 : CollatzResearch.WordTrace tailWord_158844 prefixEnd_158844 54375547388587837212997 := by
  unfold tailWord_158844
  simp only [CollatzResearch.WordTrace]
  refine ⟨2896758318271395620253793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3862344424361860827005057 2896758318271395620253793)
  ·
    refine ⟨2172568738703546715190345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2896758318271395620253793 2172568738703546715190345)
    ·
      refine ⟨1629426554027660036392759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2172568738703546715190345 1629426554027660036392759)
      ·
        refine ⟨2444139831041490054589139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1629426554027660036392759 2444139831041490054589139)
        ·
          refine ⟨3666209746562235081883709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2444139831041490054589139 3666209746562235081883709)
          ·
            refine ⟨1374828654960838155706391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3666209746562235081883709 1374828654960838155706391)
            ·
              refine ⟨2062242982441257233559587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1374828654960838155706391 2062242982441257233559587)
              ·
                refine ⟨3093364473661885850339381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2062242982441257233559587 3093364473661885850339381)
                ·
                  refine ⟨290002919405801798469317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3093364473661885850339381 290002919405801798469317)
                  ·
                    refine ⟨54375547388587837212997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 290002919405801798469317 54375547388587837212997)
                    ·
                      rfl

theorem cell22_158844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 1, 1, 5, 4].length) (baseStart_158844 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_158844 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_158844 prefixEnd_158844 := by exact prefixLift 158844
  have htrace : WordTrace (prefixWord ++ tailWord_158844) baseStart_158844 baseEnd_158844 := by
    simpa [prefixWord, tailWord_158844, baseEnd_158844] using wordTrace_append hprefix tailTrace_158844
  have hstable : (prefixWord ++ tailWord_158844).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_158844).length < 2 ^ (prefixWord ++ tailWord_158844).sum := by decide
  have hdescent : baseEnd_158844 < baseStart_158844 := by decide
  rcases family_descends (prefixWord ++ tailWord_158844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_158893 : List Nat := [1, 5, 2, 1, 3, 1, 2, 1, 6]
def baseStart_158893 : Nat := 118140960795 + 158893 * 2 ^ 59
def prefixEnd_158893 : Nat := 4983230072969 + 3 ^ 40 * 158893 * 2
def baseEnd_158893 : Nat := 18130773696656014245949

theorem tailTrace_158893 : CollatzResearch.WordTrace tailWord_158893 prefixEnd_158893 18130773696656014245949 := by
  unfold tailWord_158893
  simp only [CollatzResearch.WordTrace]
  refine ⟨5795303813365272609041333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3863535875576848406027555 5795303813365272609041333)
  ·
    refine ⟨543309732502994307097625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 5795303813365272609041333 543309732502994307097625)
    ·
      refine ⟨407482299377245730323219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 543309732502994307097625 407482299377245730323219)
      ·
        refine ⟨611223449065868595484829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 407482299377245730323219 611223449065868595484829)
        ·
          refine ⟨229208793399700723306811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 611223449065868595484829 229208793399700723306811)
          ·
            refine ⟨343813190099551084960217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 229208793399700723306811 343813190099551084960217)
            ·
              refine ⟨257859892574663313720163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 343813190099551084960217 257859892574663313720163)
              ·
                refine ⟨386789838861994970580245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 257859892574663313720163 386789838861994970580245)
                ·
                  refine ⟨18130773696656014245949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 386789838861994970580245 18130773696656014245949)
                  ·
                    rfl

theorem cell22_158893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 1, 2, 1, 6].length) (baseStart_158893 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_158893 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_158893 prefixEnd_158893 := by exact prefixLift 158893
  have htrace : WordTrace (prefixWord ++ tailWord_158893) baseStart_158893 baseEnd_158893 := by
    simpa [prefixWord, tailWord_158893, baseEnd_158893] using wordTrace_append hprefix tailTrace_158893
  have hstable : (prefixWord ++ tailWord_158893).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_158893).length < 2 ^ (prefixWord ++ tailWord_158893).sum := by decide
  have hdescent : baseEnd_158893 < baseStart_158893 := by decide
  rcases family_descends (prefixWord ++ tailWord_158893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_158908 : List Nat := [2, 2, 2, 3, 2, 3, 1, 1, 1, 5]
def baseStart_158908 : Nat := 118140960795 + 158908 * 2 ^ 59
def prefixEnd_158908 : Nat := 4983230072969 + 3 ^ 40 * 158908 * 2
def baseEnd_158908 : Nat := 54397455896513003612801

theorem tailTrace_158908 : CollatzResearch.WordTrace tailWord_158908 prefixEnd_158908 54397455896513003612801 := by
  unfold tailWord_158908
  simp only [CollatzResearch.WordTrace]
  refine ⟨2897925454155465085418689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3863900605540620113891585 2897925454155465085418689)
  ·
    refine ⟨2173444090616598814064017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2897925454155465085418689 2173444090616598814064017)
    ·
      refine ⟨1630083067962449110548013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2173444090616598814064017 1630083067962449110548013)
      ·
        refine ⟨611281150485918416455505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1630083067962449110548013 611281150485918416455505)
        ·
          refine ⟨458460862864438812341629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 611281150485918416455505 458460862864438812341629)
          ·
            refine ⟨171922823574164554628111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 458460862864438812341629 171922823574164554628111)
            ·
              refine ⟨257884235361246831942167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 171922823574164554628111 257884235361246831942167)
              ·
                refine ⟨386826353041870247913251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 257884235361246831942167 386826353041870247913251)
                ·
                  refine ⟨580239529562805371869877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 386826353041870247913251 580239529562805371869877)
                  ·
                    refine ⟨54397455896513003612801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 580239529562805371869877 54397455896513003612801)
                    ·
                      rfl

theorem cell22_158908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 3, 1, 1, 1, 5].length) (baseStart_158908 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_158908 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_158908 prefixEnd_158908 := by exact prefixLift 158908
  have htrace : WordTrace (prefixWord ++ tailWord_158908) baseStart_158908 baseEnd_158908 := by
    simpa [prefixWord, tailWord_158908, baseEnd_158908] using wordTrace_append hprefix tailTrace_158908
  have hstable : (prefixWord ++ tailWord_158908).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_158908).length < 2 ^ (prefixWord ++ tailWord_158908).sum := by decide
  have hdescent : baseEnd_158908 < baseStart_158908 := by decide
  rcases family_descends (prefixWord ++ tailWord_158908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_159028 : List Nat := [2, 5, 1, 1, 1, 1, 3, 2, 6]
def baseStart_159028 : Nat := 118140960795 + 159028 * 2 ^ 59
def prefixEnd_159028 : Nat := 4983230072969 + 3 ^ 40 * 159028 * 2
def baseEnd_159028 : Nat := 18146178116290896870811

theorem tailTrace_159028 : CollatzResearch.WordTrace tailWord_159028 prefixEnd_159028 18146178116290896870811 := by
  unfold tailWord_159028
  simp only [CollatzResearch.WordTrace]
  refine ⟨2900113833938095332602869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3866818445250793776803825 2900113833938095332602869)
  ·
    refine ⟨271885671931696437431519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 2900113833938095332602869 271885671931696437431519)
    ·
      refine ⟨407828507897544656147279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 271885671931696437431519 407828507897544656147279)
      ·
        refine ⟨611742761846316984220919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 407828507897544656147279 611742761846316984220919)
        ·
          refine ⟨917614142769475476331379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 611742761846316984220919 917614142769475476331379)
          ·
            refine ⟨1376421214154213214497069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 917614142769475476331379 1376421214154213214497069)
            ·
              refine ⟨516157955307829955436401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1376421214154213214497069 516157955307829955436401)
              ·
                refine ⟨387118466480872466577301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 516157955307829955436401 387118466480872466577301)
                ·
                  refine ⟨18146178116290896870811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 387118466480872466577301 18146178116290896870811)
                  ·
                    rfl

theorem cell22_159028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 3, 2, 6].length) (baseStart_159028 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_159028 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_159028 prefixEnd_159028 := by exact prefixLift 159028
  have htrace : WordTrace (prefixWord ++ tailWord_159028) baseStart_159028 baseEnd_159028 := by
    simpa [prefixWord, tailWord_159028, baseEnd_159028] using wordTrace_append hprefix tailTrace_159028
  have hstable : (prefixWord ++ tailWord_159028).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_159028).length < 2 ^ (prefixWord ++ tailWord_159028).sum := by decide
  have hdescent : baseEnd_159028 < baseStart_159028 := by decide
  rcases family_descends (prefixWord ++ tailWord_159028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_159088 : List Nat := [2, 1, 1, 1, 4, 2, 1, 4, 3, 3]
def baseStart_159088 : Nat := 118140960795 + 159088 * 2 ^ 59
def prefixEnd_159088 : Nat := 4983230072969 + 3 ^ 40 * 159088 * 2
def baseEnd_159088 : Nat := 54459073575052534112249

theorem tailTrace_159088 : CollatzResearch.WordTrace tailWord_159088 prefixEnd_159088 54459073575052534112249 := by
  unfold tailWord_159088
  simp only [CollatzResearch.WordTrace]
  refine ⟨2901208023829410456194959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3868277365105880608259945 2901208023829410456194959)
  ·
    refine ⟨4351812035744115684292439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2901208023829410456194959 4351812035744115684292439)
    ·
      refine ⟨6527718053616173526438659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4351812035744115684292439 6527718053616173526438659)
      ·
        refine ⟨9791577080424260289657989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6527718053616173526438659 9791577080424260289657989)
        ·
          refine ⟨1835920702579548804310873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9791577080424260289657989 1835920702579548804310873)
          ·
            refine ⟨1376940526934661603233155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1835920702579548804310873 1376940526934661603233155)
            ·
              refine ⟨2065410790401992404849733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1376940526934661603233155 2065410790401992404849733)
              ·
                refine ⟨387264523200373575909325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2065410790401992404849733 387264523200373575909325)
                ·
                  refine ⟨145224196200140090965997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 387264523200373575909325 145224196200140090965997)
                  ·
                    refine ⟨54459073575052534112249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 145224196200140090965997 54459073575052534112249)
                    ·
                      rfl

theorem cell22_159088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 1, 4, 3, 3].length) (baseStart_159088 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_159088 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_159088 prefixEnd_159088 := by exact prefixLift 159088
  have htrace : WordTrace (prefixWord ++ tailWord_159088) baseStart_159088 baseEnd_159088 := by
    simpa [prefixWord, tailWord_159088, baseEnd_159088] using wordTrace_append hprefix tailTrace_159088
  have hstable : (prefixWord ++ tailWord_159088).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_159088).length < 2 ^ (prefixWord ++ tailWord_159088).sum := by decide
  have hdescent : baseEnd_159088 < baseStart_159088 := by decide
  rcases family_descends (prefixWord ++ tailWord_159088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_159101 : List Nat := [1, 4, 1, 1, 2, 2, 1, 1, 9]
def baseStart_159101 : Nat := 118140960795 + 159101 * 2 ^ 59
def prefixEnd_159101 : Nat := 4983230072969 + 3 ^ 40 * 159101 * 2
def baseEnd_159101 : Nat := 18154507913574944512403

theorem tailTrace_159101 : CollatzResearch.WordTrace tailWord_159101 prefixEnd_159101 18154507913574944512403 := by
  unfold tailWord_159101
  simp only [CollatzResearch.WordTrace]
  refine ⟨5802890196611724132613157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3868593464407816088408771 5802890196611724132613157)
  ·
    refine ⟨1088041911864698274864967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5802890196611724132613157 1088041911864698274864967)
    ·
      refine ⟨1632062867797047412297451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1088041911864698274864967 1632062867797047412297451)
      ·
        refine ⟨2448094301695571118446177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1632062867797047412297451 2448094301695571118446177)
        ·
          refine ⟨1836070726271678338834633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2448094301695571118446177 1836070726271678338834633)
          ·
            refine ⟨1377053044703758754125975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1836070726271678338834633 1377053044703758754125975)
            ·
              refine ⟨2065579567055638131188963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1377053044703758754125975 2065579567055638131188963)
              ·
                refine ⟨3098369350583457196783445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2065579567055638131188963 3098369350583457196783445)
                ·
                  refine ⟨18154507913574944512403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 3098369350583457196783445 18154507913574944512403)
                  ·
                    rfl

theorem cell22_159101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 1, 1, 9].length) (baseStart_159101 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_159101 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_159101 prefixEnd_159101 := by exact prefixLift 159101
  have htrace : WordTrace (prefixWord ++ tailWord_159101) baseStart_159101 baseEnd_159101 := by
    simpa [prefixWord, tailWord_159101, baseEnd_159101] using wordTrace_append hprefix tailTrace_159101
  have hstable : (prefixWord ++ tailWord_159101).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_159101).length < 2 ^ (prefixWord ++ tailWord_159101).sum := by decide
  have hdescent : baseEnd_159101 < baseStart_159101 := by decide
  rcases family_descends (prefixWord ++ tailWord_159101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_159135 : List Nat := [1, 1, 2, 5, 1, 2, 4, 1, 5]
def baseStart_159135 : Nat := 118140960795 + 159135 * 2 ^ 59
def prefixEnd_159135 : Nat := 4983230072969 + 3 ^ 40 * 159135 * 2
def baseEnd_159135 : Nat := 18158387545186692729035

theorem tailTrace_159135 : CollatzResearch.WordTrace tailWord_159135 prefixEnd_159135 18158387545186692729035 := by
  unfold tailWord_159135
  simp only [CollatzResearch.WordTrace]
  refine ⟨5804130278488547939350859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3869420185659031959567239 5804130278488547939350859)
  ·
    refine ⟨8706195417732821909026289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5804130278488547939350859 8706195417732821909026289)
    ·
      refine ⟨6529646563299616431769717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8706195417732821909026289 6529646563299616431769717)
      ·
        refine ⟨612154365309339040478411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 6529646563299616431769717 612154365309339040478411)
        ·
          refine ⟨918231547964008560717617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 612154365309339040478411 918231547964008560717617)
          ·
            refine ⟨688673660973006420538213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 918231547964008560717617 688673660973006420538213)
            ·
              refine ⟨129126311432438703850915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 688673660973006420538213 129126311432438703850915)
              ·
                refine ⟨193689467148658055776373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 129126311432438703850915 193689467148658055776373)
                ·
                  refine ⟨18158387545186692729035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 193689467148658055776373 18158387545186692729035)
                  ·
                    rfl

theorem cell22_159135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 4, 1, 5].length) (baseStart_159135 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_159135 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_159135 prefixEnd_159135 := by exact prefixLift 159135
  have htrace : WordTrace (prefixWord ++ tailWord_159135) baseStart_159135 baseEnd_159135 := by
    simpa [prefixWord, tailWord_159135, baseEnd_159135] using wordTrace_append hprefix tailTrace_159135
  have hstable : (prefixWord ++ tailWord_159135).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_159135).length < 2 ^ (prefixWord ++ tailWord_159135).sum := by decide
  have hdescent : baseEnd_159135 < baseStart_159135 := by decide
  rcases family_descends (prefixWord ++ tailWord_159135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_159210 : List Nat := [3, 1, 3, 1, 4, 1, 1, 1, 1, 6]
def baseStart_159210 : Nat := 118140960795 + 159210 * 2 ^ 59
def prefixEnd_159210 : Nat := 4983230072969 + 3 ^ 40 * 159210 * 2
def baseEnd_159210 : Nat := 54500836668284882561875

theorem tailTrace_159210 : CollatzResearch.WordTrace tailWord_159210 prefixEnd_159210 54500836668284882561875 := by
  unfold tailWord_159210
  simp only [CollatzResearch.WordTrace]
  refine ⟨1451716438304208937082771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3871243835477890498887389 1451716438304208937082771)
  ·
    refine ⟨2177574657456313405624157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1451716438304208937082771 2177574657456313405624157)
    ·
      refine ⟨816590496546117527109059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2177574657456313405624157 816590496546117527109059)
      ·
        refine ⟨1224885744819176290663589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 816590496546117527109059 1224885744819176290663589)
        ·
          refine ⟨229666077153595554499423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1224885744819176290663589 229666077153595554499423)
          ·
            refine ⟨344499115730393331749135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 229666077153595554499423 344499115730393331749135)
            ·
              refine ⟨516748673595589997623703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 344499115730393331749135 516748673595589997623703)
              ·
                refine ⟨775123010393384996435555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 516748673595589997623703 775123010393384996435555)
                ·
                  refine ⟨1162684515590077494653333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 775123010393384996435555 1162684515590077494653333)
                  ·
                    refine ⟨54500836668284882561875, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1162684515590077494653333 54500836668284882561875)
                    ·
                      rfl

theorem cell22_159210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 1, 1, 1, 1, 6].length) (baseStart_159210 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_159210 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_159210 prefixEnd_159210 := by exact prefixLift 159210
  have htrace : WordTrace (prefixWord ++ tailWord_159210) baseStart_159210 baseEnd_159210 := by
    simpa [prefixWord, tailWord_159210, baseEnd_159210] using wordTrace_append hprefix tailTrace_159210
  have hstable : (prefixWord ++ tailWord_159210).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_159210).length < 2 ^ (prefixWord ++ tailWord_159210).sum := by decide
  have hdescent : baseEnd_159210 < baseStart_159210 := by decide
  rcases family_descends (prefixWord ++ tailWord_159210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_159240 : List Nat := [2, 1, 3, 2, 1, 1, 3, 3, 3, 3]
def baseStart_159240 : Nat := 118140960795 + 159240 * 2 ^ 59
def prefixEnd_159240 : Nat := 4983230072969 + 3 ^ 40 * 159240 * 2
def baseEnd_159240 : Nat := 54511106281374804311783

theorem tailTrace_159240 : CollatzResearch.WordTrace tailWord_159240 prefixEnd_159240 54511106281374804311783 := by
  unfold tailWord_159240
  simp only [CollatzResearch.WordTrace]
  refine ⟨2903979971554075435961587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3871973295405433914615449 2903979971554075435961587)
  ·
    refine ⟨4355969957331113153942381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2903979971554075435961587 4355969957331113153942381)
    ·
      refine ⟨1633488733999167432728393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4355969957331113153942381 1633488733999167432728393)
      ·
        refine ⟨1225116550499375574546295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1633488733999167432728393 1225116550499375574546295)
        ·
          refine ⟨1837674825749063361819443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1225116550499375574546295 1837674825749063361819443)
          ·
            refine ⟨2756512238623595042729165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1837674825749063361819443 2756512238623595042729165)
            ·
              refine ⟨1033692089483848141023437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2756512238623595042729165 1033692089483848141023437)
              ·
                refine ⟨387634533556443052883789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1033692089483848141023437 387634533556443052883789)
                ·
                  refine ⟨145362950083666144831421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 387634533556443052883789 145362950083666144831421)
                  ·
                    refine ⟨54511106281374804311783, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 145362950083666144831421 54511106281374804311783)
                    ·
                      rfl

theorem cell22_159240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 3, 3, 3, 3].length) (baseStart_159240 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_159240 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_159240 prefixEnd_159240 := by exact prefixLift 159240
  have htrace : WordTrace (prefixWord ++ tailWord_159240) baseStart_159240 baseEnd_159240 := by
    simpa [prefixWord, tailWord_159240, baseEnd_159240] using wordTrace_append hprefix tailTrace_159240
  have hstable : (prefixWord ++ tailWord_159240).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_159240).length < 2 ^ (prefixWord ++ tailWord_159240).sum := by decide
  have hdescent : baseEnd_159240 < baseStart_159240 := by decide
  rcases family_descends (prefixWord ++ tailWord_159240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_159349 : List Nat := [1, 3, 4, 2, 1, 2, 1, 4, 4]
def baseStart_159349 : Nat := 118140960795 + 159349 * 2 ^ 59
def prefixEnd_159349 : Nat := 4983230072969 + 3 ^ 40 * 159349 * 2
def baseEnd_159349 : Nat := 18182806402978284445483

theorem tailTrace_159349 : CollatzResearch.WordTrace tailWord_159349 prefixEnd_159349 18182806402978284445483 := by
  unfold tailWord_159349
  simp only [CollatzResearch.WordTrace]
  refine ⟨5811935499713262487641101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3874623666475508325094067 5811935499713262487641101)
  ·
    refine ⟨2179475812392473432865413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5811935499713262487641101 2179475812392473432865413)
    ·
      refine ⟨408651714823588768662265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2179475812392473432865413 408651714823588768662265)
      ·
        refine ⟨306488786117691576496699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 408651714823588768662265 306488786117691576496699)
        ·
          refine ⟨459733179176537364745049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 306488786117691576496699 459733179176537364745049)
          ·
            refine ⟨344799884382403023558787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 459733179176537364745049 344799884382403023558787)
            ·
              refine ⟨517199826573604535338181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 344799884382403023558787 517199826573604535338181)
              ·
                refine ⟨96974967482550850375909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 517199826573604535338181 96974967482550850375909)
                ·
                  refine ⟨18182806402978284445483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 96974967482550850375909 18182806402978284445483)
                  ·
                    rfl

theorem cell22_159349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 2, 1, 4, 4].length) (baseStart_159349 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_159349 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_159349 prefixEnd_159349 := by exact prefixLift 159349
  have htrace : WordTrace (prefixWord ++ tailWord_159349) baseStart_159349 baseEnd_159349 := by
    simpa [prefixWord, tailWord_159349, baseEnd_159349] using wordTrace_append hprefix tailTrace_159349
  have hstable : (prefixWord ++ tailWord_159349).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_159349).length < 2 ^ (prefixWord ++ tailWord_159349).sum := by decide
  have hdescent : baseEnd_159349 < baseStart_159349 := by decide
  rcases family_descends (prefixWord ++ tailWord_159349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_159435 : List Nat := [1, 1, 1, 1, 3, 2, 1, 5, 3, 4]
def baseStart_159435 : Nat := 118140960795 + 159435 * 2 ^ 59
def prefixEnd_159435 : Nat := 4983230072969 + 3 ^ 40 * 159435 * 2
def baseEnd_159435 : Nat := 54577858766459295686185

theorem tailTrace_159435 : CollatzResearch.WordTrace tailWord_159435 prefixEnd_159435 54577858766459295686185 := by
  unfold tailWord_159435
  simp only [CollatzResearch.WordTrace]
  refine ⟨5815072177401699175271759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3876714784934466116847839 5815072177401699175271759)
  ·
    refine ⟨8722608266102548762907639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5815072177401699175271759 8722608266102548762907639)
    ·
      refine ⟨13083912399153823144361459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8722608266102548762907639 13083912399153823144361459)
      ·
        refine ⟨19625868598730734716542189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13083912399153823144361459 19625868598730734716542189)
        ·
          refine ⟨7359700724524025518703321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19625868598730734716542189 7359700724524025518703321)
          ·
            refine ⟨5519775543393019139027491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7359700724524025518703321 5519775543393019139027491)
            ·
              refine ⟨8279663315089528708541237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5519775543393019139027491 8279663315089528708541237)
              ·
                refine ⟨776218435789643316425741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8279663315089528708541237 776218435789643316425741)
                ·
                  refine ⟨291081913421116243659653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 776218435789643316425741 291081913421116243659653)
                  ·
                    refine ⟨54577858766459295686185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 291081913421116243659653 54577858766459295686185)
                    ·
                      rfl

theorem cell22_159435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 5, 3, 4].length) (baseStart_159435 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_159435 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_159435 prefixEnd_159435 := by exact prefixLift 159435
  have htrace : WordTrace (prefixWord ++ tailWord_159435) baseStart_159435 baseEnd_159435 := by
    simpa [prefixWord, tailWord_159435, baseEnd_159435] using wordTrace_append hprefix tailTrace_159435
  have hstable : (prefixWord ++ tailWord_159435).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_159435).length < 2 ^ (prefixWord ++ tailWord_159435).sum := by decide
  have hdescent : baseEnd_159435 < baseStart_159435 := by decide
  rcases family_descends (prefixWord ++ tailWord_159435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_159467 : List Nat := [1, 1, 1, 1, 2, 4, 2, 6, 4]
def baseStart_159467 : Nat := 118140960795 + 159467 * 2 ^ 59
def prefixEnd_159467 : Nat := 4983230072969 + 3 ^ 40 * 159467 * 2
def baseEnd_159467 : Nat := 18196271006807292962029

theorem tailTrace_159467 : CollatzResearch.WordTrace tailWord_159467 prefixEnd_159467 18196271006807292962029 := by
  unfold tailWord_159467
  simp only [CollatzResearch.WordTrace]
  refine ⟨5816239313285768640436655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3877492875523845760291103 5816239313285768640436655)
  ·
    refine ⟨8724358969928652960654983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5816239313285768640436655 8724358969928652960654983)
    ·
      refine ⟨13086538454892979440982475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8724358969928652960654983 13086538454892979440982475)
      ·
        refine ⟨19629807682339469161473713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13086538454892979440982475 19629807682339469161473713)
        ·
          refine ⟨14722355761754601871105285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19629807682339469161473713 14722355761754601871105285)
          ·
            refine ⟨2760441705328987850832241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14722355761754601871105285 2760441705328987850832241)
            ·
              refine ⟨2070331278996740888124181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2760441705328987850832241 2070331278996740888124181)
              ·
                refine ⟨97046778702972229130821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2070331278996740888124181 97046778702972229130821)
                ·
                  refine ⟨18196271006807292962029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 97046778702972229130821 18196271006807292962029)
                  ·
                    rfl

theorem cell22_159467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 2, 6, 4].length) (baseStart_159467 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_159467 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_159467 prefixEnd_159467 := by exact prefixLift 159467
  have htrace : WordTrace (prefixWord ++ tailWord_159467) baseStart_159467 baseEnd_159467 := by
    simpa [prefixWord, tailWord_159467, baseEnd_159467] using wordTrace_append hprefix tailTrace_159467
  have hstable : (prefixWord ++ tailWord_159467).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_159467).length < 2 ^ (prefixWord ++ tailWord_159467).sum := by decide
  have hdescent : baseEnd_159467 < baseStart_159467 := by decide
  rcases family_descends (prefixWord ++ tailWord_159467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_159480 : List Nat := [2, 1, 2, 1, 1, 2, 2, 4, 1, 6]
def baseStart_159480 : Nat := 118140960795 + 159480 * 2 ^ 59
def prefixEnd_159480 : Nat := 4983230072969 + 3 ^ 40 * 159480 * 2
def baseEnd_159480 : Nat := 54593263186094178311047

theorem tailTrace_159480 : CollatzResearch.WordTrace tailWord_159480 prefixEnd_159480 54593263186094178311047 := by
  unfold tailWord_159480
  simp only [CollatzResearch.WordTrace]
  refine ⟨2908356731119335930329947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3877808974825781240439929 2908356731119335930329947)
  ·
    refine ⟨4362535096679003895494921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2908356731119335930329947 4362535096679003895494921)
    ·
      refine ⟨3271901322509252921621191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4362535096679003895494921 3271901322509252921621191)
      ·
        refine ⟨4907851983763879382431787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3271901322509252921621191 4907851983763879382431787)
        ·
          refine ⟨7361777975645819073647681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4907851983763879382431787 7361777975645819073647681)
          ·
            refine ⟨5521333481734364305235761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7361777975645819073647681 5521333481734364305235761)
            ·
              refine ⟨4141000111300773228926821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5521333481734364305235761 4141000111300773228926821)
              ·
                refine ⟨776437520868894980423779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4141000111300773228926821 776437520868894980423779)
                ·
                  refine ⟨1164656281303342470635669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 776437520868894980423779 1164656281303342470635669)
                  ·
                    refine ⟨54593263186094178311047, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1164656281303342470635669 54593263186094178311047)
                    ·
                      rfl

theorem cell22_159480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 4, 1, 6].length) (baseStart_159480 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_159480 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_159480 prefixEnd_159480 := by exact prefixLift 159480
  have htrace : WordTrace (prefixWord ++ tailWord_159480) baseStart_159480 baseEnd_159480 := by
    simpa [prefixWord, tailWord_159480, baseEnd_159480] using wordTrace_append hprefix tailTrace_159480
  have hstable : (prefixWord ++ tailWord_159480).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_159480).length < 2 ^ (prefixWord ++ tailWord_159480).sum := by decide
  have hdescent : baseEnd_159480 < baseStart_159480 := by decide
  rcases family_descends (prefixWord ++ tailWord_159480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_159544 : List Nat := [2, 1, 2, 1, 3, 4, 1, 2, 3, 3]
def baseStart_159544 : Nat := 118140960795 + 159544 * 2 ^ 59
def prefixEnd_159544 : Nat := 4983230072969 + 3 ^ 40 * 159544 * 2
def baseEnd_159544 : Nat := 54615171694019344710851

theorem tailTrace_159544 : CollatzResearch.WordTrace tailWord_159544 prefixEnd_159544 54615171694019344710851 := by
  unfold tailWord_159544
  simp only [CollatzResearch.WordTrace]
  refine ⟨2909523867003405395494843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3879365156004540527326457 2909523867003405395494843)
  ·
    refine ⟨4364285800505108093242265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2909523867003405395494843 4364285800505108093242265)
    ·
      refine ⟨3273214350378831069931699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4364285800505108093242265 3273214350378831069931699)
      ·
        refine ⟨4909821525568246604897549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3273214350378831069931699 4909821525568246604897549)
        ·
          refine ⟨1841183072088092476836581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4909821525568246604897549 1841183072088092476836581)
          ·
            refine ⟨345221826016517339406859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1841183072088092476836581 345221826016517339406859)
            ·
              refine ⟨517832739024776009110289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 345221826016517339406859 517832739024776009110289)
              ·
                refine ⟨388374554268582006832717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 517832739024776009110289 388374554268582006832717)
                ·
                  refine ⟨145640457850718252562269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 388374554268582006832717 145640457850718252562269)
                  ·
                    refine ⟨54615171694019344710851, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 145640457850718252562269 54615171694019344710851)
                    ·
                      rfl

theorem cell22_159544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 4, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 4, 1, 2, 3, 3].length) (baseStart_159544 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_159544 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_159544 prefixEnd_159544 := by exact prefixLift 159544
  have htrace : WordTrace (prefixWord ++ tailWord_159544) baseStart_159544 baseEnd_159544 := by
    simpa [prefixWord, tailWord_159544, baseEnd_159544] using wordTrace_append hprefix tailTrace_159544
  have hstable : (prefixWord ++ tailWord_159544).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_159544).length < 2 ^ (prefixWord ++ tailWord_159544).sum := by decide
  have hdescent : baseEnd_159544 < baseStart_159544 := by decide
  rcases family_descends (prefixWord ++ tailWord_159544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_159561 : List Nat := [1, 2, 1, 1, 2, 4, 4, 3, 1, 3]
def baseStart_159561 : Nat := 118140960795 + 159561 * 2 ^ 59
def prefixEnd_159561 : Nat := 4983230072969 + 3 ^ 40 * 159561 * 2
def baseEnd_159561 : Nat := 54620991141436967035799

theorem tailTrace_159561 : CollatzResearch.WordTrace tailWord_159561 prefixEnd_159561 54620991141436967035799 := by
  unfold tailWord_159561
  simp only [CollatzResearch.WordTrace]
  refine ⟨5819667774945222694358537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3879778516630148462905691 5819667774945222694358537)
  ·
    refine ⟨4364750831208917020768903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5819667774945222694358537 4364750831208917020768903)
    ·
      refine ⟨6547126246813375531153355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4364750831208917020768903 6547126246813375531153355)
      ·
        refine ⟨9820689370220063296730033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6547126246813375531153355 9820689370220063296730033)
        ·
          refine ⟨7365517027665047472547525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9820689370220063296730033 7365517027665047472547525)
          ·
            refine ⟨1381034442687196401102661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7365517027665047472547525 1381034442687196401102661)
            ·
              refine ⟨258943958003849325206749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1381034442687196401102661 258943958003849325206749)
              ·
                refine ⟨97103984251443496952531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 258943958003849325206749 97103984251443496952531)
                ·
                  refine ⟨145655976377165245428797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 97103984251443496952531 145655976377165245428797)
                  ·
                    refine ⟨54620991141436967035799, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 145655976377165245428797 54620991141436967035799)
                    ·
                      rfl

theorem cell22_159561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 4, 3, 1, 3].length) (baseStart_159561 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_159561 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_159561 prefixEnd_159561 := by exact prefixLift 159561
  have htrace : WordTrace (prefixWord ++ tailWord_159561) baseStart_159561 baseEnd_159561 := by
    simpa [prefixWord, tailWord_159561, baseEnd_159561] using wordTrace_append hprefix tailTrace_159561
  have hstable : (prefixWord ++ tailWord_159561).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_159561).length < 2 ^ (prefixWord ++ tailWord_159561).sum := by decide
  have hdescent : baseEnd_159561 < baseStart_159561 := by decide
  rcases family_descends (prefixWord ++ tailWord_159561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_159632 : List Nat := [2, 1, 1, 1, 1, 1, 2, 5, 4, 4]
def baseStart_159632 : Nat := 118140960795 + 159632 * 2 ^ 59
def prefixEnd_159632 : Nat := 4983230072969 + 3 ^ 40 * 159632 * 2
def baseEnd_159632 : Nat := 54645295892416448510581

theorem tailTrace_159632 : CollatzResearch.WordTrace tailWord_159632 prefixEnd_159632 54645295892416448510581 := by
  unfold tailWord_159632
  simp only [CollatzResearch.WordTrace]
  refine ⟨2911128678844000910096575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3881504905125334546795433 2911128678844000910096575)
  ·
    refine ⟨4366693018266001365144863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2911128678844000910096575 4366693018266001365144863)
    ·
      refine ⟨6550039527399002047717295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4366693018266001365144863 6550039527399002047717295)
      ·
        refine ⟨9825059291098503071575943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6550039527399002047717295 9825059291098503071575943)
        ·
          refine ⟨14737588936647754607363915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9825059291098503071575943 14737588936647754607363915)
          ·
            refine ⟨22106383404971631911045873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14737588936647754607363915 22106383404971631911045873)
            ·
              refine ⟨16579787553728723933284405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22106383404971631911045873 16579787553728723933284405)
              ·
                refine ⟨1554355083162067868745413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 16579787553728723933284405 1554355083162067868745413)
                ·
                  refine ⟨291441578092887725389765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1554355083162067868745413 291441578092887725389765)
                  ·
                    refine ⟨54645295892416448510581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 291441578092887725389765 54645295892416448510581)
                    ·
                      rfl

theorem cell22_159632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 5, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 5, 4, 4].length) (baseStart_159632 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_159632 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_159632 prefixEnd_159632 := by exact prefixLift 159632
  have htrace : WordTrace (prefixWord ++ tailWord_159632) baseStart_159632 baseEnd_159632 := by
    simpa [prefixWord, tailWord_159632, baseEnd_159632] using wordTrace_append hprefix tailTrace_159632
  have hstable : (prefixWord ++ tailWord_159632).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_159632).length < 2 ^ (prefixWord ++ tailWord_159632).sum := by decide
  have hdescent : baseEnd_159632 < baseStart_159632 := by decide
  rcases family_descends (prefixWord ++ tailWord_159632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_159636 : List Nat := [2, 4, 2, 1, 1, 4, 1, 1, 6]
def baseStart_159636 : Nat := 118140960795 + 159636 * 2 ^ 59
def prefixEnd_159636 : Nat := 4983230072969 + 3 ^ 40 * 159636 * 2
def baseEnd_159636 : Nat := 18215555058053923803523

theorem tailTrace_159636 : CollatzResearch.WordTrace tailWord_159636 prefixEnd_159636 18215555058053923803523 := by
  unfold tailWord_159636
  simp only [CollatzResearch.WordTrace]
  refine ⟨2911201624836755251669381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3881602166449007002225841 2911201624836755251669381)
  ·
    refine ⟨545850304656891609688009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2911201624836755251669381 545850304656891609688009)
    ·
      refine ⟨409387728492668707266007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 545850304656891609688009 409387728492668707266007)
      ·
        refine ⟨614081592739003060899011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 409387728492668707266007 614081592739003060899011)
        ·
          refine ⟨921122389108504591348517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 614081592739003060899011 921122389108504591348517)
          ·
            refine ⟨172710447957844610877847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 921122389108504591348517 172710447957844610877847)
            ·
              refine ⟨259065671936766916316771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 172710447957844610877847 259065671936766916316771)
              ·
                refine ⟨388598507905150374475157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 259065671936766916316771 388598507905150374475157)
                ·
                  refine ⟨18215555058053923803523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 388598507905150374475157 18215555058053923803523)
                  ·
                    rfl

theorem cell22_159636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 4, 1, 1, 6].length) (baseStart_159636 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_159636 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_159636 prefixEnd_159636 := by exact prefixLift 159636
  have htrace : WordTrace (prefixWord ++ tailWord_159636) baseStart_159636 baseEnd_159636 := by
    simpa [prefixWord, tailWord_159636, baseEnd_159636] using wordTrace_append hprefix tailTrace_159636
  have hstable : (prefixWord ++ tailWord_159636).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_159636).length < 2 ^ (prefixWord ++ tailWord_159636).sum := by decide
  have hdescent : baseEnd_159636 < baseStart_159636 := by decide
  rcases family_descends (prefixWord ++ tailWord_159636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_159668 : List Nat := [2, 5, 2, 1, 2, 1, 1, 2, 1, 5]
def baseStart_159668 : Nat := 118140960795 + 159668 * 2 ^ 59
def prefixEnd_159668 : Nat := 4983230072969 + 3 ^ 40 * 159668 * 2
def baseEnd_159668 : Nat := 54657619428124354610471

theorem tailTrace_159668 : CollatzResearch.WordTrace tailWord_159668 prefixEnd_159668 54657619428124354610471 := by
  unfold tailWord_159668
  simp only [CollatzResearch.WordTrace]
  refine ⟨2911785192778789984251829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3882380257038386645669105 2911785192778789984251829)
  ·
    refine ⟨272979861823011561023609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 2911785192778789984251829 272979861823011561023609)
    ·
      refine ⟨204734896367258670767707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 272979861823011561023609 204734896367258670767707)
      ·
        refine ⟨307102344550888006151561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 204734896367258670767707 307102344550888006151561)
        ·
          refine ⟨230326758413166004613671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 307102344550888006151561 230326758413166004613671)
          ·
            refine ⟨345490137619749006920507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 230326758413166004613671 345490137619749006920507)
            ·
              refine ⟨518235206429623510380761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 345490137619749006920507 518235206429623510380761)
              ·
                refine ⟨388676404822217632785571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 518235206429623510380761 388676404822217632785571)
                ·
                  refine ⟨583014607233326449178357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 388676404822217632785571 583014607233326449178357)
                  ·
                    refine ⟨54657619428124354610471, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 583014607233326449178357 54657619428124354610471)
                    ·
                      rfl

theorem cell22_159668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 1, 1, 2, 1, 5].length) (baseStart_159668 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_159668 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_159668 prefixEnd_159668 := by exact prefixLift 159668
  have htrace : WordTrace (prefixWord ++ tailWord_159668) baseStart_159668 baseEnd_159668 := by
    simpa [prefixWord, tailWord_159668, baseEnd_159668] using wordTrace_append hprefix tailTrace_159668
  have hstable : (prefixWord ++ tailWord_159668).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_159668).length < 2 ^ (prefixWord ++ tailWord_159668).sum := by decide
  have hdescent : baseEnd_159668 < baseStart_159668 := by decide
  rcases family_descends (prefixWord ++ tailWord_159668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_159698 : List Nat := [3, 2, 2, 3, 3, 1, 1, 7]
def baseStart_159698 : Nat := 118140960795 + 159698 * 2 ^ 59
def prefixEnd_159698 : Nat := 4983230072969 + 3 ^ 40 * 159698 * 2
def baseEnd_159698 : Nat := 6074209893468252928931

theorem tailTrace_159698 : CollatzResearch.WordTrace tailWord_159698 prefixEnd_159698 6074209893468252928931 := by
  unfold tailWord_159698
  simp only [CollatzResearch.WordTrace]
  refine ⟨1456166143862223773023937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3883109716965930061397165 1456166143862223773023937)
  ·
    refine ⟨1092124607896667829767953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1456166143862223773023937 1092124607896667829767953)
    ·
      refine ⟨819093455922500872325965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1092124607896667829767953 819093455922500872325965)
      ·
        refine ⟨307160045970937827122237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 819093455922500872325965 307160045970937827122237)
        ·
          refine ⟨115185017239101685170839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 307160045970937827122237 115185017239101685170839)
          ·
            refine ⟨172777525858652527756259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 115185017239101685170839 172777525858652527756259)
            ·
              refine ⟨259166288787978791634389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 172777525858652527756259 259166288787978791634389)
              ·
                refine ⟨6074209893468252928931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 259166288787978791634389 6074209893468252928931)
                ·
                  rfl

theorem cell22_159698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 3, 1, 1, 7].length) (baseStart_159698 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_159698 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_159698 prefixEnd_159698 := by exact prefixLift 159698
  have htrace : WordTrace (prefixWord ++ tailWord_159698) baseStart_159698 baseEnd_159698 := by
    simpa [prefixWord, tailWord_159698, baseEnd_159698] using wordTrace_append hprefix tailTrace_159698
  have hstable : (prefixWord ++ tailWord_159698).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_159698).length < 2 ^ (prefixWord ++ tailWord_159698).sum := by decide
  have hdescent : baseEnd_159698 < baseStart_159698 := by decide
  rcases family_descends (prefixWord ++ tailWord_159698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_159773 : List Nat := [1, 4, 2, 2, 2, 2, 2, 2, 1, 4]
def baseStart_159773 : Nat := 118140960795 + 159773 * 2 ^ 59
def prefixEnd_159773 : Nat := 4983230072969 + 3 ^ 40 * 159773 * 2
def baseEnd_159773 : Nat := 54693563073939080735149

theorem tailTrace_159773 : CollatzResearch.WordTrace tailWord_159773 prefixEnd_159773 54693563073939080735149 := by
  unfold tailWord_159773
  simp only [CollatzResearch.WordTrace]
  refine ⟨5827400050177182901075973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3884933366784788600717315 5827400050177182901075973)
  ·
    refine ⟨1092637509408221793951745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5827400050177182901075973 1092637509408221793951745)
    ·
      refine ⟨819478132056166345463809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1092637509408221793951745 819478132056166345463809)
      ·
        refine ⟨614608599042124759097857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 819478132056166345463809 614608599042124759097857)
        ·
          refine ⟨460956449281593569323393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 614608599042124759097857 460956449281593569323393)
          ·
            refine ⟨345717336961195176992545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 460956449281593569323393 345717336961195176992545)
            ·
              refine ⟨259288002720896382744409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 345717336961195176992545 259288002720896382744409)
              ·
                refine ⟨194466002040672287058307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 259288002720896382744409 194466002040672287058307)
                ·
                  refine ⟨291699003061008430587461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 194466002040672287058307 291699003061008430587461)
                  ·
                    refine ⟨54693563073939080735149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 291699003061008430587461 54693563073939080735149)
                    ·
                      rfl

theorem cell22_159773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 2, 2, 2, 1, 4].length) (baseStart_159773 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_159773 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_159773 prefixEnd_159773 := by exact prefixLift 159773
  have htrace : WordTrace (prefixWord ++ tailWord_159773) baseStart_159773 baseEnd_159773 := by
    simpa [prefixWord, tailWord_159773, baseEnd_159773] using wordTrace_append hprefix tailTrace_159773
  have hstable : (prefixWord ++ tailWord_159773).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_159773).length < 2 ^ (prefixWord ++ tailWord_159773).sum := by decide
  have hdescent : baseEnd_159773 < baseStart_159773 := by decide
  rcases family_descends (prefixWord ++ tailWord_159773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_159831 : List Nat := [1, 1, 3, 2, 2, 1, 2, 4, 3, 3]
def baseStart_159831 : Nat := 118140960795 + 159831 * 2 ^ 59
def prefixEnd_159831 : Nat := 4983230072969 + 3 ^ 40 * 159831 * 2
def baseEnd_159831 : Nat := 54713417659246262784971

theorem tailTrace_159831 : CollatzResearch.WordTrace tailWord_159831 prefixEnd_159831 54713417659246262784971 := by
  unfold tailWord_159831
  simp only [CollatzResearch.WordTrace]
  refine ⟨5829515483967058806687347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3886343655978039204458231 5829515483967058806687347)
  ·
    refine ⟨8744273225950588210031021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5829515483967058806687347 8744273225950588210031021)
    ·
      refine ⟨3279102459731470578761633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8744273225950588210031021 3279102459731470578761633)
      ·
        refine ⟨2459326844798602934071225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3279102459731470578761633 2459326844798602934071225)
        ·
          refine ⟨1844495133598952200553419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2459326844798602934071225 1844495133598952200553419)
          ·
            refine ⟨2766742700398428300830129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1844495133598952200553419 2766742700398428300830129)
            ·
              refine ⟨2075057025298821225622597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2766742700398428300830129 2075057025298821225622597)
              ·
                refine ⟨389073192243528979804237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2075057025298821225622597 389073192243528979804237)
                ·
                  refine ⟨145902447091323367426589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 389073192243528979804237 145902447091323367426589)
                  ·
                    refine ⟨54713417659246262784971, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 145902447091323367426589 54713417659246262784971)
                    ·
                      rfl

theorem cell22_159831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 2, 4, 3, 3].length) (baseStart_159831 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_159831 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_159831 prefixEnd_159831 := by exact prefixLift 159831
  have htrace : WordTrace (prefixWord ++ tailWord_159831) baseStart_159831 baseEnd_159831 := by
    simpa [prefixWord, tailWord_159831, baseEnd_159831] using wordTrace_append hprefix tailTrace_159831
  have hstable : (prefixWord ++ tailWord_159831).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_159831).length < 2 ^ (prefixWord ++ tailWord_159831).sum := by decide
  have hdescent : baseEnd_159831 < baseStart_159831 := by decide
  rcases family_descends (prefixWord ++ tailWord_159831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_159844 : List Nat := [2, 3, 1, 1, 2, 1, 2, 1, 9]
def baseStart_159844 : Nat := 118140960795 + 159844 * 2 ^ 59
def prefixEnd_159844 : Nat := 4983230072969 + 3 ^ 40 * 159844 * 2
def baseEnd_159844 : Nat := 18239289274972854069977

theorem tailTrace_159844 : CollatzResearch.WordTrace tailWord_159844 prefixEnd_159844 18239289274972854069977 := by
  unfold tailWord_159844
  simp only [CollatzResearch.WordTrace]
  refine ⟨2914994816459981013455293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3886659755279974684607057 2914994816459981013455293)
  ·
    refine ⟨1093123056172492880045735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2914994816459981013455293 1093123056172492880045735)
    ·
      refine ⟨1639684584258739320068603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1093123056172492880045735 1639684584258739320068603)
      ·
        refine ⟨2459526876388108980102905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1639684584258739320068603 2459526876388108980102905)
        ·
          refine ⟨1844645157291081735077179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2459526876388108980102905 1844645157291081735077179)
          ·
            refine ⟨2766967735936622602615769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1844645157291081735077179 2766967735936622602615769)
            ·
              refine ⟨2075225801952466951961827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2766967735936622602615769 2075225801952466951961827)
              ·
                refine ⟨3112838702928700427942741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2075225801952466951961827 3112838702928700427942741)
                ·
                  refine ⟨18239289274972854069977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 3112838702928700427942741 18239289274972854069977)
                  ·
                    rfl

theorem cell22_159844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 2, 1, 9].length) (baseStart_159844 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_159844 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_159844 prefixEnd_159844 := by exact prefixLift 159844
  have htrace : WordTrace (prefixWord ++ tailWord_159844) baseStart_159844 baseEnd_159844 := by
    simpa [prefixWord, tailWord_159844, baseEnd_159844] using wordTrace_append hprefix tailTrace_159844
  have hstable : (prefixWord ++ tailWord_159844).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_159844).length < 2 ^ (prefixWord ++ tailWord_159844).sum := by decide
  have hdescent : baseEnd_159844 < baseStart_159844 := by decide
  rcases family_descends (prefixWord ++ tailWord_159844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_159865 : List Nat := [1, 2, 1, 3, 4, 2, 1, 4, 1, 3]
def baseStart_159865 : Nat := 118140960795 + 159865 * 2 ^ 59
def prefixEnd_159865 : Nat := 4983230072969 + 3 ^ 40 * 159865 * 2
def baseEnd_159865 : Nat := 54725056554081507434867

theorem tailTrace_159865 : CollatzResearch.WordTrace tailWord_159865 prefixEnd_159865 54725056554081507434867 := by
  unfold tailWord_159865
  simp only [CollatzResearch.WordTrace]
  refine ⟨5830755565843882613425049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3887170377229255075616699 5830755565843882613425049)
  ·
    refine ⟨4373066674382911960068787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5830755565843882613425049 4373066674382911960068787)
    ·
      refine ⟨6559600011574367940103181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4373066674382911960068787 6559600011574367940103181)
      ·
        refine ⟨2459850004340387977538693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6559600011574367940103181 2459850004340387977538693)
        ·
          refine ⟨461221875813822745788505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2459850004340387977538693 461221875813822745788505)
          ·
            refine ⟨345916406860367059341379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 461221875813822745788505 345916406860367059341379)
            ·
              refine ⟨518874610290550589012069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 345916406860367059341379 518874610290550589012069)
              ·
                refine ⟨97288989429478235439763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 518874610290550589012069 97288989429478235439763)
                ·
                  refine ⟨145933484144217353159645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 97288989429478235439763 145933484144217353159645)
                  ·
                    refine ⟨54725056554081507434867, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 145933484144217353159645 54725056554081507434867)
                    ·
                      rfl

theorem cell22_159865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 2, 1, 4, 1, 3].length) (baseStart_159865 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_159865 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_159865 prefixEnd_159865 := by exact prefixLift 159865
  have htrace : WordTrace (prefixWord ++ tailWord_159865) baseStart_159865 baseEnd_159865 := by
    simpa [prefixWord, tailWord_159865, baseEnd_159865] using wordTrace_append hprefix tailTrace_159865
  have hstable : (prefixWord ++ tailWord_159865).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_159865).length < 2 ^ (prefixWord ++ tailWord_159865).sum := by decide
  have hdescent : baseEnd_159865 < baseStart_159865 := by decide
  rcases family_descends (prefixWord ++ tailWord_159865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_159876 : List Nat := [2, 3, 2, 1, 2, 1, 3, 1, 2, 5]
def baseStart_159876 : Nat := 118140960795 + 159876 * 2 ^ 59
def prefixEnd_159876 : Nat := 4983230072969 + 3 ^ 40 * 159876 * 2
def baseEnd_159876 : Nat := 54728822078881145409833

theorem tailTrace_159876 : CollatzResearch.WordTrace tailWord_159876 prefixEnd_159876 54728822078881145409833 := by
  unfold tailWord_159876
  simp only [CollatzResearch.WordTrace]
  refine ⟨2915578384402015746037741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3887437845869354328050321 2915578384402015746037741)
  ·
    refine ⟨1093341894150755904764153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2915578384402015746037741 1093341894150755904764153)
    ·
      refine ⟨820006420613066928573115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1093341894150755904764153 820006420613066928573115)
      ·
        refine ⟨1230009630919600392859673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 820006420613066928573115 1230009630919600392859673)
        ·
          refine ⟨922507223189700294644755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1230009630919600392859673 922507223189700294644755)
          ·
            refine ⟨1383760834784550441967133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 922507223189700294644755 1383760834784550441967133)
            ·
              refine ⟨518910313044206415737675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1383760834784550441967133 518910313044206415737675)
              ·
                refine ⟨778365469566309623606513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 518910313044206415737675 778365469566309623606513)
                ·
                  refine ⟨583774102174732217704885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 778365469566309623606513 583774102174732217704885)
                  ·
                    refine ⟨54728822078881145409833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 583774102174732217704885 54728822078881145409833)
                    ·
                      rfl

theorem cell22_159876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 3, 1, 2, 5].length) (baseStart_159876 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_159876 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_159876 prefixEnd_159876 := by exact prefixLift 159876
  have htrace : WordTrace (prefixWord ++ tailWord_159876) baseStart_159876 baseEnd_159876 := by
    simpa [prefixWord, tailWord_159876, baseEnd_159876] using wordTrace_append hprefix tailTrace_159876
  have hstable : (prefixWord ++ tailWord_159876).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_159876).length < 2 ^ (prefixWord ++ tailWord_159876).sum := by decide
  have hdescent : baseEnd_159876 < baseStart_159876 := by decide
  rcases family_descends (prefixWord ++ tailWord_159876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_159891 : List Nat := [1, 1, 1, 2, 1, 2, 3, 6, 1, 4]
def baseStart_159891 : Nat := 118140960795 + 159891 * 2 ^ 59
def prefixEnd_159891 : Nat := 4983230072969 + 3 ^ 40 * 159891 * 2
def baseEnd_159891 : Nat := 54733956885426106284787

theorem tailTrace_159891 : CollatzResearch.WordTrace tailWord_159891 prefixEnd_159891 54733956885426106284787 := by
  unfold tailWord_159891
  simp only [CollatzResearch.WordTrace]
  refine ⟨5831703863749689053871527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3887802575833126035914351 5831703863749689053871527)
  ·
    refine ⟨8747555795624533580807291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5831703863749689053871527 8747555795624533580807291)
    ·
      refine ⟨13121333693436800371210937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8747555795624533580807291 13121333693436800371210937)
      ·
        refine ⟨9841000270077600278408203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13121333693436800371210937 9841000270077600278408203)
        ·
          refine ⟨14761500405116400417612305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9841000270077600278408203 14761500405116400417612305)
          ·
            refine ⟨11071125303837300313209229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14761500405116400417612305 11071125303837300313209229)
            ·
              refine ⟨4151671988938987617453461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11071125303837300313209229 4151671988938987617453461)
              ·
                refine ⟨194609624481515044568131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 4151671988938987617453461 194609624481515044568131)
                ·
                  refine ⟨291914436722272566852197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 194609624481515044568131 291914436722272566852197)
                  ·
                    refine ⟨54733956885426106284787, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 291914436722272566852197 54733956885426106284787)
                    ·
                      rfl

theorem cell22_159891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 6, 1, 4].length) (baseStart_159891 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_159891 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_159891 prefixEnd_159891 := by exact prefixLift 159891
  have htrace : WordTrace (prefixWord ++ tailWord_159891) baseStart_159891 baseEnd_159891 := by
    simpa [prefixWord, tailWord_159891, baseEnd_159891] using wordTrace_append hprefix tailTrace_159891
  have hstable : (prefixWord ++ tailWord_159891).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_159891).length < 2 ^ (prefixWord ++ tailWord_159891).sum := by decide
  have hdescent : baseEnd_159891 < baseStart_159891 := by decide
  rcases family_descends (prefixWord ++ tailWord_159891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_159936 : List Nat := [2, 1, 1, 2, 5, 1, 1, 2, 1, 6]
def baseStart_159936 : Nat := 118140960795 + 159936 * 2 ^ 59
def prefixEnd_159936 : Nat := 4983230072969 + 3 ^ 40 * 159936 * 2
def baseEnd_159936 : Nat := 54749361305060988909649

theorem tailTrace_159936 : CollatzResearch.WordTrace tailWord_159936 prefixEnd_159936 54749361305060988909649 := by
  unfold tailWord_159936
  simp only [CollatzResearch.WordTrace]
  refine ⟨2916672574293330869629831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3888896765724441159506441 2916672574293330869629831)
  ·
    refine ⟨4375008861439996304444747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2916672574293330869629831 4375008861439996304444747)
    ·
      refine ⟨6562513292159994456667121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4375008861439996304444747 6562513292159994456667121)
      ·
        refine ⟨4921884969119995842500341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6562513292159994456667121 4921884969119995842500341)
        ·
          refine ⟨461426715854999610234407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 4921884969119995842500341 461426715854999610234407)
          ·
            refine ⟨692140073782499415351611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 461426715854999610234407 692140073782499415351611)
            ·
              refine ⟨1038210110673749123027417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 692140073782499415351611 1038210110673749123027417)
              ·
                refine ⟨778657583005311842270563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1038210110673749123027417 778657583005311842270563)
                ·
                  refine ⟨1167986374507967763405845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 778657583005311842270563 1167986374507967763405845)
                  ·
                    refine ⟨54749361305060988909649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1167986374507967763405845 54749361305060988909649)
                    ·
                      rfl

theorem cell22_159936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 1, 2, 1, 6].length) (baseStart_159936 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_159936 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_159936 prefixEnd_159936 := by exact prefixLift 159936
  have htrace : WordTrace (prefixWord ++ tailWord_159936) baseStart_159936 baseEnd_159936 := by
    simpa [prefixWord, tailWord_159936, baseEnd_159936] using wordTrace_append hprefix tailTrace_159936
  have hstable : (prefixWord ++ tailWord_159936).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_159936).length < 2 ^ (prefixWord ++ tailWord_159936).sum := by decide
  have hdescent : baseEnd_159936 < baseStart_159936 := by decide
  rcases family_descends (prefixWord ++ tailWord_159936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_159957 : List Nat := [1, 3, 2, 4, 2, 2, 1, 3, 4]
def baseStart_159957 : Nat := 118140960795 + 159957 * 2 ^ 59
def prefixEnd_159957 : Nat := 4983230072969 + 3 ^ 40 * 159957 * 2
def baseEnd_159957 : Nat := 18252183344741311378195

theorem tailTrace_159957 : CollatzResearch.WordTrace tailWord_159957 prefixEnd_159957 18252183344741311378195 := by
  unfold tailWord_159957
  simp only [CollatzResearch.WordTrace]
  refine ⟨5834111081510582325774125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3889407387673721550516083 5834111081510582325774125)
  ·
    refine ⟨2187791655566468372165297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5834111081510582325774125 2187791655566468372165297)
    ·
      refine ⟨1640843741674851279123973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2187791655566468372165297 1640843741674851279123973)
      ·
        refine ⟨307658201564034614835745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1640843741674851279123973 307658201564034614835745)
        ·
          refine ⟨230743651173025961126809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 307658201564034614835745 230743651173025961126809)
          ·
            refine ⟨173057738379769470845107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 230743651173025961126809 173057738379769470845107)
            ·
              refine ⟨259586607569654206267661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 173057738379769470845107 259586607569654206267661)
              ·
                refine ⟨97344977838620327350373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 259586607569654206267661 97344977838620327350373)
                ·
                  refine ⟨18252183344741311378195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 97344977838620327350373 18252183344741311378195)
                  ·
                    rfl

theorem cell22_159957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 2, 1, 3, 4].length) (baseStart_159957 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_159957 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_159957 prefixEnd_159957 := by exact prefixLift 159957
  have htrace : WordTrace (prefixWord ++ tailWord_159957) baseStart_159957 baseEnd_159957 := by
    simpa [prefixWord, tailWord_159957, baseEnd_159957] using wordTrace_append hprefix tailTrace_159957
  have hstable : (prefixWord ++ tailWord_159957).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_159957).length < 2 ^ (prefixWord ++ tailWord_159957).sum := by decide
  have hdescent : baseEnd_159957 < baseStart_159957 := by decide
  rcases family_descends (prefixWord ++ tailWord_159957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_160034 : List Nat := [3, 3, 1, 1, 3, 1, 4, 2, 1, 3]
def baseStart_160034 : Nat := 118140960795 + 160034 * 2 ^ 59
def prefixEnd_160034 : Nat := 4983230072969 + 3 ^ 40 * 160034 * 2
def baseEnd_160034 : Nat := 54782908707821399959349

theorem tailTrace_160034 : CollatzResearch.WordTrace tailWord_160034 prefixEnd_160034 54782908707821399959349 := by
  unfold tailWord_160034
  simp only [CollatzResearch.WordTrace]
  refine ⟨1459229875557906119081789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3891279668154416317551437 1459229875557906119081789)
  ·
    refine ⟨547211203334214794655671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1459229875557906119081789 547211203334214794655671)
    ·
      refine ⟨820816805001322191983507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 547211203334214794655671 820816805001322191983507)
      ·
        refine ⟨1231225207501983287975261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 820816805001322191983507 1231225207501983287975261)
        ·
          refine ⟨461709452813243732990723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1231225207501983287975261 461709452813243732990723)
          ·
            refine ⟨692564179219865599486085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 461709452813243732990723 692564179219865599486085)
            ·
              refine ⟨129855783603724799903641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 692564179219865599486085 129855783603724799903641)
              ·
                refine ⟨97391837702793599927731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 129855783603724799903641 97391837702793599927731)
                ·
                  refine ⟨146087756554190399891597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 97391837702793599927731 146087756554190399891597)
                  ·
                    refine ⟨54782908707821399959349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 146087756554190399891597 54782908707821399959349)
                    ·
                      rfl

theorem cell22_160034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 4, 2, 1, 3].length) (baseStart_160034 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_160034 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_160034 prefixEnd_160034 := by exact prefixLift 160034
  have htrace : WordTrace (prefixWord ++ tailWord_160034) baseStart_160034 baseEnd_160034 := by
    simpa [prefixWord, tailWord_160034, baseEnd_160034] using wordTrace_append hprefix tailTrace_160034
  have hstable : (prefixWord ++ tailWord_160034).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_160034).length < 2 ^ (prefixWord ++ tailWord_160034).sum := by decide
  have hdescent : baseEnd_160034 < baseStart_160034 := by decide
  rcases family_descends (prefixWord ++ tailWord_160034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_160058 : List Nat := [3, 1, 1, 1, 4, 3, 1, 2, 6]
def baseStart_160058 : Nat := 118140960795 + 160058 * 2 ^ 59
def prefixEnd_160058 : Nat := 4983230072969 + 3 ^ 40 * 160058 * 2
def baseEnd_160058 : Nat := 18263708132764445786425

theorem tailTrace_160058 : CollatzResearch.WordTrace tailWord_160058 prefixEnd_160058 18263708132764445786425 := by
  unfold tailWord_160058
  simp only [CollatzResearch.WordTrace]
  refine ⟨1459448713536169143800207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3891863236096451050133885 1459448713536169143800207)
  ·
    refine ⟨2189173070304253715700311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1459448713536169143800207 2189173070304253715700311)
    ·
      refine ⟨3283759605456380573550467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2189173070304253715700311 3283759605456380573550467)
      ·
        refine ⟨4925639408184570860325701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3283759605456380573550467 4925639408184570860325701)
        ·
          refine ⟨923557389034607036311069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4925639408184570860325701 923557389034607036311069)
          ·
            refine ⟨346334020887977638616651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 923557389034607036311069 346334020887977638616651)
            ·
              refine ⟨519501031331966457924977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 346334020887977638616651 519501031331966457924977)
              ·
                refine ⟨389625773498974843443733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 519501031331966457924977 389625773498974843443733)
                ·
                  refine ⟨18263708132764445786425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 389625773498974843443733 18263708132764445786425)
                  ·
                    rfl

theorem cell22_160058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 3, 1, 2, 6].length) (baseStart_160058 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_160058 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_160058 prefixEnd_160058 := by exact prefixLift 160058
  have htrace : WordTrace (prefixWord ++ tailWord_160058) baseStart_160058 baseEnd_160058 := by
    simpa [prefixWord, tailWord_160058, baseEnd_160058] using wordTrace_append hprefix tailTrace_160058
  have hstable : (prefixWord ++ tailWord_160058).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_160058).length < 2 ^ (prefixWord ++ tailWord_160058).sum := by decide
  have hdescent : baseEnd_160058 < baseStart_160058 := by decide
  rcases family_descends (prefixWord ++ tailWord_160058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_160073 : List Nat := [1, 2, 1, 1, 2, 3, 1, 4, 4, 3]
def baseStart_160073 : Nat := 118140960795 + 160073 * 2 ^ 59
def prefixEnd_160073 : Nat := 4983230072969 + 3 ^ 40 * 160073 * 2
def baseEnd_160073 : Nat := 54796259204838298234229

theorem tailTrace_160073 : CollatzResearch.WordTrace tailWord_160073 prefixEnd_160073 54796259204838298234229 := by
  unfold tailWord_160073
  simp only [CollatzResearch.WordTrace]
  refine ⟨5838341949090334136996873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3892227966060222757997915 5838341949090334136996873)
  ·
    refine ⟨4378756461817750602747655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5838341949090334136996873 4378756461817750602747655)
    ·
      refine ⟨6568134692726625904121483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4378756461817750602747655 6568134692726625904121483)
      ·
        refine ⟨9852202039089938856182225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6568134692726625904121483 9852202039089938856182225)
        ·
          refine ⟨7389151529317454142136669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9852202039089938856182225 7389151529317454142136669)
          ·
            refine ⟨2770931823494045303301251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7389151529317454142136669 2770931823494045303301251)
            ·
              refine ⟨4156397735241067954951877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2770931823494045303301251 4156397735241067954951877)
              ·
                refine ⟨779324575357700241553477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4156397735241067954951877 779324575357700241553477)
                ·
                  refine ⟨146123357879568795291277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 779324575357700241553477 146123357879568795291277)
                  ·
                    refine ⟨54796259204838298234229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 146123357879568795291277 54796259204838298234229)
                    ·
                      rfl

theorem cell22_160073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 4, 4, 3].length) (baseStart_160073 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_160073 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_160073 prefixEnd_160073 := by exact prefixLift 160073
  have htrace : WordTrace (prefixWord ++ tailWord_160073) baseStart_160073 baseEnd_160073 := by
    simpa [prefixWord, tailWord_160073, baseEnd_160073] using wordTrace_append hprefix tailTrace_160073
  have hstable : (prefixWord ++ tailWord_160073).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_160073).length < 2 ^ (prefixWord ++ tailWord_160073).sum := by decide
  have hdescent : baseEnd_160073 < baseStart_160073 := by decide
  rcases family_descends (prefixWord ++ tailWord_160073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_160092 : List Nat := [2, 2, 4, 3, 1, 1, 2, 1, 6]
def baseStart_160092 : Nat := 118140960795 + 160092 * 2 ^ 59
def prefixEnd_160092 : Nat := 4983230072969 + 3 ^ 40 * 160092 * 2
def baseEnd_160092 : Nat := 18267587764376194003057

theorem tailTrace_160092 : CollatzResearch.WordTrace tailWord_160092 prefixEnd_160092 18267587764376194003057 := by
  unfold tailWord_160092
  simp only [CollatzResearch.WordTrace]
  refine ⟨2919517468010750190969265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3892689957347666921292353 2919517468010750190969265)
  ·
    refine ⟨2189638101008062643226949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2919517468010750190969265 2189638101008062643226949)
    ·
      refine ⟨410557143939011745605053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2189638101008062643226949 410557143939011745605053)
      ·
        refine ⟨153958928977129404601895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 410557143939011745605053 153958928977129404601895)
        ·
          refine ⟨230938393465694106902843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 153958928977129404601895 230938393465694106902843)
          ·
            refine ⟨346407590198541160354265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 230938393465694106902843 346407590198541160354265)
            ·
              refine ⟨259805692648905870265699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 346407590198541160354265 259805692648905870265699)
              ·
                refine ⟨389708538973358805398549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 259805692648905870265699 389708538973358805398549)
                ·
                  refine ⟨18267587764376194003057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 389708538973358805398549 18267587764376194003057)
                  ·
                    rfl

theorem cell22_160092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 1, 2, 1, 6].length) (baseStart_160092 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_160092 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_160092 prefixEnd_160092 := by exact prefixLift 160092
  have htrace : WordTrace (prefixWord ++ tailWord_160092) baseStart_160092 baseEnd_160092 := by
    simpa [prefixWord, tailWord_160092, baseEnd_160092] using wordTrace_append hprefix tailTrace_160092
  have hstable : (prefixWord ++ tailWord_160092).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_160092).length < 2 ^ (prefixWord ++ tailWord_160092).sum := by decide
  have hdescent : baseEnd_160092 < baseStart_160092 := by decide
  rcases family_descends (prefixWord ++ tailWord_160092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_160152 : List Nat := [2, 1, 2, 5, 1, 1, 3, 1, 3, 3]
def baseStart_160152 : Nat := 118140960795 + 160152 * 2 ^ 59
def prefixEnd_160152 : Nat := 4983230072969 + 3 ^ 40 * 160152 * 2
def baseEnd_160152 : Nat := 54823302519308425508987

theorem tailTrace_160152 : CollatzResearch.WordTrace tailWord_160152 prefixEnd_160152 54823302519308425508987 := by
  unfold tailWord_160152
  simp only [CollatzResearch.WordTrace]
  refine ⟨2920611657902065314561355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3894148877202753752748473 2920611657902065314561355)
  ·
    refine ⟨4380917486853097971842033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2920611657902065314561355 4380917486853097971842033)
    ·
      refine ⟨3285688115139823478881525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4380917486853097971842033 3285688115139823478881525)
      ·
        refine ⟨308033260794358451145143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 3285688115139823478881525 308033260794358451145143)
        ·
          refine ⟨462049891191537676717715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 308033260794358451145143 462049891191537676717715)
          ·
            refine ⟨693074836787306515076573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 462049891191537676717715 693074836787306515076573)
            ·
              refine ⟨259903063795239943153715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 693074836787306515076573 259903063795239943153715)
              ·
                refine ⟨389854595692859914730573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 259903063795239943153715 389854595692859914730573)
                ·
                  refine ⟨146195473384822468023965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 389854595692859914730573 146195473384822468023965)
                  ·
                    refine ⟨54823302519308425508987, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 146195473384822468023965 54823302519308425508987)
                    ·
                      rfl

theorem cell22_160152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 3, 1, 3, 3].length) (baseStart_160152 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_160152 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_160152 prefixEnd_160152 := by exact prefixLift 160152
  have htrace : WordTrace (prefixWord ++ tailWord_160152) baseStart_160152 baseEnd_160152 := by
    simpa [prefixWord, tailWord_160152, baseEnd_160152] using wordTrace_append hprefix tailTrace_160152
  have hstable : (prefixWord ++ tailWord_160152).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_160152).length < 2 ^ (prefixWord ++ tailWord_160152).sum := by decide
  have hdescent : baseEnd_160152 < baseStart_160152 := by decide
  rcases family_descends (prefixWord ++ tailWord_160152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_160225 : List Nat := [1, 2, 3, 1, 2, 2, 4, 1, 1, 5]
def baseStart_160225 : Nat := 118140960795 + 160225 * 2 ^ 59
def prefixEnd_160225 : Nat := 4983230072969 + 3 ^ 40 * 160225 * 2
def baseEnd_160225 : Nat := 54848291911160568433763

theorem tailTrace_160225 : CollatzResearch.WordTrace tailWord_160225 prefixEnd_160225 54848291911160568433763 := by
  unfold tailWord_160225
  simp only [CollatzResearch.WordTrace]
  refine ⟨5843885844539664096530129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3895923896359776064353419 5843885844539664096530129)
  ·
    refine ⟨4382914383404748072397597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5843885844539664096530129 4382914383404748072397597)
    ·
      refine ⟨1643592893776780527149099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4382914383404748072397597 1643592893776780527149099)
      ·
        refine ⟨2465389340665170790723649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1643592893776780527149099 2465389340665170790723649)
        ·
          refine ⟨1849042005498878093042737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2465389340665170790723649 1849042005498878093042737)
          ·
            refine ⟨1386781504124158569782053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1849042005498878093042737 1386781504124158569782053)
            ·
              refine ⟨260021532023279731834135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1386781504124158569782053 260021532023279731834135)
              ·
                refine ⟨390032298034919597751203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 260021532023279731834135 390032298034919597751203)
                ·
                  refine ⟨585048447052379396626805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 390032298034919597751203 585048447052379396626805)
                  ·
                    refine ⟨54848291911160568433763, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 585048447052379396626805 54848291911160568433763)
                    ·
                      rfl

theorem cell22_160225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 4, 1, 1, 5].length) (baseStart_160225 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_160225 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_160225 prefixEnd_160225 := by exact prefixLift 160225
  have htrace : WordTrace (prefixWord ++ tailWord_160225) baseStart_160225 baseEnd_160225 := by
    simpa [prefixWord, tailWord_160225, baseEnd_160225] using wordTrace_append hprefix tailTrace_160225
  have hstable : (prefixWord ++ tailWord_160225).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_160225).length < 2 ^ (prefixWord ++ tailWord_160225).sum := by decide
  have hdescent : baseEnd_160225 < baseStart_160225 := by decide
  rcases family_descends (prefixWord ++ tailWord_160225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_160304 : List Nat := [2, 1, 1, 1, 2, 3, 5, 3, 1, 3]
def baseStart_160304 : Nat := 118140960795 + 160304 * 2 ^ 59
def prefixEnd_160304 : Nat := 4983230072969 + 3 ^ 40 * 160304 * 2
def baseEnd_160304 : Nat := 54875335225630695708521

theorem tailTrace_160304 : CollatzResearch.WordTrace tailWord_160304 prefixEnd_160304 54875335225630695708521 := by
  unfold tailWord_160304
  simp only [CollatzResearch.WordTrace]
  refine ⟨2923383605626730294327983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3897844807502307059103977 2923383605626730294327983)
  ·
    refine ⟨4385075408440095441491975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2923383605626730294327983 4385075408440095441491975)
    ·
      refine ⟨6577613112660143162237963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4385075408440095441491975 6577613112660143162237963)
      ·
        refine ⟨9866419668990214743356945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6577613112660143162237963 9866419668990214743356945)
        ·
          refine ⟨7399814751742661057517709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9866419668990214743356945 7399814751742661057517709)
          ·
            refine ⟨2774930531903497896569141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7399814751742661057517709 2774930531903497896569141)
            ·
              refine ⟨260149737365952927803357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2774930531903497896569141 260149737365952927803357)
              ·
                refine ⟨97556151512232347926259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 260149737365952927803357 97556151512232347926259)
                ·
                  refine ⟨146334227268348521889389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 97556151512232347926259 146334227268348521889389)
                  ·
                    refine ⟨54875335225630695708521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 146334227268348521889389 54875335225630695708521)
                    ·
                      rfl

theorem cell22_160304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 5, 3, 1, 3].length) (baseStart_160304 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_160304 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_160304 prefixEnd_160304 := by exact prefixLift 160304
  have htrace : WordTrace (prefixWord ++ tailWord_160304) baseStart_160304 baseEnd_160304 := by
    simpa [prefixWord, tailWord_160304, baseEnd_160304] using wordTrace_append hprefix tailTrace_160304
  have hstable : (prefixWord ++ tailWord_160304).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_160304).length < 2 ^ (prefixWord ++ tailWord_160304).sum := by decide
  have hdescent : baseEnd_160304 < baseStart_160304 := by decide
  rcases family_descends (prefixWord ++ tailWord_160304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_160394 : List Nat := [3, 1, 2, 3, 3, 1, 2, 1, 1, 5]
def baseStart_160394 : Nat := 118140960795 + 160394 * 2 ^ 59
def prefixEnd_160394 : Nat := 4983230072969 + 3 ^ 40 * 160394 * 2
def baseEnd_160394 : Nat := 54906144064900460958245

theorem tailTrace_160394 : CollatzResearch.WordTrace tailWord_160394 prefixEnd_160394 54906144064900460958245 := by
  unfold tailWord_160394
  simp only [CollatzResearch.WordTrace]
  refine ⟨1462512445231851489858059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3900033187284937306288157 1462512445231851489858059)
  ·
    refine ⟨2193768667847777234787089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1462512445231851489858059 2193768667847777234787089)
    ·
      refine ⟨1645326500885832926090317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2193768667847777234787089 1645326500885832926090317)
      ·
        refine ⟨616997437832187347283869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1645326500885832926090317 616997437832187347283869)
        ·
          refine ⟨231374039187070255231451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 616997437832187347283869 231374039187070255231451)
          ·
            refine ⟨347061058780605382847177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 231374039187070255231451 347061058780605382847177)
            ·
              refine ⟨260295794085454037135383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 347061058780605382847177 260295794085454037135383)
              ·
                refine ⟨390443691128181055703075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 260295794085454037135383 390443691128181055703075)
                ·
                  refine ⟨585665536692271583554613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 390443691128181055703075 585665536692271583554613)
                  ·
                    refine ⟨54906144064900460958245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 585665536692271583554613 54906144064900460958245)
                    ·
                      rfl

theorem cell22_160394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 1, 2, 1, 1, 5].length) (baseStart_160394 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_160394 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_160394 prefixEnd_160394 := by exact prefixLift 160394
  have htrace : WordTrace (prefixWord ++ tailWord_160394) baseStart_160394 baseEnd_160394 := by
    simpa [prefixWord, tailWord_160394, baseEnd_160394] using wordTrace_append hprefix tailTrace_160394
  have hstable : (prefixWord ++ tailWord_160394).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_160394).length < 2 ^ (prefixWord ++ tailWord_160394).sum := by decide
  have hdescent : baseEnd_160394 < baseStart_160394 := by decide
  rcases family_descends (prefixWord ++ tailWord_160394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_160407 : List Nat := [1, 1, 3, 3, 2, 1, 5, 6]
def baseStart_160407 : Nat := 118140960795 + 160407 * 2 ^ 59
def prefixEnd_160407 : Nat := 4983230072969 + 3 ^ 40 * 160407 * 2
def baseEnd_160407 : Nat := 6101177136730306709245

theorem tailTrace_160407 : CollatzResearch.WordTrace tailWord_160407 prefixEnd_160407 6101177136730306709245 := by
  unfold tailWord_160407
  simp only [CollatzResearch.WordTrace]
  refine ⟨5850523929880309179655475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3900349286586872786436983 5850523929880309179655475)
  ·
    refine ⟨8775785894820463769483213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5850523929880309179655475 8775785894820463769483213)
    ·
      refine ⟨3290919710557673913556205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8775785894820463769483213 3290919710557673913556205)
      ·
        refine ⟨1234094891459127717583577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3290919710557673913556205 1234094891459127717583577)
        ·
          refine ⟨925571168594345788187683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1234094891459127717583577 925571168594345788187683)
          ·
            refine ⟨1388356752891518682281525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 925571168594345788187683 1388356752891518682281525)
            ·
              refine ⟨130158445583579876463893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1388356752891518682281525 130158445583579876463893)
              ·
                refine ⟨6101177136730306709245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 130158445583579876463893 6101177136730306709245)
                ·
                  rfl

theorem cell22_160407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 5, 6].length) (baseStart_160407 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_160407 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_160407 prefixEnd_160407 := by exact prefixLift 160407
  have htrace : WordTrace (prefixWord ++ tailWord_160407) baseStart_160407 baseEnd_160407 := by
    simpa [prefixWord, tailWord_160407, baseEnd_160407] using wordTrace_append hprefix tailTrace_160407
  have hstable : (prefixWord ++ tailWord_160407).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_160407).length < 2 ^ (prefixWord ++ tailWord_160407).sum := by decide
  have hdescent : baseEnd_160407 < baseStart_160407 := by decide
  rcases family_descends (prefixWord ++ tailWord_160407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_160544 : List Nat := [2, 1, 1, 5, 1, 2, 2, 2, 2, 4]
def baseStart_160544 : Nat := 118140960795 + 160544 * 2 ^ 59
def prefixEnd_160544 : Nat := 4983230072969 + 3 ^ 40 * 160544 * 2
def baseEnd_160544 : Nat := 54957492130350069707785

theorem tailTrace_160544 : CollatzResearch.WordTrace tailWord_160544 prefixEnd_160544 54957492130350069707785 := by
  unfold tailWord_160544
  simp only [CollatzResearch.WordTrace]
  refine ⟨2927760365191990788696343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3903680486922654384928457 2927760365191990788696343)
  ·
    refine ⟨4391640547787986183044515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2927760365191990788696343 4391640547787986183044515)
    ·
      refine ⟨6587460821681979274566773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4391640547787986183044515 6587460821681979274566773)
      ·
        refine ⟨617574452032685556990635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 6587460821681979274566773 617574452032685556990635)
        ·
          refine ⟨926361678049028335485953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 617574452032685556990635 926361678049028335485953)
          ·
            refine ⟨694771258536771251614465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 926361678049028335485953 694771258536771251614465)
            ·
              refine ⟨521078443902578438710849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 694771258536771251614465 521078443902578438710849)
              ·
                refine ⟨390808832926933829033137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 521078443902578438710849 390808832926933829033137)
                ·
                  refine ⟨293106624695200371774853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 390808832926933829033137 293106624695200371774853)
                  ·
                    refine ⟨54957492130350069707785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 293106624695200371774853 54957492130350069707785)
                    ·
                      rfl

theorem cell22_160544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 2, 2, 2, 4].length) (baseStart_160544 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_160544 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_160544 prefixEnd_160544 := by exact prefixLift 160544
  have htrace : WordTrace (prefixWord ++ tailWord_160544) baseStart_160544 baseEnd_160544 := by
    simpa [prefixWord, tailWord_160544, baseEnd_160544] using wordTrace_append hprefix tailTrace_160544
  have hstable : (prefixWord ++ tailWord_160544).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_160544).length < 2 ^ (prefixWord ++ tailWord_160544).sum := by decide
  have hdescent : baseEnd_160544 < baseStart_160544 := by decide
  rcases family_descends (prefixWord ++ tailWord_160544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_160546 : List Nat := [3, 3, 1, 1, 2, 2, 1, 4, 2, 3]
def baseStart_160546 : Nat := 118140960795 + 160546 * 2 ^ 59
def prefixEnd_160546 : Nat := 4983230072969 + 3 ^ 40 * 160546 * 2
def baseEnd_160546 : Nat := 54958176771222731157779

theorem tailTrace_160546 : CollatzResearch.WordTrace tailWord_160546 prefixEnd_160546 54958176771222731157779 := by
  unfold tailWord_160546
  simp only [CollatzResearch.WordTrace]
  refine ⟨1463898419094183979741373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3903729117584490612643661 1463898419094183979741373)
  ·
    refine ⟨548961907160318992403015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1463898419094183979741373 548961907160318992403015)
    ·
      refine ⟨823442860740478488604523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 548961907160318992403015 823442860740478488604523)
      ·
        refine ⟨1235164291110717732906785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 823442860740478488604523 1235164291110717732906785)
        ·
          refine ⟨926373218333038299680089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1235164291110717732906785 926373218333038299680089)
          ·
            refine ⟨694779913749778724760067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 926373218333038299680089 694779913749778724760067)
            ·
              refine ⟨1042169870624668087140101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 694779913749778724760067 1042169870624668087140101)
              ·
                refine ⟨195406850742125266338769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1042169870624668087140101 195406850742125266338769)
                ·
                  refine ⟨146555138056593949754077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 195406850742125266338769 146555138056593949754077)
                  ·
                    refine ⟨54958176771222731157779, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 146555138056593949754077 54958176771222731157779)
                    ·
                      rfl

theorem cell22_160546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 1, 4, 2, 3].length) (baseStart_160546 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_160546 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_160546 prefixEnd_160546 := by exact prefixLift 160546
  have htrace : WordTrace (prefixWord ++ tailWord_160546) baseStart_160546 baseEnd_160546 := by
    simpa [prefixWord, tailWord_160546, baseEnd_160546] using wordTrace_append hprefix tailTrace_160546
  have hstable : (prefixWord ++ tailWord_160546).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_160546).length < 2 ^ (prefixWord ++ tailWord_160546).sum := by decide
  have hdescent : baseEnd_160546 < baseStart_160546 := by decide
  rcases family_descends (prefixWord ++ tailWord_160546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_160572 : List Nat := [2, 2, 2, 2, 1, 1, 1, 1, 4, 6]
def baseStart_160572 : Nat := 118140960795 + 160572 * 2 ^ 59
def prefixEnd_160572 : Nat := 4983230072969 + 3 ^ 40 * 160572 * 2
def baseEnd_160572 : Nat := 54967077102567330007699

theorem tailTrace_160572 : CollatzResearch.WordTrace tailWord_160572 prefixEnd_160572 54967077102567330007699 := by
  unfold tailWord_160572
  simp only [CollatzResearch.WordTrace]
  refine ⟨2928270987141271179705985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3904361316188361572941313 2928270987141271179705985)
  ·
    refine ⟨2196203240355953384779489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2928270987141271179705985 2196203240355953384779489)
    ·
      refine ⟨1647152430266965038584617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2196203240355953384779489 1647152430266965038584617)
      ·
        refine ⟨1235364322700223778938463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1647152430266965038584617 1235364322700223778938463)
        ·
          refine ⟨1853046484050335668407695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1235364322700223778938463 1853046484050335668407695)
          ·
            refine ⟨2779569726075503502611543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1853046484050335668407695 2779569726075503502611543)
            ·
              refine ⟨4169354589113255253917315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2779569726075503502611543 4169354589113255253917315)
              ·
                refine ⟨6254031883669882880875973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4169354589113255253917315 6254031883669882880875973)
                ·
                  refine ⟨1172630978188103040164245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6254031883669882880875973 1172630978188103040164245)
                  ·
                    refine ⟨54967077102567330007699, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1172630978188103040164245 54967077102567330007699)
                    ·
                      rfl

theorem cell22_160572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 1, 4, 6].length) (baseStart_160572 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_160572 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_160572 prefixEnd_160572 := by exact prefixLift 160572
  have htrace : WordTrace (prefixWord ++ tailWord_160572) baseStart_160572 baseEnd_160572 := by
    simpa [prefixWord, tailWord_160572, baseEnd_160572] using wordTrace_append hprefix tailTrace_160572
  have hstable : (prefixWord ++ tailWord_160572).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_160572).length < 2 ^ (prefixWord ++ tailWord_160572).sum := by decide
  have hdescent : baseEnd_160572 < baseStart_160572 := by decide
  rcases family_descends (prefixWord ++ tailWord_160572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_160632 : List Nat := [2, 1, 2, 1, 1, 1, 1, 5, 8]
def baseStart_160632 : Nat := 118140960795 + 160632 * 2 ^ 59
def prefixEnd_160632 : Nat := 4983230072969 + 3 ^ 40 * 160632 * 2
def baseEnd_160632 : Nat := 18329205442915724502505

theorem tailTrace_160632 : CollatzResearch.WordTrace tailWord_160632 prefixEnd_160632 18329205442915724502505 := by
  unfold tailWord_160632
  simp only [CollatzResearch.WordTrace]
  refine ⟨2929365177032586303298075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3905820236043448404397433 2929365177032586303298075)
  ·
    refine ⟨4394047765548879454947113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2929365177032586303298075 4394047765548879454947113)
    ·
      refine ⟨3295535824161659591210335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4394047765548879454947113 3295535824161659591210335)
      ·
        refine ⟨4943303736242489386815503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3295535824161659591210335 4943303736242489386815503)
        ·
          refine ⟨7414955604363734080223255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4943303736242489386815503 7414955604363734080223255)
          ·
            refine ⟨11122433406545601120334883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7414955604363734080223255 11122433406545601120334883)
            ·
              refine ⟨16683650109818401680502325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11122433406545601120334883 16683650109818401680502325)
              ·
                refine ⟨1564092197795475157547093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 16683650109818401680502325 1564092197795475157547093)
                ·
                  refine ⟨18329205442915724502505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 1564092197795475157547093 18329205442915724502505)
                  ·
                    rfl

theorem cell22_160632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 5, 8].length) (baseStart_160632 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_160632 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_160632 prefixEnd_160632 := by exact prefixLift 160632
  have htrace : WordTrace (prefixWord ++ tailWord_160632) baseStart_160632 baseEnd_160632 := by
    simpa [prefixWord, tailWord_160632, baseEnd_160632] using wordTrace_append hprefix tailTrace_160632
  have hstable : (prefixWord ++ tailWord_160632).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_160632).length < 2 ^ (prefixWord ++ tailWord_160632).sum := by decide
  have hdescent : baseEnd_160632 < baseStart_160632 := by decide
  rcases family_descends (prefixWord ++ tailWord_160632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_160681 : List Nat := [1, 2, 1, 1, 1, 1, 7, 3, 2, 3]
def baseStart_160681 : Nat := 118140960795 + 160681 * 2 ^ 59
def prefixEnd_160681 : Nat := 4983230072969 + 3 ^ 40 * 160681 * 2
def baseEnd_160681 : Nat := 55004390030127379032365

theorem tailTrace_160681 : CollatzResearch.WordTrace tailWord_160681 prefixEnd_160681 55004390030127379032365 := by
  unfold tailWord_160681
  simp only [CollatzResearch.WordTrace]
  refine ⟨5860517530887653975129897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3907011687258435983419931 5860517530887653975129897)
  ·
    refine ⟨4395388148165740481347423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5860517530887653975129897 4395388148165740481347423)
    ·
      refine ⟨6593082222248610722021135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4395388148165740481347423 6593082222248610722021135)
      ·
        refine ⟨9889623333372916083031703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6593082222248610722021135 9889623333372916083031703)
        ·
          refine ⟨14834435000059374124547555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9889623333372916083031703 14834435000059374124547555)
          ·
            refine ⟨22251652500089061186821333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14834435000059374124547555 22251652500089061186821333)
            ·
              refine ⟨521523105470837371566125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 22251652500089061186821333 521523105470837371566125)
              ·
                refine ⟨195571164551564014337297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 521523105470837371566125 195571164551564014337297)
                ·
                  refine ⟨146678373413673010752973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 195571164551564014337297 146678373413673010752973)
                  ·
                    refine ⟨55004390030127379032365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 146678373413673010752973 55004390030127379032365)
                    ·
                      rfl

theorem cell22_160681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 7, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 7, 3, 2, 3].length) (baseStart_160681 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_160681 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_160681 prefixEnd_160681 := by exact prefixLift 160681
  have htrace : WordTrace (prefixWord ++ tailWord_160681) baseStart_160681 baseEnd_160681 := by
    simpa [prefixWord, tailWord_160681, baseEnd_160681] using wordTrace_append hprefix tailTrace_160681
  have hstable : (prefixWord ++ tailWord_160681).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_160681).length < 2 ^ (prefixWord ++ tailWord_160681).sum := by decide
  have hdescent : baseEnd_160681 < baseStart_160681 := by decide
  rcases family_descends (prefixWord ++ tailWord_160681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_160696 : List Nat := [2, 1, 2, 1, 2, 5, 2, 1, 2, 4]
def baseStart_160696 : Nat := 118140960795 + 160696 * 2 ^ 59
def prefixEnd_160696 : Nat := 4983230072969 + 3 ^ 40 * 160696 * 2
def baseEnd_160696 : Nat := 55009524836672339907319

theorem tailTrace_160696 : CollatzResearch.WordTrace tailWord_160696 prefixEnd_160696 55009524836672339907319 := by
  unfold tailWord_160696
  simp only [CollatzResearch.WordTrace]
  refine ⟨2930532312916655768462971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3907376417222207691283961 2930532312916655768462971)
  ·
    refine ⟨4395798469374983652694457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2930532312916655768462971 4395798469374983652694457)
    ·
      refine ⟨3296848852031237739520843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4395798469374983652694457 3296848852031237739520843)
      ·
        refine ⟨4945273278046856609281265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3296848852031237739520843 4945273278046856609281265)
        ·
          refine ⟨3708954958535142456960949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4945273278046856609281265 3708954958535142456960949)
          ·
            refine ⟨347714527362669605340089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 3708954958535142456960949 347714527362669605340089)
            ·
              refine ⟨260785895522002204005067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 347714527362669605340089 260785895522002204005067)
              ·
                refine ⟨391178843283003306007601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 260785895522002204005067 391178843283003306007601)
                ·
                  refine ⟨293384132462252479505701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 391178843283003306007601 293384132462252479505701)
                  ·
                    refine ⟨55009524836672339907319, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 293384132462252479505701 55009524836672339907319)
                    ·
                      rfl

theorem cell22_160696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 5, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 5, 2, 1, 2, 4].length) (baseStart_160696 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_160696 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_160696 prefixEnd_160696 := by exact prefixLift 160696
  have htrace : WordTrace (prefixWord ++ tailWord_160696) baseStart_160696 baseEnd_160696 := by
    simpa [prefixWord, tailWord_160696, baseEnd_160696] using wordTrace_append hprefix tailTrace_160696
  have hstable : (prefixWord ++ tailWord_160696).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_160696).length < 2 ^ (prefixWord ++ tailWord_160696).sum := by decide
  have hdescent : baseEnd_160696 < baseStart_160696 := by decide
  rcases family_descends (prefixWord ++ tailWord_160696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_160710 : List Nat := [6, 1, 3, 1, 2, 1, 2, 2, 1, 3]
def baseStart_160710 : Nat := 118140960795 + 160710 * 2 ^ 59
def prefixEnd_160710 : Nat := 4983230072969 + 3 ^ 40 * 160710 * 2
def baseEnd_160710 : Nat := 55014317322780970057277

theorem tailTrace_160710 : CollatzResearch.WordTrace tailWord_160710 prefixEnd_160710 55014317322780970057277 := by
  unfold tailWord_160710
  simp only [CollatzResearch.WordTrace]
  refine ⟨183174226493205997747987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 3907716831855061285290389 183174226493205997747987)
  ·
    refine ⟨274761339739808996621981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 183174226493205997747987 274761339739808996621981)
    ·
      refine ⟨103035502402428373733243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 274761339739808996621981 103035502402428373733243)
      ·
        refine ⟨154553253603642560599865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103035502402428373733243 154553253603642560599865)
        ·
          refine ⟨115914940202731920449899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 154553253603642560599865 115914940202731920449899)
          ·
            refine ⟨173872410304097880674849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 115914940202731920449899 173872410304097880674849)
            ·
              refine ⟨130404307728073410506137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 173872410304097880674849 130404307728073410506137)
              ·
                refine ⟨97803230796055057879603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 130404307728073410506137 97803230796055057879603)
                ·
                  refine ⟨146704846194082586819405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 97803230796055057879603 146704846194082586819405)
                  ·
                    refine ⟨55014317322780970057277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 146704846194082586819405 55014317322780970057277)
                    ·
                      rfl

theorem cell22_160710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 2, 1, 2, 2, 1, 3].length) (baseStart_160710 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_160710 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_160710 prefixEnd_160710 := by exact prefixLift 160710
  have htrace : WordTrace (prefixWord ++ tailWord_160710) baseStart_160710 baseEnd_160710 := by
    simpa [prefixWord, tailWord_160710, baseEnd_160710] using wordTrace_append hprefix tailTrace_160710
  have hstable : (prefixWord ++ tailWord_160710).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_160710).length < 2 ^ (prefixWord ++ tailWord_160710).sum := by decide
  have hdescent : baseEnd_160710 < baseStart_160710 := by decide
  rcases family_descends (prefixWord ++ tailWord_160710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_160743 : List Nat := [1, 1, 5, 2, 2, 2, 1, 2, 3, 3]
def baseStart_160743 : Nat := 118140960795 + 160743 * 2 ^ 59
def prefixEnd_160743 : Nat := 4983230072969 + 3 ^ 40 * 160743 * 2
def baseEnd_160743 : Nat := 55025613897179883982175

theorem tailTrace_160743 : CollatzResearch.WordTrace tailWord_160743 prefixEnd_160743 55025613897179883982175 := by
  unfold tailWord_160743
  simp only [CollatzResearch.WordTrace]
  refine ⟨5862778856663038563886883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3908519237775359042591255 5862778856663038563886883)
  ·
    refine ⟨8794168284994557845830325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5862778856663038563886883 8794168284994557845830325)
    ·
      refine ⟨824453276718239798046593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 8794168284994557845830325 824453276718239798046593)
      ·
        refine ⟨618339957538679848534945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 824453276718239798046593 618339957538679848534945)
        ·
          refine ⟨463754968154009886401209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 618339957538679848534945 463754968154009886401209)
          ·
            refine ⟨347816226115507414800907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 463754968154009886401209 347816226115507414800907)
            ·
              refine ⟨521724339173261122201361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 347816226115507414800907 521724339173261122201361)
              ·
                refine ⟨391293254379945841651021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 521724339173261122201361 391293254379945841651021)
                ·
                  refine ⟨146734970392479690619133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 391293254379945841651021 146734970392479690619133)
                  ·
                    refine ⟨55025613897179883982175, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 146734970392479690619133 55025613897179883982175)
                    ·
                      rfl

theorem cell22_160743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 2, 1, 2, 3, 3].length) (baseStart_160743 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_160743 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_160743 prefixEnd_160743 := by exact prefixLift 160743
  have htrace : WordTrace (prefixWord ++ tailWord_160743) baseStart_160743 baseEnd_160743 := by
    simpa [prefixWord, tailWord_160743, baseEnd_160743] using wordTrace_append hprefix tailTrace_160743
  have hstable : (prefixWord ++ tailWord_160743).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_160743).length < 2 ^ (prefixWord ++ tailWord_160743).sum := by decide
  have hdescent : baseEnd_160743 < baseStart_160743 := by decide
  rcases family_descends (prefixWord ++ tailWord_160743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_160801 : List Nat := [1, 2, 3, 2, 3, 1, 2, 2, 6]
def baseStart_160801 : Nat := 118140960795 + 160801 * 2 ^ 59
def prefixEnd_160801 : Nat := 4983230072969 + 3 ^ 40 * 160801 * 2
def baseEnd_160801 : Nat := 18348489494162355343999

theorem tailTrace_160801 : CollatzResearch.WordTrace tailWord_160801 prefixEnd_160801 18348489494162355343999 := by
  unfold tailWord_160801
  simp only [CollatzResearch.WordTrace]
  refine ⟨5864894290452914469498257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3909929526968609646332171 5864894290452914469498257)
  ·
    refine ⟨4398670717839685852123693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5864894290452914469498257 4398670717839685852123693)
    ·
      refine ⟨1649501519189882194546385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4398670717839685852123693 1649501519189882194546385)
      ·
        refine ⟨1237126139392411645909789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1649501519189882194546385 1237126139392411645909789)
        ·
          refine ⟨463922302272154367216171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1237126139392411645909789 463922302272154367216171)
          ·
            refine ⟨695883453408231550824257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 463922302272154367216171 695883453408231550824257)
            ·
              refine ⟨521912590056173663118193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 695883453408231550824257 521912590056173663118193)
              ·
                refine ⟨391434442542130247338645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 521912590056173663118193 391434442542130247338645)
                ·
                  refine ⟨18348489494162355343999, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 391434442542130247338645 18348489494162355343999)
                  ·
                    rfl

theorem cell22_160801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 2, 2, 6].length) (baseStart_160801 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_160801 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_160801 prefixEnd_160801 := by exact prefixLift 160801
  have htrace : WordTrace (prefixWord ++ tailWord_160801) baseStart_160801 baseEnd_160801 := by
    simpa [prefixWord, tailWord_160801, baseEnd_160801] using wordTrace_append hprefix tailTrace_160801
  have hstable : (prefixWord ++ tailWord_160801).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_160801).length < 2 ^ (prefixWord ++ tailWord_160801).sum := by decide
  have hdescent : baseEnd_160801 < baseStart_160801 := by decide
  rcases family_descends (prefixWord ++ tailWord_160801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_160803 : List Nat := [1, 1, 1, 4, 3, 3, 2, 2, 1, 4]
def baseStart_160803 : Nat := 118140960795 + 160803 * 2 ^ 59
def prefixEnd_160803 : Nat := 4983230072969 + 3 ^ 40 * 160803 * 2
def baseEnd_160803 : Nat := 55046153123359727481991

theorem tailTrace_160803 : CollatzResearch.WordTrace tailWord_160803 prefixEnd_160803 55046153123359727481991 := by
  unfold tailWord_160803
  simp only [CollatzResearch.WordTrace]
  refine ⟨5864967236445668811071063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3909978157630445874047375 5864967236445668811071063)
  ·
    refine ⟨8797450854668503216606595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5864967236445668811071063 8797450854668503216606595)
    ·
      refine ⟨13196176282002754824909893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8797450854668503216606595 13196176282002754824909893)
      ·
        refine ⟨2474283052875516529670605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13196176282002754824909893 2474283052875516529670605)
        ·
          refine ⟨927856144828318698626477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2474283052875516529670605 927856144828318698626477)
          ·
            refine ⟨347946054310619511984929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 927856144828318698626477 347946054310619511984929)
            ·
              refine ⟨260959540732964633988697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 347946054310619511984929 260959540732964633988697)
              ·
                refine ⟨195719655549723475491523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 260959540732964633988697 195719655549723475491523)
                ·
                  refine ⟨293579483324585213237285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 195719655549723475491523 293579483324585213237285)
                  ·
                    refine ⟨55046153123359727481991, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 293579483324585213237285 55046153123359727481991)
                    ·
                      rfl

theorem cell22_160803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 3, 2, 2, 1, 4].length) (baseStart_160803 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_160803 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_160803 prefixEnd_160803 := by exact prefixLift 160803
  have htrace : WordTrace (prefixWord ++ tailWord_160803) baseStart_160803 baseEnd_160803 := by
    simpa [prefixWord, tailWord_160803, baseEnd_160803] using wordTrace_append hprefix tailTrace_160803
  have hstable : (prefixWord ++ tailWord_160803).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_160803).length < 2 ^ (prefixWord ++ tailWord_160803).sum := by decide
  have hdescent : baseEnd_160803 < baseStart_160803 := by decide
  rcases family_descends (prefixWord ++ tailWord_160803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_160816 : List Nat := [2, 1, 1, 1, 2, 4, 1, 1, 6, 3]
def baseStart_160816 : Nat := 118140960795 + 160816 * 2 ^ 59
def prefixEnd_160816 : Nat := 4983230072969 + 3 ^ 40 * 160816 * 2
def baseEnd_160816 : Nat := 55050603289032026906951

theorem tailTrace_160816 : CollatzResearch.WordTrace tailWord_160816 prefixEnd_160816 55050603289032026906951 := by
  unfold tailWord_160816
  simp only [CollatzResearch.WordTrace]
  refine ⟨2932720692699286015647151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3910294256932381354196201 2932720692699286015647151)
  ·
    refine ⟨4399081039048929023470727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2932720692699286015647151 4399081039048929023470727)
    ·
      refine ⟨6598621558573393535206091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4399081039048929023470727 6598621558573393535206091)
      ·
        refine ⟨9897932337860090302809137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6598621558573393535206091 9897932337860090302809137)
        ·
          refine ⟨7423449253395067727106853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9897932337860090302809137 7423449253395067727106853)
          ·
            refine ⟨1391896735011575198832535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7423449253395067727106853 1391896735011575198832535)
            ·
              refine ⟨2087845102517362798248803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1391896735011575198832535 2087845102517362798248803)
              ·
                refine ⟨3131767653776044197373205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2087845102517362798248803 3131767653776044197373205)
                ·
                  refine ⟨146801608770752071751869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3131767653776044197373205 146801608770752071751869)
                  ·
                    refine ⟨55050603289032026906951, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 146801608770752071751869 55050603289032026906951)
                    ·
                      rfl

theorem cell22_160816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 1, 1, 6, 3].length) (baseStart_160816 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_160816 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_160816 prefixEnd_160816 := by exact prefixLift 160816
  have htrace : WordTrace (prefixWord ++ tailWord_160816) baseStart_160816 baseEnd_160816 := by
    simpa [prefixWord, tailWord_160816, baseEnd_160816] using wordTrace_append hprefix tailTrace_160816
  have hstable : (prefixWord ++ tailWord_160816).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_160816).length < 2 ^ (prefixWord ++ tailWord_160816).sum := by decide
  have hdescent : baseEnd_160816 < baseStart_160816 := by decide
  rcases family_descends (prefixWord ++ tailWord_160816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_160820 : List Nat := [2, 5, 1, 2, 1, 1, 2, 3, 1, 4]
def baseStart_160820 : Nat := 118140960795 + 160820 * 2 ^ 59
def prefixEnd_160820 : Nat := 4983230072969 + 3 ^ 40 * 160820 * 2
def baseEnd_160820 : Nat := 55051972570777349806939

theorem tailTrace_160820 : CollatzResearch.WordTrace tailWord_160820 prefixEnd_160820 55051972570777349806939 := by
  unfold tailWord_160820
  simp only [CollatzResearch.WordTrace]
  refine ⟨2932793638692040357219957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3910391518256053809626609 2932793638692040357219957)
  ·
    refine ⟨274949403627378783489371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 2932793638692040357219957 274949403627378783489371)
    ·
      refine ⟨412424105441068175234057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 274949403627378783489371 412424105441068175234057)
      ·
        refine ⟨309318079080801131425543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 412424105441068175234057 309318079080801131425543)
        ·
          refine ⟨463977118621201697138315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 309318079080801131425543 463977118621201697138315)
          ·
            refine ⟨695965677931802545707473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 463977118621201697138315 695965677931802545707473)
            ·
              refine ⟨521974258448851909280605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 695965677931802545707473 521974258448851909280605)
              ·
                refine ⟨195740346918319465980227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 521974258448851909280605 195740346918319465980227)
                ·
                  refine ⟨293610520377479198970341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 195740346918319465980227 293610520377479198970341)
                  ·
                    refine ⟨55051972570777349806939, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 293610520377479198970341 55051972570777349806939)
                    ·
                      rfl

theorem cell22_160820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 2, 3, 1, 4].length) (baseStart_160820 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_160820 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_160820 prefixEnd_160820 := by exact prefixLift 160820
  have htrace : WordTrace (prefixWord ++ tailWord_160820) baseStart_160820 baseEnd_160820 := by
    simpa [prefixWord, tailWord_160820, baseEnd_160820] using wordTrace_append hprefix tailTrace_160820
  have hstable : (prefixWord ++ tailWord_160820).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_160820).length < 2 ^ (prefixWord ++ tailWord_160820).sum := by decide
  have hdescent : baseEnd_160820 < baseStart_160820 := by decide
  rcases family_descends (prefixWord ++ tailWord_160820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_160846 : List Nat := [4, 1, 1, 1, 1, 3, 4, 7]
def baseStart_160846 : Nat := 118140960795 + 160846 * 2 ^ 59
def prefixEnd_160846 : Nat := 4983230072969 + 3 ^ 40 * 160846 * 2
def baseEnd_160846 : Nat := 6117874766902438739651

theorem tailTrace_160846 : CollatzResearch.WordTrace tailWord_160846 prefixEnd_160846 6117874766902438739651 := by
  unfold tailWord_160846
  simp only [CollatzResearch.WordTrace]
  refine ⟨733316946911235894360799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3911023716859924769924261 733316946911235894360799)
  ·
    refine ⟨1099975420366853841541199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 733316946911235894360799 1099975420366853841541199)
    ·
      refine ⟨1649963130550280762311799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1099975420366853841541199 1649963130550280762311799)
      ·
        refine ⟨2474944695825421143467699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1649963130550280762311799 2474944695825421143467699)
        ·
          refine ⟨3712417043738131715201549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2474944695825421143467699 3712417043738131715201549)
          ·
            refine ⟨1392156391401799393200581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3712417043738131715201549 1392156391401799393200581)
            ·
              refine ⟨261029323387837386225109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1392156391401799393200581 261029323387837386225109)
              ·
                refine ⟨6117874766902438739651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 261029323387837386225109 6117874766902438739651)
                ·
                  rfl

theorem cell22_160846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 4, 7].length) (baseStart_160846 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_160846 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_160846 prefixEnd_160846 := by exact prefixLift 160846
  have htrace : WordTrace (prefixWord ++ tailWord_160846) baseStart_160846 baseEnd_160846 := by
    simpa [prefixWord, tailWord_160846, baseEnd_160846] using wordTrace_append hprefix tailTrace_160846
  have hstable : (prefixWord ++ tailWord_160846).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_160846).length < 2 ^ (prefixWord ++ tailWord_160846).sum := by decide
  have hdescent : baseEnd_160846 < baseStart_160846 := by decide
  rcases family_descends (prefixWord ++ tailWord_160846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_160850 : List Nat := [3, 2, 2, 1, 3, 2, 1, 3, 2, 3]
def baseStart_160850 : Nat := 118140960795 + 160850 * 2 ^ 59
def prefixEnd_160850 : Nat := 4983230072969 + 3 ^ 40 * 160850 * 2
def baseEnd_160850 : Nat := 55062242183867271556847

theorem tailTrace_160850 : CollatzResearch.WordTrace tailWord_160850 prefixEnd_160850 55062242183867271556847 := by
  unfold tailWord_160850
  simp only [CollatzResearch.WordTrace]
  refine ⟨1466670366818848959508001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3911120978183597225354669 1466670366818848959508001)
  ·
    refine ⟨1100002775114136719631001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1466670366818848959508001 1100002775114136719631001)
    ·
      refine ⟨825002081335602539723251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1100002775114136719631001 825002081335602539723251)
      ·
        refine ⟨1237503122003403809584877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 825002081335602539723251 1237503122003403809584877)
        ·
          refine ⟨464063670751276428594329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1237503122003403809584877 464063670751276428594329)
          ·
            refine ⟨348047753063457321445747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 464063670751276428594329 348047753063457321445747)
            ·
              refine ⟨522071629595185982168621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 348047753063457321445747 522071629595185982168621)
              ·
                refine ⟨195776861098194743313233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 522071629595185982168621 195776861098194743313233)
                ·
                  refine ⟨146832645823646057484925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 195776861098194743313233 146832645823646057484925)
                  ·
                    refine ⟨55062242183867271556847, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 146832645823646057484925 55062242183867271556847)
                    ·
                      rfl

theorem cell22_160850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 2, 1, 3, 2, 3].length) (baseStart_160850 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_160850 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_160850 prefixEnd_160850 := by exact prefixLift 160850
  have htrace : WordTrace (prefixWord ++ tailWord_160850) baseStart_160850 baseEnd_160850 := by
    simpa [prefixWord, tailWord_160850, baseEnd_160850] using wordTrace_append hprefix tailTrace_160850
  have hstable : (prefixWord ++ tailWord_160850).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_160850).length < 2 ^ (prefixWord ++ tailWord_160850).sum := by decide
  have hdescent : baseEnd_160850 < baseStart_160850 := by decide
  rcases family_descends (prefixWord ++ tailWord_160850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_160854 : List Nat := [5, 2, 2, 1, 2, 2, 1, 2, 1, 4]
def baseStart_160854 : Nat := 118140960795 + 160854 * 2 ^ 59
def prefixEnd_160854 : Nat := 4983230072969 + 3 ^ 40 * 160854 * 2
def baseEnd_160854 : Nat := 55063611465612594456835

theorem tailTrace_160854 : CollatzResearch.WordTrace tailWord_160854 prefixEnd_160854 55063611465612594456835 := by
  unfold tailWord_160854
  simp only [CollatzResearch.WordTrace]
  refine ⟨366676709953806532573601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 3911218239507269680785077 366676709953806532573601)
  ·
    refine ⟨275007532465354899430201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 366676709953806532573601 275007532465354899430201)
    ·
      refine ⟨206255649349016174572651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 275007532465354899430201 206255649349016174572651)
      ·
        refine ⟨309383474023524261858977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 206255649349016174572651 309383474023524261858977)
        ·
          refine ⟨232037605517643196394233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 309383474023524261858977 232037605517643196394233)
          ·
            refine ⟨174028204138232397295675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 232037605517643196394233 174028204138232397295675)
            ·
              refine ⟨261042306207348595943513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 174028204138232397295675 261042306207348595943513)
              ·
                refine ⟨195781729655511446957635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 261042306207348595943513 195781729655511446957635)
                ·
                  refine ⟨293672594483267170436453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 195781729655511446957635 293672594483267170436453)
                  ·
                    refine ⟨55063611465612594456835, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 293672594483267170436453 55063611465612594456835)
                    ·
                      rfl

theorem cell22_160854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 2, 1, 2, 1, 4].length) (baseStart_160854 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_160854 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_160854 prefixEnd_160854 := by exact prefixLift 160854
  have htrace : WordTrace (prefixWord ++ tailWord_160854) baseStart_160854 baseEnd_160854 := by
    simpa [prefixWord, tailWord_160854, baseEnd_160854] using wordTrace_append hprefix tailTrace_160854
  have hstable : (prefixWord ++ tailWord_160854).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_160854).length < 2 ^ (prefixWord ++ tailWord_160854).sum := by decide
  have hdescent : baseEnd_160854 < baseStart_160854 := by decide
  rcases family_descends (prefixWord ++ tailWord_160854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_160953 : List Nat := [1, 2, 1, 4, 1, 4, 2, 1, 6]
def baseStart_160953 : Nat := 118140960795 + 160953 * 2 ^ 59
def prefixEnd_160953 : Nat := 4983230072969 + 3 ^ 40 * 160953 * 2
def baseEnd_160953 : Nat := 18365833729603112077177

theorem tailTrace_160953 : CollatzResearch.WordTrace tailWord_160953 prefixEnd_160953 18365833729603112077177 := by
  unfold tailWord_160953
  simp only [CollatzResearch.WordTrace]
  refine ⟨5870438185902244429031513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3913625457268162952687675 5870438185902244429031513)
  ·
    refine ⟨4402828639426683321773635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5870438185902244429031513 4402828639426683321773635)
    ·
      refine ⟨6604242959140024982660453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4402828639426683321773635 6604242959140024982660453)
      ·
        refine ⟨1238295554838754684248835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6604242959140024982660453 1238295554838754684248835)
        ·
          refine ⟨1857443332258132026373253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1238295554838754684248835 1857443332258132026373253)
          ·
            refine ⟨348270624798399754944985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1857443332258132026373253 348270624798399754944985)
            ·
              refine ⟨261202968598799816208739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 348270624798399754944985 261202968598799816208739)
              ·
                refine ⟨391804452898199724313109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 261202968598799816208739 391804452898199724313109)
                ·
                  refine ⟨18365833729603112077177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 391804452898199724313109 18365833729603112077177)
                  ·
                    rfl

theorem cell22_160953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 4, 2, 1, 6].length) (baseStart_160953 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_160953 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_160953 prefixEnd_160953 := by exact prefixLift 160953
  have htrace : WordTrace (prefixWord ++ tailWord_160953) baseStart_160953 baseEnd_160953 := by
    simpa [prefixWord, tailWord_160953, baseEnd_160953] using wordTrace_append hprefix tailTrace_160953
  have hstable : (prefixWord ++ tailWord_160953).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_160953).length < 2 ^ (prefixWord ++ tailWord_160953).sum := by decide
  have hdescent : baseEnd_160953 < baseStart_160953 := by decide
  rcases family_descends (prefixWord ++ tailWord_160953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
