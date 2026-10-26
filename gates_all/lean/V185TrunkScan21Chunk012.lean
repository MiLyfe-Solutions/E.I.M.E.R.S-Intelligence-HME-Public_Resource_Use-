import V185TrunkScan21Chunk011

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental

namespace V185TrunkScan21Incremental

def tailWord_142928 : List Nat := [2, 1, 1, 1, 1, 3, 4, 2, 6]
def baseStart_142928 : Nat := 118140960795 + 142928 * 2 ^ 59
def prefixEnd_142928 : Nat := 4983230072969 + 3 ^ 40 * 142928 * 2
def baseEnd_142928 : Nat := 32618116882632012107863

theorem tailTrace_142928 : CollatzResearch.WordTrace tailWord_142928 prefixEnd_142928 32618116882632012107863 := by
  unfold tailWord_142928
  simp only [CollatzResearch.WordTrace]
  refine ⟨2606506213101870502058719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3475341617469160669411625 2606506213101870502058719)
  ·
    refine ⟨3909759319652805753088079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2606506213101870502058719 3909759319652805753088079)
    ·
      refine ⟨5864638979479208629632119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3909759319652805753088079 5864638979479208629632119)
      ·
        refine ⟨8796958469218812944448179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5864638979479208629632119 8796958469218812944448179)
        ·
          refine ⟨13195437703828219416672269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8796958469218812944448179 13195437703828219416672269)
          ·
            refine ⟨4948289138935582281252101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13195437703828219416672269 4948289138935582281252101)
            ·
              refine ⟨927804213550421677734769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4948289138935582281252101 927804213550421677734769)
              ·
                refine ⟨695853160162816258301077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 927804213550421677734769 695853160162816258301077)
                ·
                  refine ⟨32618116882632012107863, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 695853160162816258301077 32618116882632012107863)
                  ·
                    rfl

theorem cell21_142928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 4, 2, 6].length) (baseStart_142928 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_142928 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_142928 prefixEnd_142928 := by exact prefixLift 142928
  have htrace : WordTrace (prefixWord ++ tailWord_142928) baseStart_142928 baseEnd_142928 := by
    simpa [prefixWord, tailWord_142928, baseEnd_142928] using wordTrace_append hprefix tailTrace_142928
  have hstable : (prefixWord ++ tailWord_142928).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_142928).length < 2 ^ (prefixWord ++ tailWord_142928).sum := by decide
  have hdescent : baseEnd_142928 < baseStart_142928 := by decide
  rcases family_descends (prefixWord ++ tailWord_142928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_142934 : List Nat := [5, 2, 2, 2, 1, 1, 8]
def baseStart_142934 : Nat := 118140960795 + 142934 * 2 ^ 59
def prefixEnd_142934 : Nat := 4983230072969 + 3 ^ 40 * 142934 * 2
def baseEnd_142934 : Nat := 3624387351597481667539

theorem tailTrace_142934 : CollatzResearch.WordTrace tailWord_142934 prefixEnd_142934 3624387351597481667539 := by
  unfold tailWord_142934
  simp only [CollatzResearch.WordTrace]
  refine ⟨325826954011375251802241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 3475487509454669352557237 325826954011375251802241)
  ·
    refine ⟨244370215508531438851681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 325826954011375251802241 244370215508531438851681)
    ·
      refine ⟨183277661631398579138761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 244370215508531438851681 183277661631398579138761)
      ·
        refine ⟨137458246223548934354071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 183277661631398579138761 137458246223548934354071)
        ·
          refine ⟨206187369335323401531107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 137458246223548934354071 206187369335323401531107)
          ·
            refine ⟨309281054002985102296661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 206187369335323401531107 309281054002985102296661)
            ·
              refine ⟨3624387351597481667539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 309281054002985102296661 3624387351597481667539)
              ·
                rfl

theorem cell21_142934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 1, 8].length) (baseStart_142934 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_142934 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_142934 prefixEnd_142934 := by exact prefixLift 142934
  have htrace : WordTrace (prefixWord ++ tailWord_142934) baseStart_142934 baseEnd_142934 := by
    simpa [prefixWord, tailWord_142934, baseEnd_142934] using wordTrace_append hprefix tailTrace_142934
  have hstable : (prefixWord ++ tailWord_142934).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_142934).length < 2 ^ (prefixWord ++ tailWord_142934).sum := by decide
  have hdescent : baseEnd_142934 < baseStart_142934 := by decide
  rcases family_descends (prefixWord ++ tailWord_142934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_143052 : List Nat := [2, 2, 1, 5, 3, 8]
def baseStart_143052 : Nat := 118140960795 + 143052 * 2 ^ 59
def prefixEnd_143052 : Nat := 4983230072969 + 3 ^ 40 * 143052 * 2
def baseEnd_143052 : Nat := 1209126495260568594109

theorem tailTrace_143052 : CollatzResearch.WordTrace tailWord_143052 prefixEnd_143052 1209126495260568594109 := by
  unfold tailWord_143052
  simp only [CollatzResearch.WordTrace]
  refine ⟨2608767538877255090815705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3478356718503006787754273 2608767538877255090815705)
  ·
    refine ⟨1956575654157941318111779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2608767538877255090815705 1956575654157941318111779)
    ·
      refine ⟨2934863481236911977167669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1956575654157941318111779 2934863481236911977167669)
      ·
        refine ⟨275143451365960497859469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 2934863481236911977167669 275143451365960497859469)
        ·
          refine ⟨103178794262235186697301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 275143451365960497859469 103178794262235186697301)
          ·
            refine ⟨1209126495260568594109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 103178794262235186697301 1209126495260568594109)
            ·
              rfl

theorem cell21_143052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 3, 8].length) (baseStart_143052 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_143052 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_143052 prefixEnd_143052 := by exact prefixLift 143052
  have htrace : WordTrace (prefixWord ++ tailWord_143052) baseStart_143052 baseEnd_143052 := by
    simpa [prefixWord, tailWord_143052, baseEnd_143052] using wordTrace_append hprefix tailTrace_143052
  have hstable : (prefixWord ++ tailWord_143052).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_143052).length < 2 ^ (prefixWord ++ tailWord_143052).sum := by decide
  have hdescent : baseEnd_143052 < baseStart_143052 := by decide
  rcases family_descends (prefixWord ++ tailWord_143052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_143114 : List Nat := [3, 1, 2, 2, 1, 5, 1, 2, 4]
def baseStart_143114 : Nat := 118140960795 + 143114 * 2 ^ 59
def prefixEnd_143114 : Nat := 4983230072969 + 3 ^ 40 * 143114 * 2
def baseEnd_143114 : Nat := 32660564616737022007483

theorem tailTrace_143114 : CollatzResearch.WordTrace tailWord_143114 prefixEnd_143114 32660564616737022007483 := by
  unfold tailWord_143114
  simp only [CollatzResearch.WordTrace]
  refine ⟨1304949100882473692597099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3479864269019929846925597 1304949100882473692597099)
  ·
    refine ⟨1957423651323710538895649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1304949100882473692597099 1957423651323710538895649)
    ·
      refine ⟨1468067738492782904171737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1957423651323710538895649 1468067738492782904171737)
      ·
        refine ⟨1101050803869587178128803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1468067738492782904171737 1101050803869587178128803)
        ·
          refine ⟨1651576205804380767193205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1101050803869587178128803 1651576205804380767193205)
          ·
            refine ⟨154835269294160696924363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1651576205804380767193205 154835269294160696924363)
            ·
              refine ⟨232252903941241045386545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 154835269294160696924363 232252903941241045386545)
              ·
                refine ⟨174189677955930784039909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 232252903941241045386545 174189677955930784039909)
                ·
                  refine ⟨32660564616737022007483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 174189677955930784039909 32660564616737022007483)
                  ·
                    rfl

theorem cell21_143114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 5, 1, 2, 4].length) (baseStart_143114 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_143114 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_143114 prefixEnd_143114 := by exact prefixLift 143114
  have htrace : WordTrace (prefixWord ++ tailWord_143114) baseStart_143114 baseEnd_143114 := by
    simpa [prefixWord, tailWord_143114, baseEnd_143114] using wordTrace_append hprefix tailTrace_143114
  have hstable : (prefixWord ++ tailWord_143114).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_143114).length < 2 ^ (prefixWord ++ tailWord_143114).sum := by decide
  have hdescent : baseEnd_143114 < baseStart_143114 := by decide
  rcases family_descends (prefixWord ++ tailWord_143114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_143176 : List Nat := [2, 1, 3, 1, 1, 5, 3, 2, 3]
def baseStart_143176 : Nat := 118140960795 + 143176 * 2 ^ 59
def prefixEnd_143176 : Nat := 4983230072969 + 3 ^ 40 * 143176 * 2
def baseEnd_143176 : Nat := 32674713861438691974023

theorem tailTrace_143176 : CollatzResearch.WordTrace tailWord_143176 prefixEnd_143176 32674713861438691974023 := by
  unfold tailWord_143176
  simp only [CollatzResearch.WordTrace]
  refine ⟨2611028864652639679572691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3481371819536852906096921 2611028864652639679572691)
  ·
    refine ⟨3916543296978959519359037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2611028864652639679572691 3916543296978959519359037)
    ·
      refine ⟨1468703736367109819759639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3916543296978959519359037 1468703736367109819759639)
      ·
        refine ⟨2203055604550664729639459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1468703736367109819759639 2203055604550664729639459)
        ·
          refine ⟨3304583406825997094459189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2203055604550664729639459 3304583406825997094459189)
          ·
            refine ⟨309804694389937227605549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 3304583406825997094459189 309804694389937227605549)
            ·
              refine ⟨116176760396226460352081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 309804694389937227605549 116176760396226460352081)
              ·
                refine ⟨87132570297169845264061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 116176760396226460352081 87132570297169845264061)
                ·
                  refine ⟨32674713861438691974023, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 87132570297169845264061 32674713861438691974023)
                  ·
                    rfl

theorem cell21_143176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 5, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 5, 3, 2, 3].length) (baseStart_143176 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_143176 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_143176 prefixEnd_143176 := by exact prefixLift 143176
  have htrace : WordTrace (prefixWord ++ tailWord_143176) baseStart_143176 baseEnd_143176 := by
    simpa [prefixWord, tailWord_143176, baseEnd_143176] using wordTrace_append hprefix tailTrace_143176
  have hstable : (prefixWord ++ tailWord_143176).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_143176).length < 2 ^ (prefixWord ++ tailWord_143176).sum := by decide
  have hdescent : baseEnd_143176 < baseStart_143176 := by decide
  rcases family_descends (prefixWord ++ tailWord_143176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_143201 : List Nat := [1, 2, 3, 1, 1, 1, 4, 1, 7]
def baseStart_143201 : Nat := 118140960795 + 143201 * 2 ^ 59
def prefixEnd_143201 : Nat := 4983230072969 + 3 ^ 40 * 143201 * 2
def baseEnd_143201 : Nat := 32680419202044204057305

theorem tailTrace_143201 : CollatzResearch.WordTrace tailWord_143201 prefixEnd_143201 32680419202044204057305 := by
  unfold tailWord_143201
  simp only [CollatzResearch.WordTrace]
  refine ⟨5222969554214708628805457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3481979702809805752536971 5222969554214708628805457)
  ·
    refine ⟨3917227165661031471604093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5222969554214708628805457 3917227165661031471604093)
    ·
      refine ⟨1468960187122886801851535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3917227165661031471604093 1468960187122886801851535)
      ·
        refine ⟨2203440280684330202777303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1468960187122886801851535 2203440280684330202777303)
        ·
          refine ⟨3305160421026495304165955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2203440280684330202777303 3305160421026495304165955)
          ·
            refine ⟨4957740631539742956248933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3305160421026495304165955 4957740631539742956248933)
            ·
              refine ⟨929576368413701804296675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4957740631539742956248933 929576368413701804296675)
              ·
                refine ⟨1394364552620552706445013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 929576368413701804296675 1394364552620552706445013)
                ·
                  refine ⟨32680419202044204057305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1394364552620552706445013 32680419202044204057305)
                  ·
                    rfl

theorem cell21_143201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 4, 1, 7].length) (baseStart_143201 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_143201 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_143201 prefixEnd_143201 := by exact prefixLift 143201
  have htrace : WordTrace (prefixWord ++ tailWord_143201) baseStart_143201 baseEnd_143201 := by
    simpa [prefixWord, tailWord_143201, baseEnd_143201] using wordTrace_append hprefix tailTrace_143201
  have hstable : (prefixWord ++ tailWord_143201).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_143201).length < 2 ^ (prefixWord ++ tailWord_143201).sum := by decide
  have hdescent : baseEnd_143201 < baseStart_143201 := by decide
  rcases family_descends (prefixWord ++ tailWord_143201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_143235 : List Nat := [1, 1, 1, 3, 4, 3, 1, 4, 3]
def baseStart_143235 : Nat := 118140960795 + 143235 * 2 ^ 59
def prefixEnd_143235 : Nat := 4983230072969 + 3 ^ 40 * 143235 * 2
def baseEnd_143235 : Nat := 32688178465267700490569

theorem tailTrace_143235 : CollatzResearch.WordTrace tailWord_143235 prefixEnd_143235 32688178465267700490569 := by
  unfold tailWord_143235
  simp only [CollatzResearch.WordTrace]
  refine ⟨5224209636091532435543159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3482806424061021623695439 5224209636091532435543159)
  ·
    refine ⟨7836314454137298653314739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5224209636091532435543159 7836314454137298653314739)
    ·
      refine ⟨11754471681205947979972109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7836314454137298653314739 11754471681205947979972109)
      ·
        refine ⟨4407926880452230492489541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11754471681205947979972109 4407926880452230492489541)
        ·
          refine ⟨826486290084793217341789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4407926880452230492489541 826486290084793217341789)
          ·
            refine ⟨309932358781797456503171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 826486290084793217341789 309932358781797456503171)
            ·
              refine ⟨464898538172696184754757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 309932358781797456503171 464898538172696184754757)
              ·
                refine ⟨87168475907380534641517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 464898538172696184754757 87168475907380534641517)
                ·
                  refine ⟨32688178465267700490569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 87168475907380534641517 32688178465267700490569)
                  ·
                    rfl

theorem cell21_143235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 3, 1, 4, 3].length) (baseStart_143235 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_143235 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_143235 prefixEnd_143235 := by exact prefixLift 143235
  have htrace : WordTrace (prefixWord ++ tailWord_143235) baseStart_143235 baseEnd_143235 := by
    simpa [prefixWord, tailWord_143235, baseEnd_143235] using wordTrace_append hprefix tailTrace_143235
  have hstable : (prefixWord ++ tailWord_143235).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_143235).length < 2 ^ (prefixWord ++ tailWord_143235).sum := by decide
  have hdescent : baseEnd_143235 < baseStart_143235 := by decide
  rcases family_descends (prefixWord ++ tailWord_143235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_143294 : List Nat := [4, 2, 1, 1, 1, 3, 1, 3, 5]
def baseStart_143294 : Nat := 118140960795 + 143294 * 2 ^ 59
def prefixEnd_143294 : Nat := 4983230072969 + 3 ^ 40 * 143294 * 2
def baseEnd_143294 : Nat := 32701643069096709007115

theorem tailTrace_143294 : CollatzResearch.WordTrace tailWord_143294 prefixEnd_143294 32701643069096709007115 := by
  unfold tailWord_143294
  simp only [CollatzResearch.WordTrace]
  refine ⟨653295192859723188992617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3484241028585190341293957 653295192859723188992617)
  ·
    refine ⟨489971394644792391744463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 653295192859723188992617 489971394644792391744463)
    ·
      refine ⟨734957091967188587616695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 489971394644792391744463 734957091967188587616695)
      ·
        refine ⟨1102435637950782881425043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 734957091967188587616695 1102435637950782881425043)
        ·
          refine ⟨1653653456926174322137565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1102435637950782881425043 1653653456926174322137565)
          ·
            refine ⟨620120046347315370801587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1653653456926174322137565 620120046347315370801587)
            ·
              refine ⟨930180069520973056202381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 620120046347315370801587 930180069520973056202381)
              ·
                refine ⟨348817526070364896075893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 930180069520973056202381 348817526070364896075893)
                ·
                  refine ⟨32701643069096709007115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 348817526070364896075893 32701643069096709007115)
                  ·
                    rfl

theorem cell21_143294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 1, 3, 5].length) (baseStart_143294 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_143294 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_143294 prefixEnd_143294 := by exact prefixLift 143294
  have htrace : WordTrace (prefixWord ++ tailWord_143294) baseStart_143294 baseEnd_143294 := by
    simpa [prefixWord, tailWord_143294, baseEnd_143294] using wordTrace_append hprefix tailTrace_143294
  have hstable : (prefixWord ++ tailWord_143294).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_143294).length < 2 ^ (prefixWord ++ tailWord_143294).sum := by decide
  have hdescent : baseEnd_143294 < baseStart_143294 := by decide
  rcases family_descends (prefixWord ++ tailWord_143294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_143314 : List Nat := [3, 2, 2, 3, 3, 1, 2, 5]
def baseStart_143314 : Nat := 118140960795 + 143314 * 2 ^ 59
def prefixEnd_143314 : Nat := 4983230072969 + 3 ^ 40 * 143314 * 2
def baseEnd_143314 : Nat := 10902069113860372891247

theorem tailTrace_143314 : CollatzResearch.WordTrace tailWord_143314 prefixEnd_143314 10902069113860372891247 := by
  unfold tailWord_143314
  simp only [CollatzResearch.WordTrace]
  refine ⟨1306772750701332231917249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3484727335203552618445997 1306772750701332231917249)
  ·
    refine ⟨980079563025999173937937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1306772750701332231917249 980079563025999173937937)
    ·
      refine ⟨735059672269499380453453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 980079563025999173937937 735059672269499380453453)
      ·
        refine ⟨275647377101062267670045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 735059672269499380453453 275647377101062267670045)
        ·
          refine ⟨103367766412898350376267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 275647377101062267670045 103367766412898350376267)
          ·
            refine ⟨155051649619347525564401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 103367766412898350376267 155051649619347525564401)
            ·
              refine ⟨116288737214510644173301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 155051649619347525564401 116288737214510644173301)
              ·
                refine ⟨10902069113860372891247, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 116288737214510644173301 10902069113860372891247)
                ·
                  rfl

theorem cell21_143314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 3, 1, 2, 5].length) (baseStart_143314 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_143314 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_143314 prefixEnd_143314 := by exact prefixLift 143314
  have htrace : WordTrace (prefixWord ++ tailWord_143314) baseStart_143314 baseEnd_143314 := by
    simpa [prefixWord, tailWord_143314, baseEnd_143314] using wordTrace_append hprefix tailTrace_143314
  have hstable : (prefixWord ++ tailWord_143314).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_143314).length < 2 ^ (prefixWord ++ tailWord_143314).sum := by decide
  have hdescent : baseEnd_143314 < baseStart_143314 := by decide
  rcases family_descends (prefixWord ++ tailWord_143314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_143491 : List Nat := [1, 1, 1, 3, 3, 3, 4, 5]
def baseStart_143491 : Nat := 118140960795 + 143491 * 2 ^ 59
def prefixEnd_143491 : Nat := 4983230072969 + 3 ^ 40 * 143491 * 2
def baseEnd_143491 : Nat := 10915533717689381407793

theorem tailTrace_143491 : CollatzResearch.WordTrace tailWord_143491 prefixEnd_143491 10915533717689381407793 := by
  unfold tailWord_143491
  simp only [CollatzResearch.WordTrace]
  refine ⟨5233546723164088156862327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3489031148776058771241551 5233546723164088156862327)
  ·
    refine ⟨7850320084746132235293491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5233546723164088156862327 7850320084746132235293491)
    ·
      refine ⟨11775480127119198352940237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7850320084746132235293491 11775480127119198352940237)
      ·
        refine ⟨4415805047669699382352589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11775480127119198352940237 4415805047669699382352589)
        ·
          refine ⟨1655926892876137268382221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4415805047669699382352589 1655926892876137268382221)
          ·
            refine ⟨620972584828551475643333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1655926892876137268382221 620972584828551475643333)
            ·
              refine ⟨116432359655353401683125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 620972584828551475643333 116432359655353401683125)
              ·
                refine ⟨10915533717689381407793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 116432359655353401683125 10915533717689381407793)
                ·
                  rfl

theorem cell21_143491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 4, 5].length) (baseStart_143491 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_143491 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_143491 prefixEnd_143491 := by exact prefixLift 143491
  have htrace : WordTrace (prefixWord ++ tailWord_143491) baseStart_143491 baseEnd_143491 := by
    simpa [prefixWord, tailWord_143491, baseEnd_143491] using wordTrace_append hprefix tailTrace_143491
  have hstable : (prefixWord ++ tailWord_143491).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_143491).length < 2 ^ (prefixWord ++ tailWord_143491).sum := by decide
  have hdescent : baseEnd_143491 < baseStart_143491 := by decide
  rcases family_descends (prefixWord ++ tailWord_143491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_143573 : List Nat := [1, 3, 2, 4, 2, 2, 2, 2, 3]
def baseStart_143573 : Nat := 118140960795 + 143573 * 2 ^ 59
def prefixEnd_143573 : Nat := 4983230072969 + 3 ^ 40 * 143573 * 2
def baseEnd_143573 : Nat := 32765314670254223856545

theorem tailTrace_143573 : CollatzResearch.WordTrace tailWord_143573 prefixEnd_143573 32765314670254223856545 := by
  unfold tailWord_143573
  simp only [CollatzResearch.WordTrace]
  refine ⟨5236537508867016161347373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3491025005911344107564915 5236537508867016161347373)
  ·
    refine ⟨1963701565825131060505265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5236537508867016161347373 1963701565825131060505265)
    ·
      refine ⟨1472776174368848295378949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1963701565825131060505265 1472776174368848295378949)
      ·
        refine ⟨276145532694159055383553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1472776174368848295378949 276145532694159055383553)
        ·
          refine ⟨207109149520619291537665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 276145532694159055383553 207109149520619291537665)
          ·
            refine ⟨155331862140464468653249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 207109149520619291537665 155331862140464468653249)
            ·
              refine ⟨116498896605348351489937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 155331862140464468653249 116498896605348351489937)
              ·
                refine ⟨87374172454011263617453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 116498896605348351489937 87374172454011263617453)
                ·
                  refine ⟨32765314670254223856545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 87374172454011263617453 32765314670254223856545)
                  ·
                    rfl

theorem cell21_143573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 2, 2, 2, 3].length) (baseStart_143573 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_143573 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_143573 prefixEnd_143573 := by exact prefixLift 143573
  have htrace : WordTrace (prefixWord ++ tailWord_143573) baseStart_143573 baseEnd_143573 := by
    simpa [prefixWord, tailWord_143573, baseEnd_143573] using wordTrace_append hprefix tailTrace_143573
  have hstable : (prefixWord ++ tailWord_143573).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_143573).length < 2 ^ (prefixWord ++ tailWord_143573).sum := by decide
  have hdescent : baseEnd_143573 < baseStart_143573 := by decide
  rcases family_descends (prefixWord ++ tailWord_143573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_143784 : List Nat := [2, 1, 6, 1, 1, 2, 2, 3, 3]
def baseStart_143784 : Nat := 118140960795 + 143784 * 2 ^ 59
def prefixEnd_143784 : Nat := 4983230072969 + 3 ^ 40 * 143784 * 2
def baseEnd_143784 : Nat := 32813467744964745839447

theorem tailTrace_143784 : CollatzResearch.WordTrace tailWord_143784 prefixEnd_143784 32813467744964745839447 := by
  unfold tailWord_143784
  simp only [CollatzResearch.WordTrace]
  refine ⟨2622116655551299598639203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3496155540735066131518937 2622116655551299598639203)
  ·
    refine ⟨3933174983326949397958805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2622116655551299598639203 3933174983326949397958805)
    ·
      refine ⟨184367577343450753029319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 3933174983326949397958805 184367577343450753029319)
      ·
        refine ⟨276551366015176129543979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 184367577343450753029319 276551366015176129543979)
        ·
          refine ⟨414827049022764194315969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 276551366015176129543979 414827049022764194315969)
          ·
            refine ⟨311120286767073145736977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 414827049022764194315969 311120286767073145736977)
            ·
              refine ⟨233340215075304859302733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 311120286767073145736977 233340215075304859302733)
              ·
                refine ⟨87502580653239322238525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 233340215075304859302733 87502580653239322238525)
                ·
                  refine ⟨32813467744964745839447, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 87502580653239322238525 32813467744964745839447)
                  ·
                    rfl

theorem cell21_143784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 2, 2, 3, 3].length) (baseStart_143784 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_143784 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_143784 prefixEnd_143784 := by exact prefixLift 143784
  have htrace : WordTrace (prefixWord ++ tailWord_143784) baseStart_143784 baseEnd_143784 := by
    simpa [prefixWord, tailWord_143784, baseEnd_143784] using wordTrace_append hprefix tailTrace_143784
  have hstable : (prefixWord ++ tailWord_143784).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_143784).length < 2 ^ (prefixWord ++ tailWord_143784).sum := by decide
  have hdescent : baseEnd_143784 < baseStart_143784 := by decide
  rcases family_descends (prefixWord ++ tailWord_143784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_143854 : List Nat := [4, 1, 2, 1, 2, 2, 9]
def baseStart_143854 : Nat := 118140960795 + 143854 * 2 ^ 59
def prefixEnd_143854 : Nat := 4983230072969 + 3 ^ 40 * 143854 * 2
def baseEnd_143854 : Nat := 3647715855406686630293

theorem tailTrace_143854 : CollatzResearch.WordTrace tailWord_143854 prefixEnd_143854 3647715855406686630293 := by
  unfold tailWord_143854
  simp only [CollatzResearch.WordTrace]
  refine ⟨655848302606125144040827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3497857613899334101551077 655848302606125144040827)
  ·
    refine ⟨983772453909187716061241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 655848302606125144040827 983772453909187716061241)
    ·
      refine ⟨737829340431890787045931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 983772453909187716061241 737829340431890787045931)
      ·
        refine ⟨1106744010647836180568897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 737829340431890787045931 1106744010647836180568897)
        ·
          refine ⟨830058007985877135426673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1106744010647836180568897 830058007985877135426673)
          ·
            refine ⟨622543505989407851570005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 830058007985877135426673 622543505989407851570005)
            ·
              refine ⟨3647715855406686630293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 622543505989407851570005 3647715855406686630293)
              ·
                rfl

theorem cell21_143854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 9].length) (baseStart_143854 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_143854 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_143854 prefixEnd_143854 := by exact prefixLift 143854
  have htrace : WordTrace (prefixWord ++ tailWord_143854) baseStart_143854 baseEnd_143854 := by
    simpa [prefixWord, tailWord_143854, baseEnd_143854] using wordTrace_append hprefix tailTrace_143854
  have hstable : (prefixWord ++ tailWord_143854).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_143854).length < 2 ^ (prefixWord ++ tailWord_143854).sum := by decide
  have hdescent : baseEnd_143854 < baseStart_143854 := by decide
  rcases family_descends (prefixWord ++ tailWord_143854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_143874 : List Nat := [3, 4, 1, 2, 2, 1, 1, 3, 4]
def baseStart_143874 : Nat := 118140960795 + 143874 * 2 ^ 59
def prefixEnd_143874 : Nat := 4983230072969 + 3 ^ 40 * 143874 * 2
def baseEnd_143874 : Nat := 32834006971144589339263

theorem tailTrace_143874 : CollatzResearch.WordTrace tailWord_143874 prefixEnd_143874 32834006971144589339263 := by
  unfold tailWord_143874
  simp only [CollatzResearch.WordTrace]
  refine ⟨1311878970194136142013669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3498343920517696378703117 1311878970194136142013669)
  ·
    refine ⟨245977306911400526627563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1311878970194136142013669 245977306911400526627563)
    ·
      refine ⟨368965960367100789941345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 245977306911400526627563 368965960367100789941345)
      ·
        refine ⟨276724470275325592456009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 368965960367100789941345 276724470275325592456009)
        ·
          refine ⟨207543352706494194342007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 276724470275325592456009 207543352706494194342007)
          ·
            refine ⟨311315029059741291513011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 207543352706494194342007 311315029059741291513011)
            ·
              refine ⟨466972543589611937269517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 311315029059741291513011 466972543589611937269517)
              ·
                refine ⟨175114703846104476476069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 466972543589611937269517 175114703846104476476069)
                ·
                  refine ⟨32834006971144589339263, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 175114703846104476476069 32834006971144589339263)
                  ·
                    rfl

theorem cell21_143874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 1, 1, 3, 4].length) (baseStart_143874 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_143874 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_143874 prefixEnd_143874 := by exact prefixLift 143874
  have htrace : WordTrace (prefixWord ++ tailWord_143874) baseStart_143874 baseEnd_143874 := by
    simpa [prefixWord, tailWord_143874, baseEnd_143874] using wordTrace_append hprefix tailTrace_143874
  have hstable : (prefixWord ++ tailWord_143874).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_143874).length < 2 ^ (prefixWord ++ tailWord_143874).sum := by decide
  have hdescent : baseEnd_143874 < baseStart_143874 := by decide
  rcases family_descends (prefixWord ++ tailWord_143874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_143930 : List Nat := [3, 1, 1, 1, 3, 3, 3, 6]
def baseStart_143930 : Nat := 118140960795 + 143930 * 2 ^ 59
def prefixEnd_143930 : Nat := 4983230072969 + 3 ^ 40 * 143930 * 2
def baseEnd_143930 : Nat := 10948928978033645468605

theorem tailTrace_143930 : CollatzResearch.WordTrace tailWord_143930 prefixEnd_143930 10948928978033645468605 := by
  unfold tailWord_143930
  simp only [CollatzResearch.WordTrace]
  refine ⟨1312389592143416533023311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3499705579049110754728829 1312389592143416533023311)
  ·
    refine ⟨1968584388215124799534967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1312389592143416533023311 1968584388215124799534967)
    ·
      refine ⟨2952876582322687199302451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1968584388215124799534967 2952876582322687199302451)
      ·
        refine ⟨4429314873484030798953677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2952876582322687199302451 4429314873484030798953677)
        ·
          refine ⟨1660993077556511549607629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4429314873484030798953677 1660993077556511549607629)
          ·
            refine ⟨622872404083691831102861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1660993077556511549607629 622872404083691831102861)
            ·
              refine ⟨233577151531384436663573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 622872404083691831102861 233577151531384436663573)
              ·
                refine ⟨10948928978033645468605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 233577151531384436663573 10948928978033645468605)
                ·
                  rfl

theorem cell21_143930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 3, 6].length) (baseStart_143930 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_143930 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_143930 prefixEnd_143930 := by exact prefixLift 143930
  have htrace : WordTrace (prefixWord ++ tailWord_143930) baseStart_143930 baseEnd_143930 := by
    simpa [prefixWord, tailWord_143930, baseEnd_143930] using wordTrace_append hprefix tailTrace_143930
  have hstable : (prefixWord ++ tailWord_143930).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_143930).length < 2 ^ (prefixWord ++ tailWord_143930).sum := by decide
  have hdescent : baseEnd_143930 < baseStart_143930 := by decide
  rcases family_descends (prefixWord ++ tailWord_143930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_143978 : List Nat := [3, 1, 3, 2, 1, 1, 1, 6, 3]
def baseStart_143978 : Nat := 118140960795 + 143978 * 2 ^ 59
def prefixEnd_143978 : Nat := 4983230072969 + 3 ^ 40 * 143978 * 2
def baseEnd_143978 : Nat := 32857741188063519605717

theorem tailTrace_143978 : CollatzResearch.WordTrace tailWord_143978 prefixEnd_143978 32857741188063519605717 := by
  unfold tailWord_143978
  simp only [CollatzResearch.WordTrace]
  refine ⟨1312827268099942582460147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3500872714933180219893725 1312827268099942582460147)
  ·
    refine ⟨1969240902149913873690221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1312827268099942582460147 1969240902149913873690221)
    ·
      refine ⟨738465338306217702633833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1969240902149913873690221 738465338306217702633833)
      ·
        refine ⟨553849003729663276975375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 738465338306217702633833 553849003729663276975375)
        ·
          refine ⟨830773505594494915463063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 553849003729663276975375 830773505594494915463063)
          ·
            refine ⟨1246160258391742373194595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 830773505594494915463063 1246160258391742373194595)
            ·
              refine ⟨1869240387587613559791893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1246160258391742373194595 1869240387587613559791893)
              ·
                refine ⟨87620643168169385615245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1869240387587613559791893 87620643168169385615245)
                ·
                  refine ⟨32857741188063519605717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 87620643168169385615245 32857741188063519605717)
                  ·
                    rfl

theorem cell21_143978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 1, 6, 3].length) (baseStart_143978 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_143978 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_143978 prefixEnd_143978 := by exact prefixLift 143978
  have htrace : WordTrace (prefixWord ++ tailWord_143978) baseStart_143978 baseEnd_143978 := by
    simpa [prefixWord, tailWord_143978, baseEnd_143978] using wordTrace_append hprefix tailTrace_143978
  have hstable : (prefixWord ++ tailWord_143978).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_143978).length < 2 ^ (prefixWord ++ tailWord_143978).sum := by decide
  have hdescent : baseEnd_143978 < baseStart_143978 := by decide
  rcases family_descends (prefixWord ++ tailWord_143978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_144082 : List Nat := [3, 2, 2, 2, 3, 9]
def baseStart_144082 : Nat := 118140960795 + 144082 * 2 ^ 59
def prefixEnd_144082 : Nat := 4983230072969 + 3 ^ 40 * 144082 * 2
def baseEnd_144082 : Nat := 1217832422406757402673

theorem tailTrace_144082 : CollatzResearch.WordTrace tailWord_144082 prefixEnd_144082 1217832422406757402673 := by
  unfold tailWord_144082
  simp only [CollatzResearch.WordTrace]
  refine ⟨1313775566005749022906625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3503401509348664061084333 1313775566005749022906625)
  ·
    refine ⟨985331674504311767179969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1313775566005749022906625 985331674504311767179969)
    ·
      refine ⟨738998755878233825384977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 985331674504311767179969 738998755878233825384977)
      ·
        refine ⟨554249066908675369038733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 738998755878233825384977 554249066908675369038733)
        ·
          refine ⟨207843400090753263389525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 554249066908675369038733 207843400090753263389525)
          ·
            refine ⟨1217832422406757402673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 207843400090753263389525 1217832422406757402673)
            ·
              rfl

theorem cell21_144082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 9].length) (baseStart_144082 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_144082 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_144082 prefixEnd_144082 := by exact prefixLift 144082
  have htrace : WordTrace (prefixWord ++ tailWord_144082) baseStart_144082 baseEnd_144082 := by
    simpa [prefixWord, tailWord_144082, baseEnd_144082] using wordTrace_append hprefix tailTrace_144082
  have hstable : (prefixWord ++ tailWord_144082).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_144082).length < 2 ^ (prefixWord ++ tailWord_144082).sum := by decide
  have hdescent : baseEnd_144082 < baseStart_144082 := by decide
  rcases family_descends (prefixWord ++ tailWord_144082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_144096 : List Nat := [2, 1, 1, 3, 1, 2, 1, 5, 5]
def baseStart_144096 : Nat := 118140960795 + 144096 * 2 ^ 59
def prefixEnd_144096 : Nat := 4983230072969 + 3 ^ 40 * 144096 * 2
def baseEnd_144096 : Nat := 32884670395721536638809

theorem tailTrace_144096 : CollatzResearch.WordTrace tailWord_144096 prefixEnd_144096 32884670395721536638809 := by
  unfold tailWord_144096
  simp only [CollatzResearch.WordTrace]
  refine ⟨2627806442986138241318071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3503741923981517655090761 2627806442986138241318071)
  ·
    refine ⟨3941709664479207361977107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2627806442986138241318071 3941709664479207361977107)
    ·
      refine ⟨5912564496718811042965661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3941709664479207361977107 5912564496718811042965661)
      ·
        refine ⟨2217211686269554141112123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5912564496718811042965661 2217211686269554141112123)
        ·
          refine ⟨3325817529404331211668185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2217211686269554141112123 3325817529404331211668185)
          ·
            refine ⟨2494363147053248408751139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3325817529404331211668185 2494363147053248408751139)
            ·
              refine ⟨3741544720579872613126709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2494363147053248408751139 3741544720579872613126709)
              ·
                refine ⟨350769817554363057480629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3741544720579872613126709 350769817554363057480629)
                ·
                  refine ⟨32884670395721536638809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 350769817554363057480629 32884670395721536638809)
                  ·
                    rfl

theorem cell21_144096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 5, 5].length) (baseStart_144096 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_144096 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_144096 prefixEnd_144096 := by exact prefixLift 144096
  have htrace : WordTrace (prefixWord ++ tailWord_144096) baseStart_144096 baseEnd_144096 := by
    simpa [prefixWord, tailWord_144096, baseEnd_144096] using wordTrace_append hprefix tailTrace_144096
  have hstable : (prefixWord ++ tailWord_144096).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_144096).length < 2 ^ (prefixWord ++ tailWord_144096).sum := by decide
  have hdescent : baseEnd_144096 < baseStart_144096 := by decide
  rcases family_descends (prefixWord ++ tailWord_144096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_144099 : List Nat := [1, 1, 1, 7, 1, 3, 1, 6]
def baseStart_144099 : Nat := 118140960795 + 144099 * 2 ^ 59
def prefixEnd_144099 : Nat := 4983230072969 + 3 ^ 40 * 144099 * 2
def baseEnd_144099 : Nat := 10961785012198066029601

theorem tailTrace_144099 : CollatzResearch.WordTrace tailWord_144099 prefixEnd_144099 10961785012198066029601 := by
  unfold tailWord_144099
  simp only [CollatzResearch.WordTrace]
  refine ⟨5255722304961407994995351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3503814869974271996663567 5255722304961407994995351)
  ·
    refine ⟨7883583457442111992493027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5255722304961407994995351 7883583457442111992493027)
    ·
      refine ⟨11825375186163167988739541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7883583457442111992493027 11825375186163167988739541)
      ·
        refine ⟨277157230925699249736083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 11825375186163167988739541 277157230925699249736083)
        ·
          refine ⟨415735846388548874604125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 277157230925699249736083 415735846388548874604125)
          ·
            refine ⟨155900942395705827976547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 415735846388548874604125 155900942395705827976547)
            ·
              refine ⟨233851413593558741964821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 155900942395705827976547 233851413593558741964821)
              ·
                refine ⟨10961785012198066029601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 233851413593558741964821 10961785012198066029601)
                ·
                  rfl

theorem cell21_144099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 3, 1, 6].length) (baseStart_144099 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_144099 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_144099 prefixEnd_144099 := by exact prefixLift 144099
  have htrace : WordTrace (prefixWord ++ tailWord_144099) baseStart_144099 baseEnd_144099 := by
    simpa [prefixWord, tailWord_144099, baseEnd_144099] using wordTrace_append hprefix tailTrace_144099
  have hstable : (prefixWord ++ tailWord_144099).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_144099).length < 2 ^ (prefixWord ++ tailWord_144099).sum := by decide
  have hdescent : baseEnd_144099 < baseStart_144099 := by decide
  rcases family_descends (prefixWord ++ tailWord_144099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_144172 : List Nat := [2, 2, 1, 1, 1, 4, 1, 4, 5]
def baseStart_144172 : Nat := 118140960795 + 144172 * 2 ^ 59
def prefixEnd_144172 : Nat := 4983230072969 + 3 ^ 40 * 144172 * 2
def baseEnd_144172 : Nat := 32902014631162293371987

theorem tailTrace_144172 : CollatzResearch.WordTrace tailWord_144172 prefixEnd_144172 32902014631162293371987 := by
  unfold tailWord_144172
  simp only [CollatzResearch.WordTrace]
  refine ⟨2629192416848470731201385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3505589889131294308268513 2629192416848470731201385)
  ·
    refine ⟨1971894312636353048401039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2629192416848470731201385 1971894312636353048401039)
    ·
      refine ⟨2957841468954529572601559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1971894312636353048401039 2957841468954529572601559)
      ·
        refine ⟨4436762203431794358902339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2957841468954529572601559 4436762203431794358902339)
        ·
          refine ⟨6655143305147691538353509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4436762203431794358902339 6655143305147691538353509)
          ·
            refine ⟨1247839369715192163441283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6655143305147691538353509 1247839369715192163441283)
            ·
              refine ⟨1871759054572788245161925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1247839369715192163441283 1871759054572788245161925)
              ·
                refine ⟨350954822732397795967861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1871759054572788245161925 350954822732397795967861)
                ·
                  refine ⟨32902014631162293371987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 350954822732397795967861 32902014631162293371987)
                  ·
                    rfl

theorem cell21_144172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 5].length) (baseStart_144172 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_144172 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_144172 prefixEnd_144172 := by exact prefixLift 144172
  have htrace : WordTrace (prefixWord ++ tailWord_144172) baseStart_144172 baseEnd_144172 := by
    simpa [prefixWord, tailWord_144172, baseEnd_144172] using wordTrace_append hprefix tailTrace_144172
  have hstable : (prefixWord ++ tailWord_144172).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_144172).length < 2 ^ (prefixWord ++ tailWord_144172).sum := by decide
  have hdescent : baseEnd_144172 < baseStart_144172 := by decide
  rcases family_descends (prefixWord ++ tailWord_144172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_144217 : List Nat := [1, 2, 1, 2, 2, 4, 1, 8]
def baseStart_144217 : Nat := 118140960795 + 144217 * 2 ^ 59
def prefixEnd_144217 : Nat := 4983230072969 + 3 ^ 40 * 144217 * 2
def baseEnd_144217 : Nat := 10970761414750738373965

theorem tailTrace_144217 : CollatzResearch.WordTrace tailWord_144217 prefixEnd_144217 10970761414750738373965 := by
  unfold tailWord_144217
  simp only [CollatzResearch.WordTrace]
  refine ⟨5260026118533914147790905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3506684079022609431860603 5260026118533914147790905)
  ·
    refine ⟨3945019588900435610843179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5260026118533914147790905 3945019588900435610843179)
    ·
      refine ⟨5917529383350653416264769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3945019588900435610843179 5917529383350653416264769)
      ·
        refine ⟨4438147037512990062198577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5917529383350653416264769 4438147037512990062198577)
        ·
          refine ⟨3328610278134742546648933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4438147037512990062198577 3328610278134742546648933)
          ·
            refine ⟨624114427150264227496675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3328610278134742546648933 624114427150264227496675)
            ·
              refine ⟨936171640725396341245013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 624114427150264227496675 936171640725396341245013)
              ·
                refine ⟨10970761414750738373965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 936171640725396341245013 10970761414750738373965)
                ·
                  rfl

theorem cell21_144217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 1, 8].length) (baseStart_144217 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_144217 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_144217 prefixEnd_144217 := by exact prefixLift 144217
  have htrace : WordTrace (prefixWord ++ tailWord_144217) baseStart_144217 baseEnd_144217 := by
    simpa [prefixWord, tailWord_144217, baseEnd_144217] using wordTrace_append hprefix tailTrace_144217
  have hstable : (prefixWord ++ tailWord_144217).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_144217).length < 2 ^ (prefixWord ++ tailWord_144217).sum := by decide
  have hdescent : baseEnd_144217 < baseStart_144217 := by decide
  rcases family_descends (prefixWord ++ tailWord_144217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_144254 : List Nat := [4, 2, 3, 1, 2, 1, 2, 2, 4]
def baseStart_144254 : Nat := 118140960795 + 144254 * 2 ^ 59
def prefixEnd_144254 : Nat := 4983230072969 + 3 ^ 40 * 144254 * 2
def baseEnd_144254 : Nat := 32920728148348373005153

theorem tailTrace_144254 : CollatzResearch.WordTrace tailWord_144254 prefixEnd_144254 32920728148348373005153 := by
  unfold tailWord_144254
  simp only [CollatzResearch.WordTrace]
  refine ⟨657671952424983683360977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3507583746266579644591877 657671952424983683360977)
  ·
    refine ⟨493253964318737762520733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 657671952424983683360977 493253964318737762520733)
    ·
      refine ⟨184970236619526660945275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 493253964318737762520733 184970236619526660945275)
      ·
        refine ⟨277455354929289991417913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 184970236619526660945275 277455354929289991417913)
        ·
          refine ⟨208091516196967493563435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 277455354929289991417913 208091516196967493563435)
          ·
            refine ⟨312137274295451240345153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 208091516196967493563435 312137274295451240345153)
            ·
              refine ⟨234102955721588430258865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 312137274295451240345153 234102955721588430258865)
              ·
                refine ⟨175577216791191322694149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 234102955721588430258865 175577216791191322694149)
                ·
                  refine ⟨32920728148348373005153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 175577216791191322694149 32920728148348373005153)
                  ·
                    rfl

theorem cell21_144254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 1, 2, 2, 4].length) (baseStart_144254 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_144254 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_144254 prefixEnd_144254 := by exact prefixLift 144254
  have htrace : WordTrace (prefixWord ++ tailWord_144254) baseStart_144254 baseEnd_144254 := by
    simpa [prefixWord, tailWord_144254, baseEnd_144254] using wordTrace_append hprefix tailTrace_144254
  have hstable : (prefixWord ++ tailWord_144254).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_144254).length < 2 ^ (prefixWord ++ tailWord_144254).sum := by decide
  have hdescent : baseEnd_144254 < baseStart_144254 := by decide
  rcases family_descends (prefixWord ++ tailWord_144254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_144279 : List Nat := [1, 1, 3, 3, 1, 2, 1, 5, 4]
def baseStart_144279 : Nat := 118140960795 + 144279 * 2 ^ 59
def prefixEnd_144279 : Nat := 4983230072969 + 3 ^ 40 * 144279 * 2
def baseEnd_144279 : Nat := 32926433488953885088435

theorem tailTrace_144279 : CollatzResearch.WordTrace tailWord_144279 prefixEnd_144279 32926433488953885088435 := by
  unfold tailWord_144279
  simp only [CollatzResearch.WordTrace]
  refine ⟨5262287444309298736547891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3508191629539532491031927 5262287444309298736547891)
  ·
    refine ⟨7893431166463948104821837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5262287444309298736547891 7893431166463948104821837)
    ·
      refine ⟨2960036687423980539308189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7893431166463948104821837 2960036687423980539308189)
      ·
        refine ⟨1110013757783992702240571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2960036687423980539308189 1110013757783992702240571)
        ·
          refine ⟨1665020636675989053360857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1110013757783992702240571 1665020636675989053360857)
          ·
            refine ⟨1248765477506991790020643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1665020636675989053360857 1248765477506991790020643)
            ·
              refine ⟨1873148216260487685030965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1248765477506991790020643 1873148216260487685030965)
              ·
                refine ⟨175607645274420720471653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1873148216260487685030965 175607645274420720471653)
                ·
                  refine ⟨32926433488953885088435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 175607645274420720471653 32926433488953885088435)
                  ·
                    rfl

theorem cell21_144279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 1, 5, 4].length) (baseStart_144279 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_144279 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_144279 prefixEnd_144279 := by exact prefixLift 144279
  have htrace : WordTrace (prefixWord ++ tailWord_144279) baseStart_144279 baseEnd_144279 := by
    simpa [prefixWord, tailWord_144279, baseEnd_144279] using wordTrace_append hprefix tailTrace_144279
  have hstable : (prefixWord ++ tailWord_144279).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_144279).length < 2 ^ (prefixWord ++ tailWord_144279).sum := by decide
  have hdescent : baseEnd_144279 < baseStart_144279 := by decide
  rcases family_descends (prefixWord ++ tailWord_144279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_144369 : List Nat := [1, 2, 2, 2, 4, 1, 9]
def baseStart_144369 : Nat := 118140960795 + 144369 * 2 ^ 59
def prefixEnd_144369 : Nat := 4983230072969 + 3 ^ 40 * 144369 * 2
def baseEnd_144369 : Nat := 3660774746125969843139

theorem tailTrace_144369 : CollatzResearch.WordTrace tailWord_144369 prefixEnd_144369 3660774746125969843139 := by
  unfold tailWord_144369
  simp only [CollatzResearch.WordTrace]
  refine ⟨5265570013983244107324161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3510380009322162738216107 5265570013983244107324161)
  ·
    refine ⟨3949177510487433080493121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5265570013983244107324161 3949177510487433080493121)
    ·
      refine ⟨2961883132865574810369841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3949177510487433080493121 2961883132865574810369841)
      ·
        refine ⟨2221412349649181107777381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2961883132865574810369841 2221412349649181107777381)
        ·
          refine ⟨416514815559221457708259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2221412349649181107777381 416514815559221457708259)
          ·
            refine ⟨624772223338832186562389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 416514815559221457708259 624772223338832186562389)
            ·
              refine ⟨3660774746125969843139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 624772223338832186562389 3660774746125969843139)
              ·
                rfl

theorem cell21_144369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 9].length) (baseStart_144369 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_144369 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_144369 prefixEnd_144369 := by exact prefixLift 144369
  have htrace : WordTrace (prefixWord ++ tailWord_144369) baseStart_144369 baseEnd_144369 := by
    simpa [prefixWord, tailWord_144369, baseEnd_144369] using wordTrace_append hprefix tailTrace_144369
  have hstable : (prefixWord ++ tailWord_144369).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_144369).length < 2 ^ (prefixWord ++ tailWord_144369).sum := by decide
  have hdescent : baseEnd_144369 < baseStart_144369 := by decide
  rcases family_descends (prefixWord ++ tailWord_144369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_144462 : List Nat := [4, 1, 1, 1, 1, 3, 5, 5]
def baseStart_144462 : Nat := 118140960795 + 144462 * 2 ^ 59
def prefixEnd_144462 : Nat := 4983230072969 + 3 ^ 40 * 144462 * 2
def baseEnd_144462 : Nat := 10989398860728744512687

theorem tailTrace_144462 : CollatzResearch.WordTrace tailWord_144462 prefixEnd_144462 10989398860728744512687 := by
  unfold tailWord_144462
  simp only [CollatzResearch.WordTrace]
  refine ⟨658620250330790123807455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3512641335097547326973093 658620250330790123807455)
  ·
    refine ⟨987930375496185185711183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 658620250330790123807455 987930375496185185711183)
    ·
      refine ⟨1481895563244277778566775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 987930375496185185711183 1481895563244277778566775)
      ·
        refine ⟨2222843344866416667850163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1481895563244277778566775 2222843344866416667850163)
        ·
          refine ⟨3334265017299625001775245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2222843344866416667850163 3334265017299625001775245)
          ·
            refine ⟨1250349381487359375665717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3334265017299625001775245 1250349381487359375665717)
            ·
              refine ⟨117220254514439941468661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1250349381487359375665717 117220254514439941468661)
              ·
                refine ⟨10989398860728744512687, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 117220254514439941468661 10989398860728744512687)
                ·
                  rfl

theorem cell21_144462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 5, 5].length) (baseStart_144462 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_144462 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_144462 prefixEnd_144462 := by exact prefixLift 144462
  have htrace : WordTrace (prefixWord ++ tailWord_144462) baseStart_144462 baseEnd_144462 := by
    simpa [prefixWord, tailWord_144462, baseEnd_144462] using wordTrace_append hprefix tailTrace_144462
  have hstable : (prefixWord ++ tailWord_144462).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_144462).length < 2 ^ (prefixWord ++ tailWord_144462).sum := by decide
  have hdescent : baseEnd_144462 < baseStart_144462 := by decide
  rcases family_descends (prefixWord ++ tailWord_144462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_144476 : List Nat := [2, 2, 4, 1, 1, 1, 1, 2, 7]
def baseStart_144476 : Nat := 118140960795 + 144476 * 2 ^ 59
def prefixEnd_144476 : Nat := 4983230072969 + 3 ^ 40 * 144476 * 2
def baseEnd_144476 : Nat := 32971391572925320304699

theorem tailTrace_144476 : CollatzResearch.WordTrace tailWord_144476 prefixEnd_144476 32971391572925320304699 := by
  unfold tailWord_144476
  simp only [CollatzResearch.WordTrace]
  refine ⟨2634736312297800690734641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3512981749730400920979521 2634736312297800690734641)
  ·
    refine ⟨1976052234223350518050981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2634736312297800690734641 1976052234223350518050981)
    ·
      refine ⟨370509793916878222134559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1976052234223350518050981 370509793916878222134559)
      ·
        refine ⟨555764690875317333201839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 370509793916878222134559 555764690875317333201839)
        ·
          refine ⟨833647036312975999802759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 555764690875317333201839 833647036312975999802759)
          ·
            refine ⟨1250470554469463999704139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 833647036312975999802759 1250470554469463999704139)
            ·
              refine ⟨1875705831704195999556209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1250470554469463999704139 1875705831704195999556209)
              ·
                refine ⟨1406779373778146999667157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1875705831704195999556209 1406779373778146999667157)
                ·
                  refine ⟨32971391572925320304699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1406779373778146999667157 32971391572925320304699)
                  ·
                    rfl

theorem cell21_144476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 1, 2, 7].length) (baseStart_144476 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_144476 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_144476 prefixEnd_144476 := by exact prefixLift 144476
  have htrace : WordTrace (prefixWord ++ tailWord_144476) baseStart_144476 baseEnd_144476 := by
    simpa [prefixWord, tailWord_144476, baseEnd_144476] using wordTrace_append hprefix tailTrace_144476
  have hstable : (prefixWord ++ tailWord_144476).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_144476).length < 2 ^ (prefixWord ++ tailWord_144476).sum := by decide
  have hdescent : baseEnd_144476 < baseStart_144476 := by decide
  rcases family_descends (prefixWord ++ tailWord_144476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_144493 : List Nat := [1, 5, 1, 1, 2, 3, 2, 1, 5]
def baseStart_144493 : Nat := 118140960795 + 144493 * 2 ^ 59
def prefixEnd_144493 : Nat := 4983230072969 + 3 ^ 40 * 144493 * 2
def baseEnd_144493 : Nat := 32975271204537068521331

theorem tailTrace_144493 : CollatzResearch.WordTrace tailWord_144493 prefixEnd_144493 32975271204537068521331 := by
  unfold tailWord_144493
  simp only [CollatzResearch.WordTrace]
  refine ⟨5270092665534013284838133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3513395110356008856558755 5270092665534013284838133)
  ·
    refine ⟨494071187393813745453575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 5270092665534013284838133 494071187393813745453575)
    ·
      refine ⟨741106781090720618180363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 494071187393813745453575 741106781090720618180363)
      ·
        refine ⟨1111660171636080927270545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 741106781090720618180363 1111660171636080927270545)
        ·
          refine ⟨833745128727060695452909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1111660171636080927270545 833745128727060695452909)
          ·
            refine ⟨312654423272647760794841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 833745128727060695452909 312654423272647760794841)
            ·
              refine ⟨234490817454485820596131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 312654423272647760794841 234490817454485820596131)
              ·
                refine ⟨351736226181728730894197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 234490817454485820596131 351736226181728730894197)
                ·
                  refine ⟨32975271204537068521331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 351736226181728730894197 32975271204537068521331)
                  ·
                    rfl

theorem cell21_144493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 3, 2, 1, 5].length) (baseStart_144493 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_144493 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_144493 prefixEnd_144493 := by exact prefixLift 144493
  have htrace : WordTrace (prefixWord ++ tailWord_144493) baseStart_144493 baseEnd_144493 := by
    simpa [prefixWord, tailWord_144493, baseEnd_144493] using wordTrace_append hprefix tailTrace_144493
  have hstable : (prefixWord ++ tailWord_144493).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_144493).length < 2 ^ (prefixWord ++ tailWord_144493).sum := by decide
  have hdescent : baseEnd_144493 < baseStart_144493 := by decide
  rcases family_descends (prefixWord ++ tailWord_144493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_144521 : List Nat := [1, 2, 1, 1, 4, 4, 1, 7]
def baseStart_144521 : Nat := 118140960795 + 144521 * 2 ^ 59
def prefixEnd_144521 : Nat := 4983230072969 + 3 ^ 40 * 144521 * 2
def baseEnd_144521 : Nat := 10993887062005080684869

theorem tailTrace_144521 : CollatzResearch.WordTrace tailWord_144521 prefixEnd_144521 10993887062005080684869 := by
  unfold tailWord_144521
  simp only [CollatzResearch.WordTrace]
  refine ⟨5271113909432574066857417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3514075939621716044571611 5271113909432574066857417)
  ·
    refine ⟨3953335432074430550143063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5271113909432574066857417 3953335432074430550143063)
    ·
      refine ⟨5930003148111645825214595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3953335432074430550143063 5930003148111645825214595)
      ·
        refine ⟨8895004722167468737821893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5930003148111645825214595 8895004722167468737821893)
        ·
          refine ⟨1667813385406400388341605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8895004722167468737821893 1667813385406400388341605)
          ·
            refine ⟨312715009763700072814051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1667813385406400388341605 312715009763700072814051)
            ·
              refine ⟨469072514645550109221077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 312715009763700072814051 469072514645550109221077)
              ·
                refine ⟨10993887062005080684869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 469072514645550109221077 10993887062005080684869)
                ·
                  rfl

theorem cell21_144521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 4, 1, 7].length) (baseStart_144521 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_144521 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_144521 prefixEnd_144521 := by exact prefixLift 144521
  have htrace : WordTrace (prefixWord ++ tailWord_144521) baseStart_144521 baseEnd_144521 := by
    simpa [prefixWord, tailWord_144521, baseEnd_144521] using wordTrace_append hprefix tailTrace_144521
  have hstable : (prefixWord ++ tailWord_144521).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_144521).length < 2 ^ (prefixWord ++ tailWord_144521).sum := by decide
  have hdescent : baseEnd_144521 < baseStart_144521 := by decide
  rcases family_descends (prefixWord ++ tailWord_144521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_144538 : List Nat := [3, 1, 1, 5, 1, 3, 7]
def baseStart_144538 : Nat := 118140960795 + 144538 * 2 ^ 59
def prefixEnd_144538 : Nat := 4983230072969 + 3 ^ 40 * 144538 * 2
def baseEnd_144538 : Nat := 3665060090847443363471

theorem tailTrace_144538 : CollatzResearch.WordTrace tailWord_144538 prefixEnd_144538 3665060090847443363471 := by
  unfold tailWord_144538
  simp only [CollatzResearch.WordTrace]
  refine ⟨1317933487592746492556567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3514489300247323980150845 1317933487592746492556567)
  ·
    refine ⟨1976900231389119738834851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1317933487592746492556567 1976900231389119738834851)
    ·
      refine ⟨2965350347083679608252277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1976900231389119738834851 2965350347083679608252277)
      ·
        refine ⟨278001595039094963273651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 2965350347083679608252277 278001595039094963273651)
        ·
          refine ⟨417002392558642444910477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 278001595039094963273651 417002392558642444910477)
          ·
            refine ⟨156375897209490916841429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 417002392558642444910477 156375897209490916841429)
            ·
              refine ⟨3665060090847443363471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 156375897209490916841429 3665060090847443363471)
              ·
                rfl

theorem cell21_144538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 3, 7].length) (baseStart_144538 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_144538 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_144538 prefixEnd_144538 := by exact prefixLift 144538
  have htrace : WordTrace (prefixWord ++ tailWord_144538) baseStart_144538 baseEnd_144538 := by
    simpa [prefixWord, tailWord_144538, baseEnd_144538] using wordTrace_append hprefix tailTrace_144538
  have hstable : (prefixWord ++ tailWord_144538).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_144538).length < 2 ^ (prefixWord ++ tailWord_144538).sum := by decide
  have hdescent : baseEnd_144538 < baseStart_144538 := by decide
  rcases family_descends (prefixWord ++ tailWord_144538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_144597 : List Nat := [1, 3, 2, 4, 1, 10]
def baseStart_144597 : Nat := 118140960795 + 144597 * 2 ^ 59
def prefixEnd_144597 : Nat := 4983230072969 + 3 ^ 40 * 144597 * 2
def baseEnd_144597 : Nat := 1222185385979851806955

theorem tailTrace_144597 : CollatzResearch.WordTrace tailWord_144597 prefixEnd_144597 1222185385979851806955 := by
  unfold tailWord_144597
  simp only [CollatzResearch.WordTrace]
  refine ⟨5273885857157239046624045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3515923904771492697749363 5273885857157239046624045)
  ·
    refine ⟨1977707196433964642484017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5273885857157239046624045 1977707196433964642484017)
    ·
      refine ⟨1483280397325473481863013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1977707196433964642484017 1483280397325473481863013)
      ·
        refine ⟨278115074498526277849315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1483280397325473481863013 278115074498526277849315)
        ·
          refine ⟨417172611747789416773973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 278115074498526277849315 417172611747789416773973)
          ·
            refine ⟨1222185385979851806955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 417172611747789416773973 1222185385979851806955)
            ·
              rfl

theorem cell21_144597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 10].length) (baseStart_144597 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_144597 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_144597 prefixEnd_144597 := by exact prefixLift 144597
  have htrace : WordTrace (prefixWord ++ tailWord_144597) baseStart_144597 baseEnd_144597 := by
    simpa [prefixWord, tailWord_144597, baseEnd_144597] using wordTrace_append hprefix tailTrace_144597
  have hstable : (prefixWord ++ tailWord_144597).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_144597).length < 2 ^ (prefixWord ++ tailWord_144597).sum := by decide
  have hdescent : baseEnd_144597 < baseStart_144597 := by decide
  rcases family_descends (prefixWord ++ tailWord_144597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_144600 : List Nat := [2, 1, 2, 2, 5, 1, 2, 2, 4]
def baseStart_144600 : Nat := 118140960795 + 144600 * 2 ^ 59
def prefixEnd_144600 : Nat := 4983230072969 + 3 ^ 40 * 144600 * 2
def baseEnd_144600 : Nat := 32999690062328660237779

theorem tailTrace_144600 : CollatzResearch.WordTrace tailWord_144600 prefixEnd_144600 32999690062328660237779 := by
  unfold tailWord_144600
  simp only [CollatzResearch.WordTrace]
  refine ⟨2636997638073185279491627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3515996850764247039322169 2636997638073185279491627)
  ·
    refine ⟨3955496457109777919237441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2636997638073185279491627 3955496457109777919237441)
    ·
      refine ⟨2966622342832333439428081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3955496457109777919237441 2966622342832333439428081)
      ·
        refine ⟨2224966757124250079571061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2966622342832333439428081 2224966757124250079571061)
        ·
          refine ⟨208590633480398444959787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 2224966757124250079571061 208590633480398444959787)
          ·
            refine ⟨312885950220597667439681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 208590633480398444959787 312885950220597667439681)
            ·
              refine ⟨234664462665448250579761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 312885950220597667439681 234664462665448250579761)
              ·
                refine ⟨175998346999086187934821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 234664462665448250579761 175998346999086187934821)
                ·
                  refine ⟨32999690062328660237779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 175998346999086187934821 32999690062328660237779)
                  ·
                    rfl

theorem cell21_144600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 1, 2, 2, 4].length) (baseStart_144600 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_144600 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_144600 prefixEnd_144600 := by exact prefixLift 144600
  have htrace : WordTrace (prefixWord ++ tailWord_144600) baseStart_144600 baseEnd_144600 := by
    simpa [prefixWord, tailWord_144600, baseEnd_144600] using wordTrace_append hprefix tailTrace_144600
  have hstable : (prefixWord ++ tailWord_144600).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_144600).length < 2 ^ (prefixWord ++ tailWord_144600).sum := by decide
  have hdescent : baseEnd_144600 < baseStart_144600 := by decide
  rcases family_descends (prefixWord ++ tailWord_144600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_144645 : List Nat := [1, 3, 1, 1, 2, 1, 6, 3, 3]
def baseStart_144645 : Nat := 118140960795 + 144645 * 2 ^ 59
def prefixEnd_144645 : Nat := 4983230072969 + 3 ^ 40 * 144645 * 2
def baseEnd_144645 : Nat := 33009959675418581987687

theorem tailTrace_144645 : CollatzResearch.WordTrace tailWord_144645 prefixEnd_144645 33009959675418581987687 := by
  unfold tailWord_144645
  simp only [CollatzResearch.WordTrace]
  refine ⟨5275636560983343244371389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3517091040655562162914259 5275636560983343244371389)
  ·
    refine ⟨1978363710368753716639271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5275636560983343244371389 1978363710368753716639271)
    ·
      refine ⟨2967545565553130574958907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1978363710368753716639271 2967545565553130574958907)
      ·
        refine ⟨4451318348329695862438361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2967545565553130574958907 4451318348329695862438361)
        ·
          refine ⟨3338488761247271896828771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4451318348329695862438361 3338488761247271896828771)
          ·
            refine ⟨5007733141870907845243157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3338488761247271896828771 5007733141870907845243157)
            ·
              refine ⟨234737491025198805245773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 5007733141870907845243157 234737491025198805245773)
              ·
                refine ⟨88026559134449551967165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 234737491025198805245773 88026559134449551967165)
                ·
                  refine ⟨33009959675418581987687, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 88026559134449551967165 33009959675418581987687)
                  ·
                    rfl

theorem cell21_144645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 6, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 6, 3, 3].length) (baseStart_144645 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_144645 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_144645 prefixEnd_144645 := by exact prefixLift 144645
  have htrace : WordTrace (prefixWord ++ tailWord_144645) baseStart_144645 baseEnd_144645 := by
    simpa [prefixWord, tailWord_144645, baseEnd_144645] using wordTrace_append hprefix tailTrace_144645
  have hstable : (prefixWord ++ tailWord_144645).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_144645).length < 2 ^ (prefixWord ++ tailWord_144645).sum := by decide
  have hdescent : baseEnd_144645 < baseStart_144645 := by decide
  rcases family_descends (prefixWord ++ tailWord_144645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_144676 : List Nat := [2, 3, 1, 3, 1, 1, 5, 1, 4]
def baseStart_144676 : Nat := 118140960795 + 144676 * 2 ^ 59
def prefixEnd_144676 : Nat := 4983230072969 + 3 ^ 40 * 144676 * 2
def baseEnd_144676 : Nat := 33017034297769416970957

theorem tailTrace_144676 : CollatzResearch.WordTrace tailWord_144676 prefixEnd_144676 33017034297769416970957 := by
  unfold tailWord_144676
  simp only [CollatzResearch.WordTrace]
  refine ⟨2638383611935517769374941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3517844815914023692499921 2638383611935517769374941)
  ·
    refine ⟨989393854475819163515603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2638383611935517769374941 989393854475819163515603)
    ·
      refine ⟨1484090781713728745273405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 989393854475819163515603 1484090781713728745273405)
      ·
        refine ⟨556534043142648279477527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1484090781713728745273405 556534043142648279477527)
        ·
          refine ⟨834801064713972419216291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 556534043142648279477527 834801064713972419216291)
          ·
            refine ⟨1252201597070958628824437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 834801064713972419216291 1252201597070958628824437)
            ·
              refine ⟨117393899725402371452291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1252201597070958628824437 117393899725402371452291)
              ·
                refine ⟨176090849588103557178437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 117393899725402371452291 176090849588103557178437)
                ·
                  refine ⟨33017034297769416970957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 176090849588103557178437 33017034297769416970957)
                  ·
                    rfl

theorem cell21_144676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 5, 1, 4].length) (baseStart_144676 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_144676 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_144676 prefixEnd_144676 := by exact prefixLift 144676
  have htrace : WordTrace (prefixWord ++ tailWord_144676) baseStart_144676 baseEnd_144676 := by
    simpa [prefixWord, tailWord_144676, baseEnd_144676] using wordTrace_append hprefix tailTrace_144676
  have hstable : (prefixWord ++ tailWord_144676).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_144676).length < 2 ^ (prefixWord ++ tailWord_144676).sum := by decide
  have hdescent : baseEnd_144676 < baseStart_144676 := by decide
  rcases family_descends (prefixWord ++ tailWord_144676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_144690 : List Nat := [3, 2, 1, 1, 4, 1, 4, 5]
def baseStart_144690 : Nat := 118140960795 + 144690 * 2 ^ 59
def prefixEnd_144690 : Nat := 4983230072969 + 3 ^ 40 * 144690 * 2
def baseEnd_144690 : Nat := 11006743096169501245865

theorem tailTrace_144690 : CollatzResearch.WordTrace tailWord_144690 prefixEnd_144690 11006743096169501245865 := by
  unfold tailWord_144690
  simp only [CollatzResearch.WordTrace]
  refine ⟨1319319461455078982439881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3518185230546877286506349 1319319461455078982439881)
  ·
    refine ⟨989489596091309236829911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1319319461455078982439881 989489596091309236829911)
    ·
      refine ⟨1484234394136963855244867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 989489596091309236829911 1484234394136963855244867)
      ·
        refine ⟨2226351591205445782867301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1484234394136963855244867 2226351591205445782867301)
        ·
          refine ⟨417440923351021084287619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2226351591205445782867301 417440923351021084287619)
          ·
            refine ⟨626161385026531626431429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 417440923351021084287619 626161385026531626431429)
            ·
              refine ⟨117405259692474679955893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 626161385026531626431429 117405259692474679955893)
              ·
                refine ⟨11006743096169501245865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 117405259692474679955893 11006743096169501245865)
                ·
                  rfl

theorem cell21_144690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 4, 5].length) (baseStart_144690 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_144690 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_144690 prefixEnd_144690 := by exact prefixLift 144690
  have htrace : WordTrace (prefixWord ++ tailWord_144690) baseStart_144690 baseEnd_144690 := by
    simpa [prefixWord, tailWord_144690, baseEnd_144690] using wordTrace_append hprefix tailTrace_144690
  have hstable : (prefixWord ++ tailWord_144690).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_144690).length < 2 ^ (prefixWord ++ tailWord_144690).sum := by decide
  have hdescent : baseEnd_144690 < baseStart_144690 := by decide
  rcases family_descends (prefixWord ++ tailWord_144690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_144718 : List Nat := [4, 1, 1, 1, 1, 1, 3, 3, 6]
def baseStart_144718 : Nat := 118140960795 + 144718 * 2 ^ 59
def prefixEnd_144718 : Nat := 4983230072969 + 3 ^ 40 * 144718 * 2
def baseEnd_144718 : Nat := 33026619269986677270871

theorem tailTrace_144718 : CollatzResearch.WordTrace tailWord_144718 prefixEnd_144718 33026619269986677270871 := by
  unfold tailWord_144718
  simp only [CollatzResearch.WordTrace]
  refine ⟨659787386214859588972351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3518866059812584474519205 659787386214859588972351)
  ·
    refine ⟨989681079322289383458527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 659787386214859588972351 989681079322289383458527)
    ·
      refine ⟨1484521618983434075187791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 989681079322289383458527 1484521618983434075187791)
      ·
        refine ⟨2226782428475151112781687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1484521618983434075187791 2226782428475151112781687)
        ·
          refine ⟨3340173642712726669172531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2226782428475151112781687 3340173642712726669172531)
          ·
            refine ⟨5010260464069090003758797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3340173642712726669172531 5010260464069090003758797)
            ·
              refine ⟨1878847674025908751409549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5010260464069090003758797 1878847674025908751409549)
              ·
                refine ⟨704567877759715781778581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1878847674025908751409549 704567877759715781778581)
                ·
                  refine ⟨33026619269986677270871, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 704567877759715781778581 33026619269986677270871)
                  ·
                    rfl

theorem cell21_144718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 3, 3, 6].length) (baseStart_144718 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_144718 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_144718 prefixEnd_144718 := by exact prefixLift 144718
  have htrace : WordTrace (prefixWord ++ tailWord_144718) baseStart_144718 baseEnd_144718 := by
    simpa [prefixWord, tailWord_144718, baseEnd_144718] using wordTrace_append hprefix tailTrace_144718
  have hstable : (prefixWord ++ tailWord_144718).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_144718).length < 2 ^ (prefixWord ++ tailWord_144718).sum := by decide
  have hdescent : baseEnd_144718 < baseStart_144718 := by decide
  rcases family_descends (prefixWord ++ tailWord_144718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_144749 : List Nat := [1, 5, 1, 1, 1, 3, 2, 7]
def baseStart_144749 : Nat := 118140960795 + 144749 * 2 ^ 59
def prefixEnd_144749 : Nat := 4983230072969 + 3 ^ 40 * 144749 * 2
def baseEnd_144749 : Nat := 11011231297445837418047

theorem tailTrace_144749 : CollatzResearch.WordTrace tailWord_144749 prefixEnd_144749 11011231297445837418047 := by
  unfold tailWord_144749
  simp only [CollatzResearch.WordTrace]
  refine ⟨5279429752606569006157301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3519619835071046004104867 5279429752606569006157301)
  ·
    refine ⟨494946539306865844327247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 5279429752606569006157301 494946539306865844327247)
    ·
      refine ⟨742419808960298766490871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 494946539306865844327247 742419808960298766490871)
      ·
        refine ⟨1113629713440448149736307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 742419808960298766490871 1113629713440448149736307)
        ·
          refine ⟨1670444570160672224604461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1113629713440448149736307 1670444570160672224604461)
          ·
            refine ⟨626416713810252084226673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1670444570160672224604461 626416713810252084226673)
            ·
              refine ⟨469812535357689063170005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 626416713810252084226673 469812535357689063170005)
              ·
                refine ⟨11011231297445837418047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 469812535357689063170005 11011231297445837418047)
                ·
                  rfl

theorem cell21_144749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 2, 7].length) (baseStart_144749 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_144749 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_144749 prefixEnd_144749 := by exact prefixLift 144749
  have htrace : WordTrace (prefixWord ++ tailWord_144749) baseStart_144749 baseEnd_144749 := by
    simpa [prefixWord, tailWord_144749, baseEnd_144749] using wordTrace_append hprefix tailTrace_144749
  have hstable : (prefixWord ++ tailWord_144749).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_144749).length < 2 ^ (prefixWord ++ tailWord_144749).sum := by decide
  have hdescent : baseEnd_144749 < baseStart_144749 := by decide
  rcases family_descends (prefixWord ++ tailWord_144749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_144766 : List Nat := [4, 2, 3, 2, 10]
def baseStart_144766 : Nat := 118140960795 + 144766 * 2 ^ 59
def prefixEnd_144766 : Nat := 4983230072969 + 3 ^ 40 * 144766 * 2
def baseEnd_144766 : Nat := 407871278073447660133

theorem tailTrace_144766 : CollatzResearch.WordTrace tailWord_144766 prefixEnd_144766 407871278073447660133 := by
  unfold tailWord_144766
  simp only [CollatzResearch.WordTrace]
  refine ⟨660006224193122613690769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3520033195696653939684101 660006224193122613690769)
  ·
    refine ⟨495004668144841960268077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 660006224193122613690769 495004668144841960268077)
    ·
      refine ⟨185626750554315735100529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 495004668144841960268077 185626750554315735100529)
      ·
        refine ⟨139220062915736801325397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 185626750554315735100529 139220062915736801325397)
        ·
          refine ⟨407871278073447660133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 10 139220062915736801325397 407871278073447660133)
          ·
            rfl

theorem cell21_144766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 10].length) (baseStart_144766 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_144766 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_144766 prefixEnd_144766 := by exact prefixLift 144766
  have htrace : WordTrace (prefixWord ++ tailWord_144766) baseStart_144766 baseEnd_144766 := by
    simpa [prefixWord, tailWord_144766, baseEnd_144766] using wordTrace_append hprefix tailTrace_144766
  have hstable : (prefixWord ++ tailWord_144766).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_144766).length < 2 ^ (prefixWord ++ tailWord_144766).sum := by decide
  have hdescent : baseEnd_144766 < baseStart_144766 := by decide
  rcases family_descends (prefixWord ++ tailWord_144766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_144825 : List Nat := [1, 2, 1, 4, 4, 1, 8]
def baseStart_144825 : Nat := 118140960795 + 144825 * 2 ^ 59
def prefixEnd_144825 : Nat := 4983230072969 + 3 ^ 40 * 144825 * 2
def baseEnd_144825 : Nat := 3672337569753140998591

theorem tailTrace_144825 : CollatzResearch.WordTrace tailWord_144825 prefixEnd_144825 3672337569753140998591 := by
  unfold tailWord_144825
  simp only [CollatzResearch.WordTrace]
  refine ⟨5282201700331233985923929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3521467800220822657282619 5282201700331233985923929)
  ·
    refine ⟨3961651275248425489442947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5282201700331233985923929 3961651275248425489442947)
    ·
      refine ⟨5942476912872638234164421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3961651275248425489442947 5942476912872638234164421)
      ·
        refine ⟨1114214421163619668905829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5942476912872638234164421 1114214421163619668905829)
        ·
          refine ⟨208915203968178687919843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1114214421163619668905829 208915203968178687919843)
          ·
            refine ⟨313372805952268031879765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 208915203968178687919843 313372805952268031879765)
            ·
              refine ⟨3672337569753140998591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 313372805952268031879765 3672337569753140998591)
              ·
                rfl

theorem cell21_144825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 1, 8].length) (baseStart_144825 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_144825 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_144825 prefixEnd_144825 := by exact prefixLift 144825
  have htrace : WordTrace (prefixWord ++ tailWord_144825) baseStart_144825 baseEnd_144825 := by
    simpa [prefixWord, tailWord_144825, baseEnd_144825] using wordTrace_append hprefix tailTrace_144825
  have hstable : (prefixWord ++ tailWord_144825).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_144825).length < 2 ^ (prefixWord ++ tailWord_144825).sum := by decide
  have hdescent : baseEnd_144825 < baseStart_144825 := by decide
  rcases family_descends (prefixWord ++ tailWord_144825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_144949 : List Nat := [1, 3, 3, 1, 1, 4, 1, 4, 3]
def baseStart_144949 : Nat := 118140960795 + 144949 * 2 ^ 59
def prefixEnd_144949 : Nat := 4983230072969 + 3 ^ 40 * 144949 * 2
def baseEnd_144949 : Nat := 33079336617181608920399

theorem tailTrace_144949 : CollatzResearch.WordTrace tailWord_144949 prefixEnd_144949 33079336617181608920399 := by
  unfold tailWord_144949
  simp only [CollatzResearch.WordTrace]
  refine ⟨5286724351882003163437901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3524482901254668775625267 5286724351882003163437901)
  ·
    refine ⟨1982521631955751186289213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5286724351882003163437901 1982521631955751186289213)
    ·
      refine ⟨743445611983406694858455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1982521631955751186289213 743445611983406694858455)
      ·
        refine ⟨1115168417975110042287683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 743445611983406694858455 1115168417975110042287683)
        ·
          refine ⟨1672752626962665063431525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1115168417975110042287683 1672752626962665063431525)
          ·
            refine ⟨313641117555499699393411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1672752626962665063431525 313641117555499699393411)
            ·
              refine ⟨470461676333249549090117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 313641117555499699393411 470461676333249549090117)
              ·
                refine ⟨88211564312484290454397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 470461676333249549090117 88211564312484290454397)
                ·
                  refine ⟨33079336617181608920399, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 88211564312484290454397 33079336617181608920399)
                  ·
                    rfl

theorem cell21_144949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 4, 1, 4, 3].length) (baseStart_144949 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_144949 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_144949 prefixEnd_144949 := by exact prefixLift 144949
  have htrace : WordTrace (prefixWord ++ tailWord_144949) baseStart_144949 baseEnd_144949 := by
    simpa [prefixWord, tailWord_144949, baseEnd_144949] using wordTrace_append hprefix tailTrace_144949
  have hstable : (prefixWord ++ tailWord_144949).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_144949).length < 2 ^ (prefixWord ++ tailWord_144949).sum := by decide
  have hdescent : baseEnd_144949 < baseStart_144949 := by decide
  rcases family_descends (prefixWord ++ tailWord_144949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_144966 : List Nat := [6, 1, 1, 1, 3, 1, 1, 2, 5]
def baseStart_144966 : Nat := 118140960795 + 144966 * 2 ^ 59
def prefixEnd_144966 : Nat := 4983230072969 + 3 ^ 40 * 144966 * 2
def baseEnd_144966 : Nat := 33083216248793357137031

theorem tailTrace_144966 : CollatzResearch.WordTrace tailWord_144966 prefixEnd_144966 33083216248793357137031 := by
  unfold tailWord_144966
  simp only [CollatzResearch.WordTrace]
  refine ⟨165229512275637970837711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 3524896261880276711204501 165229512275637970837711)
  ·
    refine ⟨247844268413456956256567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 165229512275637970837711 247844268413456956256567)
    ·
      refine ⟨371766402620185434384851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 247844268413456956256567 371766402620185434384851)
      ·
        refine ⟨557649603930278151577277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 371766402620185434384851 557649603930278151577277)
        ·
          refine ⟨209118601473854306841479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 557649603930278151577277 209118601473854306841479)
          ·
            refine ⟨313677902210781460262219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 209118601473854306841479 313677902210781460262219)
            ·
              refine ⟨470516853316172190393329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 313677902210781460262219 470516853316172190393329)
              ·
                refine ⟨352887639987129142794997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 470516853316172190393329 352887639987129142794997)
                ·
                  refine ⟨33083216248793357137031, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 352887639987129142794997 33083216248793357137031)
                  ·
                    rfl

theorem cell21_144966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 1, 1, 2, 5].length) (baseStart_144966 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_144966 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_144966 prefixEnd_144966 := by exact prefixLift 144966
  have htrace : WordTrace (prefixWord ++ tailWord_144966) baseStart_144966 baseEnd_144966 := by
    simpa [prefixWord, tailWord_144966, baseEnd_144966] using wordTrace_append hprefix tailTrace_144966
  have hstable : (prefixWord ++ tailWord_144966).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_144966).length < 2 ^ (prefixWord ++ tailWord_144966).sum := by decide
  have hdescent : baseEnd_144966 < baseStart_144966 := by decide
  rcases family_descends (prefixWord ++ tailWord_144966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_144977 : List Nat := [1, 2, 2, 1, 3, 2, 5, 5]
def baseStart_144977 : Nat := 118140960795 + 144977 * 2 ^ 59
def prefixEnd_144977 : Nat := 4983230072969 + 3 ^ 40 * 144977 * 2
def baseEnd_144977 : Nat := 11028575532886594151225

theorem tailTrace_144977 : CollatzResearch.WordTrace tailWord_144977 prefixEnd_144977 11028575532886594151225 := by
  unfold tailWord_144977
  simp only [CollatzResearch.WordTrace]
  refine ⟨5287745595780563945457185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3525163730520375963638123 5287745595780563945457185)
  ·
    refine ⟨3965809196835422959092889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5287745595780563945457185 3965809196835422959092889)
    ·
      refine ⟨2974356897626567219319667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3965809196835422959092889 2974356897626567219319667)
      ·
        refine ⟨4461535346439850828979501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2974356897626567219319667 4461535346439850828979501)
        ·
          refine ⟨1673075754914944060867313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4461535346439850828979501 1673075754914944060867313)
          ·
            refine ⟨1254806816186208045650485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1673075754914944060867313 1254806816186208045650485)
            ·
              refine ⟨117638139017457004279733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1254806816186208045650485 117638139017457004279733)
              ·
                refine ⟨11028575532886594151225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 117638139017457004279733 11028575532886594151225)
                ·
                  rfl

theorem cell21_144977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 5, 5].length) (baseStart_144977 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_144977 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_144977 prefixEnd_144977 := by exact prefixLift 144977
  have htrace : WordTrace (prefixWord ++ tailWord_144977) baseStart_144977 baseEnd_144977 := by
    simpa [prefixWord, tailWord_144977, baseEnd_144977] using wordTrace_append hprefix tailTrace_144977
  have hstable : (prefixWord ++ tailWord_144977).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_144977).length < 2 ^ (prefixWord ++ tailWord_144977).sum := by decide
  have hdescent : baseEnd_144977 < baseStart_144977 := by decide
  rcases family_descends (prefixWord ++ tailWord_144977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_145008 : List Nat := [2, 1, 1, 1, 6, 2, 2, 1, 5]
def baseStart_145008 : Nat := 118140960795 + 145008 * 2 ^ 59
def prefixEnd_145008 : Nat := 4983230072969 + 3 ^ 40 * 145008 * 2
def baseEnd_145008 : Nat := 33092801221010617436945

theorem tailTrace_145008 : CollatzResearch.WordTrace tailWord_145008 prefixEnd_145008 33092801221010617436945 := by
  unfold tailWord_145008
  simp only [CollatzResearch.WordTrace]
  refine ⟨2644438129334128119917839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3525917505778837493223785 2644438129334128119917839)
  ·
    refine ⟨3966657194001192179876759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2644438129334128119917839 3966657194001192179876759)
    ·
      refine ⟨5949985791001788269815139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3966657194001192179876759 5949985791001788269815139)
      ·
        refine ⟨8924978686502682404722709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5949985791001788269815139 8924978686502682404722709)
        ·
          refine ⟨418358375929813237721377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 8924978686502682404722709 418358375929813237721377)
          ·
            refine ⟨313768781947359928291033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 418358375929813237721377 313768781947359928291033)
            ·
              refine ⟨235326586460519946218275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 313768781947359928291033 235326586460519946218275)
              ·
                refine ⟨352989879690779919327413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 235326586460519946218275 352989879690779919327413)
                ·
                  refine ⟨33092801221010617436945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 352989879690779919327413 33092801221010617436945)
                  ·
                    rfl

theorem cell21_145008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 2, 2, 1, 5].length) (baseStart_145008 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_145008 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_145008 prefixEnd_145008 := by exact prefixLift 145008
  have htrace : WordTrace (prefixWord ++ tailWord_145008) baseStart_145008 baseEnd_145008 := by
    simpa [prefixWord, tailWord_145008, baseEnd_145008] using wordTrace_append hprefix tailTrace_145008
  have hstable : (prefixWord ++ tailWord_145008).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_145008).length < 2 ^ (prefixWord ++ tailWord_145008).sum := by decide
  have hdescent : baseEnd_145008 < baseStart_145008 := by decide
  rcases family_descends (prefixWord ++ tailWord_145008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_145036 : List Nat := [2, 2, 1, 2, 1, 1, 5, 7]
def baseStart_145036 : Nat := 118140960795 + 145036 * 2 ^ 59
def prefixEnd_145036 : Nat := 4983230072969 + 3 ^ 40 * 145036 * 2
def baseEnd_145036 : Nat := 11033063734162930323407

theorem tailTrace_145036 : CollatzResearch.WordTrace tailWord_145036 prefixEnd_145036 11033063734162930323407 := by
  unfold tailWord_145036
  simp only [CollatzResearch.WordTrace]
  refine ⟨2644948751283408510927481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3526598335044544681236641 2644948751283408510927481)
  ·
    refine ⟨1983711563462556383195611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2644948751283408510927481 1983711563462556383195611)
    ·
      refine ⟨2975567345193834574793417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1983711563462556383195611 2975567345193834574793417)
      ·
        refine ⟨2231675508895375931095063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2975567345193834574793417 2231675508895375931095063)
        ·
          refine ⟨3347513263343063896642595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2231675508895375931095063 3347513263343063896642595)
          ·
            refine ⟨5021269895014595844963893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3347513263343063896642595 5021269895014595844963893)
            ·
              refine ⟨470744052657618360465365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 5021269895014595844963893 470744052657618360465365)
              ·
                refine ⟨11033063734162930323407, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 470744052657618360465365 11033063734162930323407)
                ·
                  rfl

theorem cell21_145036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 5, 7].length) (baseStart_145036 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_145036 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_145036 prefixEnd_145036 := by exact prefixLift 145036
  have htrace : WordTrace (prefixWord ++ tailWord_145036) baseStart_145036 baseEnd_145036 := by
    simpa [prefixWord, tailWord_145036, baseEnd_145036] using wordTrace_append hprefix tailTrace_145036
  have hstable : (prefixWord ++ tailWord_145036).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_145036).length < 2 ^ (prefixWord ++ tailWord_145036).sum := by decide
  have hdescent : baseEnd_145036 < baseStart_145036 := by decide
  rcases family_descends (prefixWord ++ tailWord_145036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_145205 : List Nat := [1, 3, 3, 1, 4, 1, 1, 7]
def baseStart_145205 : Nat := 118140960795 + 145205 * 2 ^ 59
def prefixEnd_145205 : Nat := 4983230072969 + 3 ^ 40 * 145205 * 2
def baseEnd_145205 : Nat := 11045919768327350884403

theorem tailTrace_145205 : CollatzResearch.WordTrace tailWord_145205 prefixEnd_145205 11045919768327350884403 := by
  unfold tailWord_145205
  simp only [CollatzResearch.WordTrace]
  refine ⟨5296061438954558884757069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3530707625969705923171379 5296061438954558884757069)
  ·
    refine ⟨1986023039607959581783901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5296061438954558884757069 1986023039607959581783901)
    ·
      refine ⟨744758639852984843168963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1986023039607959581783901 744758639852984843168963)
      ·
        refine ⟨1117137959779477264753445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 744758639852984843168963 1117137959779477264753445)
        ·
          refine ⟨209463367458651987141271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1117137959779477264753445 209463367458651987141271)
          ·
            refine ⟨314195051187977980711907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 209463367458651987141271 314195051187977980711907)
            ·
              refine ⟨471292576781966971067861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 314195051187977980711907 471292576781966971067861)
              ·
                refine ⟨11045919768327350884403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 471292576781966971067861 11045919768327350884403)
                ·
                  rfl

theorem cell21_145205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 1, 1, 7].length) (baseStart_145205 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_145205 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_145205 prefixEnd_145205 := by exact prefixLift 145205
  have htrace : WordTrace (prefixWord ++ tailWord_145205) baseStart_145205 baseEnd_145205 := by
    simpa [prefixWord, tailWord_145205, baseEnd_145205] using wordTrace_append hprefix tailTrace_145205
  have hstable : (prefixWord ++ tailWord_145205).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_145205).length < 2 ^ (prefixWord ++ tailWord_145205).sum := by decide
  have hdescent : baseEnd_145205 < baseStart_145205 := by decide
  rcases family_descends (prefixWord ++ tailWord_145205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_145222 : List Nat := [6, 1, 1, 2, 1, 1, 9]
def baseStart_145222 : Nat := 118140960795 + 145222 * 2 ^ 59
def prefixEnd_145222 : Nat := 4983230072969 + 3 ^ 40 * 145222 * 2
def baseEnd_145222 : Nat := 3682404326288200096649

theorem tailTrace_145222 : CollatzResearch.WordTrace tailWord_145222 prefixEnd_145222 3682404326288200096649 := by
  unfold tailWord_145222
  simp only [CollatzResearch.WordTrace]
  refine ⟨165521296246655337128935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 3531120986595313858750613 165521296246655337128935)
  ·
    refine ⟨248281944369983005693403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 165521296246655337128935 248281944369983005693403)
    ·
      refine ⟨372422916554974508540105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 248281944369983005693403 372422916554974508540105)
      ·
        refine ⟨279317187416230881405079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 372422916554974508540105 279317187416230881405079)
        ·
          refine ⟨418975781124346322107619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 279317187416230881405079 418975781124346322107619)
          ·
            refine ⟨628463671686519483161429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 418975781124346322107619 628463671686519483161429)
            ·
              refine ⟨3682404326288200096649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 628463671686519483161429 3682404326288200096649)
              ·
                rfl

theorem cell21_145222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 9].length) (baseStart_145222 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_145222 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_145222 prefixEnd_145222 := by exact prefixLift 145222
  have htrace : WordTrace (prefixWord ++ tailWord_145222) baseStart_145222 baseEnd_145222 := by
    simpa [prefixWord, tailWord_145222, baseEnd_145222] using wordTrace_append hprefix tailTrace_145222
  have hstable : (prefixWord ++ tailWord_145222).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_145222).length < 2 ^ (prefixWord ++ tailWord_145222).sum := by decide
  have hdescent : baseEnd_145222 < baseStart_145222 := by decide
  rcases family_descends (prefixWord ++ tailWord_145222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_145236 : List Nat := [2, 4, 1, 1, 3, 1, 3, 1, 5]
def baseStart_145236 : Nat := 118140960795 + 145236 * 2 ^ 59
def prefixEnd_145236 : Nat := 4983230072969 + 3 ^ 40 * 145236 * 2
def baseEnd_145236 : Nat := 33144833927332887636479

theorem tailTrace_145236 : CollatzResearch.WordTrace tailWord_145236 prefixEnd_145236 33144833927332887636479 := by
  unfold tailWord_145236
  simp only [CollatzResearch.WordTrace]
  refine ⟨2648596050921125589567781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3531461401228167452757041 2648596050921125589567781)
  ·
    refine ⟨496611759547711048043959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2648596050921125589567781 496611759547711048043959)
    ·
      refine ⟨744917639321566572065939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 496611759547711048043959 744917639321566572065939)
      ·
        refine ⟨1117376458982349858098909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 744917639321566572065939 1117376458982349858098909)
        ·
          refine ⟨419016172118381196787091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1117376458982349858098909 419016172118381196787091)
          ·
            refine ⟨628524258177571795180637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 419016172118381196787091 628524258177571795180637)
            ·
              refine ⟨235696596816589423192739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 628524258177571795180637 235696596816589423192739)
              ·
                refine ⟨353544895224884134789109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 235696596816589423192739 353544895224884134789109)
                ·
                  refine ⟨33144833927332887636479, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 353544895224884134789109 33144833927332887636479)
                  ·
                    rfl

theorem cell21_145236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 3, 1, 5].length) (baseStart_145236 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_145236 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_145236 prefixEnd_145236 := by exact prefixLift 145236
  have htrace : WordTrace (prefixWord ++ tailWord_145236) baseStart_145236 baseEnd_145236 := by
    simpa [prefixWord, tailWord_145236, baseEnd_145236] using wordTrace_append hprefix tailTrace_145236
  have hstable : (prefixWord ++ tailWord_145236).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_145236).length < 2 ^ (prefixWord ++ tailWord_145236).sum := by decide
  have hdescent : baseEnd_145236 < baseStart_145236 := by decide
  rcases family_descends (prefixWord ++ tailWord_145236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_145281 : List Nat := [1, 2, 4, 4, 1, 9]
def baseStart_145281 : Nat := 118140960795 + 145281 * 2 ^ 59
def prefixEnd_145281 : Nat := 4983230072969 + 3 ^ 40 * 145281 * 2
def baseEnd_145281 : Nat := 1227966797793437384681

theorem tailTrace_145281 : CollatzResearch.WordTrace tailWord_145281 prefixEnd_145281 1227966797793437384681 := by
  unfold tailWord_145281
  simp only [CollatzResearch.WordTrace]
  refine ⟨5298833386679223864523697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3532555591119482576349131 5298833386679223864523697)
  ·
    refine ⟨3974125040009417898392773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5298833386679223864523697 3974125040009417898392773)
    ·
      refine ⟨745148445001765855948645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3974125040009417898392773 745148445001765855948645)
      ·
        refine ⟨139715333437831097990371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 745148445001765855948645 139715333437831097990371)
        ·
          refine ⟨209573000156746646985557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 139715333437831097990371 209573000156746646985557)
          ·
            refine ⟨1227966797793437384681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 209573000156746646985557 1227966797793437384681)
            ·
              rfl

theorem cell21_145281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 9].length) (baseStart_145281 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_145281 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_145281 prefixEnd_145281 := by exact prefixLift 145281
  have htrace : WordTrace (prefixWord ++ tailWord_145281) baseStart_145281 baseEnd_145281 := by
    simpa [prefixWord, tailWord_145281, baseEnd_145281] using wordTrace_append hprefix tailTrace_145281
  have hstable : (prefixWord ++ tailWord_145281).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_145281).length < 2 ^ (prefixWord ++ tailWord_145281).sum := by decide
  have hdescent : baseEnd_145281 < baseStart_145281 := by decide
  rcases family_descends (prefixWord ++ tailWord_145281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_145287 : List Nat := [1, 1, 4, 2, 5, 1, 2, 2, 3]
def baseStart_145287 : Nat := 118140960795 + 145287 * 2 ^ 59
def prefixEnd_145287 : Nat := 4983230072969 + 3 ^ 40 * 145287 * 2
def baseEnd_145287 : Nat := 33156472822168132286375

theorem tailTrace_145287 : CollatzResearch.WordTrace tailWord_145287 prefixEnd_145287 33156472822168132286375 := by
  unfold tailWord_145287
  simp only [CollatzResearch.WordTrace]
  refine ⟨5299052224657486889242115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3532701483104991259494743 5299052224657486889242115)
  ·
    refine ⟨7948578336986230333863173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5299052224657486889242115 7948578336986230333863173)
    ·
      refine ⟨1490358438184918187599345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7948578336986230333863173 1490358438184918187599345)
      ·
        refine ⟨1117768828638688640699509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1490358438184918187599345 1117768828638688640699509)
        ·
          refine ⟨104790827684877060065579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 1117768828638688640699509 104790827684877060065579)
          ·
            refine ⟨157186241527315590098369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 104790827684877060065579 157186241527315590098369)
            ·
              refine ⟨117889681145486692573777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 157186241527315590098369 117889681145486692573777)
              ·
                refine ⟨88417260859115019430333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 117889681145486692573777 88417260859115019430333)
                ·
                  refine ⟨33156472822168132286375, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 88417260859115019430333 33156472822168132286375)
                  ·
                    rfl

theorem cell21_145287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 5, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 5, 1, 2, 2, 3].length) (baseStart_145287 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_145287 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_145287 prefixEnd_145287 := by exact prefixLift 145287
  have htrace : WordTrace (prefixWord ++ tailWord_145287) baseStart_145287 baseEnd_145287 := by
    simpa [prefixWord, tailWord_145287, baseEnd_145287] using wordTrace_append hprefix tailTrace_145287
  have hstable : (prefixWord ++ tailWord_145287).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_145287).length < 2 ^ (prefixWord ++ tailWord_145287).sum := by decide
  have hdescent : baseEnd_145287 < baseStart_145287 := by decide
  rcases family_descends (prefixWord ++ tailWord_145287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_145298 : List Nat := [3, 2, 3, 2, 1, 3, 1, 6]
def baseStart_145298 : Nat := 118140960795 + 145298 * 2 ^ 59
def prefixEnd_145298 : Nat := 4983230072969 + 3 ^ 40 * 145298 * 2
def baseEnd_145298 : Nat := 11052994390678185867673

theorem tailTrace_145298 : CollatzResearch.WordTrace tailWord_145298 prefixEnd_145298 11052994390678185867673 := by
  unfold tailWord_145298
  simp only [CollatzResearch.WordTrace]
  refine ⟨1324863356904408941973137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3532968951745090511928365 1324863356904408941973137)
  ·
    refine ⟨993647517678306706479853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1324863356904408941973137 993647517678306706479853)
    ·
      refine ⟨372617819129365014929945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 993647517678306706479853 372617819129365014929945)
      ·
        refine ⟨279463364347023761197459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 372617819129365014929945 279463364347023761197459)
        ·
          refine ⟨419195046520535641796189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 279463364347023761197459 419195046520535641796189)
          ·
            refine ⟨157198142445200865673571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 419195046520535641796189 157198142445200865673571)
            ·
              refine ⟨235797213667801298510357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 157198142445200865673571 235797213667801298510357)
              ·
                refine ⟨11052994390678185867673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 235797213667801298510357 11052994390678185867673)
                ·
                  rfl

theorem cell21_145298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 3, 1, 6].length) (baseStart_145298 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_145298 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_145298 prefixEnd_145298 := by exact prefixLift 145298
  have htrace : WordTrace (prefixWord ++ tailWord_145298) baseStart_145298 baseEnd_145298 := by
    simpa [prefixWord, tailWord_145298, baseEnd_145298] using wordTrace_append hprefix tailTrace_145298
  have hstable : (prefixWord ++ tailWord_145298).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_145298).length < 2 ^ (prefixWord ++ tailWord_145298).sum := by decide
  have hdescent : baseEnd_145298 < baseStart_145298 := by decide
  rcases family_descends (prefixWord ++ tailWord_145298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_145329 : List Nat := [1, 2, 2, 4, 2, 2, 2, 3, 3]
def baseStart_145329 : Nat := 118140960795 + 145329 * 2 ^ 59
def prefixEnd_145329 : Nat := 4983230072969 + 3 ^ 40 * 145329 * 2
def baseEnd_145329 : Nat := 33166057794385392586289

theorem tailTrace_145329 : CollatzResearch.WordTrace tailWord_145329 prefixEnd_145329 33166057794385392586289 := by
  unfold tailWord_145329
  simp only [CollatzResearch.WordTrace]
  refine ⟨5300584090505328062271041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3533722727003552041514027 5300584090505328062271041)
  ·
    refine ⟨3975438067878996046703281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5300584090505328062271041 3975438067878996046703281)
    ·
      refine ⟨2981578550909247035027461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3975438067878996046703281 2981578550909247035027461)
      ·
        refine ⟨559045978295483819067649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2981578550909247035027461 559045978295483819067649)
        ·
          refine ⟨419284483721612864300737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 559045978295483819067649 419284483721612864300737)
          ·
            refine ⟨314463362791209648225553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 419284483721612864300737 314463362791209648225553)
            ·
              refine ⟨235847522093407236169165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 314463362791209648225553 235847522093407236169165)
              ·
                refine ⟨88442820785027713563437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 235847522093407236169165 88442820785027713563437)
                ·
                  refine ⟨33166057794385392586289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 88442820785027713563437 33166057794385392586289)
                  ·
                    rfl

theorem cell21_145329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 2, 2, 3, 3].length) (baseStart_145329 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_145329 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_145329 prefixEnd_145329 := by exact prefixLift 145329
  have htrace : WordTrace (prefixWord ++ tailWord_145329) baseStart_145329 baseEnd_145329 := by
    simpa [prefixWord, tailWord_145329, baseEnd_145329] using wordTrace_append hprefix tailTrace_145329
  have hstable : (prefixWord ++ tailWord_145329).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_145329).length < 2 ^ (prefixWord ++ tailWord_145329).sum := by decide
  have hdescent : baseEnd_145329 < baseStart_145329 := by decide
  rcases family_descends (prefixWord ++ tailWord_145329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_145416 : List Nat := [2, 1, 3, 2, 1, 2, 4, 6]
def baseStart_145416 : Nat := 118140960795 + 145416 * 2 ^ 59
def prefixEnd_145416 : Nat := 4983230072969 + 3 ^ 40 * 145416 * 2
def baseEnd_145416 : Nat := 11061970793230858212037

theorem tailTrace_145416 : CollatzResearch.WordTrace tailWord_145416 prefixEnd_145416 11061970793230858212037 := by
  unfold tailWord_145416
  simp only [CollatzResearch.WordTrace]
  refine ⟨2651878620595070960344051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3535838160793427947125401 2651878620595070960344051)
  ·
    refine ⟨3977817930892606440516077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2651878620595070960344051 3977817930892606440516077)
    ·
      refine ⟨1491681724084727415193529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3977817930892606440516077 1491681724084727415193529)
      ·
        refine ⟨1118761293063545561395147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1491681724084727415193529 1118761293063545561395147)
        ·
          refine ⟨1678141939595318342092721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1118761293063545561395147 1678141939595318342092721)
          ·
            refine ⟨1258606454696488756569541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1678141939595318342092721 1258606454696488756569541)
            ·
              refine ⟨235988710255591641856789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1258606454696488756569541 235988710255591641856789)
              ·
                refine ⟨11061970793230858212037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 235988710255591641856789 11061970793230858212037)
                ·
                  rfl

theorem cell21_145416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 4, 6].length) (baseStart_145416 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_145416 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_145416 prefixEnd_145416 := by exact prefixLift 145416
  have htrace : WordTrace (prefixWord ++ tailWord_145416) baseStart_145416 baseEnd_145416 := by
    simpa [prefixWord, tailWord_145416, baseEnd_145416] using wordTrace_append hprefix tailTrace_145416
  have hstable : (prefixWord ++ tailWord_145416).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_145416).length < 2 ^ (prefixWord ++ tailWord_145416).sum := by decide
  have hdescent : baseEnd_145416 < baseStart_145416 := by decide
  rcases family_descends (prefixWord ++ tailWord_145416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_145461 : List Nat := [1, 3, 3, 1, 1, 1, 2, 3, 6]
def baseStart_145461 : Nat := 118140960795 + 145461 * 2 ^ 59
def prefixEnd_145461 : Nat := 4983230072969 + 3 ^ 40 * 145461 * 2
def baseEnd_145461 : Nat := 33196181992782496386019

theorem tailTrace_145461 : CollatzResearch.WordTrace tailWord_145461 prefixEnd_145461 33196181992782496386019 := by
  unfold tailWord_145461
  simp only [CollatzResearch.WordTrace]
  refine ⟨5305398526027114606076237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3536932350684743070717491 5305398526027114606076237)
  ·
    refine ⟨1989524447260167977278589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5305398526027114606076237 1989524447260167977278589)
    ·
      refine ⟨746071667722562991479471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1989524447260167977278589 746071667722562991479471)
      ·
        refine ⟨1119107501583844487219207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 746071667722562991479471 1119107501583844487219207)
        ·
          refine ⟨1678661252375766730828811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1119107501583844487219207 1678661252375766730828811)
          ·
            refine ⟨2517991878563650096243217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1678661252375766730828811 2517991878563650096243217)
            ·
              refine ⟨1888493908922737572182413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2517991878563650096243217 1888493908922737572182413)
              ·
                refine ⟨708185215846026589568405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1888493908922737572182413 708185215846026589568405)
                ·
                  refine ⟨33196181992782496386019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 708185215846026589568405 33196181992782496386019)
                  ·
                    rfl

theorem cell21_145461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 2, 3, 6].length) (baseStart_145461 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_145461 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_145461 prefixEnd_145461 := by exact prefixLift 145461
  have htrace : WordTrace (prefixWord ++ tailWord_145461) baseStart_145461 baseEnd_145461 := by
    simpa [prefixWord, tailWord_145461, baseEnd_145461] using wordTrace_append hprefix tailTrace_145461
  have hstable : (prefixWord ++ tailWord_145461).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_145461).length < 2 ^ (prefixWord ++ tailWord_145461).sum := by decide
  have hdescent : baseEnd_145461 < baseStart_145461 := by decide
  rcases family_descends (prefixWord ++ tailWord_145461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_145475 : List Nat := [1, 1, 1, 3, 1, 2, 2, 10]
def baseStart_145475 : Nat := 118140960795 + 145475 * 2 ^ 59
def prefixEnd_145475 : Nat := 4983230072969 + 3 ^ 40 * 145475 * 2
def baseEnd_145475 : Nat := 11066458994507194384219

theorem tailTrace_145475 : CollatzResearch.WordTrace tailWord_145475 prefixEnd_145475 11066458994507194384219 := by
  unfold tailWord_145475
  simp only [CollatzResearch.WordTrace]
  refine ⟨5305909147976394997085879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3537272765317596664723919 5305909147976394997085879)
  ·
    refine ⟨7958863721964592495628819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5305909147976394997085879 7958863721964592495628819)
    ·
      refine ⟨11938295582946888743443229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7958863721964592495628819 11938295582946888743443229)
      ·
        refine ⟨4476860843605083278791211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11938295582946888743443229 4476860843605083278791211)
        ·
          refine ⟨6715291265407624918186817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4476860843605083278791211 6715291265407624918186817)
          ·
            refine ⟨5036468449055718688640113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6715291265407624918186817 5036468449055718688640113)
            ·
              refine ⟨3777351336791789016480085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5036468449055718688640113 3777351336791789016480085)
              ·
                refine ⟨11066458994507194384219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 3777351336791789016480085 11066458994507194384219)
                ·
                  rfl

theorem cell21_145475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 10].length) (baseStart_145475 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_145475 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_145475 prefixEnd_145475 := by exact prefixLift 145475
  have htrace : WordTrace (prefixWord ++ tailWord_145475) baseStart_145475 baseEnd_145475 := by
    simpa [prefixWord, tailWord_145475, baseEnd_145475] using wordTrace_append hprefix tailTrace_145475
  have hstable : (prefixWord ++ tailWord_145475).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_145475).length < 2 ^ (prefixWord ++ tailWord_145475).sum := by decide
  have hdescent : baseEnd_145475 < baseStart_145475 := by decide
  rcases family_descends (prefixWord ++ tailWord_145475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_145568 : List Nat := [2, 1, 1, 4, 2, 4, 7]
def baseStart_145568 : Nat := 118140960795 + 145568 * 2 ^ 59
def prefixEnd_145568 : Nat := 4983230072969 + 3 ^ 40 * 145568 * 2
def baseEnd_145568 : Nat := 3691177872286009789163

theorem tailTrace_145568 : CollatzResearch.WordTrace tailWord_145568 prefixEnd_145568 3691177872286009789163 := by
  unfold tailWord_145568
  simp only [CollatzResearch.WordTrace]
  refine ⟨2654650568319735940110679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3539534091092981253480905 2654650568319735940110679)
  ·
    refine ⟨3981975852479603910166019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2654650568319735940110679 3981975852479603910166019)
    ·
      refine ⟨5972963778719405865249029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3981975852479603910166019 5972963778719405865249029)
      ·
        refine ⟨1119930708509888599734193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5972963778719405865249029 1119930708509888599734193)
        ·
          refine ⟨839948031382416449800645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1119930708509888599734193 839948031382416449800645)
          ·
            refine ⟨157490255884203084337621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 839948031382416449800645 157490255884203084337621)
            ·
              refine ⟨3691177872286009789163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 157490255884203084337621 3691177872286009789163)
              ·
                rfl

theorem cell21_145568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 4, 7].length) (baseStart_145568 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_145568 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_145568 prefixEnd_145568 := by exact prefixLift 145568
  have htrace : WordTrace (prefixWord ++ tailWord_145568) baseStart_145568 baseEnd_145568 := by
    simpa [prefixWord, tailWord_145568, baseEnd_145568] using wordTrace_append hprefix tailTrace_145568
  have hstable : (prefixWord ++ tailWord_145568).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_145568).length < 2 ^ (prefixWord ++ tailWord_145568).sum := by decide
  have hdescent : baseEnd_145568 < baseStart_145568 := by decide
  rcases family_descends (prefixWord ++ tailWord_145568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_145585 : List Nat := [1, 2, 2, 5, 2, 1, 2, 6]
def baseStart_145585 : Nat := 118140960795 + 145585 * 2 ^ 59
def prefixEnd_145585 : Nat := 4983230072969 + 3 ^ 40 * 145585 * 2
def baseEnd_145585 : Nat := 11074826827395278773033

theorem tailTrace_145585 : CollatzResearch.WordTrace tailWord_145585 prefixEnd_145585 11074826827395278773033 := by
  unfold tailWord_145585
  simp only [CollatzResearch.WordTrace]
  refine ⟨5309921177577883783590209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3539947451718589189060139 5309921177577883783590209)
  ·
    refine ⟨3982440883183412837692657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5309921177577883783590209 3982440883183412837692657)
    ·
      refine ⟨2986830662387559628269493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3982440883183412837692657 2986830662387559628269493)
      ·
        refine ⟨280015374598833715150265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 2986830662387559628269493 280015374598833715150265)
        ·
          refine ⟨210011530949125286362699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 280015374598833715150265 210011530949125286362699)
          ·
            refine ⟨315017296423687929544049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 210011530949125286362699 315017296423687929544049)
            ·
              refine ⟨236262972317765947158037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 315017296423687929544049 236262972317765947158037)
              ·
                refine ⟨11074826827395278773033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 236262972317765947158037 11074826827395278773033)
                ·
                  rfl

theorem cell21_145585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 1, 2, 6].length) (baseStart_145585 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_145585 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_145585 prefixEnd_145585 := by exact prefixLift 145585
  have htrace : WordTrace (prefixWord ++ tailWord_145585) baseStart_145585 baseEnd_145585 := by
    simpa [prefixWord, tailWord_145585, baseEnd_145585] using wordTrace_append hprefix tailTrace_145585
  have hstable : (prefixWord ++ tailWord_145585).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_145585).length < 2 ^ (prefixWord ++ tailWord_145585).sum := by decide
  have hdescent : baseEnd_145585 < baseStart_145585 := by decide
  rcases family_descends (prefixWord ++ tailWord_145585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_145602 : List Nat := [3, 5, 1, 1, 1, 1, 2, 7]
def baseStart_145602 : Nat := 118140960795 + 145602 * 2 ^ 59
def prefixEnd_145602 : Nat := 4983230072969 + 3 ^ 40 * 145602 * 2
def baseEnd_145602 : Nat := 11076120037932528178577

theorem tailTrace_145602 : CollatzResearch.WordTrace tailWord_145602 prefixEnd_145602 11076120037932528178577 := by
  unfold tailWord_145602
  simp only [CollatzResearch.WordTrace]
  refine ⟨1327635304629073921739765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3540360812344197124639373 1327635304629073921739765)
  ·
    refine ⟨124465809808975680163103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 1327635304629073921739765 124465809808975680163103)
    ·
      refine ⟨186698714713463520244655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 124465809808975680163103 186698714713463520244655)
      ·
        refine ⟨280048072070195280366983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 186698714713463520244655 280048072070195280366983)
        ·
          refine ⟨420072108105292920550475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 280048072070195280366983 420072108105292920550475)
          ·
            refine ⟨630108162157939380825713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 420072108105292920550475 630108162157939380825713)
            ·
              refine ⟨472581121618454535619285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 630108162157939380825713 472581121618454535619285)
              ·
                refine ⟨11076120037932528178577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 472581121618454535619285 11076120037932528178577)
                ·
                  rfl

theorem cell21_145602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 2, 7].length) (baseStart_145602 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_145602 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_145602 prefixEnd_145602 := by exact prefixLift 145602
  have htrace : WordTrace (prefixWord ++ tailWord_145602) baseStart_145602 baseEnd_145602 := by
    simpa [prefixWord, tailWord_145602, baseEnd_145602] using wordTrace_append hprefix tailTrace_145602
  have hstable : (prefixWord ++ tailWord_145602).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_145602).length < 2 ^ (prefixWord ++ tailWord_145602).sum := by decide
  have hdescent : baseEnd_145602 < baseStart_145602 := by decide
  rcases family_descends (prefixWord ++ tailWord_145602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_145658 : List Nat := [3, 1, 1, 1, 1, 5, 1, 1, 7]
def baseStart_145658 : Nat := 118140960795 + 145658 * 2 ^ 59
def prefixEnd_145658 : Nat := 4983230072969 + 3 ^ 40 * 145658 * 2
def baseEnd_145658 : Nat := 33241140076753931602283

theorem tailTrace_145658 : CollatzResearch.WordTrace tailWord_145658 prefixEnd_145658 33241140076753931602283 := by
  unfold tailWord_145658
  simp only [CollatzResearch.WordTrace]
  refine ⟨1328145926578354312749407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3541722470875611500665085 1328145926578354312749407)
  ·
    refine ⟨1992218889867531469124111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1328145926578354312749407 1992218889867531469124111)
    ·
      refine ⟨2988328334801297203686167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1992218889867531469124111 2988328334801297203686167)
      ·
        refine ⟨4482492502201945805529251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2988328334801297203686167 4482492502201945805529251)
        ·
          refine ⟨6723738753302918708293877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4482492502201945805529251 6723738753302918708293877)
          ·
            refine ⟨630350508122148628902551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 6723738753302918708293877 630350508122148628902551)
            ·
              refine ⟨945525762183222943353827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 630350508122148628902551 945525762183222943353827)
              ·
                refine ⟨1418288643274834415030741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 945525762183222943353827 1418288643274834415030741)
                ·
                  refine ⟨33241140076753931602283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1418288643274834415030741 33241140076753931602283)
                  ·
                    rfl

theorem cell21_145658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 1, 1, 7].length) (baseStart_145658 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_145658 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_145658 prefixEnd_145658 := by exact prefixLift 145658
  have htrace : WordTrace (prefixWord ++ tailWord_145658) baseStart_145658 baseEnd_145658 := by
    simpa [prefixWord, tailWord_145658, baseEnd_145658] using wordTrace_append hprefix tailTrace_145658
  have hstable : (prefixWord ++ tailWord_145658).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_145658).length < 2 ^ (prefixWord ++ tailWord_145658).sum := by decide
  have hdescent : baseEnd_145658 < baseStart_145658 := by decide
  rcases family_descends (prefixWord ++ tailWord_145658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_145720 : List Nat := [2, 1, 2, 1, 3, 1, 6, 5]
def baseStart_145720 : Nat := 118140960795 + 145720 * 2 ^ 59
def prefixEnd_145720 : Nat := 4983230072969 + 3 ^ 40 * 145720 * 2
def baseEnd_145720 : Nat := 11085096440485200522941

theorem tailTrace_145720 : CollatzResearch.WordTrace tailWord_145720 prefixEnd_145720 11085096440485200522941 := by
  unfold tailWord_145720
  simp only [CollatzResearch.WordTrace]
  refine ⟨2657422516044400919877307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3543230021392534559836409 2657422516044400919877307)
  ·
    refine ⟨3986133774066601379815961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2657422516044400919877307 3986133774066601379815961)
    ·
      refine ⟨2989600330549951034861971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3986133774066601379815961 2989600330549951034861971)
      ·
        refine ⟨4484400495824926552292957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2989600330549951034861971 4484400495824926552292957)
        ·
          refine ⟨1681650185934347457109859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4484400495824926552292957 1681650185934347457109859)
          ·
            refine ⟨2522475278901521185664789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1681650185934347457109859 2522475278901521185664789)
            ·
              refine ⟨118241028698508805578037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 2522475278901521185664789 118241028698508805578037)
              ·
                refine ⟨11085096440485200522941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 118241028698508805578037 11085096440485200522941)
                ·
                  rfl

theorem cell21_145720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 6, 5].length) (baseStart_145720 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_145720 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_145720 prefixEnd_145720 := by exact prefixLift 145720
  have htrace : WordTrace (prefixWord ++ tailWord_145720) baseStart_145720 baseEnd_145720 := by
    simpa [prefixWord, tailWord_145720, baseEnd_145720] using wordTrace_append hprefix tailTrace_145720
  have hstable : (prefixWord ++ tailWord_145720).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_145720).length < 2 ^ (prefixWord ++ tailWord_145720).sum := by decide
  have hdescent : baseEnd_145720 < baseStart_145720 := by decide
  rcases family_descends (prefixWord ++ tailWord_145720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_145900 : List Nat := [2, 2, 1, 1, 2, 1, 3, 1, 8]
def baseStart_145900 : Nat := 118140960795 + 145900 * 2 ^ 59
def prefixEnd_145900 : Nat := 4983230072969 + 3 ^ 40 * 145900 * 2
def baseEnd_145900 : Nat := 33296367773815288568455

theorem tailTrace_145900 : CollatzResearch.WordTrace tailWord_145900 prefixEnd_145900 33296367773815288568455 := by
  unfold tailWord_145900
  simp only [CollatzResearch.WordTrace]
  refine ⟨2660705085718346290653577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3547606780957795054204769 2660705085718346290653577)
  ·
    refine ⟨1995528814288759717990183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2660705085718346290653577 1995528814288759717990183)
    ·
      refine ⟨2993293221433139576985275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1995528814288759717990183 2993293221433139576985275)
      ·
        refine ⟨4489939832149709365477913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2993293221433139576985275 4489939832149709365477913)
        ·
          refine ⟨3367454874112282024108435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4489939832149709365477913 3367454874112282024108435)
          ·
            refine ⟨5051182311168423036162653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3367454874112282024108435 5051182311168423036162653)
            ·
              refine ⟨1894193366688158638560995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5051182311168423036162653 1894193366688158638560995)
              ·
                refine ⟨2841290050032237957841493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1894193366688158638560995 2841290050032237957841493)
                ·
                  refine ⟨33296367773815288568455, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 2841290050032237957841493 33296367773815288568455)
                  ·
                    rfl

theorem cell21_145900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 8].length) (baseStart_145900 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_145900 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_145900 prefixEnd_145900 := by exact prefixLift 145900
  have htrace : WordTrace (prefixWord ++ tailWord_145900) baseStart_145900 baseEnd_145900 := by
    simpa [prefixWord, tailWord_145900, baseEnd_145900] using wordTrace_append hprefix tailTrace_145900
  have hstable : (prefixWord ++ tailWord_145900).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_145900).length < 2 ^ (prefixWord ++ tailWord_145900).sum := by decide
  have hdescent : baseEnd_145900 < baseStart_145900 := by decide
  rcases family_descends (prefixWord ++ tailWord_145900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_145917 : List Nat := [1, 4, 1, 1, 1, 3, 2, 4, 4]
def baseStart_145917 : Nat := 118140960795 + 145917 * 2 ^ 59
def prefixEnd_145917 : Nat := 4983230072969 + 3 ^ 40 * 145917 * 2
def baseEnd_145917 : Nat := 33300247405427036785087

theorem tailTrace_145917 : CollatzResearch.WordTrace tailWord_145917 prefixEnd_145917 33300247405427036785087 := by
  unfold tailWord_145917
  simp only [CollatzResearch.WordTrace]
  refine ⟨5322030212375104484676005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3548020141583402989784003 5322030212375104484676005)
  ·
    refine ⟨997880664820332090876751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5322030212375104484676005 997880664820332090876751)
    ·
      refine ⟨1496820997230498136315127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 997880664820332090876751 1496820997230498136315127)
      ·
        refine ⟨2245231495845747204472691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1496820997230498136315127 2245231495845747204472691)
        ·
          refine ⟨3367847243768620806709037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2245231495845747204472691 3367847243768620806709037)
          ·
            refine ⟨1262942716413232802515889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3367847243768620806709037 1262942716413232802515889)
            ·
              refine ⟨947207037309924601886917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1262942716413232802515889 947207037309924601886917)
              ·
                refine ⟨177601319495610862853797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 947207037309924601886917 177601319495610862853797)
                ·
                  refine ⟨33300247405427036785087, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 177601319495610862853797 33300247405427036785087)
                  ·
                    rfl

theorem cell21_145917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 2, 4, 4].length) (baseStart_145917 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_145917 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_145917 prefixEnd_145917 := by exact prefixLift 145917
  have htrace : WordTrace (prefixWord ++ tailWord_145917) baseStart_145917 baseEnd_145917 := by
    simpa [prefixWord, tailWord_145917, baseEnd_145917] using wordTrace_append hprefix tailTrace_145917
  have hstable : (prefixWord ++ tailWord_145917).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_145917).length < 2 ^ (prefixWord ++ tailWord_145917).sum := by decide
  have hdescent : baseEnd_145917 < baseStart_145917 := by decide
  rcases family_descends (prefixWord ++ tailWord_145917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_145926 : List Nat := [6, 2, 1, 1, 1, 3, 2, 1, 4]
def baseStart_145926 : Nat := 118140960795 + 145926 * 2 ^ 59
def prefixEnd_145926 : Nat := 4983230072969 + 3 ^ 40 * 145926 * 2
def baseEnd_145926 : Nat := 33302301328045021135069

theorem tailTrace_145926 : CollatzResearch.WordTrace tailWord_145926 prefixEnd_145926 33302301328045021135069 := by
  unfold tailWord_145926
  simp only [CollatzResearch.WordTrace]
  refine ⟨166323702166953094429801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 3548238979561666014502421 166323702166953094429801)
  ·
    refine ⟨124742776625214820822351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 166323702166953094429801 124742776625214820822351)
    ·
      refine ⟨187114164937822231233527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 124742776625214820822351 187114164937822231233527)
      ·
        refine ⟨280671247406733346850291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 187114164937822231233527 280671247406733346850291)
        ·
          refine ⟨421006871110100020275437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 280671247406733346850291 421006871110100020275437)
          ·
            refine ⟨157877576666287507603289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 421006871110100020275437 157877576666287507603289)
            ·
              refine ⟨118408182499715630702467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 157877576666287507603289 118408182499715630702467)
              ·
                refine ⟨177612273749573446053701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 118408182499715630702467 177612273749573446053701)
                ·
                  refine ⟨33302301328045021135069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 177612273749573446053701 33302301328045021135069)
                  ·
                    rfl

theorem cell21_145926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 3, 2, 1, 4].length) (baseStart_145926 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_145926 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_145926 prefixEnd_145926 := by exact prefixLift 145926
  have htrace : WordTrace (prefixWord ++ tailWord_145926) baseStart_145926 baseEnd_145926 := by
    simpa [prefixWord, tailWord_145926, baseEnd_145926] using wordTrace_append hprefix tailTrace_145926
  have hstable : (prefixWord ++ tailWord_145926).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_145926).length < 2 ^ (prefixWord ++ tailWord_145926).sum := by decide
  have hdescent : baseEnd_145926 < baseStart_145926 := by decide
  rcases family_descends (prefixWord ++ tailWord_145926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_145931 : List Nat := [1, 1, 1, 1, 7, 1, 1, 8]
def baseStart_145931 : Nat := 118140960795 + 145931 * 2 ^ 59
def prefixEnd_145931 : Nat := 4983230072969 + 3 ^ 40 * 145931 * 2
def baseEnd_145931 : Nat := 11101147465388707850575

theorem tailTrace_145931 : CollatzResearch.WordTrace tailWord_145931 prefixEnd_145931 11101147465388707850575 := by
  unfold tailWord_145931
  simp only [CollatzResearch.WordTrace]
  refine ⟨5322540834324384875685647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3548360556216256583790431 5322540834324384875685647)
  ·
    refine ⟨7983811251486577313528471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5322540834324384875685647 7983811251486577313528471)
    ·
      refine ⟨11975716877229865970292707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7983811251486577313528471 11975716877229865970292707)
      ·
        refine ⟨17963575315844798955439061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11975716877229865970292707 17963575315844798955439061)
        ·
          refine ⟨421021296465112475518103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 17963575315844798955439061 421021296465112475518103)
          ·
            refine ⟨631531944697668713277155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 421021296465112475518103 631531944697668713277155)
            ·
              refine ⟨947297917046503069915733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 631531944697668713277155 947297917046503069915733)
              ·
                refine ⟨11101147465388707850575, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 947297917046503069915733 11101147465388707850575)
                ·
                  rfl

theorem cell21_145931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 1, 8].length) (baseStart_145931 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_145931 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_145931 prefixEnd_145931 := by exact prefixLift 145931
  have htrace : WordTrace (prefixWord ++ tailWord_145931) baseStart_145931 baseEnd_145931 := by
    simpa [prefixWord, tailWord_145931, baseEnd_145931] using wordTrace_append hprefix tailTrace_145931
  have hstable : (prefixWord ++ tailWord_145931).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_145931).length < 2 ^ (prefixWord ++ tailWord_145931).sum := by decide
  have hdescent : baseEnd_145931 < baseStart_145931 := by decide
  rcases family_descends (prefixWord ++ tailWord_145931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_145934 : List Nat := [4, 1, 1, 2, 3, 2, 1, 3, 4]
def baseStart_145934 : Nat := 118140960795 + 145934 * 2 ^ 59
def prefixEnd_145934 : Nat := 4983230072969 + 3 ^ 40 * 145934 * 2
def baseEnd_145934 : Nat := 33304127037038785001719

theorem tailTrace_145934 : CollatzResearch.WordTrace tailWord_145934 prefixEnd_145934 33304127037038785001719 := by
  unfold tailWord_145934
  simp only [CollatzResearch.WordTrace]
  refine ⟨665331281664189548505607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3548433502209010925363237 665331281664189548505607)
  ·
    refine ⟨997996922496284322758411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 665331281664189548505607 997996922496284322758411)
    ·
      refine ⟨1496995383744426484137617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 997996922496284322758411 1496995383744426484137617)
      ·
        refine ⟨1122746537808319863103213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1496995383744426484137617 1122746537808319863103213)
        ·
          refine ⟨421029951678119948663705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1122746537808319863103213 421029951678119948663705)
          ·
            refine ⟨315772463758589961497779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 421029951678119948663705 315772463758589961497779)
            ·
              refine ⟨473658695637884942246669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 315772463758589961497779 473658695637884942246669)
              ·
                refine ⟨177622010864206853342501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 473658695637884942246669 177622010864206853342501)
                ·
                  refine ⟨33304127037038785001719, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 177622010864206853342501 33304127037038785001719)
                  ·
                    rfl

theorem cell21_145934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 2, 1, 3, 4].length) (baseStart_145934 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_145934 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_145934 prefixEnd_145934 := by exact prefixLift 145934
  have htrace : WordTrace (prefixWord ++ tailWord_145934) baseStart_145934 baseEnd_145934 := by
    simpa [prefixWord, tailWord_145934, baseEnd_145934] using wordTrace_append hprefix tailTrace_145934
  have hstable : (prefixWord ++ tailWord_145934).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_145934).length < 2 ^ (prefixWord ++ tailWord_145934).sum := by decide
  have hdescent : baseEnd_145934 < baseStart_145934 := by decide
  rcases family_descends (prefixWord ++ tailWord_145934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_145965 : List Nat := [1, 5, 4, 1, 10]
def baseStart_145965 : Nat := 118140960795 + 145965 * 2 ^ 59
def prefixEnd_145965 : Nat := 4983230072969 + 3 ^ 40 * 145965 * 2
def baseEnd_145965 : Nat := 411249403202340987469

theorem tailTrace_145965 : CollatzResearch.WordTrace tailWord_145965 prefixEnd_145965 411249403202340987469 := by
  unfold tailWord_145965
  simp only [CollatzResearch.WordTrace]
  refine ⟨5323780916201208682423349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3549187277467472454948899 5323780916201208682423349)
  ·
    refine ⟨499104460893863313977189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 5323780916201208682423349 499104460893863313977189)
    ·
      refine ⟨93582086417599371370723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 499104460893863313977189 93582086417599371370723)
      ·
        refine ⟨140373129626399057056085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93582086417599371370723 140373129626399057056085)
        ·
          refine ⟨411249403202340987469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 10 140373129626399057056085 411249403202340987469)
          ·
            rfl

theorem cell21_145965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 10].length) (baseStart_145965 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_145965 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_145965 prefixEnd_145965 := by exact prefixLift 145965
  have htrace : WordTrace (prefixWord ++ tailWord_145965) baseStart_145965 baseEnd_145965 := by
    simpa [prefixWord, tailWord_145965, baseEnd_145965] using wordTrace_append hprefix tailTrace_145965
  have hstable : (prefixWord ++ tailWord_145965).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_145965).length < 2 ^ (prefixWord ++ tailWord_145965).sum := by decide
  have hdescent : baseEnd_145965 < baseStart_145965 := by decide
  rcases family_descends (prefixWord ++ tailWord_145965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_145982 : List Nat := [4, 2, 1, 4, 1, 2, 1, 6]
def baseStart_145982 : Nat := 118140960795 + 145982 * 2 ^ 59
def prefixEnd_145982 : Nat := 4983230072969 + 3 ^ 40 * 145982 * 2
def baseEnd_145982 : Nat := 11105027097000456067207

theorem tailTrace_145982 : CollatzResearch.WordTrace tailWord_145982 prefixEnd_145982 11105027097000456067207 := by
  unfold tailWord_145982
  simp only [CollatzResearch.WordTrace]
  refine ⟨665550119642452573224025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3549600638093080390528133 665550119642452573224025)
  ·
    refine ⟨499162589731839429918019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 665550119642452573224025 499162589731839429918019)
    ·
      refine ⟨748743884597759144877029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 499162589731839429918019 748743884597759144877029)
      ·
        refine ⟨140389478362079839664443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 748743884597759144877029 140389478362079839664443)
        ·
          refine ⟨210584217543119759496665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 140389478362079839664443 210584217543119759496665)
          ·
            refine ⟨157938163157339819622499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 210584217543119759496665 157938163157339819622499)
            ·
              refine ⟨236907244736009729433749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 157938163157339819622499 236907244736009729433749)
              ·
                refine ⟨11105027097000456067207, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 236907244736009729433749 11105027097000456067207)
                ·
                  rfl

theorem cell21_145982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 2, 1, 6].length) (baseStart_145982 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_145982 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_145982 prefixEnd_145982 := by exact prefixLift 145982
  have htrace : WordTrace (prefixWord ++ tailWord_145982) baseStart_145982 baseEnd_145982 := by
    simpa [prefixWord, tailWord_145982, baseEnd_145982] using wordTrace_append hprefix tailTrace_145982
  have hstable : (prefixWord ++ tailWord_145982).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_145982).length < 2 ^ (prefixWord ++ tailWord_145982).sum := by decide
  have hdescent : baseEnd_145982 < baseStart_145982 := by decide
  rcases family_descends (prefixWord ++ tailWord_145982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_146024 : List Nat := [2, 1, 4, 3, 2, 1, 8]
def baseStart_146024 : Nat := 118140960795 + 146024 * 2 ^ 59
def prefixEnd_146024 : Nat := 4983230072969 + 3 ^ 40 * 146024 * 2
def baseEnd_146024 : Nat := 3702740695913180944615

theorem tailTrace_146024 : CollatzResearch.WordTrace tailWord_146024 prefixEnd_146024 3702740695913180944615 := by
  unfold tailWord_146024
  simp only [CollatzResearch.WordTrace]
  refine ⟨2662966411493730879410563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3550621881991641172547417 2662966411493730879410563)
  ·
    refine ⟨3994449617240596319115845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2662966411493730879410563 3994449617240596319115845)
    ·
      refine ⟨748959303232611809834221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3994449617240596319115845 748959303232611809834221)
      ·
        refine ⟨280859738712229428687833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 748959303232611809834221 280859738712229428687833)
        ·
          refine ⟨210644804034172071515875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 280859738712229428687833 210644804034172071515875)
          ·
            refine ⟨315967206051258107273813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 210644804034172071515875 315967206051258107273813)
            ·
              refine ⟨3702740695913180944615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 315967206051258107273813 3702740695913180944615)
              ·
                rfl

theorem cell21_146024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 1, 8].length) (baseStart_146024 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_146024 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_146024 prefixEnd_146024 := by exact prefixLift 146024
  have htrace : WordTrace (prefixWord ++ tailWord_146024) baseStart_146024 baseEnd_146024 := by
    simpa [prefixWord, tailWord_146024, baseEnd_146024] using wordTrace_append hprefix tailTrace_146024
  have hstable : (prefixWord ++ tailWord_146024).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_146024).length < 2 ^ (prefixWord ++ tailWord_146024).sum := by decide
  have hdescent : baseEnd_146024 < baseStart_146024 := by decide
  rcases family_descends (prefixWord ++ tailWord_146024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_146058 : List Nat := [3, 1, 2, 3, 4, 1, 2, 5]
def baseStart_146058 : Nat := 118140960795 + 146058 * 2 ^ 59
def prefixEnd_146058 : Nat := 4983230072969 + 3 ^ 40 * 146058 * 2
def baseEnd_146058 : Nat := 11110808508814041644933

theorem tailTrace_146058 : CollatzResearch.WordTrace tailWord_146058 prefixEnd_146058 11110808508814041644933 := by
  unfold tailWord_146058
  simp only [CollatzResearch.WordTrace]
  refine ⟨1331793226216071391389707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3551448603242857043705885 1331793226216071391389707)
  ·
    refine ⟨1997689839324107087084561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1331793226216071391389707 1997689839324107087084561)
    ·
      refine ⟨1498267379493080315313421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1997689839324107087084561 1498267379493080315313421)
      ·
        refine ⟨561850267309905118242533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1498267379493080315313421 561850267309905118242533)
        ·
          refine ⟨105346925120607209670475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 561850267309905118242533 105346925120607209670475)
          ·
            refine ⟨158020387680910814505713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 105346925120607209670475 158020387680910814505713)
            ·
              refine ⟨118515290760683110879285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 158020387680910814505713 118515290760683110879285)
              ·
                refine ⟨11110808508814041644933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 118515290760683110879285 11110808508814041644933)
                ·
                  rfl

theorem cell21_146058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 4, 1, 2, 5].length) (baseStart_146058 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_146058 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_146058 prefixEnd_146058 := by exact prefixLift 146058
  have htrace : WordTrace (prefixWord ++ tailWord_146058) baseStart_146058 baseEnd_146058 := by
    simpa [prefixWord, tailWord_146058, baseEnd_146058] using wordTrace_append hprefix tailTrace_146058
  have hstable : (prefixWord ++ tailWord_146058).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_146058).length < 2 ^ (prefixWord ++ tailWord_146058).sum := by decide
  have hdescent : baseEnd_146058 < baseStart_146058 := by decide
  rcases family_descends (prefixWord ++ tailWord_146058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_146103 : List Nat := [1, 1, 3, 1, 6, 2, 2, 1, 4]
def baseStart_146103 : Nat := 118140960795 + 146103 * 2 ^ 59
def prefixEnd_146103 : Nat := 4983230072969 + 3 ^ 40 * 146103 * 2
def baseEnd_146103 : Nat := 33342695139532046684707

theorem tailTrace_146103 : CollatzResearch.WordTrace tailWord_146103 prefixEnd_146103 33342695139532046684707 := by
  unfold tailWord_146103
  simp only [CollatzResearch.WordTrace]
  refine ⟨5328814189701258250946963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3552542793134172167297975 5328814189701258250946963)
  ·
    refine ⟨7993221284551887376420445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5328814189701258250946963 7993221284551887376420445)
    ·
      refine ⟨2997457981706957766157667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7993221284551887376420445 2997457981706957766157667)
      ·
        refine ⟨4496186972560436649236501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2997457981706957766157667 4496186972560436649236501)
        ·
          refine ⟨210758764338770467932961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 4496186972560436649236501 210758764338770467932961)
          ·
            refine ⟨158069073254077850949721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 210758764338770467932961 158069073254077850949721)
            ·
              refine ⟨118551804940558388212291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 158069073254077850949721 118551804940558388212291)
              ·
                refine ⟨177827707410837582318437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 118551804940558388212291 177827707410837582318437)
                ·
                  refine ⟨33342695139532046684707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 177827707410837582318437 33342695139532046684707)
                  ·
                    rfl

theorem cell21_146103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 2, 2, 1, 4].length) (baseStart_146103 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_146103 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_146103 prefixEnd_146103 := by exact prefixLift 146103
  have htrace : WordTrace (prefixWord ++ tailWord_146103) baseStart_146103 baseEnd_146103 := by
    simpa [prefixWord, tailWord_146103, baseEnd_146103] using wordTrace_append hprefix tailTrace_146103
  have hstable : (prefixWord ++ tailWord_146103).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_146103).length < 2 ^ (prefixWord ++ tailWord_146103).sum := by decide
  have hdescent : baseEnd_146103 < baseStart_146103 := by decide
  rcases family_descends (prefixWord ++ tailWord_146103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_146145 : List Nat := [1, 2, 3, 1, 4, 1, 1, 4, 4]
def baseStart_146145 : Nat := 118140960795 + 146145 * 2 ^ 59
def prefixEnd_146145 : Nat := 4983230072969 + 3 ^ 40 * 146145 * 2
def baseEnd_146145 : Nat := 33352280111749306984621

theorem tailTrace_146145 : CollatzResearch.WordTrace tailWord_146145 prefixEnd_146145 33352280111749306984621 := by
  unfold tailWord_146145
  simp only [CollatzResearch.WordTrace]
  refine ⟨5330346055549099423975889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3553564037032732949317259 5330346055549099423975889)
  ·
    refine ⟨3997759541661824567981917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5330346055549099423975889 3997759541661824567981917)
    ·
      refine ⟨1499159828123184212993219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3997759541661824567981917 1499159828123184212993219)
      ·
        refine ⟨2248739742184776319489829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1499159828123184212993219 2248739742184776319489829)
        ·
          refine ⟨421638701659645559904343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2248739742184776319489829 421638701659645559904343)
          ·
            refine ⟨632458052489468339856515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 421638701659645559904343 632458052489468339856515)
            ·
              refine ⟨948687078734202509784773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 632458052489468339856515 948687078734202509784773)
              ·
                refine ⟨177878827262662970584645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 948687078734202509784773 177878827262662970584645)
                ·
                  refine ⟨33352280111749306984621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 177878827262662970584645 33352280111749306984621)
                  ·
                    rfl

theorem cell21_146145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 1, 4, 4].length) (baseStart_146145 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_146145 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_146145 prefixEnd_146145 := by exact prefixLift 146145
  have htrace : WordTrace (prefixWord ++ tailWord_146145) baseStart_146145 baseEnd_146145 := by
    simpa [prefixWord, tailWord_146145, baseEnd_146145] using wordTrace_append hprefix tailTrace_146145
  have hstable : (prefixWord ++ tailWord_146145).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_146145).length < 2 ^ (prefixWord ++ tailWord_146145).sum := by decide
  have hdescent : baseEnd_146145 < baseStart_146145 := by decide
  rcases family_descends (prefixWord ++ tailWord_146145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_146148 : List Nat := [2, 3, 1, 1, 1, 4, 4, 2, 3]
def baseStart_146148 : Nat := 118140960795 + 146148 * 2 ^ 59
def prefixEnd_146148 : Nat := 4983230072969 + 3 ^ 40 * 146148 * 2
def baseEnd_146148 : Nat := 33352964752621968434615

theorem tailTrace_146148 : CollatzResearch.WordTrace tailWord_146148 prefixEnd_146148 33352964752621968434615 := by
  unfold tailWord_146148
  simp only [CollatzResearch.WordTrace]
  refine ⟨2665227737269115468167549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3553636983025487290890065 2665227737269115468167549)
  ·
    refine ⟨999460401475918300562831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2665227737269115468167549 999460401475918300562831)
    ·
      refine ⟨1499190602213877450844247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 999460401475918300562831 1499190602213877450844247)
      ·
        refine ⟨2248785903320816176266371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1499190602213877450844247 2248785903320816176266371)
        ·
          refine ⟨3373178854981224264399557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2248785903320816176266371 3373178854981224264399557)
          ·
            refine ⟨632471035308979549574917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3373178854981224264399557 632471035308979549574917)
            ·
              refine ⟨118588319120433665545297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 632471035308979549574917 118588319120433665545297)
              ·
                refine ⟨88941239340325249158973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 118588319120433665545297 88941239340325249158973)
                ·
                  refine ⟨33352964752621968434615, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 88941239340325249158973 33352964752621968434615)
                  ·
                    rfl

theorem cell21_146148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 4, 2, 3].length) (baseStart_146148 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_146148 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_146148 prefixEnd_146148 := by exact prefixLift 146148
  have htrace : WordTrace (prefixWord ++ tailWord_146148) baseStart_146148 baseEnd_146148 := by
    simpa [prefixWord, tailWord_146148, baseEnd_146148] using wordTrace_append hprefix tailTrace_146148
  have hstable : (prefixWord ++ tailWord_146148).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_146148).length < 2 ^ (prefixWord ++ tailWord_146148).sum := by decide
  have hdescent : baseEnd_146148 < baseStart_146148 := by decide
  rcases family_descends (prefixWord ++ tailWord_146148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_146159 : List Nat := [1, 1, 2, 1, 5, 2, 3, 6]
def baseStart_146159 : Nat := 118140960795 + 146159 * 2 ^ 59
def prefixEnd_146159 : Nat := 4983230072969 + 3 ^ 40 * 146159 * 2
def baseEnd_146159 : Nat := 11118491700829464583753

theorem tailTrace_146159 : CollatzResearch.WordTrace tailWord_146159 prefixEnd_146159 11118491700829464583753 := by
  unfold tailWord_146159
  simp only [CollatzResearch.WordTrace]
  refine ⟨5330856677498379814985531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3553904451665586543323687 5330856677498379814985531)
  ·
    refine ⟨7996285016247569722478297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5330856677498379814985531 7996285016247569722478297)
    ·
      refine ⟨5997213762185677291858723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7996285016247569722478297 5997213762185677291858723)
      ·
        refine ⟨8995820643278515937788085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5997213762185677291858723 8995820643278515937788085)
        ·
          refine ⟨843358185307360869167633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 8995820643278515937788085 843358185307360869167633)
          ·
            refine ⟨632518638980520651875725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 843358185307360869167633 632518638980520651875725)
            ·
              refine ⟨237194489617695244453397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 632518638980520651875725 237194489617695244453397)
              ·
                refine ⟨11118491700829464583753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 237194489617695244453397 11118491700829464583753)
                ·
                  rfl

theorem cell21_146159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 3, 6].length) (baseStart_146159 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_146159 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_146159 prefixEnd_146159 := by exact prefixLift 146159
  have htrace : WordTrace (prefixWord ++ tailWord_146159) baseStart_146159 baseEnd_146159 := by
    simpa [prefixWord, tailWord_146159, baseEnd_146159] using wordTrace_append hprefix tailTrace_146159
  have hstable : (prefixWord ++ tailWord_146159).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_146159).length < 2 ^ (prefixWord ++ tailWord_146159).sum := by decide
  have hdescent : baseEnd_146159 < baseStart_146159 := by decide
  rcases family_descends (prefixWord ++ tailWord_146159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_146165 : List Nat := [1, 3, 6, 1, 1, 1, 1, 2, 5]
def baseStart_146165 : Nat := 118140960795 + 146165 * 2 ^ 59
def prefixEnd_146165 : Nat := 4983230072969 + 3 ^ 40 * 146165 * 2
def baseEnd_146165 : Nat := 33356844384233716651247

theorem tailTrace_146165 : CollatzResearch.WordTrace tailWord_146165 prefixEnd_146165 33356844384233716651247 := by
  unfold tailWord_146165
  simp only [CollatzResearch.WordTrace]
  refine ⟨5331075515476642839703949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3554050343651095226469299 5331075515476642839703949)
  ·
    refine ⟨1999153318303741064888981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5331075515476642839703949 1999153318303741064888981)
    ·
      refine ⟨93710311795487862416671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 1999153318303741064888981 93710311795487862416671)
      ·
        refine ⟨140565467693231793625007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93710311795487862416671 140565467693231793625007)
        ·
          refine ⟨210848201539847690437511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 140565467693231793625007 210848201539847690437511)
          ·
            refine ⟨316272302309771535656267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 210848201539847690437511 316272302309771535656267)
            ·
              refine ⟨474408453464657303484401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 316272302309771535656267 474408453464657303484401)
              ·
                refine ⟨355806340098492977613301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 474408453464657303484401 355806340098492977613301)
                ·
                  refine ⟨33356844384233716651247, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 355806340098492977613301 33356844384233716651247)
                  ·
                    rfl

theorem cell21_146165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 1, 1, 2, 5].length) (baseStart_146165 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_146165 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_146165 prefixEnd_146165 := by exact prefixLift 146165
  have htrace : WordTrace (prefixWord ++ tailWord_146165) baseStart_146165 baseEnd_146165 := by
    simpa [prefixWord, tailWord_146165, baseEnd_146165] using wordTrace_append hprefix tailTrace_146165
  have hstable : (prefixWord ++ tailWord_146165).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_146165).length < 2 ^ (prefixWord ++ tailWord_146165).sum := by decide
  have hdescent : baseEnd_146165 < baseStart_146165 := by decide
  rcases family_descends (prefixWord ++ tailWord_146165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_146207 : List Nat := [1, 1, 2, 4, 2, 2, 2, 4, 3]
def baseStart_146207 : Nat := 118140960795 + 146207 * 2 ^ 59
def prefixEnd_146207 : Nat := 4983230072969 + 3 ^ 40 * 146207 * 2
def baseEnd_146207 : Nat := 33366429356450976951161

theorem tailTrace_146207 : CollatzResearch.WordTrace tailWord_146207 prefixEnd_146207 33366429356450976951161 := by
  unfold tailWord_146207
  simp only [CollatzResearch.WordTrace]
  refine ⟨5332607381324484012732875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3555071587549656008488583 5332607381324484012732875)
  ·
    refine ⟨7998911071986726019099313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5332607381324484012732875 7998911071986726019099313)
    ·
      refine ⟨5999183303990044514324485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7998911071986726019099313 5999183303990044514324485)
      ·
        refine ⟨1124846869498133346435841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5999183303990044514324485 1124846869498133346435841)
        ·
          refine ⟨843635152123600009826881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1124846869498133346435841 843635152123600009826881)
          ·
            refine ⟨632726364092700007370161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 843635152123600009826881 632726364092700007370161)
            ·
              refine ⟨474544773069525005527621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 632726364092700007370161 474544773069525005527621)
              ·
                refine ⟨88977144950535938536429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 474544773069525005527621 88977144950535938536429)
                ·
                  refine ⟨33366429356450976951161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 88977144950535938536429 33366429356450976951161)
                  ·
                    rfl

theorem cell21_146207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 2, 4, 3].length) (baseStart_146207 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_146207 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_146207 prefixEnd_146207 := by exact prefixLift 146207
  have htrace : WordTrace (prefixWord ++ tailWord_146207) baseStart_146207 baseEnd_146207 := by
    simpa [prefixWord, tailWord_146207, baseEnd_146207] using wordTrace_append hprefix tailTrace_146207
  have hstable : (prefixWord ++ tailWord_146207).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_146207).length < 2 ^ (prefixWord ++ tailWord_146207).sum := by decide
  have hdescent : baseEnd_146207 < baseStart_146207 := by decide
  rcases family_descends (prefixWord ++ tailWord_146207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_146266 : List Nat := [3, 1, 1, 2, 1, 4, 3, 1, 5]
def baseStart_146266 : Nat := 118140960795 + 146266 * 2 ^ 59
def prefixEnd_146266 : Nat := 4983230072969 + 3 ^ 40 * 146266 * 2
def baseEnd_146266 : Nat := 33379893960279985467707

theorem tailTrace_146266 : CollatzResearch.WordTrace tailWord_146266 prefixEnd_146266 33379893960279985467707 := by
  unfold tailWord_146266
  simp only [CollatzResearch.WordTrace]
  refine ⟨1333689822027684272282663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3556506192073824726087101 1333689822027684272282663)
  ·
    refine ⟨2000534733041526408423995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1333689822027684272282663 2000534733041526408423995)
    ·
      refine ⟨3000802099562289612635993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2000534733041526408423995 3000802099562289612635993)
      ·
        refine ⟨2250601574671717209476995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3000802099562289612635993 2250601574671717209476995)
        ·
          refine ⟨3375902362007575814215493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2250601574671717209476995 3375902362007575814215493)
          ·
            refine ⟨632981692876420465165405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3375902362007575814215493 632981692876420465165405)
            ·
              refine ⟨237368134828657674437027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 632981692876420465165405 237368134828657674437027)
              ·
                refine ⟨356052202242986511655541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 237368134828657674437027 356052202242986511655541)
                ·
                  refine ⟨33379893960279985467707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 356052202242986511655541 33379893960279985467707)
                  ·
                    rfl

theorem cell21_146266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 3, 1, 5].length) (baseStart_146266 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_146266 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_146266 prefixEnd_146266 := by exact prefixLift 146266
  have htrace : WordTrace (prefixWord ++ tailWord_146266) baseStart_146266 baseEnd_146266 := by
    simpa [prefixWord, tailWord_146266, baseEnd_146266] using wordTrace_append hprefix tailTrace_146266
  have hstable : (prefixWord ++ tailWord_146266).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_146266).length < 2 ^ (prefixWord ++ tailWord_146266).sum := by decide
  have hdescent : baseEnd_146266 < baseStart_146266 := by decide
  rcases family_descends (prefixWord ++ tailWord_146266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_146314 : List Nat := [3, 1, 2, 4, 1, 2, 2, 2, 4]
def baseStart_146314 : Nat := 118140960795 + 146314 * 2 ^ 59
def prefixEnd_146314 : Nat := 4983230072969 + 3 ^ 40 * 146314 * 2
def baseEnd_146314 : Nat := 33390848214242568667609

theorem tailTrace_146314 : CollatzResearch.WordTrace tailWord_146314 prefixEnd_146314 33390848214242568667609 := by
  unfold tailWord_146314
  simp only [CollatzResearch.WordTrace]
  refine ⟨1334127497984210321719499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3557673327957894191251997 1334127497984210321719499)
  ·
    refine ⟨2001191246976315482579249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1334127497984210321719499 2001191246976315482579249)
    ·
      refine ⟨1500893435232236611934437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2001191246976315482579249 1500893435232236611934437)
      ·
        refine ⟨281417519106044364737707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1500893435232236611934437 281417519106044364737707)
        ·
          refine ⟨422126278659066547106561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 281417519106044364737707 422126278659066547106561)
          ·
            refine ⟨316594708994299910329921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 422126278659066547106561 316594708994299910329921)
            ·
              refine ⟨237446031745724932747441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 316594708994299910329921 237446031745724932747441)
              ·
                refine ⟨178084523809293699560581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 237446031745724932747441 178084523809293699560581)
                ·
                  refine ⟨33390848214242568667609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 178084523809293699560581 33390848214242568667609)
                  ·
                    rfl

theorem cell21_146314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 2, 2, 2, 4].length) (baseStart_146314 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_146314 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_146314 prefixEnd_146314 := by exact prefixLift 146314
  have htrace : WordTrace (prefixWord ++ tailWord_146314) baseStart_146314 baseEnd_146314 := by
    simpa [prefixWord, tailWord_146314, baseEnd_146314] using wordTrace_append hprefix tailTrace_146314
  have hstable : (prefixWord ++ tailWord_146314).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_146314).length < 2 ^ (prefixWord ++ tailWord_146314).sum := by decide
  have hdescent : baseEnd_146314 < baseStart_146314 := by decide
  rcases family_descends (prefixWord ++ tailWord_146314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_146421 : List Nat := [1, 3, 5, 2, 1, 2, 7]
def baseStart_146421 : Nat := 118140960795 + 146421 * 2 ^ 59
def prefixEnd_146421 : Nat := 4983230072969 + 3 ^ 40 * 146421 * 2
def baseEnd_146421 : Nat := 3712807452448240042673

theorem tailTrace_146421 : CollatzResearch.WordTrace tailWord_146421 prefixEnd_146421 3712807452448240042673 := by
  unfold tailWord_146421
  simp only [CollatzResearch.WordTrace]
  refine ⟨5340412602549198561023117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3560275068366132374015411 5340412602549198561023117)
  ·
    refine ⟨2002654725955949460383669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5340412602549198561023117 2002654725955949460383669)
    ·
      refine ⟨187748880558370261910969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 2002654725955949460383669 187748880558370261910969)
      ·
        refine ⟨140811660418777696433227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 187748880558370261910969 140811660418777696433227)
        ·
          refine ⟨211217490628166544649841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 140811660418777696433227 211217490628166544649841)
          ·
            refine ⟨158413117971124908487381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 211217490628166544649841 158413117971124908487381)
            ·
              refine ⟨3712807452448240042673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 158413117971124908487381 3712807452448240042673)
              ·
                rfl

theorem cell21_146421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 2, 7].length) (baseStart_146421 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_146421 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_146421 prefixEnd_146421 := by exact prefixLift 146421
  have htrace : WordTrace (prefixWord ++ tailWord_146421) baseStart_146421 baseEnd_146421 := by
    simpa [prefixWord, tailWord_146421, baseEnd_146421] using wordTrace_append hprefix tailTrace_146421
  have hstable : (prefixWord ++ tailWord_146421).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_146421).length < 2 ^ (prefixWord ++ tailWord_146421).sum := by decide
  have hdescent : baseEnd_146421 < baseStart_146421 := by decide
  rcases family_descends (prefixWord ++ tailWord_146421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_146497 : List Nat := [1, 2, 5, 1, 4, 1, 1, 6]
def baseStart_146497 : Nat := 118140960795 + 146497 * 2 ^ 59
def prefixEnd_146497 : Nat := 4983230072969 + 3 ^ 40 * 146497 * 2
def baseEnd_146497 : Nat := 11144203769158305705745

theorem tailTrace_146497 : CollatzResearch.WordTrace tailWord_146497 prefixEnd_146497 11144203769158305705745 := by
  unfold tailWord_146497
  simp only [CollatzResearch.WordTrace]
  refine ⟨5343184550273863540789745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3562123033515909027193163 5343184550273863540789745)
  ·
    refine ⟨4007388412705397655592309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5343184550273863540789745 4007388412705397655592309)
    ·
      refine ⟨375692663691131030211779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 4007388412705397655592309 375692663691131030211779)
      ·
        refine ⟨563538995536696545317669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 375692663691131030211779 563538995536696545317669)
        ·
          refine ⟨105663561663130602247063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 563538995536696545317669 105663561663130602247063)
          ·
            refine ⟨158495342494695903370595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 105663561663130602247063 158495342494695903370595)
            ·
              refine ⟨237743013742043855055893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 158495342494695903370595 237743013742043855055893)
              ·
                refine ⟨11144203769158305705745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 237743013742043855055893 11144203769158305705745)
                ·
                  rfl

theorem cell21_146497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 4, 1, 1, 6].length) (baseStart_146497 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_146497 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_146497 prefixEnd_146497 := by exact prefixLift 146497
  have htrace : WordTrace (prefixWord ++ tailWord_146497) baseStart_146497 baseEnd_146497 := by
    simpa [prefixWord, tailWord_146497, baseEnd_146497] using wordTrace_append hprefix tailTrace_146497
  have hstable : (prefixWord ++ tailWord_146497).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_146497).length < 2 ^ (prefixWord ++ tailWord_146497).sum := by decide
  have hdescent : baseEnd_146497 < baseStart_146497 := by decide
  rcases family_descends (prefixWord ++ tailWord_146497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_146542 : List Nat := [4, 1, 2, 2, 1, 4, 1, 2, 4]
def baseStart_146542 : Nat := 118140960795 + 146542 * 2 ^ 59
def prefixEnd_146542 : Nat := 4983230072969 + 3 ^ 40 * 146542 * 2
def baseEnd_146542 : Nat := 33442880920564838867143

theorem tailTrace_146542 : CollatzResearch.WordTrace tailWord_146542 prefixEnd_146542 33442880920564838867143 := by
  unfold tailWord_146542
  simp only [CollatzResearch.WordTrace]
  refine ⟨668103229388854528272235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3563217223407224150785253 668103229388854528272235)
  ·
    refine ⟨1002154844083281792408353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 668103229388854528272235 1002154844083281792408353)
    ·
      refine ⟨751616133062461344306265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1002154844083281792408353 751616133062461344306265)
      ·
        refine ⟨563712099796846008229699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 751616133062461344306265 563712099796846008229699)
        ·
          refine ⟨845568149695269012344549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 563712099796846008229699 845568149695269012344549)
          ·
            refine ⟨158544028067862939814603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 845568149695269012344549 158544028067862939814603)
            ·
              refine ⟨237816042101794409721905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 158544028067862939814603 237816042101794409721905)
              ·
                refine ⟨178362031576345807291429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 237816042101794409721905 178362031576345807291429)
                ·
                  refine ⟨33442880920564838867143, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 178362031576345807291429 33442880920564838867143)
                  ·
                    rfl

theorem cell21_146542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 4, 1, 2, 4].length) (baseStart_146542 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_146542 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_146542 prefixEnd_146542 := by exact prefixLift 146542
  have htrace : WordTrace (prefixWord ++ tailWord_146542) baseStart_146542 baseEnd_146542 := by
    simpa [prefixWord, tailWord_146542, baseEnd_146542] using wordTrace_append hprefix tailTrace_146542
  have hstable : (prefixWord ++ tailWord_146542).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_146542).length < 2 ^ (prefixWord ++ tailWord_146542).sum := by decide
  have hdescent : baseEnd_146542 < baseStart_146542 := by decide
  rcases family_descends (prefixWord ++ tailWord_146542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_146584 : List Nat := [2, 1, 2, 4, 2, 1, 1, 2, 6]
def baseStart_146584 : Nat := 118140960795 + 146584 * 2 ^ 59
def prefixEnd_146584 : Nat := 4983230072969 + 3 ^ 40 * 146584 * 2
def baseEnd_146584 : Nat := 33452465892782099167057

theorem tailTrace_146584 : CollatzResearch.WordTrace tailWord_146584 prefixEnd_146584 33452465892782099167057 := by
  unfold tailWord_146584
  simp only [CollatzResearch.WordTrace]
  refine ⟨2673178850479338699603403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3564238467305784932804537 2673178850479338699603403)
  ·
    refine ⟨4009768275719008049405105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2673178850479338699603403 4009768275719008049405105)
    ·
      refine ⟨3007326206789256037053829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4009768275719008049405105 3007326206789256037053829)
      ·
        refine ⟨563873663772985506947593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3007326206789256037053829 563873663772985506947593)
        ·
          refine ⟨422905247829739130210695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 563873663772985506947593 422905247829739130210695)
          ·
            refine ⟨634357871744608695316043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 422905247829739130210695 634357871744608695316043)
            ·
              refine ⟨951536807616913042974065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 634357871744608695316043 951536807616913042974065)
              ·
                refine ⟨713652605712684782230549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 951536807616913042974065 713652605712684782230549)
                ·
                  refine ⟨33452465892782099167057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 713652605712684782230549 33452465892782099167057)
                  ·
                    rfl

theorem cell21_146584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 1, 2, 6].length) (baseStart_146584 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_146584 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_146584 prefixEnd_146584 := by exact prefixLift 146584
  have htrace : WordTrace (prefixWord ++ tailWord_146584) baseStart_146584 baseEnd_146584 := by
    simpa [prefixWord, tailWord_146584, baseEnd_146584] using wordTrace_append hprefix tailTrace_146584
  have hstable : (prefixWord ++ tailWord_146584).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_146584).length < 2 ^ (prefixWord ++ tailWord_146584).sum := by decide
  have hdescent : baseEnd_146584 < baseStart_146584 := by decide
  rcases family_descends (prefixWord ++ tailWord_146584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_146660 : List Nat := [2, 3, 1, 1, 1, 2, 3, 4, 4]
def baseStart_146660 : Nat := 118140960795 + 146660 * 2 ^ 59
def prefixEnd_146660 : Nat := 4983230072969 + 3 ^ 40 * 146660 * 2
def baseEnd_146660 : Nat := 33469810128222855900235

theorem tailTrace_146660 : CollatzResearch.WordTrace tailWord_146660 prefixEnd_146660 33469810128222855900235 := by
  unfold tailWord_146660
  simp only [CollatzResearch.WordTrace]
  refine ⟨2674564824341671189486717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3566086432455561585982289 2674564824341671189486717)
  ·
    refine ⟨1002961809128126696057519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2674564824341671189486717 1002961809128126696057519)
    ·
      refine ⟨1504442713692190044086279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1002961809128126696057519 1504442713692190044086279)
      ·
        refine ⟨2256664070538285066129419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1504442713692190044086279 2256664070538285066129419)
        ·
          refine ⟨3384996105807427599194129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2256664070538285066129419 3384996105807427599194129)
          ·
            refine ⟨2538747079355570699395597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3384996105807427599194129 2538747079355570699395597)
            ·
              refine ⟨952030154758339012273349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2538747079355570699395597 952030154758339012273349)
              ·
                refine ⟨178505654017188564801253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 952030154758339012273349 178505654017188564801253)
                ·
                  refine ⟨33469810128222855900235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 178505654017188564801253 33469810128222855900235)
                  ·
                    rfl

theorem cell21_146660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 3, 4, 4].length) (baseStart_146660 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_146660 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_146660 prefixEnd_146660 := by exact prefixLift 146660
  have htrace : WordTrace (prefixWord ++ tailWord_146660) baseStart_146660 baseEnd_146660 := by
    simpa [prefixWord, tailWord_146660, baseEnd_146660] using wordTrace_append hprefix tailTrace_146660
  have hstable : (prefixWord ++ tailWord_146660).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_146660).length < 2 ^ (prefixWord ++ tailWord_146660).sum := by decide
  have hdescent : baseEnd_146660 < baseStart_146660 := by decide
  rcases family_descends (prefixWord ++ tailWord_146660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_146691 : List Nat := [1, 1, 1, 3, 2, 5, 3, 5]
def baseStart_146691 : Nat := 118140960795 + 146691 * 2 ^ 59
def prefixEnd_146691 : Nat := 4983230072969 + 3 ^ 40 * 146691 * 2
def baseEnd_146691 : Nat := 11158961583524563627835

theorem tailTrace_146691 : CollatzResearch.WordTrace tailWord_146691 prefixEnd_146691 11158961583524563627835 := by
  unfold tailWord_146691
  simp only [CollatzResearch.WordTrace]
  refine ⟨5350260311571034673351927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3566840207714023115567951 5350260311571034673351927)
  ·
    refine ⟨8025390467356552010027891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5350260311571034673351927 8025390467356552010027891)
    ·
      refine ⟨12038085701034828015041837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8025390467356552010027891 12038085701034828015041837)
      ·
        refine ⟨4514282137888060505640689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12038085701034828015041837 4514282137888060505640689)
        ·
          refine ⟨3385711603416045379230517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4514282137888060505640689 3385711603416045379230517)
          ·
            refine ⟨317410462820254254302861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 3385711603416045379230517 317410462820254254302861)
            ·
              refine ⟨119028923557595345363573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 317410462820254254302861 119028923557595345363573)
              ·
                refine ⟨11158961583524563627835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 119028923557595345363573 11158961583524563627835)
                ·
                  rfl

theorem cell21_146691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 5, 3, 5].length) (baseStart_146691 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_146691 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_146691 prefixEnd_146691 := by exact prefixLift 146691
  have htrace : WordTrace (prefixWord ++ tailWord_146691) baseStart_146691 baseEnd_146691 := by
    simpa [prefixWord, tailWord_146691, baseEnd_146691] using wordTrace_append hprefix tailTrace_146691
  have hstable : (prefixWord ++ tailWord_146691).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_146691).length < 2 ^ (prefixWord ++ tailWord_146691).sum := by decide
  have hdescent : baseEnd_146691 < baseStart_146691 := by decide
  rcases family_descends (prefixWord ++ tailWord_146691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_146742 : List Nat := [5, 1, 2, 3, 1, 2, 2, 5]
def baseStart_146742 : Nat := 118140960795 + 146742 * 2 ^ 59
def prefixEnd_146742 : Nat := 4983230072969 + 3 ^ 40 * 146742 * 2
def baseEnd_146742 : Nat := 11162841215136311844467

theorem tailTrace_146742 : CollatzResearch.WordTrace tailWord_146742 prefixEnd_146742 11162841215136311844467 := by
  unfold tailWord_146742
  simp only [CollatzResearch.WordTrace]
  refine ⟨334507527149141898966155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 3568080289590846922305653 334507527149141898966155)
  ·
    refine ⟨501761290723712848449233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 334507527149141898966155 501761290723712848449233)
    ·
      refine ⟨376320968042784636336925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 501761290723712848449233 376320968042784636336925)
      ·
        refine ⟨141120363016044238626347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 376320968042784636336925 141120363016044238626347)
        ·
          refine ⟨211680544524066357939521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 141120363016044238626347 211680544524066357939521)
          ·
            refine ⟨158760408393049768454641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 211680544524066357939521 158760408393049768454641)
            ·
              refine ⟨119070306294787326340981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 158760408393049768454641 119070306294787326340981)
              ·
                refine ⟨11162841215136311844467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 119070306294787326340981 11162841215136311844467)
                ·
                  rfl

theorem cell21_146742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 2, 2, 5].length) (baseStart_146742 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_146742 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_146742 prefixEnd_146742 := by exact prefixLift 146742
  have htrace : WordTrace (prefixWord ++ tailWord_146742) baseStart_146742 baseEnd_146742 := by
    simpa [prefixWord, tailWord_146742, baseEnd_146742] using wordTrace_append hprefix tailTrace_146742
  have hstable : (prefixWord ++ tailWord_146742).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_146742).length < 2 ^ (prefixWord ++ tailWord_146742).sum := by decide
  have hdescent : baseEnd_146742 < baseStart_146742 := by decide
  rcases family_descends (prefixWord ++ tailWord_146742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_146756 : List Nat := [2, 3, 4, 1, 1, 1, 3, 3, 3]
def baseStart_146756 : Nat := 118140960795 + 146756 * 2 ^ 59
def prefixEnd_146756 : Nat := 4983230072969 + 3 ^ 40 * 146756 * 2
def baseEnd_146756 : Nat := 33491718636148022300039

theorem tailTrace_146756 : CollatzResearch.WordTrace tailWord_146756 prefixEnd_146756 33491718636148022300039 := by
  unfold tailWord_146756
  simp only [CollatzResearch.WordTrace]
  refine ⟨2676315528167775387234061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3568420704223700516312081 2676315528167775387234061)
  ·
    refine ⟨1003618323062915770212773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2676315528167775387234061 1003618323062915770212773)
    ·
      refine ⟨188178435574296706914895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1003618323062915770212773 188178435574296706914895)
      ·
        refine ⟨282267653361445060372343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 188178435574296706914895 282267653361445060372343)
        ·
          refine ⟨423401480042167590558515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 282267653361445060372343 423401480042167590558515)
          ·
            refine ⟨635102220063251385837773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 423401480042167590558515 635102220063251385837773)
            ·
              refine ⟨238163332523719269689165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 635102220063251385837773 238163332523719269689165)
              ·
                refine ⟨89311249696394726133437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 238163332523719269689165 89311249696394726133437)
                ·
                  refine ⟨33491718636148022300039, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 89311249696394726133437 33491718636148022300039)
                  ·
                    rfl

theorem cell21_146756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 3, 3, 3].length) (baseStart_146756 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_146756 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_146756 prefixEnd_146756 := by exact prefixLift 146756
  have htrace : WordTrace (prefixWord ++ tailWord_146756) baseStart_146756 baseEnd_146756 := by
    simpa [prefixWord, tailWord_146756, baseEnd_146756] using wordTrace_append hprefix tailTrace_146756
  have hstable : (prefixWord ++ tailWord_146756).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_146756).length < 2 ^ (prefixWord ++ tailWord_146756).sum := by decide
  have hdescent : baseEnd_146756 < baseStart_146756 := by decide
  rcases family_descends (prefixWord ++ tailWord_146756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_146871 : List Nat := [1, 1, 3, 1, 3, 2, 2, 2, 6]
def baseStart_146871 : Nat := 118140960795 + 146871 * 2 ^ 59
def prefixEnd_146871 : Nat := 4983230072969 + 3 ^ 40 * 146871 * 2
def baseEnd_146871 : Nat := 33517963202933377883137

theorem tailTrace_146871 : CollatzResearch.WordTrace tailWord_146871 prefixEnd_146871 33517963202933377883137 := by
  unfold tailWord_146871
  simp only [CollatzResearch.WordTrace]
  refine ⟨5356825450918925414904467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3571216967279283609936311 5356825450918925414904467)
  ·
    refine ⟨8035238176378388122356701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5356825450918925414904467 8035238176378388122356701)
    ·
      refine ⟨3013214316141895545883763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8035238176378388122356701 3013214316141895545883763)
      ·
        refine ⟨4519821474212843318825645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3013214316141895545883763 4519821474212843318825645)
        ·
          refine ⟨1694933052829816244559617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4519821474212843318825645 1694933052829816244559617)
          ·
            refine ⟨1271199789622362183419713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1694933052829816244559617 1271199789622362183419713)
            ·
              refine ⟨953399842216771637564785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1271199789622362183419713 953399842216771637564785)
              ·
                refine ⟨715049881662578728173589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 953399842216771637564785 715049881662578728173589)
                ·
                  refine ⟨33517963202933377883137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 715049881662578728173589 33517963202933377883137)
                  ·
                    rfl

theorem cell21_146871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 2, 2, 6].length) (baseStart_146871 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_146871 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_146871 prefixEnd_146871 := by exact prefixLift 146871
  have htrace : WordTrace (prefixWord ++ tailWord_146871) baseStart_146871 baseEnd_146871 := by
    simpa [prefixWord, tailWord_146871, baseEnd_146871] using wordTrace_append hprefix tailTrace_146871
  have hstable : (prefixWord ++ tailWord_146871).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_146871).length < 2 ^ (prefixWord ++ tailWord_146871).sum := by decide
  have hdescent : baseEnd_146871 < baseStart_146871 := by decide
  rcases family_descends (prefixWord ++ tailWord_146871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_146905 : List Nat := [1, 2, 1, 2, 4, 3, 3, 1, 4]
def baseStart_146905 : Nat := 118140960795 + 146905 * 2 ^ 59
def prefixEnd_146905 : Nat := 4983230072969 + 3 ^ 40 * 146905 * 2
def baseEnd_146905 : Nat := 33525722466156874316401

theorem tailTrace_146905 : CollatzResearch.WordTrace tailWord_146905 prefixEnd_146905 33525722466156874316401 := by
  unfold tailWord_146905
  simp only [CollatzResearch.WordTrace]
  refine ⟨5358065532795749221642169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3572043688530499481094779 5358065532795749221642169)
  ·
    refine ⟨4018549149596811916231627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5358065532795749221642169 4018549149596811916231627)
    ·
      refine ⟨6027823724395217874347441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4018549149596811916231627 6027823724395217874347441)
      ·
        refine ⟨4520867793296413405760581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6027823724395217874347441 4520867793296413405760581)
        ·
          refine ⟨847662711243077513580109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4520867793296413405760581 847662711243077513580109)
          ·
            refine ⟨317873516716154067592541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 847662711243077513580109 317873516716154067592541)
            ·
              refine ⟨119202568768557775347203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 317873516716154067592541 119202568768557775347203)
              ·
                refine ⟨178803853152836663020805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 119202568768557775347203 178803853152836663020805)
                ·
                  refine ⟨33525722466156874316401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 178803853152836663020805 33525722466156874316401)
                  ·
                    rfl

theorem cell21_146905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 3, 3, 1, 4].length) (baseStart_146905 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_146905 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_146905 prefixEnd_146905 := by exact prefixLift 146905
  have htrace : WordTrace (prefixWord ++ tailWord_146905) baseStart_146905 baseEnd_146905 := by
    simpa [prefixWord, tailWord_146905, baseEnd_146905] using wordTrace_append hprefix tailTrace_146905
  have hstable : (prefixWord ++ tailWord_146905).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_146905).length < 2 ^ (prefixWord ++ tailWord_146905).sum := by decide
  have hdescent : baseEnd_146905 < baseStart_146905 := by decide
  rcases family_descends (prefixWord ++ tailWord_146905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_146919 : List Nat := [1, 1, 5, 2, 1, 2, 4, 5]
def baseStart_146919 : Nat := 118140960795 + 146919 * 2 ^ 59
def prefixEnd_146919 : Nat := 4983230072969 + 3 ^ 40 * 146919 * 2
def baseEnd_146919 : Nat := 11176305818965320361013

theorem tailTrace_146919 : CollatzResearch.WordTrace tailWord_146919 prefixEnd_146919 11176305818965320361013 := by
  unfold tailWord_146919
  simp only [CollatzResearch.WordTrace]
  refine ⟨5358576154745029612651811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3572384103163353075101207 5358576154745029612651811)
  ·
    refine ⟨8037864232117544418977717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5358576154745029612651811 8037864232117544418977717)
    ·
      refine ⟨753549771761019789279161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 8037864232117544418977717 753549771761019789279161)
      ·
        refine ⟨565162328820764841959371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 753549771761019789279161 565162328820764841959371)
        ·
          refine ⟨847743493231147262939057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 565162328820764841959371 847743493231147262939057)
          ·
            refine ⟨635807619923360447204293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 847743493231147262939057 635807619923360447204293)
            ·
              refine ⟨119213928735630083850805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 635807619923360447204293 119213928735630083850805)
              ·
                refine ⟨11176305818965320361013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 119213928735630083850805 11176305818965320361013)
                ·
                  rfl

theorem cell21_146919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 4, 5].length) (baseStart_146919 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_146919 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_146919 prefixEnd_146919 := by exact prefixLift 146919
  have htrace : WordTrace (prefixWord ++ tailWord_146919) baseStart_146919 baseEnd_146919 := by
    simpa [prefixWord, tailWord_146919, baseEnd_146919] using wordTrace_append hprefix tailTrace_146919
  have hstable : (prefixWord ++ tailWord_146919).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_146919).length < 2 ^ (prefixWord ++ tailWord_146919).sum := by decide
  have hdescent : baseEnd_146919 < baseStart_146919 := by decide
  rcases family_descends (prefixWord ++ tailWord_146919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_146925 : List Nat := [1, 5, 1, 3, 3, 1, 1, 3, 3]
def baseStart_146925 : Nat := 118140960795 + 146925 * 2 ^ 59
def prefixEnd_146925 : Nat := 4983230072969 + 3 ^ 40 * 146925 * 2
def baseEnd_146925 : Nat := 33530286738641283983027

theorem tailTrace_146925 : CollatzResearch.WordTrace tailWord_146925 prefixEnd_146925 33530286738641283983027 := by
  unfold tailWord_146925
  simp only [CollatzResearch.WordTrace]
  refine ⟨5358794992723292637370229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3572529995148861758246819 5358794992723292637370229)
  ·
    refine ⟨502387030567808684753459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 5358794992723292637370229 502387030567808684753459)
    ·
      refine ⟨753580545851713027130189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 502387030567808684753459 753580545851713027130189)
      ·
        refine ⟨282592704694392385173821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 753580545851713027130189 282592704694392385173821)
        ·
          refine ⟨105972264260397144440183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 282592704694392385173821 105972264260397144440183)
          ·
            refine ⟨158958396390595716660275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 105972264260397144440183 158958396390595716660275)
            ·
              refine ⟨238437594585893574990413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 158958396390595716660275 238437594585893574990413)
              ·
                refine ⟨89414097969710090621405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 238437594585893574990413 89414097969710090621405)
                ·
                  refine ⟨33530286738641283983027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 89414097969710090621405 33530286738641283983027)
                  ·
                    rfl

theorem cell21_146925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 3, 1, 1, 3, 3].length) (baseStart_146925 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_146925 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_146925 prefixEnd_146925 := by exact prefixLift 146925
  have htrace : WordTrace (prefixWord ++ tailWord_146925) baseStart_146925 baseEnd_146925 := by
    simpa [prefixWord, tailWord_146925, baseEnd_146925] using wordTrace_append hprefix tailTrace_146925
  have hstable : (prefixWord ++ tailWord_146925).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_146925).length < 2 ^ (prefixWord ++ tailWord_146925).sum := by decide
  have hdescent : baseEnd_146925 < baseStart_146925 := by decide
  rcases family_descends (prefixWord ++ tailWord_146925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_146978 : List Nat := [3, 3, 1, 1, 1, 1, 4, 7]
def baseStart_146978 : Nat := 118140960795 + 146978 * 2 ^ 59
def prefixEnd_146978 : Nat := 4983230072969 + 3 ^ 40 * 146978 * 2
def baseEnd_146978 : Nat := 11180794020241656533195

theorem tailTrace_146978 : CollatzResearch.WordTrace tailWord_146978 prefixEnd_146978 11180794020241656533195 := by
  unfold tailWord_146978
  simp only [CollatzResearch.WordTrace]
  refine ⟨1340182015382820672262397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3573818707687521792699725 1340182015382820672262397)
  ·
    refine ⟨502568255768557752098399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1340182015382820672262397 502568255768557752098399)
    ·
      refine ⟨753852383652836628147599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 502568255768557752098399 753852383652836628147599)
      ·
        refine ⟨1130778575479254942221399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 753852383652836628147599 1130778575479254942221399)
        ·
          refine ⟨1696167863218882413332099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1130778575479254942221399 1696167863218882413332099)
          ·
            refine ⟨2544251794828323619998149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1696167863218882413332099 2544251794828323619998149)
            ·
              refine ⟨477047211530310678749653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2544251794828323619998149 477047211530310678749653)
              ·
                refine ⟨11180794020241656533195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 477047211530310678749653 11180794020241656533195)
                ·
                  rfl

theorem cell21_146978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 4, 7].length) (baseStart_146978 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_146978 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_146978 prefixEnd_146978 := by exact prefixLift 146978
  have htrace : WordTrace (prefixWord ++ tailWord_146978) baseStart_146978 baseEnd_146978 := by
    simpa [prefixWord, tailWord_146978, baseEnd_146978] using wordTrace_append hprefix tailTrace_146978
  have hstable : (prefixWord ++ tailWord_146978).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_146978).length < 2 ^ (prefixWord ++ tailWord_146978).sum := by decide
  have hdescent : baseEnd_146978 < baseStart_146978 := by decide
  rcases family_descends (prefixWord ++ tailWord_146978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_146998 : List Nat := [5, 1, 2, 1, 3, 1, 2, 2, 4]
def baseStart_146998 : Nat := 118140960795 + 146998 * 2 ^ 59
def prefixEnd_146998 : Nat := 4983230072969 + 3 ^ 40 * 146998 * 2
def baseEnd_146998 : Nat := 33546946333209379266211

theorem tailTrace_146998 : CollatzResearch.WordTrace tailWord_146998 prefixEnd_146998 33546946333209379266211 := by
  unfold tailWord_146998
  simp only [CollatzResearch.WordTrace]
  refine ⟨335091095091176631548603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 3574305014305884069851765 335091095091176631548603)
  ·
    refine ⟨502636642636764947322905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 335091095091176631548603 502636642636764947322905)
    ·
      refine ⟨376977481977573710492179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 502636642636764947322905 376977481977573710492179)
      ·
        refine ⟨565466222966360565738269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 376977481977573710492179 565466222966360565738269)
        ·
          refine ⟨212049833612385212151851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 565466222966360565738269 212049833612385212151851)
          ·
            refine ⟨318074750418577818227777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 212049833612385212151851 318074750418577818227777)
            ·
              refine ⟨238556062813933363670833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 318074750418577818227777 238556062813933363670833)
              ·
                refine ⟨178917047110450022753125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 238556062813933363670833 178917047110450022753125)
                ·
                  refine ⟨33546946333209379266211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 178917047110450022753125 33546946333209379266211)
                  ·
                    rfl

theorem cell21_146998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 1, 2, 2, 4].length) (baseStart_146998 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_146998 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_146998 prefixEnd_146998 := by exact prefixLift 146998
  have htrace : WordTrace (prefixWord ++ tailWord_146998) baseStart_146998 baseEnd_146998 := by
    simpa [prefixWord, tailWord_146998, baseEnd_146998] using wordTrace_append hprefix tailTrace_146998
  have hstable : (prefixWord ++ tailWord_146998).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_146998).length < 2 ^ (prefixWord ++ tailWord_146998).sum := by decide
  have hdescent : baseEnd_146998 < baseStart_146998 := by decide
  rcases family_descends (prefixWord ++ tailWord_146998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_147009 : List Nat := [1, 2, 5, 1, 1, 1, 2, 3, 5]
def baseStart_147009 : Nat := 118140960795 + 147009 * 2 ^ 59
def prefixEnd_147009 : Nat := 4983230072969 + 3 ^ 40 * 147009 * 2
def baseEnd_147009 : Nat := 33549456683075804582855

theorem tailTrace_147009 : CollatzResearch.WordTrace tailWord_147009 prefixEnd_147009 33549456683075804582855 := by
  unfold tailWord_147009
  simp only [CollatzResearch.WordTrace]
  refine ⟨5361858724418974983428081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3574572482945983322285387 5361858724418974983428081)
  ·
    refine ⟨4021394043314231237571061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5361858724418974983428081 4021394043314231237571061)
    ·
      refine ⟨377005691560709178522287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 4021394043314231237571061 377005691560709178522287)
      ·
        refine ⟨565508537341063767783431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 377005691560709178522287 565508537341063767783431)
        ·
          refine ⟨848262806011595651675147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 565508537341063767783431 848262806011595651675147)
          ·
            refine ⟨1272394209017393477512721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 848262806011595651675147 1272394209017393477512721)
            ·
              refine ⟨954295656763045108134541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1272394209017393477512721 954295656763045108134541)
              ·
                refine ⟨357860871286141915550453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 954295656763045108134541 357860871286141915550453)
                ·
                  refine ⟨33549456683075804582855, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 357860871286141915550453 33549456683075804582855)
                  ·
                    rfl

theorem cell21_147009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 2, 3, 5].length) (baseStart_147009 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_147009 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_147009 prefixEnd_147009 := by exact prefixLift 147009
  have htrace : WordTrace (prefixWord ++ tailWord_147009) baseStart_147009 baseEnd_147009 := by
    simpa [prefixWord, tailWord_147009, baseEnd_147009] using wordTrace_append hprefix tailTrace_147009
  have hstable : (prefixWord ++ tailWord_147009).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_147009).length < 2 ^ (prefixWord ++ tailWord_147009).sum := by decide
  have hdescent : baseEnd_147009 < baseStart_147009 := by decide
  rcases family_descends (prefixWord ++ tailWord_147009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_147130 : List Nat := [3, 1, 1, 1, 2, 5, 2, 6]
def baseStart_147130 : Nat := 118140960795 + 147130 * 2 ^ 59
def prefixEnd_147130 : Nat := 4983230072969 + 3 ^ 40 * 147130 * 2
def baseEnd_147130 : Nat := 11192356843868827688647

theorem tailTrace_147130 : CollatzResearch.WordTrace tailWord_147130 prefixEnd_147130 11192356843868827688647 := by
  unfold tailWord_147130
  simp only [CollatzResearch.WordTrace]
  refine ⟨1341567989245153162145711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3577514637987075099055229 1341567989245153162145711)
  ·
    refine ⟨2012351983867729743218567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1341567989245153162145711 2012351983867729743218567)
    ·
      refine ⟨3018527975801594614827851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2012351983867729743218567 3018527975801594614827851)
      ·
        refine ⟨4527791963702391922241777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3018527975801594614827851 4527791963702391922241777)
        ·
          refine ⟨3395843972776793941681333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4527791963702391922241777 3395843972776793941681333)
          ·
            refine ⟨318360372447824432032625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 3395843972776793941681333 318360372447824432032625)
            ·
              refine ⟨238770279335868324024469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 318360372447824432032625 238770279335868324024469)
              ·
                refine ⟨11192356843868827688647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 238770279335868324024469 11192356843868827688647)
                ·
                  rfl

theorem cell21_147130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 5, 2, 6].length) (baseStart_147130 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_147130 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_147130 prefixEnd_147130 := by exact prefixLift 147130
  have htrace : WordTrace (prefixWord ++ tailWord_147130) baseStart_147130 baseEnd_147130 := by
    simpa [prefixWord, tailWord_147130, baseEnd_147130] using wordTrace_append hprefix tailTrace_147130
  have hstable : (prefixWord ++ tailWord_147130).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_147130).length < 2 ^ (prefixWord ++ tailWord_147130).sum := by decide
  have hdescent : baseEnd_147130 < baseStart_147130 := by decide
  rcases family_descends (prefixWord ++ tailWord_147130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_147144 : List Nat := [2, 1, 3, 1, 2, 2, 2, 1, 7]
def baseStart_147144 : Nat := 118140960795 + 147144 * 2 ^ 59
def prefixEnd_147144 : Nat := 4983230072969 + 3 ^ 40 * 147144 * 2
def baseEnd_147144 : Nat := 33580265522345569832579

theorem tailTrace_147144 : CollatzResearch.WordTrace tailWord_147144 prefixEnd_147144 33580265522345569832579 := by
  unfold tailWord_147144
  simp only [CollatzResearch.WordTrace]
  refine ⟨2683391289464946519796243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3577855052619928693061657 2683391289464946519796243)
  ·
    refine ⟨4025086934197419779694365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2683391289464946519796243 4025086934197419779694365)
    ·
      refine ⟨1509407600324032417385387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4025086934197419779694365 1509407600324032417385387)
      ·
        refine ⟨2264111400486048626078081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1509407600324032417385387 2264111400486048626078081)
        ·
          refine ⟨1698083550364536469558561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2264111400486048626078081 1698083550364536469558561)
          ·
            refine ⟨1273562662773402352168921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1698083550364536469558561 1273562662773402352168921)
            ·
              refine ⟨955171997080051764126691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1273562662773402352168921 955171997080051764126691)
              ·
                refine ⟨1432757995620077646190037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 955171997080051764126691 1432757995620077646190037)
                ·
                  refine ⟨33580265522345569832579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1432757995620077646190037 33580265522345569832579)
                  ·
                    rfl

theorem cell21_147144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 2, 1, 7].length) (baseStart_147144 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_147144 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_147144 prefixEnd_147144 := by exact prefixLift 147144
  have htrace : WordTrace (prefixWord ++ tailWord_147144) baseStart_147144 baseEnd_147144 := by
    simpa [prefixWord, tailWord_147144, baseEnd_147144] using wordTrace_append hprefix tailTrace_147144
  have hstable : (prefixWord ++ tailWord_147144).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_147144).length < 2 ^ (prefixWord ++ tailWord_147144).sum := by decide
  have hdescent : baseEnd_147144 < baseStart_147144 := by decide
  rcases family_descends (prefixWord ++ tailWord_147144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_147237 : List Nat := [1, 3, 1, 2, 3, 3, 2, 1, 5]
def baseStart_147237 : Nat := 118140960795 + 147237 * 2 ^ 59
def prefixEnd_147237 : Nat := 4983230072969 + 3 ^ 40 * 147237 * 2
def baseEnd_147237 : Nat := 33601489389398074782389

theorem tailTrace_147237 : CollatzResearch.WordTrace tailWord_147237 prefixEnd_147237 33601489389398074782389 := by
  unfold tailWord_147237
  simp only [CollatzResearch.WordTrace]
  refine ⟨5370174567592969922727965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3580116378395313281818643 5370174567592969922727965)
  ·
    refine ⟨2013815462847363721022987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5370174567592969922727965 2013815462847363721022987)
    ·
      refine ⟨3020723194271045581534481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2013815462847363721022987 3020723194271045581534481)
      ·
        refine ⟨2265542395703284186150861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3020723194271045581534481 2265542395703284186150861)
        ·
          refine ⟨849578398388731569806573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2265542395703284186150861 849578398388731569806573)
          ·
            refine ⟨318591899395774338677465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 849578398388731569806573 318591899395774338677465)
            ·
              refine ⟨238943924546830754008099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 318591899395774338677465 238943924546830754008099)
              ·
                refine ⟨358415886820246131012149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 238943924546830754008099 358415886820246131012149)
                ·
                  refine ⟨33601489389398074782389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 358415886820246131012149 33601489389398074782389)
                  ·
                    rfl

theorem cell21_147237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 3, 2, 1, 5].length) (baseStart_147237 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_147237 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_147237 prefixEnd_147237 := by exact prefixLift 147237
  have htrace : WordTrace (prefixWord ++ tailWord_147237) baseStart_147237 baseEnd_147237 := by
    simpa [prefixWord, tailWord_147237, baseEnd_147237] using wordTrace_append hprefix tailTrace_147237
  have hstable : (prefixWord ++ tailWord_147237).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_147237).length < 2 ^ (prefixWord ++ tailWord_147237).sum := by decide
  have hdescent : baseEnd_147237 < baseStart_147237 := by decide
  rcases family_descends (prefixWord ++ tailWord_147237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_147254 : List Nat := [5, 1, 2, 2, 1, 1, 2, 2, 5]
def baseStart_147254 : Nat := 118140960795 + 147254 * 2 ^ 59
def prefixEnd_147254 : Nat := 4983230072969 + 3 ^ 40 * 147254 * 2
def baseEnd_147254 : Nat := 33605369021009822999021

theorem tailTrace_147254 : CollatzResearch.WordTrace tailWord_147254 prefixEnd_147254 33605369021009822999021 := by
  unfold tailWord_147254
  simp only [CollatzResearch.WordTrace]
  refine ⟨335674663033211364131051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 3580529739020921217397877 335674663033211364131051)
  ·
    refine ⟨503511994549817046196577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 335674663033211364131051 503511994549817046196577)
    ·
      refine ⟨377633995912362784647433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 503511994549817046196577 377633995912362784647433)
      ·
        refine ⟨283225496934272088485575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 377633995912362784647433 283225496934272088485575)
        ·
          refine ⟨424838245401408132728363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 283225496934272088485575 424838245401408132728363)
          ·
            refine ⟨637257368102112199092545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 424838245401408132728363 637257368102112199092545)
            ·
              refine ⟨477943026076584149319409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 637257368102112199092545 477943026076584149319409)
              ·
                refine ⟨358457269557438111989557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 477943026076584149319409 358457269557438111989557)
                ·
                  refine ⟨33605369021009822999021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 358457269557438111989557 33605369021009822999021)
                  ·
                    rfl

theorem cell21_147254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 2, 2, 5].length) (baseStart_147254 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_147254 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_147254 prefixEnd_147254 := by exact prefixLift 147254
  have htrace : WordTrace (prefixWord ++ tailWord_147254) baseStart_147254 baseEnd_147254 := by
    simpa [prefixWord, tailWord_147254, baseEnd_147254] using wordTrace_append hprefix tailTrace_147254
  have hstable : (prefixWord ++ tailWord_147254).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_147254).length < 2 ^ (prefixWord ++ tailWord_147254).sum := by decide
  have hdescent : baseEnd_147254 < baseStart_147254 := by decide
  rcases family_descends (prefixWord ++ tailWord_147254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_147257 : List Nat := [1, 2, 1, 7, 2, 1, 2, 5]
def baseStart_147257 : Nat := 118140960795 + 147257 * 2 ^ 59
def prefixEnd_147257 : Nat := 4983230072969 + 3 ^ 40 * 147257 * 2
def baseEnd_147257 : Nat := 11202017887294161483005

theorem tailTrace_147257 : CollatzResearch.WordTrace tailWord_147257 prefixEnd_147257 11202017887294161483005 := by
  unfold tailWord_147257
  simp only [CollatzResearch.WordTrace]
  refine ⟨5370904027520513338456025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3580602685013675558970683 5370904027520513338456025)
  ·
    refine ⟨4028178020640385003842019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5370904027520513338456025 4028178020640385003842019)
    ·
      refine ⟨6042267030960577505763029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4028178020640385003842019 6042267030960577505763029)
      ·
        refine ⟨141615633538138535291321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 6042267030960577505763029 141615633538138535291321)
        ·
          refine ⟨106211725153603901468491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 141615633538138535291321 106211725153603901468491)
          ·
            refine ⟨159317587730405852202737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 106211725153603901468491 159317587730405852202737)
            ·
              refine ⟨119488190797804389152053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 159317587730405852202737 119488190797804389152053)
              ·
                refine ⟨11202017887294161483005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 119488190797804389152053 11202017887294161483005)
                ·
                  rfl

theorem cell21_147257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 2, 1, 2, 5].length) (baseStart_147257 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_147257 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_147257 prefixEnd_147257 := by exact prefixLift 147257
  have htrace : WordTrace (prefixWord ++ tailWord_147257) baseStart_147257 baseEnd_147257 := by
    simpa [prefixWord, tailWord_147257, baseEnd_147257] using wordTrace_append hprefix tailTrace_147257
  have hstable : (prefixWord ++ tailWord_147257).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_147257).length < 2 ^ (prefixWord ++ tailWord_147257).sum := by decide
  have hdescent : baseEnd_147257 < baseStart_147257 := by decide
  rcases family_descends (prefixWord ++ tailWord_147257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_147282 : List Nat := [3, 2, 2, 1, 1, 5, 7]
def baseStart_147282 : Nat := 118140960795 + 147282 * 2 ^ 59
def prefixEnd_147282 : Nat := 4983230072969 + 3 ^ 40 * 147282 * 2
def baseEnd_147282 : Nat := 3734639889165332948033

theorem tailTrace_147282 : CollatzResearch.WordTrace tailWord_147282 prefixEnd_147282 3734639889165332948033 := by
  unfold tailWord_147282
  simp only [CollatzResearch.WordTrace]
  refine ⟨1342953963107485652029025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3581210568286628405410733 1342953963107485652029025)
  ·
    refine ⟨1007215472330614239021769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1342953963107485652029025 1007215472330614239021769)
    ·
      refine ⟨755411604247960679266327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1007215472330614239021769 755411604247960679266327)
      ·
        refine ⟨1133117406371941018899491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 755411604247960679266327 1133117406371941018899491)
        ·
          refine ⟨1699676109557911528349237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1133117406371941018899491 1699676109557911528349237)
          ·
            refine ⟨159344635271054205782741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1699676109557911528349237 159344635271054205782741)
            ·
              refine ⟨3734639889165332948033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 159344635271054205782741 3734639889165332948033)
              ·
                rfl

theorem cell21_147282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 5, 7].length) (baseStart_147282 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_147282 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_147282 prefixEnd_147282 := by exact prefixLift 147282
  have htrace : WordTrace (prefixWord ++ tailWord_147282) baseStart_147282 baseEnd_147282 := by
    simpa [prefixWord, tailWord_147282, baseEnd_147282] using wordTrace_append hprefix tailTrace_147282
  have hstable : (prefixWord ++ tailWord_147282).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_147282).length < 2 ^ (prefixWord ++ tailWord_147282).sum := by decide
  have hdescent : baseEnd_147282 < baseStart_147282 := by decide
  rcases family_descends (prefixWord ++ tailWord_147282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_147350 : List Nat := [5, 3, 1, 1, 3, 1, 1, 6]
def baseStart_147350 : Nat := 118140960795 + 147350 * 2 ^ 59
def prefixEnd_147350 : Nat := 4983230072969 + 3 ^ 40 * 147350 * 2
def baseEnd_147350 : Nat := 11209092509644996466275

theorem tailTrace_147350 : CollatzResearch.WordTrace tailWord_147350 prefixEnd_147350 11209092509644996466275 := by
  unfold tailWord_147350
  simp only [CollatzResearch.WordTrace]
  refine ⟨335893501011474388849469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 3582864010789060147727669 335893501011474388849469)
  ·
    refine ⟨125960062879302895818551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 335893501011474388849469 125960062879302895818551)
    ·
      refine ⟨188940094318954343727827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 125960062879302895818551 188940094318954343727827)
      ·
        refine ⟨283410141478431515591741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 188940094318954343727827 283410141478431515591741)
        ·
          refine ⟨106278803054411818346903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 283410141478431515591741 106278803054411818346903)
          ·
            refine ⟨159418204581617727520355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 106278803054411818346903 159418204581617727520355)
            ·
              refine ⟨239127306872426591280533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 159418204581617727520355 239127306872426591280533)
              ·
                refine ⟨11209092509644996466275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 239127306872426591280533 11209092509644996466275)
                ·
                  rfl

theorem cell21_147350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 3, 1, 1, 6].length) (baseStart_147350 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_147350 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_147350 prefixEnd_147350 := by exact prefixLift 147350
  have htrace : WordTrace (prefixWord ++ tailWord_147350) baseStart_147350 baseEnd_147350 := by
    simpa [prefixWord, tailWord_147350, baseEnd_147350] using wordTrace_append hprefix tailTrace_147350
  have hstable : (prefixWord ++ tailWord_147350).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_147350).length < 2 ^ (prefixWord ++ tailWord_147350).sum := by decide
  have hdescent : baseEnd_147350 < baseStart_147350 := by decide
  rcases family_descends (prefixWord ++ tailWord_147350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_147493 : List Nat := [1, 3, 1, 2, 2, 3, 2, 7]
def baseStart_147493 : Nat := 118140960795 + 147493 * 2 ^ 59
def prefixEnd_147493 : Nat := 4983230072969 + 3 ^ 40 * 147493 * 2
def baseEnd_147493 : Nat := 11219970692399506171733

theorem tailTrace_147493 : CollatzResearch.WordTrace tailWord_147493 prefixEnd_147493 11219970692399506171733 := by
  unfold tailWord_147493
  simp only [CollatzResearch.WordTrace]
  refine ⟨5379511654665525644047133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3586341103110350429364755 5379511654665525644047133)
  ·
    refine ⟨2017316870499572116517675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5379511654665525644047133 2017316870499572116517675)
    ·
      refine ⟨3025975305749358174776513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2017316870499572116517675 3025975305749358174776513)
      ·
        refine ⟨2269481479312018631082385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3025975305749358174776513 2269481479312018631082385)
        ·
          refine ⟨1702111109484013973311789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2269481479312018631082385 1702111109484013973311789)
          ·
            refine ⟨638291666056505239991921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1702111109484013973311789 638291666056505239991921)
            ·
              refine ⟨478718749542378929993941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 638291666056505239991921 478718749542378929993941)
              ·
                refine ⟨11219970692399506171733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 478718749542378929993941 11219970692399506171733)
                ·
                  rfl

theorem cell21_147493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 2, 7].length) (baseStart_147493 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_147493 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_147493 prefixEnd_147493 := by exact prefixLift 147493
  have htrace : WordTrace (prefixWord ++ tailWord_147493) baseStart_147493 baseEnd_147493 := by
    simpa [prefixWord, tailWord_147493, baseEnd_147493] using wordTrace_append hprefix tailTrace_147493
  have hstable : (prefixWord ++ tailWord_147493).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_147493).length < 2 ^ (prefixWord ++ tailWord_147493).sum := by decide
  have hdescent : baseEnd_147493 < baseStart_147493 := by decide
  rcases family_descends (prefixWord ++ tailWord_147493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_147634 : List Nat := [3, 2, 1, 1, 1, 3, 5, 2, 3]
def baseStart_147634 : Nat := 118140960795 + 147634 * 2 ^ 59
def prefixEnd_147634 : Nat := 4983230072969 + 3 ^ 40 * 147634 * 2
def baseEnd_147634 : Nat := 33692090198213606664911

theorem tailTrace_147634 : CollatzResearch.WordTrace tailWord_147634 prefixEnd_147634 33692090198213606664911 := by
  unfold tailWord_147634
  simp only [CollatzResearch.WordTrace]
  refine ⟨1346163586788676681232489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3589769564769804483286637 1346163586788676681232489)
  ·
    refine ⟨1009622690091507510924367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1346163586788676681232489 1009622690091507510924367)
    ·
      refine ⟨1514434035137261266386551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1009622690091507510924367 1514434035137261266386551)
      ·
        refine ⟨2271651052705891899579827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1514434035137261266386551 2271651052705891899579827)
        ·
          refine ⟨3407476579058837849369741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2271651052705891899579827 3407476579058837849369741)
          ·
            refine ⟨1277803717147064193513653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3407476579058837849369741 1277803717147064193513653)
            ·
              refine ⟨119794098482537268141905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1277803717147064193513653 119794098482537268141905)
              ·
                refine ⟨89845573861902951106429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 119794098482537268141905 89845573861902951106429)
                ·
                  refine ⟨33692090198213606664911, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 89845573861902951106429 33692090198213606664911)
                  ·
                    rfl

theorem cell21_147634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 5, 2, 3].length) (baseStart_147634 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_147634 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_147634 prefixEnd_147634 := by exact prefixLift 147634
  have htrace : WordTrace (prefixWord ++ tailWord_147634) baseStart_147634 baseEnd_147634 := by
    simpa [prefixWord, tailWord_147634, baseEnd_147634] using wordTrace_append hprefix tailTrace_147634
  have hstable : (prefixWord ++ tailWord_147634).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_147634).length < 2 ^ (prefixWord ++ tailWord_147634).sum := by decide
  have hdescent : baseEnd_147634 < baseStart_147634 := by decide
  rcases family_descends (prefixWord ++ tailWord_147634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_147648 : List Nat := [2, 1, 1, 2, 5, 1, 4, 1, 4]
def baseStart_147648 : Nat := 118140960795 + 147648 * 2 ^ 59
def prefixEnd_147648 : Nat := 4983230072969 + 3 ^ 40 * 147648 * 2
def baseEnd_147648 : Nat := 33695285188952693431549

theorem tailTrace_147648 : CollatzResearch.WordTrace tailWord_147648 prefixEnd_147648 33695285188952693431549 := by
  unfold tailWord_147648
  simp only [CollatzResearch.WordTrace]
  refine ⟨2692582484551993557969799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3590109979402658077293065 2692582484551993557969799)
  ·
    refine ⟨4038873726827990336954699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2692582484551993557969799 4038873726827990336954699)
    ·
      refine ⟨6058310590241985505432049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4038873726827990336954699 6058310590241985505432049)
      ·
        refine ⟨4543732942681489129074037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6058310590241985505432049 4543732942681489129074037)
        ·
          refine ⟨425974963376389605850691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 4543732942681489129074037 425974963376389605850691)
          ·
            refine ⟨638962445064584408776037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 425974963376389605850691 638962445064584408776037)
            ·
              refine ⟨119805458449609576645507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 638962445064584408776037 119805458449609576645507)
              ·
                refine ⟨179708187674414364968261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 119805458449609576645507 179708187674414364968261)
                ·
                  refine ⟨33695285188952693431549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 179708187674414364968261 33695285188952693431549)
                  ·
                    rfl

theorem cell21_147648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 4, 1, 4].length) (baseStart_147648 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_147648 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_147648 prefixEnd_147648 := by exact prefixLift 147648
  have htrace : WordTrace (prefixWord ++ tailWord_147648) baseStart_147648 baseEnd_147648 := by
    simpa [prefixWord, tailWord_147648, baseEnd_147648] using wordTrace_append hprefix tailTrace_147648
  have hstable : (prefixWord ++ tailWord_147648).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_147648).length < 2 ^ (prefixWord ++ tailWord_147648).sum := by decide
  have hdescent : baseEnd_147648 < baseStart_147648 := by decide
  rcases family_descends (prefixWord ++ tailWord_147648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_147659 : List Nat := [1, 1, 1, 1, 3, 2, 4, 1, 7]
def baseStart_147659 : Nat := 118140960795 + 147659 * 2 ^ 59
def prefixEnd_147659 : Nat := 4983230072969 + 3 ^ 40 * 147659 * 2
def baseEnd_147659 : Nat := 33697795538819118748193

theorem tailTrace_147659 : CollatzResearch.WordTrace tailWord_147659 prefixEnd_147659 33697795538819118748193 := by
  unfold tailWord_147659
  simp only [CollatzResearch.WordTrace]
  refine ⟨5385566172064135994590031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3590377448042757329726687 5385566172064135994590031)
  ·
    refine ⟨8078349258096203991885047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5385566172064135994590031 8078349258096203991885047)
    ·
      refine ⟨12117523887144305987827571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8078349258096203991885047 12117523887144305987827571)
      ·
        refine ⟨18176285830716458981741357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12117523887144305987827571 18176285830716458981741357)
        ·
          refine ⟨6816107186518672118153009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18176285830716458981741357 6816107186518672118153009)
          ·
            refine ⟨5112080389889004088614757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6816107186518672118153009 5112080389889004088614757)
            ·
              refine ⟨958515073104188266615267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5112080389889004088614757 958515073104188266615267)
              ·
                refine ⟨1437772609656282399922901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 958515073104188266615267 1437772609656282399922901)
                ·
                  refine ⟨33697795538819118748193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1437772609656282399922901 33697795538819118748193)
                  ·
                    rfl

theorem cell21_147659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 4, 1, 7].length) (baseStart_147659 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_147659 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_147659 prefixEnd_147659 := by exact prefixLift 147659
  have htrace : WordTrace (prefixWord ++ tailWord_147659) baseStart_147659 baseEnd_147659 := by
    simpa [prefixWord, tailWord_147659, baseEnd_147659] using wordTrace_append hprefix tailTrace_147659
  have hstable : (prefixWord ++ tailWord_147659).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_147659).length < 2 ^ (prefixWord ++ tailWord_147659).sum := by decide
  have hdescent : baseEnd_147659 < baseStart_147659 := by decide
  rcases family_descends (prefixWord ++ tailWord_147659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_147741 : List Nat := [1, 4, 2, 3, 2, 2, 1, 2, 4]
def baseStart_147741 : Nat := 118140960795 + 147741 * 2 ^ 59
def prefixEnd_147741 : Nat := 4983230072969 + 3 ^ 40 * 147741 * 2
def baseEnd_147741 : Nat := 33716509056005198381359

theorem tailTrace_147741 : CollatzResearch.WordTrace tailWord_147741 prefixEnd_147741 33716509056005198381359 := by
  unfold tailWord_147741
  simp only [CollatzResearch.WordTrace]
  refine ⟨5388556957767063999075077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3592371305178042666050051 5388556957767063999075077)
  ·
    refine ⟨1010354429581324499826577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5388556957767063999075077 1010354429581324499826577)
    ·
      refine ⟨757765822185993374869933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1010354429581324499826577 757765822185993374869933)
      ·
        refine ⟨284162183319747515576225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 757765822185993374869933 284162183319747515576225)
        ·
          refine ⟨213121637489810636682169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 284162183319747515576225 213121637489810636682169)
          ·
            refine ⟨159841228117357977511627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 213121637489810636682169 159841228117357977511627)
            ·
              refine ⟨239761842176036966267441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 159841228117357977511627 239761842176036966267441)
              ·
                refine ⟨179821381632027724700581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 239761842176036966267441 179821381632027724700581)
                ·
                  refine ⟨33716509056005198381359, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 179821381632027724700581 33716509056005198381359)
                  ·
                    rfl

theorem cell21_147741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 2, 1, 2, 4].length) (baseStart_147741 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_147741 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_147741 prefixEnd_147741 := by exact prefixLift 147741
  have htrace : WordTrace (prefixWord ++ tailWord_147741) baseStart_147741 baseEnd_147741 := by
    simpa [prefixWord, tailWord_147741, baseEnd_147741] using wordTrace_append hprefix tailTrace_147741
  have hstable : (prefixWord ++ tailWord_147741).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_147741).length < 2 ^ (prefixWord ++ tailWord_147741).sum := by decide
  have hdescent : baseEnd_147741 < baseStart_147741 := by decide
  rcases family_descends (prefixWord ++ tailWord_147741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_147758 : List Nat := [4, 1, 3, 3, 1, 1, 3, 1, 4]
def baseStart_147758 : Nat := 118140960795 + 147758 * 2 ^ 59
def prefixEnd_147758 : Nat := 4983230072969 + 3 ^ 40 * 147758 * 2
def baseEnd_147758 : Nat := 33720388687616946597991

theorem tailTrace_147758 : CollatzResearch.WordTrace tailWord_147758 prefixEnd_147758 33720388687616946597991 := by
  unfold tailWord_147758
  simp only [CollatzResearch.WordTrace]
  refine ⟨673647124838184487805491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3592784665803650601629285 673647124838184487805491)
  ·
    refine ⟨1010470687257276731708237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 673647124838184487805491 1010470687257276731708237)
    ·
      refine ⟨378926507721478774390589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1010470687257276731708237 378926507721478774390589)
      ·
        refine ⟨142097440395554540396471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 378926507721478774390589 142097440395554540396471)
        ·
          refine ⟨213146160593331810594707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 142097440395554540396471 213146160593331810594707)
          ·
            refine ⟨319719240889997715892061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 213146160593331810594707 319719240889997715892061)
            ·
              refine ⟨119894715333749143459523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 319719240889997715892061 119894715333749143459523)
              ·
                refine ⟨179842073000623715189285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 119894715333749143459523 179842073000623715189285)
                ·
                  refine ⟨33720388687616946597991, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 179842073000623715189285 33720388687616946597991)
                  ·
                    rfl

theorem cell21_147758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 1, 3, 1, 4].length) (baseStart_147758 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_147758 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_147758 prefixEnd_147758 := by exact prefixLift 147758
  have htrace : WordTrace (prefixWord ++ tailWord_147758) baseStart_147758 baseEnd_147758 := by
    simpa [prefixWord, tailWord_147758, baseEnd_147758] using wordTrace_append hprefix tailTrace_147758
  have hstable : (prefixWord ++ tailWord_147758).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_147758).length < 2 ^ (prefixWord ++ tailWord_147758).sum := by decide
  have hdescent : baseEnd_147758 < baseStart_147758 := by decide
  rcases family_descends (prefixWord ++ tailWord_147758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_147980 : List Nat := [2, 2, 1, 2, 4, 1, 3, 1, 5]
def baseStart_147980 : Nat := 118140960795 + 147980 * 2 ^ 59
def prefixEnd_147980 : Nat := 4983230072969 + 3 ^ 40 * 147980 * 2
def baseEnd_147980 : Nat := 33771052112193893897537

theorem tailTrace_147980 : CollatzResearch.WordTrace tailWord_147980 prefixEnd_147980 33771052112193893897537 := by
  unfold tailWord_147980
  simp only [CollatzResearch.WordTrace]
  refine ⟨2698637001950603908512697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3598182669267471878016929 2698637001950603908512697)
  ·
    refine ⟨2023977751462952931384523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2698637001950603908512697 2023977751462952931384523)
    ·
      refine ⟨3035966627194429397076785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2023977751462952931384523 3035966627194429397076785)
      ·
        refine ⟨2276974970395822047807589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3035966627194429397076785 2276974970395822047807589)
        ·
          refine ⟨426932806949216633963923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2276974970395822047807589 426932806949216633963923)
          ·
            refine ⟨640399210423824950945885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 426932806949216633963923 640399210423824950945885)
            ·
              refine ⟨240149703908934356604707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 640399210423824950945885 240149703908934356604707)
              ·
                refine ⟨360224555863401534907061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 240149703908934356604707 360224555863401534907061)
                ·
                  refine ⟨33771052112193893897537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 360224555863401534907061 33771052112193893897537)
                  ·
                    rfl

theorem cell21_147980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 3, 1, 5].length) (baseStart_147980 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_147980 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_147980 prefixEnd_147980 := by exact prefixLift 147980
  have htrace : WordTrace (prefixWord ++ tailWord_147980) baseStart_147980 baseEnd_147980 := by
    simpa [prefixWord, tailWord_147980, baseEnd_147980] using wordTrace_append hprefix tailTrace_147980
  have hstable : (prefixWord ++ tailWord_147980).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_147980).length < 2 ^ (prefixWord ++ tailWord_147980).sum := by decide
  have hdescent : baseEnd_147980 < baseStart_147980 := by decide
  rcases family_descends (prefixWord ++ tailWord_147980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_148135 : List Nat := [1, 1, 6, 3, 2, 1, 7]
def baseStart_148135 : Nat := 118140960795 + 148135 * 2 ^ 59
def prefixEnd_148135 : Nat := 4983230072969 + 3 ^ 40 * 148135 * 2
def baseEnd_148135 : Nat := 3756269469327563201543

theorem tailTrace_148135 : CollatzResearch.WordTrace tailWord_148135 prefixEnd_148135 3756269469327563201543 := by
  unfold tailWord_148135
  simp only [CollatzResearch.WordTrace]
  refine ⟨5402927318339669288917859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3601951545559779525945239 5402927318339669288917859)
  ·
    refine ⟨8104390977509503933376789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5402927318339669288917859 8104390977509503933376789)
    ·
      refine ⟨379893327070757996877037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 8104390977509503933376789 379893327070757996877037)
      ·
        refine ⟨142459997651534248828889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 379893327070757996877037 142459997651534248828889)
        ·
          refine ⟨106844998238650686621667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 142459997651534248828889 106844998238650686621667)
          ·
            refine ⟨160267497357976029932501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 106844998238650686621667 160267497357976029932501)
            ·
              refine ⟨3756269469327563201543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 160267497357976029932501 3756269469327563201543)
              ·
                rfl

theorem cell21_148135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 2, 1, 7].length) (baseStart_148135 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_148135 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_148135 prefixEnd_148135 := by exact prefixLift 148135
  have htrace : WordTrace (prefixWord ++ tailWord_148135) baseStart_148135 baseEnd_148135 := by
    simpa [prefixWord, tailWord_148135, baseEnd_148135] using wordTrace_append hprefix tailTrace_148135
  have hstable : (prefixWord ++ tailWord_148135).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_148135).length < 2 ^ (prefixWord ++ tailWord_148135).sum := by decide
  have hdescent : baseEnd_148135 < baseStart_148135 := by decide
  rcases family_descends (prefixWord ++ tailWord_148135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_148146 : List Nat := [3, 2, 1, 1, 1, 2, 1, 6, 4]
def baseStart_148146 : Nat := 118140960795 + 148146 * 2 ^ 59
def prefixEnd_148146 : Nat := 4983230072969 + 3 ^ 40 * 148146 * 2
def baseEnd_148146 : Nat := 33808935573814494130531

theorem tailTrace_148146 : CollatzResearch.WordTrace tailWord_148146 prefixEnd_148146 33808935573814494130531 := by
  unfold tailWord_148146
  simp only [CollatzResearch.WordTrace]
  refine ⟨1350832130324954541892073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3602219014199878778378861 1350832130324954541892073)
  ·
    refine ⟨1013124097743715906419055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1350832130324954541892073 1013124097743715906419055)
    ·
      refine ⟨1519686146615573859628583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1013124097743715906419055 1519686146615573859628583)
      ·
        refine ⟨2279529219923360789442875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1519686146615573859628583 2279529219923360789442875)
        ·
          refine ⟨3419293829885041184164313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2279529219923360789442875 3419293829885041184164313)
          ·
            refine ⟨2564470372413780888123235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3419293829885041184164313 2564470372413780888123235)
            ·
              refine ⟨3846705558620671332184853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2564470372413780888123235 3846705558620671332184853)
              ·
                refine ⟨180314323060343968696165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3846705558620671332184853 180314323060343968696165)
                ·
                  refine ⟨33808935573814494130531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 180314323060343968696165 33808935573814494130531)
                  ·
                    rfl

theorem cell21_148146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 6, 4].length) (baseStart_148146 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_148146 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_148146 prefixEnd_148146 := by exact prefixLift 148146
  have htrace : WordTrace (prefixWord ++ tailWord_148146) baseStart_148146 baseEnd_148146 := by
    simpa [prefixWord, tailWord_148146, baseEnd_148146] using wordTrace_append hprefix tailTrace_148146
  have hstable : (prefixWord ++ tailWord_148146).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_148146).length < 2 ^ (prefixWord ++ tailWord_148146).sum := by decide
  have hdescent : baseEnd_148146 < baseStart_148146 := by decide
  rcases family_descends (prefixWord ++ tailWord_148146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_148149 : List Nat := [1, 3, 3, 3, 1, 3, 1, 1, 5]
def baseStart_148149 : Nat := 118140960795 + 148149 * 2 ^ 59
def prefixEnd_148149 : Nat := 4983230072969 + 3 ^ 40 * 148149 * 2
def baseEnd_148149 : Nat := 33809620214687155580525

theorem tailTrace_148149 : CollatzResearch.WordTrace tailWord_148149 prefixEnd_148149 33809620214687155580525 := by
  unfold tailWord_148149
  simp only [CollatzResearch.WordTrace]
  refine ⟨5403437940288949679927501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3602291960192633119951667 5403437940288949679927501)
  ·
    refine ⟨2026289227608356129972813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5403437940288949679927501 2026289227608356129972813)
    ·
      refine ⟨759858460353133548739805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2026289227608356129972813 759858460353133548739805)
      ·
        refine ⟨284946922632425080777427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 759858460353133548739805 284946922632425080777427)
        ·
          refine ⟨427420383948637621166141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 284946922632425080777427 427420383948637621166141)
          ·
            refine ⟨160282643980739107937303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 427420383948637621166141 160282643980739107937303)
            ·
              refine ⟨240423965971108661905955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 160282643980739107937303 240423965971108661905955)
              ·
                refine ⟨360635948956662992858933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 240423965971108661905955 360635948956662992858933)
                ·
                  refine ⟨33809620214687155580525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 360635948956662992858933 33809620214687155580525)
                  ·
                    rfl

theorem cell21_148149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 3, 1, 1, 5].length) (baseStart_148149 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_148149 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_148149 prefixEnd_148149 := by exact prefixLift 148149
  have htrace : WordTrace (prefixWord ++ tailWord_148149) baseStart_148149 baseEnd_148149 := by
    simpa [prefixWord, tailWord_148149, baseEnd_148149] using wordTrace_append hprefix tailTrace_148149
  have hstable : (prefixWord ++ tailWord_148149).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_148149).length < 2 ^ (prefixWord ++ tailWord_148149).sum := by decide
  have hdescent : baseEnd_148149 < baseStart_148149 := by decide
  rcases family_descends (prefixWord ++ tailWord_148149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_148160 : List Nat := [2, 1, 1, 2, 4, 2, 1, 8]
def baseStart_148160 : Nat := 118140960795 + 148160 * 2 ^ 59
def prefixEnd_148160 : Nat := 4983230072969 + 3 ^ 40 * 148160 * 2
def baseEnd_148160 : Nat := 11270710188184526965723

theorem tailTrace_148160 : CollatzResearch.WordTrace tailWord_148160 prefixEnd_148160 11270710188184526965723 := by
  unfold tailWord_148160
  simp only [CollatzResearch.WordTrace]
  refine ⟨2701919571624549279288967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3602559428832732372385289 2701919571624549279288967)
  ·
    refine ⟨4052879357436823918933451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2701919571624549279288967 4052879357436823918933451)
    ·
      refine ⟨6079319036155235878400177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4052879357436823918933451 6079319036155235878400177)
      ·
        refine ⟨4559489277116426908800133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6079319036155235878400177 4559489277116426908800133)
        ·
          refine ⟨854904239459330045400025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4559489277116426908800133 854904239459330045400025)
          ·
            refine ⟨641178179594497534050019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 854904239459330045400025 641178179594497534050019)
            ·
              refine ⟨961767269391746301075029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 641178179594497534050019 961767269391746301075029)
              ·
                refine ⟨11270710188184526965723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 961767269391746301075029 11270710188184526965723)
                ·
                  rfl

theorem cell21_148160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 1, 8].length) (baseStart_148160 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_148160 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_148160 prefixEnd_148160 := by exact prefixLift 148160
  have htrace : WordTrace (prefixWord ++ tailWord_148160) baseStart_148160 baseEnd_148160 := by
    simpa [prefixWord, tailWord_148160, baseEnd_148160] using wordTrace_append hprefix tailTrace_148160
  have hstable : (prefixWord ++ tailWord_148160).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_148160).length < 2 ^ (prefixWord ++ tailWord_148160).sum := by decide
  have hdescent : baseEnd_148160 < baseStart_148160 := by decide
  rcases family_descends (prefixWord ++ tailWord_148160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_148208 : List Nat := [2, 1, 1, 1, 3, 1, 5, 4, 3]
def baseStart_148208 : Nat := 118140960795 + 148208 * 2 ^ 59
def prefixEnd_148208 : Nat := 4983230072969 + 3 ^ 40 * 148208 * 2
def baseEnd_148208 : Nat := 33823084818516164097071

theorem tailTrace_148208 : CollatzResearch.WordTrace tailWord_148208 prefixEnd_148208 33823084818516164097071 := by
  unfold tailWord_148208
  simp only [CollatzResearch.WordTrace]
  refine ⟨2702794923537601378162639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3603726564716801837550185 2702794923537601378162639)
  ·
    refine ⟨4054192385306402067243959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2702794923537601378162639 4054192385306402067243959)
    ·
      refine ⟨6081288577959603100865939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4054192385306402067243959 6081288577959603100865939)
      ·
        refine ⟨9121932866939404651298909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6081288577959603100865939 9121932866939404651298909)
        ·
          refine ⟨3420724825102276744237091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9121932866939404651298909 3420724825102276744237091)
          ·
            refine ⟨5131087237653415116355637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3420724825102276744237091 5131087237653415116355637)
            ·
              refine ⟨481039428530007667158341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 5131087237653415116355637 481039428530007667158341)
              ·
                refine ⟨90194892849376437592189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 481039428530007667158341 90194892849376437592189)
                ·
                  refine ⟨33823084818516164097071, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 90194892849376437592189 33823084818516164097071)
                  ·
                    rfl

theorem cell21_148208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 5, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 5, 4, 3].length) (baseStart_148208 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_148208 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_148208 prefixEnd_148208 := by exact prefixLift 148208
  have htrace : WordTrace (prefixWord ++ tailWord_148208) baseStart_148208 baseEnd_148208 := by
    simpa [prefixWord, tailWord_148208, baseEnd_148208] using wordTrace_append hprefix tailTrace_148208
  have hstable : (prefixWord ++ tailWord_148208).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_148208).length < 2 ^ (prefixWord ++ tailWord_148208).sum := by decide
  have hdescent : baseEnd_148208 < baseStart_148208 := by decide
  rcases family_descends (prefixWord ++ tailWord_148208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_148405 : List Nat := [1, 3, 3, 2, 1, 1, 5, 5]
def baseStart_148405 : Nat := 118140960795 + 148405 * 2 ^ 59
def prefixEnd_148405 : Nat := 4983230072969 + 3 ^ 40 * 148405 * 2
def baseEnd_148405 : Nat := 11289347634162533104445

theorem tailTrace_148405 : CollatzResearch.WordTrace tailWord_148405 prefixEnd_148405 11289347634162533104445 := by
  unfold tailWord_148405
  simp only [CollatzResearch.WordTrace]
  refine ⟨5412775027361505401246669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3608516684907670267497779 5412775027361505401246669)
  ·
    refine ⟨2029790635260564525467501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5412775027361505401246669 2029790635260564525467501)
    ·
      refine ⟨761171488222711697050313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2029790635260564525467501 761171488222711697050313)
      ·
        refine ⟨570878616167033772787735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 761171488222711697050313 570878616167033772787735)
        ·
          refine ⟨856317924250550659181603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 570878616167033772787735 856317924250550659181603)
          ·
            refine ⟨1284476886375825988772405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 856317924250550659181603 1284476886375825988772405)
            ·
              refine ⟨120419708097733686447413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1284476886375825988772405 120419708097733686447413)
              ·
                refine ⟨11289347634162533104445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 120419708097733686447413 11289347634162533104445)
                ·
                  rfl

theorem cell21_148405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 5, 5].length) (baseStart_148405 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_148405 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_148405 prefixEnd_148405 := by exact prefixLift 148405
  have htrace : WordTrace (prefixWord ++ tailWord_148405) baseStart_148405 baseEnd_148405 := by
    simpa [prefixWord, tailWord_148405, baseEnd_148405] using wordTrace_append hprefix tailTrace_148405
  have hstable : (prefixWord ++ tailWord_148405).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_148405).length < 2 ^ (prefixWord ++ tailWord_148405).sum := by decide
  have hdescent : baseEnd_148405 < baseStart_148405 := by decide
  rcases family_descends (prefixWord ++ tailWord_148405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_148433 : List Nat := [1, 2, 2, 1, 2, 1, 5, 1, 6]
def baseStart_148433 : Nat := 118140960795 + 148433 * 2 ^ 59
def prefixEnd_148433 : Nat := 4983230072969 + 3 ^ 40 * 148433 * 2
def baseEnd_148433 : Nat := 33874432883965772846611

theorem tailTrace_148433 : CollatzResearch.WordTrace tailWord_148433 prefixEnd_148433 33874432883965772846611 := by
  unfold tailWord_148433
  simp only [CollatzResearch.WordTrace]
  refine ⟨5413796271260066183265953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3609197514173377455510635 5413796271260066183265953)
  ·
    refine ⟨4060347203445049637449465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5413796271260066183265953 4060347203445049637449465)
    ·
      refine ⟨3045260402583787228087099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4060347203445049637449465 3045260402583787228087099)
      ·
        refine ⟨4567890603875680842130649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3045260402583787228087099 4567890603875680842130649)
        ·
          refine ⟨3425917952906760631597987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4567890603875680842130649 3425917952906760631597987)
          ·
            refine ⟨5138876929360140947396981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3425917952906760631597987 5138876929360140947396981)
            ·
              refine ⟨481769712127513213818467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 5138876929360140947396981 481769712127513213818467)
              ·
                refine ⟨722654568191269820727701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 481769712127513213818467 722654568191269820727701)
                ·
                  refine ⟨33874432883965772846611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 722654568191269820727701 33874432883965772846611)
                  ·
                    rfl

theorem cell21_148433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 5, 1, 6].length) (baseStart_148433 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_148433 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_148433 prefixEnd_148433 := by exact prefixLift 148433
  have htrace : WordTrace (prefixWord ++ tailWord_148433) baseStart_148433 baseEnd_148433 := by
    simpa [prefixWord, tailWord_148433, baseEnd_148433] using wordTrace_append hprefix tailTrace_148433
  have hstable : (prefixWord ++ tailWord_148433).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_148433).length < 2 ^ (prefixWord ++ tailWord_148433).sum := by decide
  have hdescent : baseEnd_148433 < baseStart_148433 := by decide
  rcases family_descends (prefixWord ++ tailWord_148433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_148436 : List Nat := [2, 4, 1, 2, 1, 3, 2, 1, 5]
def baseStart_148436 : Nat := 118140960795 + 148436 * 2 ^ 59
def prefixEnd_148436 : Nat := 4983230072969 + 3 ^ 40 * 148436 * 2
def baseEnd_148436 : Nat := 33875117524838434296605

theorem tailTrace_148436 : CollatzResearch.WordTrace tailWord_148436 prefixEnd_148436 33875117524838434296605 := by
  unfold tailWord_148436
  simp only [CollatzResearch.WordTrace]
  refine ⟨2706952845124598847812581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3609270460166131797083441 2706952845124598847812581)
  ·
    refine ⟨507553658460862283964859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2706952845124598847812581 507553658460862283964859)
    ·
      refine ⟨761330487691293425947289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 507553658460862283964859 761330487691293425947289)
      ·
        refine ⟨570997865768470069460467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 761330487691293425947289 570997865768470069460467)
        ·
          refine ⟨856496798652705104190701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 570997865768470069460467 856496798652705104190701)
          ·
            refine ⟨321186299494764414071513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 856496798652705104190701 321186299494764414071513)
            ·
              refine ⟨240889724621073310553635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 321186299494764414071513 240889724621073310553635)
              ·
                refine ⟨361334586931609965830453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 240889724621073310553635 361334586931609965830453)
                ·
                  refine ⟨33875117524838434296605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 361334586931609965830453 33875117524838434296605)
                  ·
                    rfl

theorem cell21_148436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 3, 2, 1, 5].length) (baseStart_148436 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_148436 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_148436 prefixEnd_148436 := by exact prefixLift 148436
  have htrace : WordTrace (prefixWord ++ tailWord_148436) baseStart_148436 baseEnd_148436 := by
    simpa [prefixWord, tailWord_148436, baseEnd_148436] using wordTrace_append hprefix tailTrace_148436
  have hstable : (prefixWord ++ tailWord_148436).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_148436).length < 2 ^ (prefixWord ++ tailWord_148436).sum := by decide
  have hdescent : baseEnd_148436 < baseStart_148436 := by decide
  rcases family_descends (prefixWord ++ tailWord_148436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_148470 : List Nat := [5, 1, 1, 1, 3, 3, 1, 3, 3]
def baseStart_148470 : Nat := 118140960795 + 148470 * 2 ^ 59
def prefixEnd_148470 : Nat := 4983230072969 + 3 ^ 40 * 148470 * 2
def baseEnd_148470 : Nat := 33882876788061930729869

theorem tailTrace_148470 : CollatzResearch.WordTrace tailWord_148470 prefixEnd_148470 33882876788061930729869 := by
  unfold tailWord_148470
  simp only [CollatzResearch.WordTrace]
  refine ⟨338446610757876343897679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 3610097181417347668241909 338446610757876343897679)
  ·
    refine ⟨507669916136814515846519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 338446610757876343897679 507669916136814515846519)
    ·
      refine ⟨761504874205221773769779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 507669916136814515846519 761504874205221773769779)
      ·
        refine ⟨1142257311307832660654669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 761504874205221773769779 1142257311307832660654669)
        ·
          refine ⟨428346491740437247745501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1142257311307832660654669 428346491740437247745501)
          ·
            refine ⟨160629934402663967904563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 428346491740437247745501 160629934402663967904563)
            ·
              refine ⟨240944901603995951856845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 160629934402663967904563 240944901603995951856845)
              ·
                refine ⟨90354338101498481946317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 240944901603995951856845 90354338101498481946317)
                ·
                  refine ⟨33882876788061930729869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 90354338101498481946317 33882876788061930729869)
                  ·
                    rfl

theorem cell21_148470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 3, 1, 3, 3].length) (baseStart_148470 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_148470 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_148470 prefixEnd_148470 := by exact prefixLift 148470
  have htrace : WordTrace (prefixWord ++ tailWord_148470) baseStart_148470 baseEnd_148470 := by
    simpa [prefixWord, tailWord_148470, baseEnd_148470] using wordTrace_append hprefix tailTrace_148470
  have hstable : (prefixWord ++ tailWord_148470).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_148470).length < 2 ^ (prefixWord ++ tailWord_148470).sum := by decide
  have hdescent : baseEnd_148470 < baseStart_148470 := by decide
  rcases family_descends (prefixWord ++ tailWord_148470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_148523 : List Nat := [1, 1, 1, 1, 2, 1, 5, 9]
def baseStart_148523 : Nat := 118140960795 + 148523 * 2 ^ 59
def prefixEnd_148523 : Nat := 4983230072969 + 3 ^ 40 * 148523 * 2
def baseEnd_148523 : Nat := 11298324036715205448809

theorem tailTrace_148523 : CollatzResearch.WordTrace tailWord_148523 prefixEnd_148523 11298324036715205448809 := by
  unfold tailWord_148523
  simp only [CollatzResearch.WordTrace]
  refine ⟨5417078840934011554042223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3611385893956007702694815 5417078840934011554042223)
  ·
    refine ⟨8125618261401017331063335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5417078840934011554042223 8125618261401017331063335)
    ·
      refine ⟨12188427392101525996595003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8125618261401017331063335 12188427392101525996595003)
      ·
        refine ⟨18282641088152288994892505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12188427392101525996595003 18282641088152288994892505)
        ·
          refine ⟨13711980816114216746169379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18282641088152288994892505 13711980816114216746169379)
          ·
            refine ⟨20567971224171325119254069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13711980816114216746169379 20567971224171325119254069)
            ·
              refine ⟨1928247302266061729930069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 20567971224171325119254069 1928247302266061729930069)
              ·
                refine ⟨11298324036715205448809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 1928247302266061729930069 11298324036715205448809)
                ·
                  rfl

theorem cell21_148523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 5, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 5, 9].length) (baseStart_148523 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_148523 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_148523 prefixEnd_148523 := by exact prefixLift 148523
  have htrace : WordTrace (prefixWord ++ tailWord_148523) baseStart_148523 baseEnd_148523 := by
    simpa [prefixWord, tailWord_148523, baseEnd_148523] using wordTrace_append hprefix tailTrace_148523
  have hstable : (prefixWord ++ tailWord_148523).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_148523).length < 2 ^ (prefixWord ++ tailWord_148523).sum := by decide
  have hdescent : baseEnd_148523 < baseStart_148523 := by decide
  rcases family_descends (prefixWord ++ tailWord_148523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_148557 : List Nat := [1, 6, 1, 1, 1, 2, 3, 6]
def baseStart_148557 : Nat := 118140960795 + 148557 * 2 ^ 59
def prefixEnd_148557 : Nat := 4983230072969 + 3 ^ 40 * 148557 * 2
def baseEnd_148557 : Nat := 11300910457789704259897

theorem tailTrace_148557 : CollatzResearch.WordTrace tailWord_148557 prefixEnd_148557 11300910457789704259897 := by
  unfold tailWord_148557
  simp only [CollatzResearch.WordTrace]
  refine ⟨5418318922810835360779925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3612212615207223573853283 5418318922810835360779925)
  ·
    refine ⟨253983699506757907536559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 5418318922810835360779925 253983699506757907536559)
    ·
      refine ⟨380975549260136861304839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 253983699506757907536559 380975549260136861304839)
      ·
        refine ⟨571463323890205291957259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 380975549260136861304839 571463323890205291957259)
        ·
          refine ⟨857194985835307937935889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 571463323890205291957259 857194985835307937935889)
          ·
            refine ⟨642896239376480953451917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 857194985835307937935889 642896239376480953451917)
            ·
              refine ⟨241086089766180357544469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 642896239376480953451917 241086089766180357544469)
              ·
                refine ⟨11300910457789704259897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 241086089766180357544469 11300910457789704259897)
                ·
                  rfl

theorem cell21_148557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 3, 6].length) (baseStart_148557 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_148557 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_148557 prefixEnd_148557 := by exact prefixLift 148557
  have htrace : WordTrace (prefixWord ++ tailWord_148557) baseStart_148557 baseEnd_148557 := by
    simpa [prefixWord, tailWord_148557, baseEnd_148557] using wordTrace_append hprefix tailTrace_148557
  have hstable : (prefixWord ++ tailWord_148557).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_148557).length < 2 ^ (prefixWord ++ tailWord_148557).sum := by decide
  have hdescent : baseEnd_148557 < baseStart_148557 := by decide
  rcases family_descends (prefixWord ++ tailWord_148557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_148588 : List Nat := [2, 2, 1, 1, 3, 2, 4, 3, 3]
def baseStart_148588 : Nat := 118140960795 + 148588 * 2 ^ 59
def prefixEnd_148588 : Nat := 4983230072969 + 3 ^ 40 * 148588 * 2
def baseEnd_148588 : Nat := 33909805995719947762961

theorem tailTrace_148588 : CollatzResearch.WordTrace tailWord_148588 prefixEnd_148588 33909805995719947762961 := by
  unfold tailWord_148588
  simp only [CollatzResearch.WordTrace]
  refine ⟨2709724792849263827579209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3612966390465685103438945 2709724792849263827579209)
  ·
    refine ⟨2032293594636947870684407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2709724792849263827579209 2032293594636947870684407)
    ·
      refine ⟨3048440391955421806026611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2032293594636947870684407 3048440391955421806026611)
      ·
        refine ⟨4572660587933132709039917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3048440391955421806026611 4572660587933132709039917)
        ·
          refine ⟨1714747720474924765889969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4572660587933132709039917 1714747720474924765889969)
          ·
            refine ⟨1286060790356193574417477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1714747720474924765889969 1286060790356193574417477)
            ·
              refine ⟨241136398191786295203277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1286060790356193574417477 241136398191786295203277)
              ·
                refine ⟨90426149321919860701229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 241136398191786295203277 90426149321919860701229)
                ·
                  refine ⟨33909805995719947762961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 90426149321919860701229 33909805995719947762961)
                  ·
                    rfl

theorem cell21_148588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 4, 3, 3].length) (baseStart_148588 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_148588 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_148588 prefixEnd_148588 := by exact prefixLift 148588
  have htrace : WordTrace (prefixWord ++ tailWord_148588) baseStart_148588 baseEnd_148588 := by
    simpa [prefixWord, tailWord_148588, baseEnd_148588] using wordTrace_append hprefix tailTrace_148588
  have hstable : (prefixWord ++ tailWord_148588).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_148588).length < 2 ^ (prefixWord ++ tailWord_148588).sum := by decide
  have hdescent : baseEnd_148588 < baseStart_148588 := by decide
  rcases family_descends (prefixWord ++ tailWord_148588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_148599 : List Nat := [1, 1, 3, 1, 1, 4, 10]
def baseStart_148599 : Nat := 118140960795 + 148599 * 2 ^ 59
def prefixEnd_148599 : Nat := 4983230072969 + 3 ^ 40 * 148599 * 2
def baseEnd_148599 : Nat := 3768035149509597008845

theorem tailTrace_148599 : CollatzResearch.WordTrace tailWord_148599 prefixEnd_148599 3768035149509597008845 := by
  unfold tailWord_148599
  simp only [CollatzResearch.WordTrace]
  refine ⟨5419850788658676533808851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3613233859105784355872567 5419850788658676533808851)
  ·
    refine ⟨8129776182988014800713277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5419850788658676533808851 8129776182988014800713277)
    ·
      refine ⟨3048666068620505550267479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8129776182988014800713277 3048666068620505550267479)
      ·
        refine ⟨4572999102930758325401219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3048666068620505550267479 4572999102930758325401219)
        ·
          refine ⟨6859498654396137488101829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4572999102930758325401219 6859498654396137488101829)
          ·
            refine ⟨1286155997699275779019093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6859498654396137488101829 1286155997699275779019093)
            ·
              refine ⟨3768035149509597008845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 1286155997699275779019093 3768035149509597008845)
              ·
                rfl

theorem cell21_148599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 10].length) (baseStart_148599 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_148599 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_148599 prefixEnd_148599 := by exact prefixLift 148599
  have htrace : WordTrace (prefixWord ++ tailWord_148599) baseStart_148599 baseEnd_148599 := by
    simpa [prefixWord, tailWord_148599, baseEnd_148599] using wordTrace_append hprefix tailTrace_148599
  have hstable : (prefixWord ++ tailWord_148599).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_148599).length < 2 ^ (prefixWord ++ tailWord_148599).sum := by decide
  have hdescent : baseEnd_148599 < baseStart_148599 := by decide
  rcases family_descends (prefixWord ++ tailWord_148599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_148768 : List Nat := [2, 1, 1, 5, 3, 1, 8]
def baseStart_148768 : Nat := 118140960795 + 148768 * 2 ^ 59
def prefixEnd_148768 : Nat := 4983230072969 + 3 ^ 40 * 148768 * 2
def baseEnd_148768 : Nat := 3772320494231070529177

theorem tailTrace_148768 : CollatzResearch.WordTrace tailWord_148768 prefixEnd_148768 3772320494231070529177 := by
  unfold tailWord_148768
  simp only [CollatzResearch.WordTrace]
  refine ⟨2713007362523209198355479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3617343150030945597807305 2713007362523209198355479)
  ·
    refine ⟨4069511043784813797533219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2713007362523209198355479 4069511043784813797533219)
    ·
      refine ⟨6104266565677220696299829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4069511043784813797533219 6104266565677220696299829)
      ·
        refine ⟨572274990532239440278109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 6104266565677220696299829 572274990532239440278109)
        ·
          refine ⟨214603121449589790104291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 572274990532239440278109 214603121449589790104291)
          ·
            refine ⟨321904682174384685156437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 214603121449589790104291 321904682174384685156437)
            ·
              refine ⟨3772320494231070529177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 321904682174384685156437 3772320494231070529177)
              ·
                rfl

theorem cell21_148768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 1, 8].length) (baseStart_148768 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_148768 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_148768 prefixEnd_148768 := by exact prefixLift 148768
  have htrace : WordTrace (prefixWord ++ tailWord_148768) baseStart_148768 baseEnd_148768 := by
    simpa [prefixWord, tailWord_148768, baseEnd_148768] using wordTrace_append hprefix tailTrace_148768
  have hstable : (prefixWord ++ tailWord_148768).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_148768).length < 2 ^ (prefixWord ++ tailWord_148768).sum := by decide
  have hdescent : baseEnd_148768 < baseStart_148768 := by decide
  rcases family_descends (prefixWord ++ tailWord_148768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_148844 : List Nat := [2, 2, 1, 1, 5, 2, 2, 6]
def baseStart_148844 : Nat := 118140960795 + 148844 * 2 ^ 59
def prefixEnd_148844 : Nat := 4983230072969 + 3 ^ 40 * 148844 * 2
def baseEnd_148844 : Nat := 11322742894506797165257

theorem tailTrace_148844 : CollatzResearch.WordTrace tailWord_148844 prefixEnd_148844 11322742894506797165257 := by
  unfold tailWord_148844
  simp only [CollatzResearch.WordTrace]
  refine ⟨2714393336385541688238793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3619191115180722250985057 2714393336385541688238793)
  ·
    refine ⟨2035795002289156266179095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2714393336385541688238793 2035795002289156266179095)
    ·
      refine ⟨3053692503433734399268643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2035795002289156266179095 3053692503433734399268643)
      ·
        refine ⟨4580538755150601598902965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3053692503433734399268643 4580538755150601598902965)
        ·
          refine ⟨429425508295368899897153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 4580538755150601598902965 429425508295368899897153)
          ·
            refine ⟨322069131221526674922865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 429425508295368899897153 322069131221526674922865)
            ·
              refine ⟨241551848416145006192149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 322069131221526674922865 241551848416145006192149)
              ·
                refine ⟨11322742894506797165257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 241551848416145006192149 11322742894506797165257)
                ·
                  rfl

theorem cell21_148844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 2, 2, 6].length) (baseStart_148844 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_148844 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_148844 prefixEnd_148844 := by exact prefixLift 148844
  have htrace : WordTrace (prefixWord ++ tailWord_148844) baseStart_148844 baseEnd_148844 := by
    simpa [prefixWord, tailWord_148844, baseEnd_148844] using wordTrace_append hprefix tailTrace_148844
  have hstable : (prefixWord ++ tailWord_148844).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_148844).length < 2 ^ (prefixWord ++ tailWord_148844).sum := by decide
  have hdescent : baseEnd_148844 < baseStart_148844 := by decide
  rcases family_descends (prefixWord ++ tailWord_148844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_148875 : List Nat := [1, 1, 1, 1, 4, 3, 2, 5, 3]
def baseStart_148875 : Nat := 118140960795 + 148875 * 2 ^ 59
def prefixEnd_148875 : Nat := 4983230072969 + 3 ^ 40 * 148875 * 2
def baseEnd_148875 : Nat := 33975303305871226479041

theorem tailTrace_148875 : CollatzResearch.WordTrace tailWord_148875 prefixEnd_148875 33975303305871226479041 := by
  unfold tailWord_148875
  simp only [CollatzResearch.WordTrace]
  refine ⟨5429917335658775670856079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3619944890439183780570719 5429917335658775670856079)
  ·
    refine ⟨8144876003488163506284119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5429917335658775670856079 8144876003488163506284119)
    ·
      refine ⟨12217314005232245259426179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8144876003488163506284119 12217314005232245259426179)
      ·
        refine ⟨18325971007848367889139269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12217314005232245259426179 18325971007848367889139269)
        ·
          refine ⟨3436119563971568979213613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18325971007848367889139269 3436119563971568979213613)
          ·
            refine ⟨1288544836489338367205105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3436119563971568979213613 1288544836489338367205105)
            ·
              refine ⟨966408627367003775403829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1288544836489338367205105 966408627367003775403829)
              ·
                refine ⟨90600808815656603944109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 966408627367003775403829 90600808815656603944109)
                ·
                  refine ⟨33975303305871226479041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 90600808815656603944109 33975303305871226479041)
                  ·
                    rfl

theorem cell21_148875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 2, 5, 3].length) (baseStart_148875 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_148875 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_148875 prefixEnd_148875 := by exact prefixLift 148875
  have htrace : WordTrace (prefixWord ++ tailWord_148875) baseStart_148875 baseEnd_148875 := by
    simpa [prefixWord, tailWord_148875, baseEnd_148875] using wordTrace_append hprefix tailTrace_148875
  have hstable : (prefixWord ++ tailWord_148875).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_148875).length < 2 ^ (prefixWord ++ tailWord_148875).sum := by decide
  have hdescent : baseEnd_148875 < baseStart_148875 := by decide
  rcases family_descends (prefixWord ++ tailWord_148875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_148889 : List Nat := [1, 2, 1, 2, 1, 5, 1, 4, 4]
def baseStart_148889 : Nat := 118140960795 + 148889 * 2 ^ 59
def prefixEnd_148889 : Nat := 4983230072969 + 3 ^ 40 * 148889 * 2
def baseEnd_148889 : Nat := 33978498296610313245679

theorem tailTrace_148889 : CollatzResearch.WordTrace tailWord_148889 prefixEnd_148889 33978498296610313245679 := by
  unfold tailWord_148889
  simp only [CollatzResearch.WordTrace]
  refine ⟨5430427957608056061865721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3620285305072037374577147 5430427957608056061865721)
  ·
    refine ⟨4072820968206042046399291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5430427957608056061865721 4072820968206042046399291)
    ·
      refine ⟨6109231452309063069598937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4072820968206042046399291 6109231452309063069598937)
      ·
        refine ⟨4581923589231797302199203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6109231452309063069598937 4581923589231797302199203)
        ·
          refine ⟨6872885383847695953298805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4581923589231797302199203 6872885383847695953298805)
          ·
            refine ⟨644333004735721495621763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 6872885383847695953298805 644333004735721495621763)
            ·
              refine ⟨966499507103582243432645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 644333004735721495621763 966499507103582243432645)
              ·
                refine ⟨181218657581921670643621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 966499507103582243432645 181218657581921670643621)
                ·
                  refine ⟨33978498296610313245679, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 181218657581921670643621 33978498296610313245679)
                  ·
                    rfl

theorem cell21_148889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 1, 4, 4].length) (baseStart_148889 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_148889 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_148889 prefixEnd_148889 := by exact prefixLift 148889
  have htrace : WordTrace (prefixWord ++ tailWord_148889) baseStart_148889 baseEnd_148889 := by
    simpa [prefixWord, tailWord_148889, baseEnd_148889] using wordTrace_append hprefix tailTrace_148889
  have hstable : (prefixWord ++ tailWord_148889).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_148889).length < 2 ^ (prefixWord ++ tailWord_148889).sum := by decide
  have hdescent : baseEnd_148889 < baseStart_148889 := by decide
  rcases family_descends (prefixWord ++ tailWord_148889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_149016 : List Nat := [2, 1, 2, 3, 5, 1, 2, 1, 4]
def baseStart_149016 : Nat := 118140960795 + 149016 * 2 ^ 59
def prefixEnd_149016 : Nat := 4983230072969 + 3 ^ 40 * 149016 * 2
def baseEnd_149016 : Nat := 34007481426886314628753

theorem tailTrace_149016 : CollatzResearch.WordTrace tailWord_149016 prefixEnd_149016 34007481426886314628753 := by
  unfold tailWord_149016
  simp only [CollatzResearch.WordTrace]
  refine ⟨2717530014073978375869451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3623373352098637834492601 2717530014073978375869451)
  ·
    refine ⟨4076295021110967563804177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2717530014073978375869451 4076295021110967563804177)
    ·
      refine ⟨3057221265833225672853133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4076295021110967563804177 3057221265833225672853133)
      ·
        refine ⟨1146457974687459627319925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3057221265833225672853133 1146457974687459627319925)
        ·
          refine ⟨107480435126949340061243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 1146457974687459627319925 107480435126949340061243)
          ·
            refine ⟨161220652690424010091865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 107480435126949340061243 161220652690424010091865)
            ·
              refine ⟨120915489517818007568899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 161220652690424010091865 120915489517818007568899)
              ·
                refine ⟨181373234276727011353349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 120915489517818007568899 181373234276727011353349)
                ·
                  refine ⟨34007481426886314628753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 181373234276727011353349 34007481426886314628753)
                  ·
                    rfl

theorem cell21_149016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 5, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 5, 1, 2, 1, 4].length) (baseStart_149016 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_149016 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_149016 prefixEnd_149016 := by exact prefixLift 149016
  have htrace : WordTrace (prefixWord ++ tailWord_149016) baseStart_149016 baseEnd_149016 := by
    simpa [prefixWord, tailWord_149016, baseEnd_149016] using wordTrace_append hprefix tailTrace_149016
  have hstable : (prefixWord ++ tailWord_149016).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_149016).length < 2 ^ (prefixWord ++ tailWord_149016).sum := by decide
  have hdescent : baseEnd_149016 < baseStart_149016 := by decide
  rcases family_descends (prefixWord ++ tailWord_149016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_149100 : List Nat := [2, 2, 1, 1, 3, 1, 1, 4, 6]
def baseStart_149100 : Nat := 118140960795 + 149100 * 2 ^ 59
def prefixEnd_149100 : Nat := 4983230072969 + 3 ^ 40 * 149100 * 2
def baseEnd_149100 : Nat := 34026651371320835228581

theorem tailTrace_149100 : CollatzResearch.WordTrace tailWord_149100 prefixEnd_149100 34026651371320835228581 := by
  unfold tailWord_149100
  simp only [CollatzResearch.WordTrace]
  refine ⟨2719061879921819548898377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3625415839895759398531169 2719061879921819548898377)
  ·
    refine ⟨2039296409941364661673783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2719061879921819548898377 2039296409941364661673783)
    ·
      refine ⟨3058944614912046992510675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2039296409941364661673783 3058944614912046992510675)
      ·
        refine ⟨4588416922368070488766013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3058944614912046992510675 4588416922368070488766013)
        ·
          refine ⟨1720656345888026433287255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4588416922368070488766013 1720656345888026433287255)
          ·
            refine ⟨2580984518832039649930883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1720656345888026433287255 2580984518832039649930883)
            ·
              refine ⟨3871476778248059474896325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2580984518832039649930883 3871476778248059474896325)
              ·
                refine ⟨725901895921511151543061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3871476778248059474896325 725901895921511151543061)
                ·
                  refine ⟨34026651371320835228581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 725901895921511151543061 34026651371320835228581)
                  ·
                    rfl

theorem cell21_149100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 6].length) (baseStart_149100 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_149100 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_149100 prefixEnd_149100 := by exact prefixLift 149100
  have htrace : WordTrace (prefixWord ++ tailWord_149100) baseStart_149100 baseEnd_149100 := by
    simpa [prefixWord, tailWord_149100, baseEnd_149100] using wordTrace_append hprefix tailTrace_149100
  have hstable : (prefixWord ++ tailWord_149100).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_149100).length < 2 ^ (prefixWord ++ tailWord_149100).sum := by decide
  have hdescent : baseEnd_149100 < baseStart_149100 := by decide
  rcases family_descends (prefixWord ++ tailWord_149100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_149117 : List Nat := [1, 4, 1, 1, 4, 2, 1, 1, 6]
def baseStart_149117 : Nat := 118140960795 + 149117 * 2 ^ 59
def prefixEnd_149117 : Nat := 4983230072969 + 3 ^ 40 * 149117 * 2
def baseEnd_149117 : Nat := 34030531002932583445213

theorem tailTrace_149117 : CollatzResearch.WordTrace tailWord_149117 prefixEnd_149117 34030531002932583445213 := by
  unfold tailWord_149117
  simp only [CollatzResearch.WordTrace]
  refine ⟨5438743800782051001165605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3625829200521367334110403 5438743800782051001165605)
  ·
    refine ⟨1019764462646634562718551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5438743800782051001165605 1019764462646634562718551)
    ·
      refine ⟨1529646693969951844077827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1019764462646634562718551 1529646693969951844077827)
      ·
        refine ⟨2294470040954927766116741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1529646693969951844077827 2294470040954927766116741)
        ·
          refine ⟨430213132679048956146889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2294470040954927766116741 430213132679048956146889)
          ·
            refine ⟨322659849509286717110167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 430213132679048956146889 322659849509286717110167)
            ·
              refine ⟨483989774263930075665251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 322659849509286717110167 483989774263930075665251)
              ·
                refine ⟨725984661395895113497877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 483989774263930075665251 725984661395895113497877)
                ·
                  refine ⟨34030531002932583445213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 725984661395895113497877 34030531002932583445213)
                  ·
                    rfl

theorem cell21_149117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 2, 1, 1, 6].length) (baseStart_149117 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_149117 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_149117 prefixEnd_149117 := by exact prefixLift 149117
  have htrace : WordTrace (prefixWord ++ tailWord_149117) baseStart_149117 baseEnd_149117 := by
    simpa [prefixWord, tailWord_149117, baseEnd_149117] using wordTrace_append hprefix tailTrace_149117
  have hstable : (prefixWord ++ tailWord_149117).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_149117).length < 2 ^ (prefixWord ++ tailWord_149117).sum := by decide
  have hdescent : baseEnd_149117 < baseStart_149117 := by decide
  rcases family_descends (prefixWord ++ tailWord_149117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_149145 : List Nat := [1, 2, 1, 2, 1, 2, 2, 3, 7]
def baseStart_149145 : Nat := 118140960795 + 149145 * 2 ^ 59
def prefixEnd_149145 : Nat := 4983230072969 + 3 ^ 40 * 149145 * 2
def baseEnd_149145 : Nat := 34036920984410756978489

theorem tailTrace_149145 : CollatzResearch.WordTrace tailWord_149145 prefixEnd_149145 34036920984410756978489 := by
  unfold tailWord_149145
  simp only [CollatzResearch.WordTrace]
  refine ⟨5439765044680611783184889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3626510029787074522123259 5439765044680611783184889)
  ·
    refine ⟨4079823783510458837388667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5439765044680611783184889 4079823783510458837388667)
    ·
      refine ⟨6119735675265688256083001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4079823783510458837388667 6119735675265688256083001)
      ·
        refine ⟨4589801756449266192062251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6119735675265688256083001 4589801756449266192062251)
        ·
          refine ⟨6884702634673899288093377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4589801756449266192062251 6884702634673899288093377)
          ·
            refine ⟨5163526976005424466070033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6884702634673899288093377 5163526976005424466070033)
            ·
              refine ⟨3872645232004068349552525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5163526976005424466070033 3872645232004068349552525)
              ·
                refine ⟨1452241962001525631082197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3872645232004068349552525 1452241962001525631082197)
                ·
                  refine ⟨34036920984410756978489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1452241962001525631082197 34036920984410756978489)
                  ·
                    rfl

theorem cell21_149145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 3, 7].length) (baseStart_149145 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_149145 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_149145 prefixEnd_149145 := by exact prefixLift 149145
  have htrace : WordTrace (prefixWord ++ tailWord_149145) baseStart_149145 baseEnd_149145 := by
    simpa [prefixWord, tailWord_149145, baseEnd_149145] using wordTrace_append hprefix tailTrace_149145
  have hstable : (prefixWord ++ tailWord_149145).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_149145).length < 2 ^ (prefixWord ++ tailWord_149145).sum := by decide
  have hdescent : baseEnd_149145 < baseStart_149145 := by decide
  rcases family_descends (prefixWord ++ tailWord_149145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_149148 : List Nat := [2, 2, 3, 2, 3, 1, 1, 7]
def baseStart_149148 : Nat := 118140960795 + 149148 * 2 ^ 59
def prefixEnd_149148 : Nat := 4983230072969 + 3 ^ 40 * 149148 * 2
def baseEnd_149148 : Nat := 11345868541761139476161

theorem tailTrace_149148 : CollatzResearch.WordTrace tailWord_149148 prefixEnd_149148 11345868541761139476161 := by
  unfold tailWord_149148
  simp only [CollatzResearch.WordTrace]
  refine ⟨2719937231834871647772049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3626582975779828863696065 2719937231834871647772049)
  ·
    refine ⟨2039952923876153735829037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2719937231834871647772049 2039952923876153735829037)
    ·
      refine ⟨764982346453557650935889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2039952923876153735829037 764982346453557650935889)
      ·
        refine ⟨573736759840168238201917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 764982346453557650935889 573736759840168238201917)
        ·
          refine ⟨215151284940063089325719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 573736759840168238201917 215151284940063089325719)
          ·
            refine ⟨322726927410094633988579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 215151284940063089325719 322726927410094633988579)
            ·
              refine ⟨484090391115141950982869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 322726927410094633988579 484090391115141950982869)
              ·
                refine ⟨11345868541761139476161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 484090391115141950982869 11345868541761139476161)
                ·
                  rfl

theorem cell21_149148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 1, 1, 7].length) (baseStart_149148 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_149148 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_149148 prefixEnd_149148 := by exact prefixLift 149148
  have htrace : WordTrace (prefixWord ++ tailWord_149148) baseStart_149148 baseEnd_149148 := by
    simpa [prefixWord, tailWord_149148, baseEnd_149148] using wordTrace_append hprefix tailTrace_149148
  have hstable : (prefixWord ++ tailWord_149148).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_149148).length < 2 ^ (prefixWord ++ tailWord_149148).sum := by decide
  have hdescent : baseEnd_149148 < baseStart_149148 := by decide
  rcases family_descends (prefixWord ++ tailWord_149148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_149154 : List Nat := [3, 3, 1, 4, 1, 2, 1, 3, 3]
def baseStart_149154 : Nat := 118140960795 + 149154 * 2 ^ 59
def prefixEnd_149154 : Nat := 4983230072969 + 3 ^ 40 * 149154 * 2
def baseEnd_149154 : Nat := 34038974907028741328471

theorem tailTrace_149154 : CollatzResearch.WordTrace tailWord_149154 prefixEnd_149154 34038974907028741328471 := by
  unfold tailWord_149154
  simp only [CollatzResearch.WordTrace]
  refine ⟨1360023325412001580065629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3626728867765337546841677 1360023325412001580065629)
  ·
    refine ⟨510008747029500592524611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1360023325412001580065629 510008747029500592524611)
    ·
      refine ⟨765013120544250888786917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 510008747029500592524611 765013120544250888786917)
      ·
        refine ⟨143439960102047041647547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 765013120544250888786917 143439960102047041647547)
        ·
          refine ⟨215159940153070562471321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 143439960102047041647547 215159940153070562471321)
          ·
            refine ⟨161369955114802921853491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 215159940153070562471321 161369955114802921853491)
            ·
              refine ⟨242054932672204382780237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 161369955114802921853491 242054932672204382780237)
              ·
                refine ⟨90770599752076643542589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 242054932672204382780237 90770599752076643542589)
                ·
                  refine ⟨34038974907028741328471, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 90770599752076643542589 34038974907028741328471)
                  ·
                    rfl

theorem cell21_149154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 2, 1, 3, 3].length) (baseStart_149154 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_149154 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_149154 prefixEnd_149154 := by exact prefixLift 149154
  have htrace : WordTrace (prefixWord ++ tailWord_149154) baseStart_149154 baseEnd_149154 := by
    simpa [prefixWord, tailWord_149154, baseEnd_149154] using wordTrace_append hprefix tailTrace_149154
  have hstable : (prefixWord ++ tailWord_149154).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_149154).length < 2 ^ (prefixWord ++ tailWord_149154).sum := by decide
  have hdescent : baseEnd_149154 < baseStart_149154 := by decide
  rcases family_descends (prefixWord ++ tailWord_149154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_149255 : List Nat := [1, 1, 4, 4, 2, 1, 1, 2, 5]
def baseStart_149255 : Nat := 118140960795 + 149255 * 2 ^ 59
def prefixEnd_149255 : Nat := 4983230072969 + 3 ^ 40 * 149255 * 2
def baseEnd_149255 : Nat := 34062024483075010144931

theorem tailTrace_149255 : CollatzResearch.WordTrace tailWord_149255 prefixEnd_149255 34062024483075010144931 := by
  unfold tailWord_149255
  simp only [CollatzResearch.WordTrace]
  refine ⟨5443777074282100569689219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3629184716188067046459479 5443777074282100569689219)
  ·
    refine ⟨8165665611423150854533829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5443777074282100569689219 8165665611423150854533829)
    ·
      refine ⟨1531062302141840785225093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8165665611423150854533829 1531062302141840785225093)
      ·
        refine ⟨287074181651595147229705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1531062302141840785225093 287074181651595147229705)
        ·
          refine ⟨215305636238696360422279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 287074181651595147229705 215305636238696360422279)
          ·
            refine ⟨322958454358044540633419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 215305636238696360422279 322958454358044540633419)
            ·
              refine ⟨484437681537066810950129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 322958454358044540633419 484437681537066810950129)
              ·
                refine ⟨363328261152800108212597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 484437681537066810950129 363328261152800108212597)
                ·
                  refine ⟨34062024483075010144931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 363328261152800108212597 34062024483075010144931)
                  ·
                    rfl

theorem cell21_149255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 1, 1, 2, 5].length) (baseStart_149255 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_149255 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_149255 prefixEnd_149255 := by exact prefixLift 149255
  have htrace : WordTrace (prefixWord ++ tailWord_149255) baseStart_149255 baseEnd_149255 := by
    simpa [prefixWord, tailWord_149255, baseEnd_149255] using wordTrace_append hprefix tailTrace_149255
  have hstable : (prefixWord ++ tailWord_149255).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_149255).length < 2 ^ (prefixWord ++ tailWord_149255).sum := by decide
  have hdescent : baseEnd_149255 < baseStart_149255 := by decide
  rcases family_descends (prefixWord ++ tailWord_149255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_149348 : List Nat := [2, 3, 1, 1, 6, 1, 1, 1, 5]
def baseStart_149348 : Nat := 118140960795 + 149348 * 2 ^ 59
def prefixEnd_149348 : Nat := 4983230072969 + 3 ^ 40 * 149348 * 2
def baseEnd_149348 : Nat := 34083248350127515094741

theorem tailTrace_149348 : CollatzResearch.WordTrace tailWord_149348 prefixEnd_149348 34083248350127515094741 := by
  unfold tailWord_149348
  simp only [CollatzResearch.WordTrace]
  refine ⟨2723584531472588726412349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3631446041963451635216465 2723584531472588726412349)
  ·
    refine ⟨1021344199302220772404631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2723584531472588726412349 1021344199302220772404631)
    ·
      refine ⟨1532016298953331158606947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1021344199302220772404631 1532016298953331158606947)
      ·
        refine ⟨2298024448429996737910421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1532016298953331158606947 2298024448429996737910421)
        ·
          refine ⟨107719896020156097089551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 2298024448429996737910421 107719896020156097089551)
          ·
            refine ⟨161579844030234145634327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 107719896020156097089551 161579844030234145634327)
            ·
              refine ⟨242369766045351218451491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 161579844030234145634327 242369766045351218451491)
              ·
                refine ⟨363554649068026827677237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 242369766045351218451491 363554649068026827677237)
                ·
                  refine ⟨34083248350127515094741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 363554649068026827677237 34083248350127515094741)
                  ·
                    rfl

theorem cell21_149348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 6, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 6, 1, 1, 1, 5].length) (baseStart_149348 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_149348 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_149348 prefixEnd_149348 := by exact prefixLift 149348
  have htrace : WordTrace (prefixWord ++ tailWord_149348) baseStart_149348 baseEnd_149348 := by
    simpa [prefixWord, tailWord_149348, baseEnd_149348] using wordTrace_append hprefix tailTrace_149348
  have hstable : (prefixWord ++ tailWord_149348).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_149348).length < 2 ^ (prefixWord ++ tailWord_149348).sum := by decide
  have hdescent : baseEnd_149348 < baseStart_149348 := by decide
  rcases family_descends (prefixWord ++ tailWord_149348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_149373 : List Nat := [1, 4, 1, 1, 2, 1, 1, 3, 7]
def baseStart_149373 : Nat := 118140960795 + 149373 * 2 ^ 59
def prefixEnd_149373 : Nat := 4983230072969 + 3 ^ 40 * 149373 * 2
def baseEnd_149373 : Nat := 34088953690733027178023

theorem tailTrace_149373 : CollatzResearch.WordTrace tailWord_149373 prefixEnd_149373 34088953690733027178023 := by
  unfold tailWord_149373
  simp only [CollatzResearch.WordTrace]
  refine ⟨5448080887854606722484773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3632053925236404481656515 5448080887854606722484773)
  ·
    refine ⟨1021515166472738760465895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5448080887854606722484773 1021515166472738760465895)
    ·
      refine ⟨1532272749709108140698843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1021515166472738760465895 1532272749709108140698843)
      ·
        refine ⟨2298409124563662211048265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1532272749709108140698843 2298409124563662211048265)
        ·
          refine ⟨1723806843422746658286199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2298409124563662211048265 1723806843422746658286199)
          ·
            refine ⟨2585710265134119987429299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1723806843422746658286199 2585710265134119987429299)
            ·
              refine ⟨3878565397701179981143949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2585710265134119987429299 3878565397701179981143949)
              ·
                refine ⟨1454462024137942492928981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3878565397701179981143949 1454462024137942492928981)
                ·
                  refine ⟨34088953690733027178023, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1454462024137942492928981 34088953690733027178023)
                  ·
                    rfl

theorem cell21_149373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 3, 7].length) (baseStart_149373 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_149373 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_149373 prefixEnd_149373 := by exact prefixLift 149373
  have htrace : WordTrace (prefixWord ++ tailWord_149373) baseStart_149373 baseEnd_149373 := by
    simpa [prefixWord, tailWord_149373, baseEnd_149373] using wordTrace_append hprefix tailTrace_149373
  have hstable : (prefixWord ++ tailWord_149373).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_149373).length < 2 ^ (prefixWord ++ tailWord_149373).sum := by decide
  have hdescent : baseEnd_149373 < baseStart_149373 := by decide
  rcases family_descends (prefixWord ++ tailWord_149373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_149511 : List Nat := [1, 1, 4, 3, 1, 4, 7]
def baseStart_149511 : Nat := 118140960795 + 149511 * 2 ^ 59
def prefixEnd_149511 : Nat := 4983230072969 + 3 ^ 40 * 149511 * 2
def baseEnd_149511 : Nat := 3791160796763939319749

theorem tailTrace_149511 : CollatzResearch.WordTrace tailWord_149511 prefixEnd_149511 3791160796763939319749 := by
  unfold tailWord_149511
  simp only [CollatzResearch.WordTrace]
  refine ⟨5453114161354656291008387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3635409440903104194005591 5453114161354656291008387)
  ·
    refine ⟨8179671242031984436512581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5453114161354656291008387 8179671242031984436512581)
    ·
      refine ⟨1533688357880997081846109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8179671242031984436512581 1533688357880997081846109)
      ·
        refine ⟨575133134205373905692291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1533688357880997081846109 575133134205373905692291)
        ·
          refine ⟨862699701308060858538437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 575133134205373905692291 862699701308060858538437)
          ·
            refine ⟨161756193995261410975957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 862699701308060858538437 161756193995261410975957)
            ·
              refine ⟨3791160796763939319749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 161756193995261410975957 3791160796763939319749)
              ·
                rfl

theorem cell21_149511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 4, 7].length) (baseStart_149511 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_149511 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_149511 prefixEnd_149511 := by exact prefixLift 149511
  have htrace : WordTrace (prefixWord ++ tailWord_149511) baseStart_149511 baseEnd_149511 := by
    simpa [prefixWord, tailWord_149511, baseEnd_149511] using wordTrace_append hprefix tailTrace_149511
  have hstable : (prefixWord ++ tailWord_149511).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_149511).length < 2 ^ (prefixWord ++ tailWord_149511).sum := by decide
  have hdescent : baseEnd_149511 < baseStart_149511 := by decide
  rcases family_descends (prefixWord ++ tailWord_149511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_149663 : List Nat := [1, 1, 2, 6, 1, 2, 1, 7]
def baseStart_149663 : Nat := 118140960795 + 149663 * 2 ^ 59
def prefixEnd_149663 : Nat := 4983230072969 + 3 ^ 40 * 149663 * 2
def baseEnd_149663 : Nat := 11385045213918989114699

theorem tailTrace_149663 : CollatzResearch.WordTrace tailWord_149663 prefixEnd_149663 11385045213918989114699 := by
  unfold tailWord_149663
  simp only [CollatzResearch.WordTrace]
  refine ⟨5458658056803986250541643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3639105371202657500361095 5458658056803986250541643)
  ·
    refine ⟨8187987085205979375812465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5458658056803986250541643 8187987085205979375812465)
    ·
      refine ⟨6140990313904484531859349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8187987085205979375812465 6140990313904484531859349)
      ·
        refine ⟨287858920964272712430907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 6140990313904484531859349 287858920964272712430907)
        ·
          refine ⟨431788381446409068646361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 287858920964272712430907 431788381446409068646361)
          ·
            refine ⟨323841286084806801484771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 431788381446409068646361 323841286084806801484771)
            ·
              refine ⟨485761929127210202227157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 323841286084806801484771 485761929127210202227157)
              ·
                refine ⟨11385045213918989114699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 485761929127210202227157 11385045213918989114699)
                ·
                  rfl

theorem cell21_149663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 2, 1, 7].length) (baseStart_149663 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_149663 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_149663 prefixEnd_149663 := by exact prefixLift 149663
  have htrace : WordTrace (prefixWord ++ tailWord_149663) baseStart_149663 baseEnd_149663 := by
    simpa [prefixWord, tailWord_149663, baseEnd_149663] using wordTrace_append hprefix tailTrace_149663
  have hstable : (prefixWord ++ tailWord_149663).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_149663).length < 2 ^ (prefixWord ++ tailWord_149663).sum := by decide
  have hdescent : baseEnd_149663 < baseStart_149663 := by decide
  rcases family_descends (prefixWord ++ tailWord_149663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_149691 : List Nat := [1, 1, 1, 1, 1, 2, 5, 3, 6]
def baseStart_149691 : Nat := 118140960795 + 149691 * 2 ^ 59
def prefixEnd_149691 : Nat := 4983230072969 + 3 ^ 40 * 149691 * 2
def baseEnd_149691 : Nat := 34161525623235140877373

theorem tailTrace_149691 : CollatzResearch.WordTrace tailWord_149691 prefixEnd_149691 34161525623235140877373 := by
  unfold tailWord_149691
  simp only [CollatzResearch.WordTrace]
  refine ⟨5459679300702547032560927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3639786200468364688373951 5459679300702547032560927)
  ·
    refine ⟨8189518951053820548841391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5459679300702547032560927 8189518951053820548841391)
    ·
      refine ⟨12284278426580730823262087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8189518951053820548841391 12284278426580730823262087)
      ·
        refine ⟨18426417639871096234893131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12284278426580730823262087 18426417639871096234893131)
        ·
          refine ⟨27639626459806644352339697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18426417639871096234893131 27639626459806644352339697)
          ·
            refine ⟨20729719844854983264254773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27639626459806644352339697 20729719844854983264254773)
            ·
              refine ⟨1943411235455154681023885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 20729719844854983264254773 1943411235455154681023885)
              ·
                refine ⟨728779213295683005383957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1943411235455154681023885 728779213295683005383957)
                ·
                  refine ⟨34161525623235140877373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 728779213295683005383957 34161525623235140877373)
                  ·
                    rfl

theorem cell21_149691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 5, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 5, 3, 6].length) (baseStart_149691 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_149691 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_149691 prefixEnd_149691 := by exact prefixLift 149691
  have htrace : WordTrace (prefixWord ++ tailWord_149691) baseStart_149691 baseEnd_149691 := by
    simpa [prefixWord, tailWord_149691, baseEnd_149691] using wordTrace_append hprefix tailTrace_149691
  have hstable : (prefixWord ++ tailWord_149691).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_149691).length < 2 ^ (prefixWord ++ tailWord_149691).sum := by decide
  have hdescent : baseEnd_149691 < baseStart_149691 := by decide
  rcases family_descends (prefixWord ++ tailWord_149691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_149722 : List Nat := [3, 1, 1, 2, 2, 1, 4, 7]
def baseStart_149722 : Nat := 118140960795 + 149722 * 2 ^ 59
def prefixEnd_149722 : Nat := 4983230072969 + 3 ^ 40 * 149722 * 2
def baseEnd_149722 : Nat := 11389533415195325286881

theorem tailTrace_149722 : CollatzResearch.WordTrace tailWord_149722 prefixEnd_149722 11389533415195325286881 := by
  unfold tailWord_149722
  simp only [CollatzResearch.WordTrace]
  refine ⟨1365202490897559831734855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3640539975726826217959613 1365202490897559831734855)
  ·
    refine ⟨2047803736346339747602283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1365202490897559831734855 2047803736346339747602283)
    ·
      refine ⟨3071705604519509621403425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2047803736346339747602283 3071705604519509621403425)
      ·
        refine ⟨2303779203389632216052569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3071705604519509621403425 2303779203389632216052569)
        ·
          refine ⟨1727834402542224162039427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2303779203389632216052569 1727834402542224162039427)
          ·
            refine ⟨2591751603813336243059141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1727834402542224162039427 2591751603813336243059141)
            ·
              refine ⟨485953425715000545573589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2591751603813336243059141 485953425715000545573589)
              ·
                refine ⟨11389533415195325286881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 485953425715000545573589 11389533415195325286881)
                ·
                  rfl

theorem cell21_149722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 4, 7].length) (baseStart_149722 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_149722 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_149722 prefixEnd_149722 := by exact prefixLift 149722
  have htrace : WordTrace (prefixWord ++ tailWord_149722) baseStart_149722 baseEnd_149722 := by
    simpa [prefixWord, tailWord_149722, baseEnd_149722] using wordTrace_append hprefix tailTrace_149722
  have hstable : (prefixWord ++ tailWord_149722).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_149722).length < 2 ^ (prefixWord ++ tailWord_149722).sum := by decide
  have hdescent : baseEnd_149722 < baseStart_149722 := by decide
  rcases family_descends (prefixWord ++ tailWord_149722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_149860 : List Nat := [2, 3, 1, 1, 3, 1, 2, 4, 4]
def baseStart_149860 : Nat := 118140960795 + 149860 * 2 ^ 59
def prefixEnd_149860 : Nat := 4983230072969 + 3 ^ 40 * 149860 * 2
def baseEnd_149860 : Nat := 34200093725728402560361

theorem tailTrace_149860 : CollatzResearch.WordTrace tailWord_149860 prefixEnd_149860 34200093725728402560361 := by
  unfold tailWord_149860
  simp only [CollatzResearch.WordTrace]
  refine ⟨2732921618545144447731517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3643895491393525930308689 2732921618545144447731517)
  ·
    refine ⟨1024845606954429167899319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2732921618545144447731517 1024845606954429167899319)
    ·
      refine ⟨1537268410431643751848979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1024845606954429167899319 1537268410431643751848979)
      ·
        refine ⟨2305902615647465627773469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1537268410431643751848979 2305902615647465627773469)
        ·
          refine ⟨864713480867799610415051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2305902615647465627773469 864713480867799610415051)
          ·
            refine ⟨1297070221301699415622577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 864713480867799610415051 1297070221301699415622577)
            ·
              refine ⟨972802665976274561716933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1297070221301699415622577 972802665976274561716933)
              ·
                refine ⟨182400499870551480321925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 972802665976274561716933 182400499870551480321925)
                ·
                  refine ⟨34200093725728402560361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 182400499870551480321925 34200093725728402560361)
                  ·
                    rfl

theorem cell21_149860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 2, 4, 4].length) (baseStart_149860 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_149860 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_149860 prefixEnd_149860 := by exact prefixLift 149860
  have htrace : WordTrace (prefixWord ++ tailWord_149860) baseStart_149860 baseEnd_149860 := by
    simpa [prefixWord, tailWord_149860, baseEnd_149860] using wordTrace_append hprefix tailTrace_149860
  have hstable : (prefixWord ++ tailWord_149860).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_149860).length < 2 ^ (prefixWord ++ tailWord_149860).sum := by decide
  have hdescent : baseEnd_149860 < baseStart_149860 := by decide
  rcases family_descends (prefixWord ++ tailWord_149860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_149874 : List Nat := [3, 2, 1, 2, 1, 3, 1, 8]
def baseStart_149874 : Nat := 118140960795 + 149874 * 2 ^ 59
def prefixEnd_149874 : Nat := 4983230072969 + 3 ^ 40 * 149874 * 2
def baseEnd_149874 : Nat := 11401096238822496442333

theorem tailTrace_149874 : CollatzResearch.WordTrace tailWord_149874 prefixEnd_149874 11401096238822496442333 := by
  unfold tailWord_149874
  simp only [CollatzResearch.WordTrace]
  refine ⟨1366588464759892321618169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3644235906026379524315117 1366588464759892321618169)
  ·
    refine ⟨1024941348569919241213627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1366588464759892321618169 1024941348569919241213627)
    ·
      refine ⟨1537412022854878861820441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1024941348569919241213627 1537412022854878861820441)
      ·
        refine ⟨1153059017141159146365331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1537412022854878861820441 1153059017141159146365331)
        ·
          refine ⟨1729588525711738719547997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1153059017141159146365331 1729588525711738719547997)
          ·
            refine ⟨648595697141902019830499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1729588525711738719547997 648595697141902019830499)
            ·
              refine ⟨972893545712853029745749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 648595697141902019830499 972893545712853029745749)
              ·
                refine ⟨11401096238822496442333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 972893545712853029745749 11401096238822496442333)
                ·
                  rfl

theorem cell21_149874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 1, 8].length) (baseStart_149874 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_149874 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_149874 prefixEnd_149874 := by exact prefixLift 149874
  have htrace : WordTrace (prefixWord ++ tailWord_149874) baseStart_149874 baseEnd_149874 := by
    simpa [prefixWord, tailWord_149874, baseEnd_149874] using wordTrace_append hprefix tailTrace_149874
  have hstable : (prefixWord ++ tailWord_149874).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_149874).length < 2 ^ (prefixWord ++ tailWord_149874).sum := by decide
  have hdescent : baseEnd_149874 < baseStart_149874 := by decide
  rcases family_descends (prefixWord ++ tailWord_149874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_149877 : List Nat := [1, 3, 4, 1, 2, 2, 1, 3, 4]
def baseStart_149877 : Nat := 118140960795 + 149877 * 2 ^ 59
def prefixEnd_149877 : Nat := 4983230072969 + 3 ^ 40 * 149877 * 2
def baseEnd_149877 : Nat := 34203973357340150776993

theorem tailTrace_149877 : CollatzResearch.WordTrace tailWord_149877 prefixEnd_149877 34203973357340150776993 := by
  unfold tailWord_149877
  simp only [CollatzResearch.WordTrace]
  refine ⟨5466463278028700798831885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3644308852019133865887923 5466463278028700798831885)
  ·
    refine ⟨2049923729260762799561957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5466463278028700798831885 2049923729260762799561957)
    ·
      refine ⟨384360699236393024917867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2049923729260762799561957 384360699236393024917867)
      ·
        refine ⟨576541048854589537376801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 384360699236393024917867 576541048854589537376801)
        ·
          refine ⟨432405786640942153032601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 576541048854589537376801 432405786640942153032601)
          ·
            refine ⟨324304339980706614774451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 432405786640942153032601 324304339980706614774451)
            ·
              refine ⟨486456509971059922161677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 324304339980706614774451 486456509971059922161677)
              ·
                refine ⟨182421191239147470810629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 486456509971059922161677 182421191239147470810629)
                ·
                  refine ⟨34203973357340150776993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 182421191239147470810629 34203973357340150776993)
                  ·
                    rfl

theorem cell21_149877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 2, 1, 3, 4].length) (baseStart_149877 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_149877 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_149877 prefixEnd_149877 := by exact prefixLift 149877
  have htrace : WordTrace (prefixWord ++ tailWord_149877) baseStart_149877 baseEnd_149877 := by
    simpa [prefixWord, tailWord_149877, baseEnd_149877] using wordTrace_append hprefix tailTrace_149877
  have hstable : (prefixWord ++ tailWord_149877).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_149877).length < 2 ^ (prefixWord ++ tailWord_149877).sum := by decide
  have hdescent : baseEnd_149877 < baseStart_149877 := by decide
  rcases family_descends (prefixWord ++ tailWord_149877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_149950 : List Nat := [4, 2, 1, 1, 1, 1, 2, 9]
def baseStart_149950 : Nat := 118140960795 + 149950 * 2 ^ 59
def prefixEnd_149950 : Nat := 4983230072969 + 3 ^ 40 * 149950 * 2
def baseEnd_149950 : Nat := 11406877650636082020059

theorem tailTrace_149950 : CollatzResearch.WordTrace tailWord_149950 prefixEnd_149950 11406877650636082020059 := by
  unfold tailWord_149950
  simp only [CollatzResearch.WordTrace]
  refine ⟨683640725845529283279913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3646083871176156177492869 683640725845529283279913)
  ·
    refine ⟨512730544384146962459935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 683640725845529283279913 512730544384146962459935)
    ·
      refine ⟨769095816576220443689903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 512730544384146962459935 769095816576220443689903)
      ·
        refine ⟨1153643724864330665534855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 769095816576220443689903 1153643724864330665534855)
        ·
          refine ⟨1730465587296495998302283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1153643724864330665534855 1730465587296495998302283)
          ·
            refine ⟨2595698380944743997453425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1730465587296495998302283 2595698380944743997453425)
            ·
              refine ⟨1946773785708557998090069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2595698380944743997453425 1946773785708557998090069)
              ·
                refine ⟨11406877650636082020059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 1946773785708557998090069 11406877650636082020059)
                ·
                  rfl

theorem cell21_149950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 2, 9].length) (baseStart_149950 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_149950 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_149950 prefixEnd_149950 := by exact prefixLift 149950
  have htrace : WordTrace (prefixWord ++ tailWord_149950) baseStart_149950 baseEnd_149950 := by
    simpa [prefixWord, tailWord_149950, baseEnd_149950] using wordTrace_append hprefix tailTrace_149950
  have hstable : (prefixWord ++ tailWord_149950).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_149950).length < 2 ^ (prefixWord ++ tailWord_149950).sum := by decide
  have hdescent : baseEnd_149950 < baseStart_149950 := by decide
  rcases family_descends (prefixWord ++ tailWord_149950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_149956 : List Nat := [2, 3, 3, 2, 2, 1, 2, 3, 3]
def baseStart_149956 : Nat := 118140960795 + 149956 * 2 ^ 59
def prefixEnd_149956 : Nat := 4983230072969 + 3 ^ 40 * 149956 * 2
def baseEnd_149956 : Nat := 34222002233653568960165

theorem tailTrace_149956 : CollatzResearch.WordTrace tailWord_149956 prefixEnd_149956 34222002233653568960165 := by
  unfold tailWord_149956
  simp only [CollatzResearch.WordTrace]
  refine ⟨2734672322371248645478861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3646229763161664860638481 2734672322371248645478861)
  ·
    refine ⟨1025502120889218242054573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2734672322371248645478861 1025502120889218242054573)
    ·
      refine ⟨384563295333456840770465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1025502120889218242054573 384563295333456840770465)
      ·
        refine ⟨288422471500092630577849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 384563295333456840770465 288422471500092630577849)
        ·
          refine ⟨216316853625069472933387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 288422471500092630577849 216316853625069472933387)
          ·
            refine ⟨324475280437604209400081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 216316853625069472933387 324475280437604209400081)
            ·
              refine ⟨243356460328203157050061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 324475280437604209400081 243356460328203157050061)
              ·
                refine ⟨91258672623076183893773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 243356460328203157050061 91258672623076183893773)
                ·
                  refine ⟨34222002233653568960165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 91258672623076183893773 34222002233653568960165)
                  ·
                    rfl

theorem cell21_149956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 1, 2, 3, 3].length) (baseStart_149956 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_149956 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_149956 prefixEnd_149956 := by exact prefixLift 149956
  have htrace : WordTrace (prefixWord ++ tailWord_149956) baseStart_149956 baseEnd_149956 := by
    simpa [prefixWord, tailWord_149956, baseEnd_149956] using wordTrace_append hprefix tailTrace_149956
  have hstable : (prefixWord ++ tailWord_149956).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_149956).length < 2 ^ (prefixWord ++ tailWord_149956).sum := by decide
  have hdescent : baseEnd_149956 < baseStart_149956 := by decide
  rcases family_descends (prefixWord ++ tailWord_149956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_150085 : List Nat := [1, 3, 1, 1, 1, 14]
def baseStart_150085 : Nat := 118140960795 + 150085 * 2 ^ 59
def prefixEnd_150085 : Nat := 4983230072969 + 3 ^ 40 * 150085 * 2
def baseEnd_150085 : Nat := 1268571918191778196663

theorem tailTrace_150085 : CollatzResearch.WordTrace tailWord_150085 prefixEnd_150085 1268571918191778196663 := by
  unfold tailWord_150085
  simp only [CollatzResearch.WordTrace]
  refine ⟨5474049661275152322403709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3649366440850101548269139 5474049661275152322403709)
  ·
    refine ⟨2052768622978182120901391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5474049661275152322403709 2052768622978182120901391)
    ·
      refine ⟨3079152934467273181352087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2052768622978182120901391 3079152934467273181352087)
      ·
        refine ⟨4618729401700909772028131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3079152934467273181352087 4618729401700909772028131)
        ·
          refine ⟨6928094102551364658042197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4618729401700909772028131 6928094102551364658042197)
          ·
            refine ⟨1268571918191778196663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 14 6928094102551364658042197 1268571918191778196663)
            ·
              rfl

theorem cell21_150085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 14].length) (baseStart_150085 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_150085 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_150085 prefixEnd_150085 := by exact prefixLift 150085
  have htrace : WordTrace (prefixWord ++ tailWord_150085) baseStart_150085 baseEnd_150085 := by
    simpa [prefixWord, tailWord_150085, baseEnd_150085] using wordTrace_append hprefix tailTrace_150085
  have hstable : (prefixWord ++ tailWord_150085).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_150085).length < 2 ^ (prefixWord ++ tailWord_150085).sum := by decide
  have hdescent : baseEnd_150085 < baseStart_150085 := by decide
  rcases family_descends (prefixWord ++ tailWord_150085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_150344 : List Nat := [2, 1, 3, 1, 1, 3, 1, 4, 5]
def baseStart_150344 : Nat := 118140960795 + 150344 * 2 ^ 59
def prefixEnd_150344 : Nat := 4983230072969 + 3 ^ 40 * 150344 * 2
def baseEnd_150344 : Nat := 34310549119851116492705

theorem tailTrace_150344 : CollatzResearch.WordTrace tailWord_150344 prefixEnd_150344 34310549119851116492705 := by
  unfold tailWord_150344
  simp only [CollatzResearch.WordTrace]
  refine ⟨2741748083668419778041043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3655664111557893037388057 2741748083668419778041043)
  ·
    refine ⟨4112622125502629667061565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2741748083668419778041043 4112622125502629667061565)
    ·
      refine ⟨1542233297063486125148087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4112622125502629667061565 1542233297063486125148087)
      ·
        refine ⟨2313349945595229187722131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1542233297063486125148087 2313349945595229187722131)
        ·
          refine ⟨3470024918392843781583197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2313349945595229187722131 3470024918392843781583197)
          ·
            refine ⟨1301259344397316418093699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3470024918392843781583197 1301259344397316418093699)
            ·
              refine ⟨1951889016595974627140549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1301259344397316418093699 1951889016595974627140549)
              ·
                refine ⟨365979190611745242588853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1951889016595974627140549 365979190611745242588853)
                ·
                  refine ⟨34310549119851116492705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 365979190611745242588853 34310549119851116492705)
                  ·
                    rfl

theorem cell21_150344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 1, 4, 5].length) (baseStart_150344 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_150344 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_150344 prefixEnd_150344 := by exact prefixLift 150344
  have htrace : WordTrace (prefixWord ++ tailWord_150344) baseStart_150344 baseEnd_150344 := by
    simpa [prefixWord, tailWord_150344, baseEnd_150344] using wordTrace_append hprefix tailTrace_150344
  have hstable : (prefixWord ++ tailWord_150344).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_150344).length < 2 ^ (prefixWord ++ tailWord_150344).sum := by decide
  have hdescent : baseEnd_150344 < baseStart_150344 := by decide
  rcases family_descends (prefixWord ++ tailWord_150344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_150375 : List Nat := [1, 1, 5, 1, 2, 2, 2, 1, 6]
def baseStart_150375 : Nat := 118140960795 + 150375 * 2 ^ 59
def prefixEnd_150375 : Nat := 4983230072969 + 3 ^ 40 * 150375 * 2
def baseEnd_150375 : Nat := 34317623742201951475975

theorem tailTrace_150375 : CollatzResearch.WordTrace tailWord_150375 prefixEnd_150375 34317623742201951475975 := by
  unfold tailWord_150375
  simp only [CollatzResearch.WordTrace]
  refine ⟨5484626830224531850460579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3656417886816354566973719 5484626830224531850460579)
  ·
    refine ⟨8226940245336797775690869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5484626830224531850460579 8226940245336797775690869)
    ·
      refine ⟨771275648000324791471019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 8226940245336797775690869 771275648000324791471019)
      ·
        refine ⟨1156913472000487187206529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 771275648000324791471019 1156913472000487187206529)
        ·
          refine ⟨867685104000365390404897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1156913472000487187206529 867685104000365390404897)
          ·
            refine ⟨650763828000274042803673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 867685104000365390404897 650763828000274042803673)
            ·
              refine ⟨488072871000205532102755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 650763828000274042803673 488072871000205532102755)
              ·
                refine ⟨732109306500308298154133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 488072871000205532102755 732109306500308298154133)
                ·
                  refine ⟨34317623742201951475975, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 732109306500308298154133 34317623742201951475975)
                  ·
                    rfl

theorem cell21_150375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 2, 1, 6].length) (baseStart_150375 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_150375 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_150375 prefixEnd_150375 := by exact prefixLift 150375
  have htrace : WordTrace (prefixWord ++ tailWord_150375) baseStart_150375 baseEnd_150375 := by
    simpa [prefixWord, tailWord_150375, baseEnd_150375] using wordTrace_append hprefix tailTrace_150375
  have hstable : (prefixWord ++ tailWord_150375).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_150375).length < 2 ^ (prefixWord ++ tailWord_150375).sum := by decide
  have hdescent : baseEnd_150375 < baseStart_150375 := by decide
  rcases family_descends (prefixWord ++ tailWord_150375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_150482 : List Nat := [3, 2, 2, 3, 1, 2, 8]
def baseStart_150482 : Nat := 118140960795 + 150482 * 2 ^ 59
def prefixEnd_150482 : Nat := 4983230072969 + 3 ^ 40 * 150482 * 2
def baseEnd_150482 : Nat := 3815782511110393688047

theorem tailTrace_150482 : CollatzResearch.WordTrace tailWord_150482 prefixEnd_150482 3815782511110393688047 := by
  unfold tailWord_150482
  simp only [CollatzResearch.WordTrace]
  refine ⟨1372132360209222281151425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3659019627224592749737133 1372132360209222281151425)
  ·
    refine ⟨1029099270156916710863569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1372132360209222281151425 1029099270156916710863569)
    ·
      refine ⟨771824452617687533147677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1029099270156916710863569 771824452617687533147677)
      ·
        refine ⟨289434169731632824930379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 771824452617687533147677 289434169731632824930379)
        ·
          refine ⟨434151254597449237395569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 289434169731632824930379 434151254597449237395569)
          ·
            refine ⟨325613440948086928046677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 434151254597449237395569 325613440948086928046677)
            ·
              refine ⟨3815782511110393688047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 325613440948086928046677 3815782511110393688047)
              ·
                rfl

theorem cell21_150482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 2, 8].length) (baseStart_150482 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_150482 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_150482 prefixEnd_150482 := by exact prefixLift 150482
  have htrace : WordTrace (prefixWord ++ tailWord_150482) baseStart_150482 baseEnd_150482 := by
    simpa [prefixWord, tailWord_150482, baseEnd_150482] using wordTrace_append hprefix tailTrace_150482
  have hstable : (prefixWord ++ tailWord_150482).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_150482).length < 2 ^ (prefixWord ++ tailWord_150482).sum := by decide
  have hdescent : baseEnd_150482 < baseStart_150482 := by decide
  rcases family_descends (prefixWord ++ tailWord_150482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_150485 : List Nat := [1, 3, 2, 3, 3, 2, 1, 2, 4]
def baseStart_150485 : Nat := 118140960795 + 150485 * 2 ^ 59
def prefixEnd_150485 : Nat := 4983230072969 + 3 ^ 40 * 150485 * 2
def baseEnd_150485 : Nat := 34342727240866204642417

theorem tailTrace_150485 : CollatzResearch.WordTrace tailWord_150485 prefixEnd_150485 34342727240866204642417 := by
  unfold tailWord_150485
  simp only [CollatzResearch.WordTrace]
  refine ⟨5488638859826020636964909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3659092573217347091309939 5488638859826020636964909)
  ·
    refine ⟨2058239572434757738861841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5488638859826020636964909 2058239572434757738861841)
    ·
      refine ⟨1543679679326068304146381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2058239572434757738861841 1543679679326068304146381)
      ·
        refine ⟨578879879747275614054893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1543679679326068304146381 578879879747275614054893)
        ·
          refine ⟨217079954905228355270585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 578879879747275614054893 217079954905228355270585)
          ·
            refine ⟨162809966178921266452939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 217079954905228355270585 162809966178921266452939)
            ·
              refine ⟨244214949268381899679409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 162809966178921266452939 244214949268381899679409)
              ·
                refine ⟨183161211951286424759557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 244214949268381899679409 183161211951286424759557)
                ·
                  refine ⟨34342727240866204642417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 183161211951286424759557 34342727240866204642417)
                  ·
                    rfl

theorem cell21_150485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 2, 1, 2, 4].length) (baseStart_150485 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_150485 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_150485 prefixEnd_150485 := by exact prefixLift 150485
  have htrace : WordTrace (prefixWord ++ tailWord_150485) baseStart_150485 baseEnd_150485 := by
    simpa [prefixWord, tailWord_150485, baseEnd_150485] using wordTrace_append hprefix tailTrace_150485
  have hstable : (prefixWord ++ tailWord_150485).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_150485).length < 2 ^ (prefixWord ++ tailWord_150485).sum := by decide
  have hdescent : baseEnd_150485 < baseStart_150485 := by decide
  rcases family_descends (prefixWord ++ tailWord_150485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_150561 : List Nat := [1, 2, 3, 2, 3, 3, 2, 1, 4]
def baseStart_150561 : Nat := 118140960795 + 150561 * 2 ^ 59
def prefixEnd_150561 : Nat := 4983230072969 + 3 ^ 40 * 150561 * 2
def baseEnd_150561 : Nat := 34360071476306961375595

theorem tailTrace_150561 : CollatzResearch.WordTrace tailWord_150561 prefixEnd_150561 34360071476306961375595 := by
  unfold tailWord_150561
  simp only [CollatzResearch.WordTrace]
  refine ⟨5491410807550685616731537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3660940538367123744487691 5491410807550685616731537)
  ·
    refine ⟨4118558105663014212548653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5491410807550685616731537 4118558105663014212548653)
    ·
      refine ⟨1544459289623630329705745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4118558105663014212548653 1544459289623630329705745)
      ·
        refine ⟨1158344467217722747279309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1544459289623630329705745 1158344467217722747279309)
        ·
          refine ⟨434379175206646030229741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1158344467217722747279309 434379175206646030229741)
          ·
            refine ⟨162892190702492261336153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 434379175206646030229741 162892190702492261336153)
            ·
              refine ⟨122169143026869196002115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 162892190702492261336153 122169143026869196002115)
              ·
                refine ⟨183253714540303794003173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 122169143026869196002115 183253714540303794003173)
                ·
                  refine ⟨34360071476306961375595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 183253714540303794003173 34360071476306961375595)
                  ·
                    rfl

theorem cell21_150561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 3, 2, 1, 4].length) (baseStart_150561 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_150561 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_150561 prefixEnd_150561 := by exact prefixLift 150561
  have htrace : WordTrace (prefixWord ++ tailWord_150561) baseStart_150561 baseEnd_150561 := by
    simpa [prefixWord, tailWord_150561, baseEnd_150561] using wordTrace_append hprefix tailTrace_150561
  have hstable : (prefixWord ++ tailWord_150561).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_150561).length < 2 ^ (prefixWord ++ tailWord_150561).sum := by decide
  have hdescent : baseEnd_150561 < baseStart_150561 := by decide
  rcases family_descends (prefixWord ++ tailWord_150561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_150586 : List Nat := [3, 1, 1, 1, 3, 1, 2, 1, 8]
def baseStart_150586 : Nat := 118140960795 + 150586 * 2 ^ 59
def prefixEnd_150586 : Nat := 4983230072969 + 3 ^ 40 * 150586 * 2
def baseEnd_150586 : Nat := 34365776816912473458877

theorem tailTrace_150586 : CollatzResearch.WordTrace tailWord_150586 prefixEnd_150586 34365776816912473458877 := by
  unfold tailWord_150586
  simp only [CollatzResearch.WordTrace]
  refine ⟨1373080658115028721597903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3661548421640076590927741 1373080658115028721597903)
  ·
    refine ⟨2059620987172543082396855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1373080658115028721597903 2059620987172543082396855)
    ·
      refine ⟨3089431480758814623595283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2059620987172543082396855 3089431480758814623595283)
      ·
        refine ⟨4634147221138221935392925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3089431480758814623595283 4634147221138221935392925)
        ·
          refine ⟨1737805207926833225772347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4634147221138221935392925 1737805207926833225772347)
          ·
            refine ⟨2606707811890249838658521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1737805207926833225772347 2606707811890249838658521)
            ·
              refine ⟨1955030858917687378993891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2606707811890249838658521 1955030858917687378993891)
              ·
                refine ⟨2932546288376531068490837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1955030858917687378993891 2932546288376531068490837)
                ·
                  refine ⟨34365776816912473458877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 2932546288376531068490837 34365776816912473458877)
                  ·
                    rfl

theorem cell21_150586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 2, 1, 8].length) (baseStart_150586 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_150586 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_150586 prefixEnd_150586 := by exact prefixLift 150586
  have htrace : WordTrace (prefixWord ++ tailWord_150586) baseStart_150586 baseEnd_150586 := by
    simpa [prefixWord, tailWord_150586, baseEnd_150586] using wordTrace_append hprefix tailTrace_150586
  have hstable : (prefixWord ++ tailWord_150586).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_150586).length < 2 ^ (prefixWord ++ tailWord_150586).sum := by decide
  have hdescent : baseEnd_150586 < baseStart_150586 := by decide
  rcases family_descends (prefixWord ++ tailWord_150586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_150654 : List Nat := [4, 2, 4, 1, 1, 1, 1, 1, 6]
def baseStart_150654 : Nat := 118140960795 + 150654 * 2 ^ 59
def prefixEnd_150654 : Nat := 4983230072969 + 3 ^ 40 * 150654 * 2
def baseEnd_150654 : Nat := 34381295343359466325405

theorem tailTrace_150654 : CollatzResearch.WordTrace tailWord_150654 prefixEnd_150654 34381295343359466325405 := by
  unfold tailWord_150654
  simp only [CollatzResearch.WordTrace]
  refine ⟨686850349526720312483377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3663201864142508333244677 686850349526720312483377)
  ·
    refine ⟨515137762145040234362533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 686850349526720312483377 515137762145040234362533)
    ·
      refine ⟨96588330402195043942975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 515137762145040234362533 96588330402195043942975)
      ·
        refine ⟨144882495603292565914463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 96588330402195043942975 144882495603292565914463)
        ·
          refine ⟨217323743404938848871695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 144882495603292565914463 217323743404938848871695)
          ·
            refine ⟨325985615107408273307543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 217323743404938848871695 325985615107408273307543)
            ·
              refine ⟨488978422661112409961315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 325985615107408273307543 488978422661112409961315)
              ·
                refine ⟨733467633991668614941973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 488978422661112409961315 733467633991668614941973)
                ·
                  refine ⟨34381295343359466325405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 733467633991668614941973 34381295343359466325405)
                  ·
                    rfl

theorem cell21_150654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 1, 1, 1, 6].length) (baseStart_150654 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_150654 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_150654 prefixEnd_150654 := by exact prefixLift 150654
  have htrace : WordTrace (prefixWord ++ tailWord_150654) baseStart_150654 baseEnd_150654 := by
    simpa [prefixWord, tailWord_150654, baseEnd_150654] using wordTrace_append hprefix tailTrace_150654
  have hstable : (prefixWord ++ tailWord_150654).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_150654).length < 2 ^ (prefixWord ++ tailWord_150654).sum := by decide
  have hdescent : baseEnd_150654 < baseStart_150654 := by decide
  rcases family_descends (prefixWord ++ tailWord_150654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_150665 : List Nat := [1, 2, 1, 1, 4, 3, 2, 4, 3]
def baseStart_150665 : Nat := 118140960795 + 150665 * 2 ^ 59
def prefixEnd_150665 : Nat := 4983230072969 + 3 ^ 40 * 150665 * 2
def baseEnd_150665 : Nat := 34383805693225891642049

theorem tailTrace_150665 : CollatzResearch.WordTrace tailWord_150665 prefixEnd_150665 34383805693225891642049 := by
  unfold tailWord_150665
  simp only [CollatzResearch.WordTrace]
  refine ⟨5495203999173911378517449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3663469332782607585678299 5495203999173911378517449)
  ·
    refine ⟨4121402999380433533888087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5495203999173911378517449 4121402999380433533888087)
    ·
      refine ⟨6182104499070650300832131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4121402999380433533888087 6182104499070650300832131)
      ·
        refine ⟨9273156748605975451248197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6182104499070650300832131 9273156748605975451248197)
        ·
          refine ⟨1738716890363620397109037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9273156748605975451248197 1738716890363620397109037)
          ·
            refine ⟨652018833886357648915889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1738716890363620397109037 652018833886357648915889)
            ·
              refine ⟨489014125414768236686917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 652018833886357648915889 489014125414768236686917)
              ·
                refine ⟨91690148515269044378797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 489014125414768236686917 91690148515269044378797)
                ·
                  refine ⟨34383805693225891642049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 91690148515269044378797 34383805693225891642049)
                  ·
                    rfl

theorem cell21_150665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 2, 4, 3].length) (baseStart_150665 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_150665 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_150665 prefixEnd_150665 := by exact prefixLift 150665
  have htrace : WordTrace (prefixWord ++ tailWord_150665) baseStart_150665 baseEnd_150665 := by
    simpa [prefixWord, tailWord_150665, baseEnd_150665] using wordTrace_append hprefix tailTrace_150665
  have hstable : (prefixWord ++ tailWord_150665).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_150665).length < 2 ^ (prefixWord ++ tailWord_150665).sum := by decide
  have hdescent : baseEnd_150665 < baseStart_150665 := by decide
  rcases family_descends (prefixWord ++ tailWord_150665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_150693 : List Nat := [1, 3, 1, 2, 1, 5, 1, 7]
def baseStart_150693 : Nat := 118140960795 + 150693 * 2 ^ 59
def prefixEnd_150693 : Nat := 4983230072969 + 3 ^ 40 * 150693 * 2
def baseEnd_150693 : Nat := 11463398558234688391775

theorem tailTrace_150693 : CollatzResearch.WordTrace tailWord_150693 prefixEnd_150693 11463398558234688391775 := by
  unfold tailWord_150693
  simp only [CollatzResearch.WordTrace]
  refine ⟨5496225243072472160536733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3664150162048314773691155 5496225243072472160536733)
  ·
    refine ⟨2061084466152177060201275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5496225243072472160536733 2061084466152177060201275)
    ·
      refine ⟨3091626699228265590301913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2061084466152177060201275 3091626699228265590301913)
      ·
        refine ⟨2318720024421199192726435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3091626699228265590301913 2318720024421199192726435)
        ·
          refine ⟨3478080036631798789089653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2318720024421199192726435 3478080036631798789089653)
          ·
            refine ⟨326070003434231136477155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 3478080036631798789089653 326070003434231136477155)
            ·
              refine ⟨489105005151346704715733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 326070003434231136477155 489105005151346704715733)
              ·
                refine ⟨11463398558234688391775, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 489105005151346704715733 11463398558234688391775)
                ·
                  rfl

theorem cell21_150693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 5, 1, 7].length) (baseStart_150693 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_150693 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_150693 prefixEnd_150693 := by exact prefixLift 150693
  have htrace : WordTrace (prefixWord ++ tailWord_150693) baseStart_150693 baseEnd_150693 := by
    simpa [prefixWord, tailWord_150693, baseEnd_150693] using wordTrace_append hprefix tailTrace_150693
  have hstable : (prefixWord ++ tailWord_150693).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_150693).length < 2 ^ (prefixWord ++ tailWord_150693).sum := by decide
  have hdescent : baseEnd_150693 < baseStart_150693 := by decide
  rcases family_descends (prefixWord ++ tailWord_150693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_150707 : List Nat := [1, 1, 1, 2, 3, 2, 2, 2, 7]
def baseStart_150707 : Nat := 118140960795 + 150707 * 2 ^ 59
def prefixEnd_150707 : Nat := 4983230072969 + 3 ^ 40 * 150707 * 2
def baseEnd_150707 : Nat := 34393390665443151941963

theorem tailTrace_150707 : CollatzResearch.WordTrace tailWord_150707 prefixEnd_150707 34393390665443151941963 := by
  unfold tailWord_150707
  simp only [CollatzResearch.WordTrace]
  refine ⟨5496735865021752551546375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3664490576681168367697583 5496735865021752551546375)
  ·
    refine ⟨8245103797532628827319563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5496735865021752551546375 8245103797532628827319563)
    ·
      refine ⟨12367655696298943240979345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8245103797532628827319563 12367655696298943240979345)
      ·
        refine ⟨9275741772224207430734509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12367655696298943240979345 9275741772224207430734509)
        ·
          refine ⟨3478403164584077786525441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9275741772224207430734509 3478403164584077786525441)
          ·
            refine ⟨2608802373438058339894081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3478403164584077786525441 2608802373438058339894081)
            ·
              refine ⟨1956601780078543754920561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2608802373438058339894081 1956601780078543754920561)
              ·
                refine ⟨1467451335058907816190421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1956601780078543754920561 1467451335058907816190421)
                ·
                  refine ⟨34393390665443151941963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1467451335058907816190421 34393390665443151941963)
                  ·
                    rfl

theorem cell21_150707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 2, 2, 7].length) (baseStart_150707 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_150707 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_150707 prefixEnd_150707 := by exact prefixLift 150707
  have htrace : WordTrace (prefixWord ++ tailWord_150707) baseStart_150707 baseEnd_150707 := by
    simpa [prefixWord, tailWord_150707, baseEnd_150707] using wordTrace_append hprefix tailTrace_150707
  have hstable : (prefixWord ++ tailWord_150707).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_150707).length < 2 ^ (prefixWord ++ tailWord_150707).sum := by decide
  have hdescent : baseEnd_150707 < baseStart_150707 := by decide
  rcases family_descends (prefixWord ++ tailWord_150707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_150854 : List Nat := [6, 1, 1, 3, 2, 1, 2, 5]
def baseStart_150854 : Nat := 118140960795 + 150854 * 2 ^ 59
def prefixEnd_150854 : Nat := 4983230072969 + 3 ^ 40 * 150854 * 2
def baseEnd_150854 : Nat := 11475646022734520997221

theorem tailTrace_150854 : CollatzResearch.WordTrace tailWord_150854 prefixEnd_150854 11475646022734520997221 := by
  unfold tailWord_150854
  simp only [CollatzResearch.WordTrace]
  refine ⟨171940543609037395535863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 3668064930326131104765077 171940543609037395535863)
  ·
    refine ⟨257910815413556093303795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 171940543609037395535863 257910815413556093303795)
    ·
      refine ⟨386866223120334139955693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 257910815413556093303795 386866223120334139955693)
      ·
        refine ⟨145074833670125302483385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 386866223120334139955693 145074833670125302483385)
        ·
          refine ⟨108806125252593976862539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 145074833670125302483385 108806125252593976862539)
          ·
            refine ⟨163209187878890965293809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 108806125252593976862539 163209187878890965293809)
            ·
              refine ⟨122406890909168223970357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 163209187878890965293809 122406890909168223970357)
              ·
                refine ⟨11475646022734520997221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 122406890909168223970357 11475646022734520997221)
                ·
                  rfl

theorem cell21_150854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 2, 1, 2, 5].length) (baseStart_150854 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_150854 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_150854 prefixEnd_150854 := by exact prefixLift 150854
  have htrace : WordTrace (prefixWord ++ tailWord_150854) baseStart_150854 baseEnd_150854 := by
    simpa [prefixWord, tailWord_150854, baseEnd_150854] using wordTrace_append hprefix tailTrace_150854
  have hstable : (prefixWord ++ tailWord_150854).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_150854).length < 2 ^ (prefixWord ++ tailWord_150854).sum := by decide
  have hdescent : baseEnd_150854 < baseStart_150854 := by decide
  rcases family_descends (prefixWord ++ tailWord_150854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_150893 : List Nat := [1, 5, 1, 1, 1, 5, 1, 1, 5]
def baseStart_150893 : Nat := 118140960795 + 150893 * 2 ^ 59
def prefixEnd_150893 : Nat := 4983230072969 + 3 ^ 40 * 150893 * 2
def baseEnd_150893 : Nat := 34435838399548161841583

theorem tailTrace_150893 : CollatzResearch.WordTrace tailWord_150893 prefixEnd_150893 34435838399548161841583 := by
  unfold tailWord_150893
  simp only [CollatzResearch.WordTrace]
  refine ⟨5503519842347906317817333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3669013228231937545211555 5503519842347906317817333)
  ·
    refine ⟨515954985220116217295375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 5503519842347906317817333 515954985220116217295375)
    ·
      refine ⟨773932477830174325943063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 515954985220116217295375 773932477830174325943063)
      ·
        refine ⟨1160898716745261488914595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 773932477830174325943063 1160898716745261488914595)
        ·
          refine ⟨1741348075117892233371893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1160898716745261488914595 1741348075117892233371893)
          ·
            refine ⟨163251382042302396878615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1741348075117892233371893 163251382042302396878615)
            ·
              refine ⟨244877073063453595317923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 163251382042302396878615 244877073063453595317923)
              ·
                refine ⟨367315609595180392976885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 244877073063453595317923 367315609595180392976885)
                ·
                  refine ⟨34435838399548161841583, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 367315609595180392976885 34435838399548161841583)
                  ·
                    rfl

theorem cell21_150893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 5, 1, 1, 5].length) (baseStart_150893 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_150893 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_150893 prefixEnd_150893 := by exact prefixLift 150893
  have htrace : WordTrace (prefixWord ++ tailWord_150893) baseStart_150893 baseEnd_150893 := by
    simpa [prefixWord, tailWord_150893, baseEnd_150893] using wordTrace_append hprefix tailTrace_150893
  have hstable : (prefixWord ++ tailWord_150893).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_150893).length < 2 ^ (prefixWord ++ tailWord_150893).sum := by decide
  have hdescent : baseEnd_150893 < baseStart_150893 := by decide
  rcases family_descends (prefixWord ++ tailWord_150893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_151073 : List Nat := [1, 2, 3, 2, 2, 3, 2, 6]
def baseStart_151073 : Nat := 118140960795 + 151073 * 2 ^ 59
def prefixEnd_151073 : Nat := 4983230072969 + 3 ^ 40 * 151073 * 2
def baseEnd_151073 : Nat := 11492305617302616280405

theorem tailTrace_151073 : CollatzResearch.WordTrace tailWord_151073 prefixEnd_151073 11492305617302616280405 := by
  unfold tailWord_151073
  simp only [CollatzResearch.WordTrace]
  refine ⟨5510084981695797059369873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3673389987797198039579915 5510084981695797059369873)
  ·
    refine ⟨4132563736271847794527405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5510084981695797059369873 4132563736271847794527405)
    ·
      refine ⟨1549711401101942922947777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4132563736271847794527405 1549711401101942922947777)
      ·
        refine ⟨1162283550826457192210833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1549711401101942922947777 1162283550826457192210833)
        ·
          refine ⟨871712663119842894158125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1162283550826457192210833 871712663119842894158125)
          ·
            refine ⟨326892248669941085309297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 871712663119842894158125 326892248669941085309297)
            ·
              refine ⟨245169186502455813981973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 326892248669941085309297 245169186502455813981973)
              ·
                refine ⟨11492305617302616280405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 245169186502455813981973 11492305617302616280405)
                ·
                  rfl

theorem cell21_151073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 3, 2, 6].length) (baseStart_151073 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_151073 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_151073 prefixEnd_151073 := by exact prefixLift 151073
  have htrace : WordTrace (prefixWord ++ tailWord_151073) baseStart_151073 baseEnd_151073 := by
    simpa [prefixWord, tailWord_151073, baseEnd_151073] using wordTrace_append hprefix tailTrace_151073
  have hstable : (prefixWord ++ tailWord_151073).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_151073).length < 2 ^ (prefixWord ++ tailWord_151073).sum := by decide
  have hdescent : baseEnd_151073 < baseStart_151073 := by decide
  rcases family_descends (prefixWord ++ tailWord_151073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_151104 : List Nat := [2, 1, 1, 2, 2, 2, 1, 7, 3]
def baseStart_151104 : Nat := 118140960795 + 151104 * 2 ^ 59
def prefixEnd_151104 : Nat := 4983230072969 + 3 ^ 40 * 151104 * 2
def baseEnd_151104 : Nat := 34483991474258683824485

theorem tailTrace_151104 : CollatzResearch.WordTrace tailWord_151104 prefixEnd_151104 34483991474258683824485 := by
  unfold tailWord_151104
  simp only [CollatzResearch.WordTrace]
  refine ⟨2755607822291744676874183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3674143763055659569165577 2755607822291744676874183)
  ·
    refine ⟨4133411733437617015311275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2755607822291744676874183 4133411733437617015311275)
    ·
      refine ⟨6200117600156425522966913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4133411733437617015311275 6200117600156425522966913)
      ·
        refine ⟨4650088200117319142225185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6200117600156425522966913 4650088200117319142225185)
        ·
          refine ⟨3487566150087989356668889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4650088200117319142225185 3487566150087989356668889)
          ·
            refine ⟨2615674612565992017501667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3487566150087989356668889 2615674612565992017501667)
            ·
              refine ⟨3923511918848988026252501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2615674612565992017501667 3923511918848988026252501)
              ·
                refine ⟨91957310598023156865293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3923511918848988026252501 91957310598023156865293)
                ·
                  refine ⟨34483991474258683824485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 91957310598023156865293 34483991474258683824485)
                  ·
                    rfl

theorem cell21_151104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 7, 3].length) (baseStart_151104 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_151104 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_151104 prefixEnd_151104 := by exact prefixLift 151104
  have htrace : WordTrace (prefixWord ++ tailWord_151104) baseStart_151104 baseEnd_151104 := by
    simpa [prefixWord, tailWord_151104, baseEnd_151104] using wordTrace_append hprefix tailTrace_151104
  have hstable : (prefixWord ++ tailWord_151104).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_151104).length < 2 ^ (prefixWord ++ tailWord_151104).sum := by decide
  have hdescent : baseEnd_151104 < baseStart_151104 := by decide
  rcases family_descends (prefixWord ++ tailWord_151104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_151180 : List Nat := [2, 2, 1, 2, 1, 1, 3, 6, 3]
def baseStart_151180 : Nat := 118140960795 + 151180 * 2 ^ 59
def prefixEnd_151180 : Nat := 4983230072969 + 3 ^ 40 * 151180 * 2
def baseEnd_151180 : Nat := 34501335709699440557663

theorem tailTrace_151180 : CollatzResearch.WordTrace tailWord_151180 prefixEnd_151180 34501335709699440557663 := by
  unfold tailWord_151180
  simp only [CollatzResearch.WordTrace]
  refine ⟨2756993796154077166757497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3675991728205436222343329 2756993796154077166757497)
  ·
    refine ⟨2067745347115557875068123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2756993796154077166757497 2067745347115557875068123)
    ·
      refine ⟨3101618020673336812602185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2067745347115557875068123 3101618020673336812602185)
      ·
        refine ⟨2326213515505002609451639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3101618020673336812602185 2326213515505002609451639)
        ·
          refine ⟨3489320273257503914177459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2326213515505002609451639 3489320273257503914177459)
          ·
            refine ⟨5233980409886255871266189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3489320273257503914177459 5233980409886255871266189)
            ·
              refine ⟨1962742653707345951724821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5233980409886255871266189 1962742653707345951724821)
              ·
                refine ⟨92003561892531841487101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1962742653707345951724821 92003561892531841487101)
                ·
                  refine ⟨34501335709699440557663, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 92003561892531841487101 34501335709699440557663)
                  ·
                    rfl

theorem cell21_151180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 3, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 3, 6, 3].length) (baseStart_151180 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_151180 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_151180 prefixEnd_151180 := by exact prefixLift 151180
  have htrace : WordTrace (prefixWord ++ tailWord_151180) baseStart_151180 baseEnd_151180 := by
    simpa [prefixWord, tailWord_151180, baseEnd_151180] using wordTrace_append hprefix tailTrace_151180
  have hstable : (prefixWord ++ tailWord_151180).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_151180).length < 2 ^ (prefixWord ++ tailWord_151180).sum := by decide
  have hdescent : baseEnd_151180 < baseStart_151180 := by decide
  rcases family_descends (prefixWord ++ tailWord_151180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_151245 : List Nat := [1, 6, 2, 1, 1, 1, 4, 1, 4]
def baseStart_151245 : Nat := 118140960795 + 151245 * 2 ^ 59
def prefixEnd_151245 : Nat := 4983230072969 + 3 ^ 40 * 151245 * 2
def baseEnd_151245 : Nat := 34516169595273771974197

theorem tailTrace_151245 : CollatzResearch.WordTrace tailWord_151245 prefixEnd_151245 34516169595273771974197 := by
  unfold tailWord_151245
  simp only [CollatzResearch.WordTrace]
  refine ⟨5516358337072670434631189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3677572224715113623087459 5516358337072670434631189)
  ·
    refine ⟨258579297050281426623337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 5516358337072670434631189 258579297050281426623337)
    ·
      refine ⟨193934472787711069967503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 258579297050281426623337 193934472787711069967503)
      ·
        refine ⟨290901709181566604951255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 193934472787711069967503 290901709181566604951255)
        ·
          refine ⟨436352563772349907426883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 290901709181566604951255 436352563772349907426883)
          ·
            refine ⟨654528845658524861140325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 436352563772349907426883 654528845658524861140325)
            ·
              refine ⟨122724158560973411463811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 654528845658524861140325 122724158560973411463811)
              ·
                refine ⟨184086237841460117195717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 122724158560973411463811 184086237841460117195717)
                ·
                  refine ⟨34516169595273771974197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 184086237841460117195717 34516169595273771974197)
                  ·
                    rfl

theorem cell21_151245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 4, 1, 4].length) (baseStart_151245 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_151245 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_151245 prefixEnd_151245 := by exact prefixLift 151245
  have htrace : WordTrace (prefixWord ++ tailWord_151245) baseStart_151245 baseEnd_151245 := by
    simpa [prefixWord, tailWord_151245, baseEnd_151245] using wordTrace_append hprefix tailTrace_151245
  have hstable : (prefixWord ++ tailWord_151245).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_151245).length < 2 ^ (prefixWord ++ tailWord_151245).sum := by decide
  have hdescent : baseEnd_151245 < baseStart_151245 := by decide
  rcases family_descends (prefixWord ++ tailWord_151245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_151346 : List Nat := [3, 2, 1, 1, 3, 3, 1, 1, 6]
def baseStart_151346 : Nat := 118140960795 + 151346 * 2 ^ 59
def prefixEnd_151346 : Nat := 4983230072969 + 3 ^ 40 * 151346 * 2
def baseEnd_151346 : Nat := 34539219171320040790657

theorem tailTrace_151346 : CollatzResearch.WordTrace tailWord_151346 prefixEnd_151346 34539219171320040790657 := by
  unfold tailWord_151346
  simp only [CollatzResearch.WordTrace]
  refine ⟨1380010527426691171014473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3680028073137843122705261 1380010527426691171014473)
  ·
    refine ⟨1035007895570018378260855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1380010527426691171014473 1035007895570018378260855)
    ·
      refine ⟨1552511843355027567391283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1035007895570018378260855 1552511843355027567391283)
      ·
        refine ⟨2328767765032541351086925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1552511843355027567391283 2328767765032541351086925)
        ·
          refine ⟨873287911887203006657597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2328767765032541351086925 873287911887203006657597)
          ·
            refine ⟨327482966957701127496599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 873287911887203006657597 327482966957701127496599)
            ·
              refine ⟨491224450436551691244899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 327482966957701127496599 491224450436551691244899)
              ·
                refine ⟨736836675654827536867349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 491224450436551691244899 736836675654827536867349)
                ·
                  refine ⟨34539219171320040790657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 736836675654827536867349 34539219171320040790657)
                  ·
                    rfl

theorem cell21_151346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 3, 1, 1, 6].length) (baseStart_151346 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_151346 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_151346 prefixEnd_151346 := by exact prefixLift 151346
  have htrace : WordTrace (prefixWord ++ tailWord_151346) baseStart_151346 baseEnd_151346 := by
    simpa [prefixWord, tailWord_151346, baseEnd_151346] using wordTrace_append hprefix tailTrace_151346
  have hstable : (prefixWord ++ tailWord_151346).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_151346).length < 2 ^ (prefixWord ++ tailWord_151346).sum := by decide
  have hdescent : baseEnd_151346 < baseStart_151346 := by decide
  rcases family_descends (prefixWord ++ tailWord_151346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_151363 : List Nat := [1, 1, 1, 3, 1, 6, 3, 1, 4]
def baseStart_151363 : Nat := 118140960795 + 151363 * 2 ^ 59
def prefixEnd_151363 : Nat := 4983230072969 + 3 ^ 40 * 151363 * 2
def baseEnd_151363 : Nat := 34543098802931789007289

theorem tailTrace_151363 : CollatzResearch.WordTrace tailWord_151363 prefixEnd_151363 34543098802931789007289 := by
  unfold tailWord_151363
  simp only [CollatzResearch.WordTrace]
  refine ⟨5520662150645176587426743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3680441433763451058284495 5520662150645176587426743)
  ·
    refine ⟨8280993225967764881140115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5520662150645176587426743 8280993225967764881140115)
    ·
      refine ⟨12421489838951647321710173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8280993225967764881140115 12421489838951647321710173)
      ·
        refine ⟨4658058689606867745641315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12421489838951647321710173 4658058689606867745641315)
        ·
          refine ⟨6987088034410301618461973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4658058689606867745641315 6987088034410301618461973)
          ·
            refine ⟨327519751612982888365405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 6987088034410301618461973 327519751612982888365405)
            ·
              refine ⟨122819906854868583137027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 327519751612982888365405 122819906854868583137027)
              ·
                refine ⟨184229860282302874705541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 122819906854868583137027 184229860282302874705541)
                ·
                  refine ⟨34543098802931789007289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 184229860282302874705541 34543098802931789007289)
                  ·
                    rfl

theorem cell21_151363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 6, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 6, 3, 1, 4].length) (baseStart_151363 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_151363 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_151363 prefixEnd_151363 := by exact prefixLift 151363
  have htrace : WordTrace (prefixWord ++ tailWord_151363) baseStart_151363 baseEnd_151363 := by
    simpa [prefixWord, tailWord_151363, baseEnd_151363] using wordTrace_append hprefix tailTrace_151363
  have hstable : (prefixWord ++ tailWord_151363).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_151363).length < 2 ^ (prefixWord ++ tailWord_151363).sum := by decide
  have hdescent : baseEnd_151363 < baseStart_151363 := by decide
  rcases family_descends (prefixWord ++ tailWord_151363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_151377 : List Nat := [1, 2, 2, 1, 5, 1, 4, 5]
def baseStart_151377 : Nat := 118140960795 + 151377 * 2 ^ 59
def prefixEnd_151377 : Nat := 4983230072969 + 3 ^ 40 * 151377 * 2
def baseEnd_151377 : Nat := 11515431264556958591309

theorem tailTrace_151377 : CollatzResearch.WordTrace tailWord_151377 prefixEnd_151377 11515431264556958591309 := by
  unfold tailWord_151377
  simp only [CollatzResearch.WordTrace]
  refine ⟨5521172772594456978436385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3680781848396304652290923 5521172772594456978436385)
  ·
    refine ⟨4140879579445842733827289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5521172772594456978436385 4140879579445842733827289)
    ·
      refine ⟨3105659684584382050370467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4140879579445842733827289 3105659684584382050370467)
      ·
        refine ⟨4658489526876573075555701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3105659684584382050370467 4658489526876573075555701)
        ·
          refine ⟨436733393144678725833347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 4658489526876573075555701 436733393144678725833347)
          ·
            refine ⟨655100089717018088750021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 436733393144678725833347 655100089717018088750021)
            ·
              refine ⟨122831266821940891640629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 655100089717018088750021 122831266821940891640629)
              ·
                refine ⟨11515431264556958591309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 122831266821940891640629 11515431264556958591309)
                ·
                  rfl

theorem cell21_151377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 4, 5].length) (baseStart_151377 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_151377 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_151377 prefixEnd_151377 := by exact prefixLift 151377
  have htrace : WordTrace (prefixWord ++ tailWord_151377) baseStart_151377 baseEnd_151377 := by
    simpa [prefixWord, tailWord_151377, baseEnd_151377] using wordTrace_append hprefix tailTrace_151377
  have hstable : (prefixWord ++ tailWord_151377).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_151377).length < 2 ^ (prefixWord ++ tailWord_151377).sum := by decide
  have hdescent : baseEnd_151377 < baseStart_151377 := by decide
  rcases family_descends (prefixWord ++ tailWord_151377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_151414 : List Nat := [5, 1, 1, 3, 3, 1, 2, 1, 4]
def baseStart_151414 : Nat := 118140960795 + 151414 * 2 ^ 59
def prefixEnd_151414 : Nat := 4983230072969 + 3 ^ 40 * 151414 * 2
def baseEnd_151414 : Nat := 34554737697767033657185

theorem tailTrace_151414 : CollatzResearch.WordTrace tailWord_151414 prefixEnd_151414 34554737697767033657185 := by
  unfold tailWord_151414
  simp only [CollatzResearch.WordTrace]
  refine ⟨345157642091275768595831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 3681681515640274865022197 345157642091275768595831)
  ·
    refine ⟨517736463136913652893747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 345157642091275768595831 517736463136913652893747)
    ·
      refine ⟨776604694705370479340621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 517736463136913652893747 776604694705370479340621)
      ·
        refine ⟨291226760514513929752733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 776604694705370479340621 291226760514513929752733)
        ·
          refine ⟨109210035192942723657275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 291226760514513929752733 109210035192942723657275)
          ·
            refine ⟨163815052789414085485913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 109210035192942723657275 163815052789414085485913)
            ·
              refine ⟨122861289592060564114435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 163815052789414085485913 122861289592060564114435)
              ·
                refine ⟨184291934388090846171653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 122861289592060564114435 184291934388090846171653)
                ·
                  refine ⟨34554737697767033657185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 184291934388090846171653 34554737697767033657185)
                  ·
                    rfl

theorem cell21_151414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 3, 1, 2, 1, 4].length) (baseStart_151414 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_151414 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_151414 prefixEnd_151414 := by exact prefixLift 151414
  have htrace : WordTrace (prefixWord ++ tailWord_151414) baseStart_151414 baseEnd_151414 := by
    simpa [prefixWord, tailWord_151414, baseEnd_151414] using wordTrace_append hprefix tailTrace_151414
  have hstable : (prefixWord ++ tailWord_151414).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_151414).length < 2 ^ (prefixWord ++ tailWord_151414).sum := by decide
  have hdescent : baseEnd_151414 < baseStart_151414 := by decide
  rcases family_descends (prefixWord ++ tailWord_151414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_151557 : List Nat := [1, 3, 1, 1, 2, 4, 1, 2, 6]
def baseStart_151557 : Nat := 118140960795 + 151557 * 2 ^ 59
def prefixEnd_151557 : Nat := 4983230072969 + 3 ^ 40 * 151557 * 2
def baseEnd_151557 : Nat := 34587372246030562773559

theorem tailTrace_151557 : CollatzResearch.WordTrace tailWord_151557 prefixEnd_151557 34587372246030562773559 := by
  unfold tailWord_151557
  simp only [CollatzResearch.WordTrace]
  refine ⟨5527737911942347719988925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3685158607961565146659283 5527737911942347719988925)
  ·
    refine ⟨2072901716978380394995847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5527737911942347719988925 2072901716978380394995847)
    ·
      refine ⟨3109352575467570592493771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2072901716978380394995847 3109352575467570592493771)
      ·
        refine ⟨4664028863201355888740657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3109352575467570592493771 4664028863201355888740657)
        ·
          refine ⟨3498021647401016916555493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4664028863201355888740657 3498021647401016916555493)
          ·
            refine ⟨655879058887690671854155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3498021647401016916555493 655879058887690671854155)
            ·
              refine ⟨983818588331536007781233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 655879058887690671854155 983818588331536007781233)
              ·
                refine ⟨737863941248652005835925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 983818588331536007781233 737863941248652005835925)
                ·
                  refine ⟨34587372246030562773559, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 737863941248652005835925 34587372246030562773559)
                  ·
                    rfl

theorem cell21_151557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 1, 2, 6].length) (baseStart_151557 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_151557 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_151557 prefixEnd_151557 := by exact prefixLift 151557
  have htrace : WordTrace (prefixWord ++ tailWord_151557) baseStart_151557 baseEnd_151557 := by
    simpa [prefixWord, tailWord_151557, baseEnd_151557] using wordTrace_append hprefix tailTrace_151557
  have hstable : (prefixWord ++ tailWord_151557).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_151557).length < 2 ^ (prefixWord ++ tailWord_151557).sum := by decide
  have hdescent : baseEnd_151557 < baseStart_151557 := by decide
  rcases family_descends (prefixWord ++ tailWord_151557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_151571 : List Nat := [1, 1, 1, 2, 1, 4, 11]
def baseStart_151571 : Nat := 118140960795 + 151571 * 2 ^ 59
def prefixEnd_151571 : Nat := 4983230072969 + 3 ^ 40 * 151571 * 2
def baseEnd_151571 : Nat := 3843396359641072171133

theorem tailTrace_151571 : CollatzResearch.WordTrace tailWord_151571 prefixEnd_151571 3843396359641072171133 := by
  unfold tailWord_151571
  simp only [CollatzResearch.WordTrace]
  refine ⟨5528248533891628110998567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3685499022594418740665711 5528248533891628110998567)
  ·
    refine ⟨8292372800837442166497851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5528248533891628110998567 8292372800837442166497851)
    ·
      refine ⟨12438559201256163249746777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8292372800837442166497851 12438559201256163249746777)
      ·
        refine ⟨9328919400942122437310083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12438559201256163249746777 9328919400942122437310083)
        ·
          refine ⟨13993379101413183655965125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9328919400942122437310083 13993379101413183655965125)
          ·
            refine ⟨2623758581514971935493461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13993379101413183655965125 2623758581514971935493461)
            ·
              refine ⟨3843396359641072171133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 2623758581514971935493461 3843396359641072171133)
              ·
                rfl

theorem cell21_151571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 11].length) (baseStart_151571 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_151571 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_151571 prefixEnd_151571 := by exact prefixLift 151571
  have htrace : WordTrace (prefixWord ++ tailWord_151571) baseStart_151571 baseEnd_151571 := by
    simpa [prefixWord, tailWord_151571, baseEnd_151571] using wordTrace_append hprefix tailTrace_151571
  have hstable : (prefixWord ++ tailWord_151571).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_151571).length < 2 ^ (prefixWord ++ tailWord_151571).sum := by decide
  have hdescent : baseEnd_151571 < baseStart_151571 := by decide
  rcases family_descends (prefixWord ++ tailWord_151571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_151647 : List Nat := [1, 1, 2, 3, 1, 1, 2, 10]
def baseStart_151647 : Nat := 118140960795 + 151647 * 2 ^ 59
def prefixEnd_151647 : Nat := 4983230072969 + 3 ^ 40 * 151647 * 2
def baseEnd_151647 : Nat := 11535970490736802091125

theorem tailTrace_151647 : CollatzResearch.WordTrace tailWord_151647 prefixEnd_151647 11535970490736802091125 := by
  unfold tailWord_151647
  simp only [CollatzResearch.WordTrace]
  refine ⟨5531020481616293090765195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3687346987744195393843463 5531020481616293090765195)
  ·
    refine ⟨8296530722424439636147793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5531020481616293090765195 8296530722424439636147793)
    ·
      refine ⟨6222398041818329727110845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8296530722424439636147793 6222398041818329727110845)
      ·
        refine ⟨2333399265681873647666567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6222398041818329727110845 2333399265681873647666567)
        ·
          refine ⟨3500098898522810471499851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2333399265681873647666567 3500098898522810471499851)
          ·
            refine ⟨5250148347784215707249777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3500098898522810471499851 5250148347784215707249777)
            ·
              refine ⟨3937611260838161780437333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5250148347784215707249777 3937611260838161780437333)
              ·
                refine ⟨11535970490736802091125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 3937611260838161780437333 11535970490736802091125)
                ·
                  rfl

theorem cell21_151647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 10].length) (baseStart_151647 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_151647 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_151647 prefixEnd_151647 := by exact prefixLift 151647
  have htrace : WordTrace (prefixWord ++ tailWord_151647) baseStart_151647 baseEnd_151647 := by
    simpa [prefixWord, tailWord_151647, baseEnd_151647] using wordTrace_append hprefix tailTrace_151647
  have hstable : (prefixWord ++ tailWord_151647).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_151647).length < 2 ^ (prefixWord ++ tailWord_151647).sum := by decide
  have hdescent : baseEnd_151647 < baseStart_151647 := by decide
  rcases family_descends (prefixWord ++ tailWord_151647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_151732 : List Nat := [2, 5, 3, 1, 2, 1, 7]
def baseStart_151732 : Nat := 118140960795 + 151732 * 2 ^ 59
def prefixEnd_151732 : Nat := 4983230072969 + 3 ^ 40 * 151732 * 2
def baseEnd_151732 : Nat := 3847478847807683039615

theorem tailTrace_151732 : CollatzResearch.WordTrace tailWord_151732 prefixEnd_151732 3847478847807683039615 := by
  unfold tailWord_151732
  simp only [CollatzResearch.WordTrace]
  refine ⟨2767060343154176303804725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3689413790872235071739633 2767060343154176303804725)
  ·
    refine ⟨259411907170704028481693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 2767060343154176303804725 259411907170704028481693)
    ·
      refine ⟨97279465189014010680635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 259411907170704028481693 97279465189014010680635)
      ·
        refine ⟨145919197783521016020953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97279465189014010680635 145919197783521016020953)
        ·
          refine ⟨109439398337640762015715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 145919197783521016020953 109439398337640762015715)
          ·
            refine ⟨164159097506461143023573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 109439398337640762015715 164159097506461143023573)
            ·
              refine ⟨3847478847807683039615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 164159097506461143023573 3847478847807683039615)
              ·
                rfl

theorem cell21_151732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 2, 1, 7].length) (baseStart_151732 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_151732 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_151732 prefixEnd_151732 := by exact prefixLift 151732
  have htrace : WordTrace (prefixWord ++ tailWord_151732) baseStart_151732 baseEnd_151732 := by
    simpa [prefixWord, tailWord_151732, baseEnd_151732] using wordTrace_append hprefix tailTrace_151732
  have hstable : (prefixWord ++ tailWord_151732).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_151732).length < 2 ^ (prefixWord ++ tailWord_151732).sum := by decide
  have hdescent : baseEnd_151732 < baseStart_151732 := by decide
  rcases family_descends (prefixWord ++ tailWord_151732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_151746 : List Nat := [3, 5, 1, 1, 1, 3, 1, 1, 5]
def baseStart_151746 : Nat := 118140960795 + 151746 * 2 ^ 59
def prefixEnd_151746 : Nat := 4983230072969 + 3 ^ 40 * 151746 * 2
def baseEnd_151746 : Nat := 34630504621008234123173

theorem tailTrace_151746 : CollatzResearch.WordTrace tailWord_151746 prefixEnd_151746 34630504621008234123173 := by
  unfold tailWord_151746
  simp only [CollatzResearch.WordTrace]
  refine ⟨1383657827064408249654773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3689754205505088665746061 1383657827064408249654773)
  ·
    refine ⟨129717921287288273405135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 1383657827064408249654773 129717921287288273405135)
    ·
      refine ⟨194576881930932410107703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 129717921287288273405135 194576881930932410107703)
      ·
        refine ⟨291865322896398615161555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 194576881930932410107703 291865322896398615161555)
        ·
          refine ⟨437797984344597922742333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 291865322896398615161555 437797984344597922742333)
          ·
            refine ⟨164174244129224221028375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 437797984344597922742333 164174244129224221028375)
            ·
              refine ⟨246261366193836331542563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 164174244129224221028375 246261366193836331542563)
              ·
                refine ⟨369392049290754497313845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 246261366193836331542563 369392049290754497313845)
                ·
                  refine ⟨34630504621008234123173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 369392049290754497313845 34630504621008234123173)
                  ·
                    rfl

theorem cell21_151746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 3, 1, 1, 5].length) (baseStart_151746 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_151746 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_151746 prefixEnd_151746 := by exact prefixLift 151746
  have htrace : WordTrace (prefixWord ++ tailWord_151746) baseStart_151746 baseEnd_151746 := by
    simpa [prefixWord, tailWord_151746, baseEnd_151746] using wordTrace_append hprefix tailTrace_151746
  have hstable : (prefixWord ++ tailWord_151746).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_151746).length < 2 ^ (prefixWord ++ tailWord_151746).sum := by decide
  have hdescent : baseEnd_151746 < baseStart_151746 := by decide
  rcases family_descends (prefixWord ++ tailWord_151746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_151802 : List Nat := [3, 1, 1, 1, 1, 6, 2, 2, 4]
def baseStart_151802 : Nat := 118140960795 + 151802 * 2 ^ 59
def prefixEnd_151802 : Nat := 4983230072969 + 3 ^ 40 * 151802 * 2
def baseEnd_151802 : Nat := 34643284583964581189725

theorem tailTrace_151802 : CollatzResearch.WordTrace tailWord_151802 prefixEnd_151802 34643284583964581189725 := by
  unfold tailWord_151802
  simp only [CollatzResearch.WordTrace]
  refine ⟨1384168449013688640664415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3691115864036503041771773 1384168449013688640664415)
  ·
    refine ⟨2076252673520532960996623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1384168449013688640664415 2076252673520532960996623)
    ·
      refine ⟨3114379010280799441494935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2076252673520532960996623 3114379010280799441494935)
      ·
        refine ⟨4671568515421199162242403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3114379010280799441494935 4671568515421199162242403)
        ·
          refine ⟨7007352773131798743363605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4671568515421199162242403 7007352773131798743363605)
          ·
            refine ⟨328469661240553066095169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 7007352773131798743363605 328469661240553066095169)
            ·
              refine ⟨246352245930414799571377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 328469661240553066095169 246352245930414799571377)
              ·
                refine ⟨184764184447811099678533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 246352245930414799571377 184764184447811099678533)
                ·
                  refine ⟨34643284583964581189725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 184764184447811099678533 34643284583964581189725)
                  ·
                    rfl

theorem cell21_151802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 6, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 6, 2, 2, 4].length) (baseStart_151802 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_151802 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_151802 prefixEnd_151802 := by exact prefixLift 151802
  have htrace : WordTrace (prefixWord ++ tailWord_151802) baseStart_151802 baseEnd_151802 := by
    simpa [prefixWord, tailWord_151802, baseEnd_151802] using wordTrace_append hprefix tailTrace_151802
  have hstable : (prefixWord ++ tailWord_151802).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_151802).length < 2 ^ (prefixWord ++ tailWord_151802).sum := by decide
  have hdescent : baseEnd_151802 < baseStart_151802 := by decide
  rcases family_descends (prefixWord ++ tailWord_151802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_151816 : List Nat := [2, 1, 3, 2, 3, 1, 3, 6]
def baseStart_151816 : Nat := 118140960795 + 151816 * 2 ^ 59
def prefixEnd_151816 : Nat := 4983230072969 + 3 ^ 40 * 151816 * 2
def baseEnd_151816 : Nat := 11548826524901222652121

theorem tailTrace_151816 : CollatzResearch.WordTrace tailWord_151816 prefixEnd_151816 11548826524901222652121 := by
  unfold tailWord_151816
  simp only [CollatzResearch.WordTrace]
  refine ⟨2768592209002017476833651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3691456278669356635778201 2768592209002017476833651)
  ·
    refine ⟨4152888313503026215250477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2768592209002017476833651 4152888313503026215250477)
    ·
      refine ⟨1557333117563634830718929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4152888313503026215250477 1557333117563634830718929)
      ·
        refine ⟨1167999838172726123039197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1557333117563634830718929 1167999838172726123039197)
        ·
          refine ⟨437999939314772296139699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1167999838172726123039197 437999939314772296139699)
          ·
            refine ⟨656999908972158444209549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 437999939314772296139699 656999908972158444209549)
            ·
              refine ⟨246374965864559416578581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 656999908972158444209549 246374965864559416578581)
              ·
                refine ⟨11548826524901222652121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 246374965864559416578581 11548826524901222652121)
                ·
                  rfl

theorem cell21_151816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 3, 6].length) (baseStart_151816 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_151816 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_151816 prefixEnd_151816 := by exact prefixLift 151816
  have htrace : WordTrace (prefixWord ++ tailWord_151816) baseStart_151816 baseEnd_151816 := by
    simpa [prefixWord, tailWord_151816, baseEnd_151816] using wordTrace_append hprefix tailTrace_151816
  have hstable : (prefixWord ++ tailWord_151816).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_151816).length < 2 ^ (prefixWord ++ tailWord_151816).sum := by decide
  have hdescent : baseEnd_151816 < baseStart_151816 := by decide
  rcases family_descends (prefixWord ++ tailWord_151816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_151853 : List Nat := [1, 5, 3, 1, 3, 1, 1, 2, 4]
def baseStart_151853 : Nat := 118140960795 + 151853 * 2 ^ 59
def prefixEnd_151853 : Nat := 4983230072969 + 3 ^ 40 * 151853 * 2
def baseEnd_151853 : Nat := 34654923478799825839621

theorem tailTrace_151853 : CollatzResearch.WordTrace tailWord_151853 prefixEnd_151853 34654923478799825839621 := by
  unfold tailWord_151853
  simp only [CollatzResearch.WordTrace]
  refine ⟨5538533918869990272764213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3692355945913326848509475 5538533918869990272764213)
  ·
    refine ⟨519237554894061588071645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 5538533918869990272764213 519237554894061588071645)
    ·
      refine ⟨194714083085273095526867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 519237554894061588071645 194714083085273095526867)
      ·
        refine ⟨292071124627909643290301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 194714083085273095526867 292071124627909643290301)
        ·
          refine ⟨109526671735466116233863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 292071124627909643290301 109526671735466116233863)
          ·
            refine ⟨164290007603199174350795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 109526671735466116233863 164290007603199174350795)
            ·
              refine ⟨246435011404798761526193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 164290007603199174350795 246435011404798761526193)
              ·
                refine ⟨184826258553599071144645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 246435011404798761526193 184826258553599071144645)
                ·
                  refine ⟨34654923478799825839621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 184826258553599071144645 34654923478799825839621)
                  ·
                    rfl

theorem cell21_151853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 3, 1, 1, 2, 4].length) (baseStart_151853 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_151853 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_151853 prefixEnd_151853 := by exact prefixLift 151853
  have htrace : WordTrace (prefixWord ++ tailWord_151853) baseStart_151853 baseEnd_151853 := by
    simpa [prefixWord, tailWord_151853, baseEnd_151853] using wordTrace_append hprefix tailTrace_151853
  have hstable : (prefixWord ++ tailWord_151853).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_151853).length < 2 ^ (prefixWord ++ tailWord_151853).sum := by decide
  have hdescent : baseEnd_151853 < baseStart_151853 := by decide
  rcases family_descends (prefixWord ++ tailWord_151853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_151861 : List Nat := [1, 3, 3, 1, 2, 1, 3, 1, 6]
def baseStart_151861 : Nat := 118140960795 + 151861 * 2 ^ 59
def prefixEnd_151861 : Nat := 4983230072969 + 3 ^ 40 * 151861 * 2
def baseEnd_151861 : Nat := 34656749187793589706271

theorem tailTrace_151861 : CollatzResearch.WordTrace tailWord_151861 prefixEnd_151861 34656749187793589706271 := by
  unfold tailWord_151861
  simp only [CollatzResearch.WordTrace]
  refine ⟨5538825702841007639055437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3692550468560671759370291 5538825702841007639055437)
  ·
    refine ⟨2077059638565377864645789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5538825702841007639055437 2077059638565377864645789)
    ·
      refine ⟨778897364462016699242171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2077059638565377864645789 778897364462016699242171)
      ·
        refine ⟨1168346046693025048863257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 778897364462016699242171 1168346046693025048863257)
        ·
          refine ⟨876259535019768786647443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1168346046693025048863257 876259535019768786647443)
          ·
            refine ⟨1314389302529653179971165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 876259535019768786647443 1314389302529653179971165)
            ·
              refine ⟨492895988448619942489187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1314389302529653179971165 492895988448619942489187)
              ·
                refine ⟨739343982672929913733781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 492895988448619942489187 739343982672929913733781)
                ·
                  refine ⟨34656749187793589706271, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 739343982672929913733781 34656749187793589706271)
                  ·
                    rfl

theorem cell21_151861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 3, 1, 6].length) (baseStart_151861 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_151861 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_151861 prefixEnd_151861 := by exact prefixLift 151861
  have htrace : WordTrace (prefixWord ++ tailWord_151861) baseStart_151861 baseEnd_151861 := by
    simpa [prefixWord, tailWord_151861, baseEnd_151861] using wordTrace_append hprefix tailTrace_151861
  have hstable : (prefixWord ++ tailWord_151861).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_151861).length < 2 ^ (prefixWord ++ tailWord_151861).sum := by decide
  have hdescent : baseEnd_151861 < baseStart_151861 := by decide
  rcases family_descends (prefixWord ++ tailWord_151861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_151892 : List Nat := [2, 4, 1, 1, 2, 3, 1, 7]
def baseStart_151892 : Nat := 118140960795 + 151892 * 2 ^ 59
def prefixEnd_151892 : Nat := 4983230072969 + 3 ^ 40 * 151892 * 2
def baseEnd_151892 : Nat := 11554607936714808229847

theorem tailTrace_151892 : CollatzResearch.WordTrace tailWord_151892 prefixEnd_151892 11554607936714808229847 := by
  unfold tailWord_151892
  simp only [CollatzResearch.WordTrace]
  refine ⟨2769978182864349966716965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3693304243819133288955953 2769978182864349966716965)
  ·
    refine ⟨519370909287065618759431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2769978182864349966716965 519370909287065618759431)
    ·
      refine ⟨779056363930598428139147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 519370909287065618759431 779056363930598428139147)
      ·
        refine ⟨1168584545895897642208721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 779056363930598428139147 1168584545895897642208721)
        ·
          refine ⟨876438409421923231656541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1168584545895897642208721 876438409421923231656541)
          ·
            refine ⟨328664403533221211871203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 876438409421923231656541 328664403533221211871203)
            ·
              refine ⟨492996605299831817806805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 328664403533221211871203 492996605299831817806805)
              ·
                refine ⟨11554607936714808229847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 492996605299831817806805 11554607936714808229847)
                ·
                  rfl

theorem cell21_151892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 3, 1, 7].length) (baseStart_151892 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_151892 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_151892 prefixEnd_151892 := by exact prefixLift 151892
  have htrace : WordTrace (prefixWord ++ tailWord_151892) baseStart_151892 baseEnd_151892 := by
    simpa [prefixWord, tailWord_151892, baseEnd_151892] using wordTrace_append hprefix tailTrace_151892
  have hstable : (prefixWord ++ tailWord_151892).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_151892).length < 2 ^ (prefixWord ++ tailWord_151892).sum := by decide
  have hdescent : baseEnd_151892 < baseStart_151892 := by decide
  rcases family_descends (prefixWord ++ tailWord_151892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_151926 : List Nat := [5, 1, 1, 4, 1, 1, 2, 6]
def baseStart_151926 : Nat := 118140960795 + 151926 * 2 ^ 59
def prefixEnd_151926 : Nat := 4983230072969 + 3 ^ 40 * 151926 * 2
def baseEnd_151926 : Nat := 11557194357789307040935

theorem tailTrace_151926 : CollatzResearch.WordTrace tailWord_151926 prefixEnd_151926 11557194357789307040935 := by
  unfold tailWord_151926
  simp only [CollatzResearch.WordTrace]
  refine ⟨346324777975345233760727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 3694130965070349160114421 346324777975345233760727)
  ·
    refine ⟨519487166963017850641091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 346324777975345233760727 519487166963017850641091)
    ·
      refine ⟨779230750444526775961637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 519487166963017850641091 779230750444526775961637)
      ·
        refine ⟨146105765708348770492807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 779230750444526775961637 146105765708348770492807)
        ·
          refine ⟨219158648562523155739211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 146105765708348770492807 219158648562523155739211)
          ·
            refine ⟨328737972843784733608817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 219158648562523155739211 328737972843784733608817)
            ·
              refine ⟨246553479632838550206613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 328737972843784733608817 246553479632838550206613)
              ·
                refine ⟨11557194357789307040935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 246553479632838550206613 11557194357789307040935)
                ·
                  rfl

theorem cell21_151926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 1, 2, 6].length) (baseStart_151926 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_151926 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_151926 prefixEnd_151926 := by exact prefixLift 151926
  have htrace : WordTrace (prefixWord ++ tailWord_151926) baseStart_151926 baseEnd_151926 := by
    simpa [prefixWord, tailWord_151926, baseEnd_151926] using wordTrace_append hprefix tailTrace_151926
  have hstable : (prefixWord ++ tailWord_151926).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_151926).length < 2 ^ (prefixWord ++ tailWord_151926).sum := by decide
  have hdescent : baseEnd_151926 < baseStart_151926 := by decide
  rcases family_descends (prefixWord ++ tailWord_151926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_152106 : List Nat := [3, 1, 4, 1, 1, 3, 1, 3, 4]
def baseStart_152106 : Nat := 118140960795 + 152106 * 2 ^ 59
def prefixEnd_152106 : Nat := 4983230072969 + 3 ^ 40 * 152106 * 2
def baseEnd_152106 : Nat := 34712661525727608122437

theorem tailTrace_152106 : CollatzResearch.WordTrace tailWord_152106 prefixEnd_152106 34712661525727608122437 := by
  unfold tailWord_152106
  simp only [CollatzResearch.WordTrace]
  refine ⟨1386940396738353620431043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3698507724635609654482781 1386940396738353620431043)
  ·
    refine ⟨2080410595107530430646565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1386940396738353620431043 2080410595107530430646565)
    ·
      refine ⟨390076986582661955746231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2080410595107530430646565 390076986582661955746231)
      ·
        refine ⟨585115479873992933619347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 390076986582661955746231 585115479873992933619347)
        ·
          refine ⟨877673219810989400429021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 585115479873992933619347 877673219810989400429021)
          ·
            refine ⟨329127457429121025160883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 877673219810989400429021 329127457429121025160883)
            ·
              refine ⟨493691186143681537741325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 329127457429121025160883 493691186143681537741325)
              ·
                refine ⟨185134194803880576652997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 493691186143681537741325 185134194803880576652997)
                ·
                  refine ⟨34712661525727608122437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 185134194803880576652997 34712661525727608122437)
                  ·
                    rfl

theorem cell21_152106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 3, 1, 3, 4].length) (baseStart_152106 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_152106 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_152106 prefixEnd_152106 := by exact prefixLift 152106
  have htrace : WordTrace (prefixWord ++ tailWord_152106) baseStart_152106 baseEnd_152106 := by
    simpa [prefixWord, tailWord_152106, baseEnd_152106] using wordTrace_append hprefix tailTrace_152106
  have hstable : (prefixWord ++ tailWord_152106).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_152106).length < 2 ^ (prefixWord ++ tailWord_152106).sum := by decide
  have hdescent : baseEnd_152106 < baseStart_152106 := by decide
  rcases family_descends (prefixWord ++ tailWord_152106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_152151 : List Nat := [1, 1, 3, 2, 2, 2, 3, 4, 3]
def baseStart_152151 : Nat := 118140960795 + 152151 * 2 ^ 59
def prefixEnd_152151 : Nat := 4983230072969 + 3 ^ 40 * 152151 * 2
def baseEnd_152151 : Nat := 34722931138817529872345

theorem tailTrace_152151 : CollatzResearch.WordTrace tailWord_152151 prefixEnd_152151 34722931138817529872345 := by
  unfold tailWord_152151
  simp only [CollatzResearch.WordTrace]
  refine ⟨5549402871790387167112307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3699601914526924778074871 5549402871790387167112307)
  ·
    refine ⟨8324104307685580750668461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5549402871790387167112307 8324104307685580750668461)
    ·
      refine ⟨3121539115382092781500673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8324104307685580750668461 3121539115382092781500673)
      ·
        refine ⟨2341154336536569586125505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3121539115382092781500673 2341154336536569586125505)
        ·
          refine ⟨1755865752402427189594129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2341154336536569586125505 1755865752402427189594129)
          ·
            refine ⟨1316899314301820392195597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1755865752402427189594129 1316899314301820392195597)
            ·
              refine ⟨493837242863182647073349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1316899314301820392195597 493837242863182647073349)
              ·
                refine ⟨92594483036846746326253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 493837242863182647073349 92594483036846746326253)
                ·
                  refine ⟨34722931138817529872345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 92594483036846746326253 34722931138817529872345)
                  ·
                    rfl

theorem cell21_152151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 3, 4, 3].length) (baseStart_152151 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_152151 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_152151 prefixEnd_152151 := by exact prefixLift 152151
  have htrace : WordTrace (prefixWord ++ tailWord_152151) baseStart_152151 baseEnd_152151 := by
    simpa [prefixWord, tailWord_152151, baseEnd_152151] using wordTrace_append hprefix tailTrace_152151
  have hstable : (prefixWord ++ tailWord_152151).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_152151).length < 2 ^ (prefixWord ++ tailWord_152151).sum := by decide
  have hdescent : baseEnd_152151 < baseStart_152151 := by decide
  rcases family_descends (prefixWord ++ tailWord_152151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_152255 : List Nat := [1, 1, 2, 2, 2, 6, 7]
def baseStart_152255 : Nat := 118140960795 + 152255 * 2 ^ 59
def prefixEnd_152255 : Nat := 4983230072969 + 3 ^ 40 * 152255 * 2
def baseEnd_152255 : Nat := 3860740595081828904311

theorem tailTrace_152255 : CollatzResearch.WordTrace tailWord_152255 prefixEnd_152255 3860740595081828904311 := by
  unfold tailWord_152255
  simp only [CollatzResearch.WordTrace]
  refine ⟨5553196063413612928898219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3702130708942408619265479 5553196063413612928898219)
  ·
    refine ⟨8329794095120419393347329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5553196063413612928898219 8329794095120419393347329)
    ·
      refine ⟨6247345571340314545010497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8329794095120419393347329 6247345571340314545010497)
      ·
        refine ⟨4685509178505235908757873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6247345571340314545010497 4685509178505235908757873)
        ·
          refine ⟨3514131883878926931568405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4685509178505235908757873 3514131883878926931568405)
          ·
            refine ⟨164724932056824699917269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 3514131883878926931568405 164724932056824699917269)
            ·
              refine ⟨3860740595081828904311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 164724932056824699917269 3860740595081828904311)
              ·
                rfl

theorem cell21_152255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 6, 7].length) (baseStart_152255 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_152255 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_152255 prefixEnd_152255 := by exact prefixLift 152255
  have htrace : WordTrace (prefixWord ++ tailWord_152255) baseStart_152255 baseEnd_152255 := by
    simpa [prefixWord, tailWord_152255, baseEnd_152255] using wordTrace_append hprefix tailTrace_152255
  have hstable : (prefixWord ++ tailWord_152255).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_152255).length < 2 ^ (prefixWord ++ tailWord_152255).sum := by decide
  have hdescent : baseEnd_152255 < baseStart_152255 := by decide
  rcases family_descends (prefixWord ++ tailWord_152255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_152317 : List Nat := [1, 4, 1, 1, 1, 1, 6, 2, 4]
def baseStart_152317 : Nat := 118140960795 + 152317 * 2 ^ 59
def prefixEnd_152317 : Nat := 4983230072969 + 3 ^ 40 * 152317 * 2
def baseEnd_152317 : Nat := 34760814600438130105339

theorem tailTrace_152317 : CollatzResearch.WordTrace tailWord_152317 prefixEnd_152317 34760814600438130105339 := by
  unfold tailWord_152317
  simp only [CollatzResearch.WordTrace]
  refine ⟨5555457389188997517655205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3703638259459331678436803 5555457389188997517655205)
  ·
    refine ⟨1041648260472937034560351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5555457389188997517655205 1041648260472937034560351)
    ·
      refine ⟨1562472390709405551840527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1041648260472937034560351 1562472390709405551840527)
      ·
        refine ⟨2343708586064108327760791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1562472390709405551840527 2343708586064108327760791)
        ·
          refine ⟨3515562879096162491641187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2343708586064108327760791 3515562879096162491641187)
          ·
            refine ⟨5273344318644243737461781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3515562879096162491641187 5273344318644243737461781)
            ·
              refine ⟨247188014936448925193521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 5273344318644243737461781 247188014936448925193521)
              ·
                refine ⟨185391011202336693895141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 247188014936448925193521 185391011202336693895141)
                ·
                  refine ⟨34760814600438130105339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 185391011202336693895141 34760814600438130105339)
                  ·
                    rfl

theorem cell21_152317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 6, 2, 4].length) (baseStart_152317 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_152317 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_152317 prefixEnd_152317 := by exact prefixLift 152317
  have htrace : WordTrace (prefixWord ++ tailWord_152317) baseStart_152317 baseEnd_152317 := by
    simpa [prefixWord, tailWord_152317, baseEnd_152317] using wordTrace_append hprefix tailTrace_152317
  have hstable : (prefixWord ++ tailWord_152317).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_152317).length < 2 ^ (prefixWord ++ tailWord_152317).sum := by decide
  have hdescent : baseEnd_152317 < baseStart_152317 := by decide
  rcases family_descends (prefixWord ++ tailWord_152317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_152348 : List Nat := [2, 2, 3, 1, 1, 4, 3, 5]
def baseStart_152348 : Nat := 118140960795 + 152348 * 2 ^ 59
def prefixEnd_152348 : Nat := 4983230072969 + 3 ^ 40 * 152348 * 2
def baseEnd_152348 : Nat := 11589296407596321696203

theorem tailTrace_152348 : CollatzResearch.WordTrace tailWord_152348 prefixEnd_152348 11589296407596321696203 := by
  unfold tailWord_152348
  simp only [CollatzResearch.WordTrace]
  refine ⟨2778294026038344906016849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3704392034717793208022465 2778294026038344906016849)
  ·
    refine ⟨2083720519528758679512637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2778294026038344906016849 2083720519528758679512637)
    ·
      refine ⟨781395194823284504817239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2083720519528758679512637 781395194823284504817239)
      ·
        refine ⟨1172092792234926757225859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 781395194823284504817239 1172092792234926757225859)
        ·
          refine ⟨1758139188352390135838789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1172092792234926757225859 1758139188352390135838789)
          ·
            refine ⟨329651097816073150469773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1758139188352390135838789 329651097816073150469773)
            ·
              refine ⟨123619161681027431426165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 329651097816073150469773 123619161681027431426165)
              ·
                refine ⟨11589296407596321696203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 123619161681027431426165 11589296407596321696203)
                ·
                  rfl

theorem cell21_152348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 4, 3, 5].length) (baseStart_152348 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_152348 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_152348 prefixEnd_152348 := by exact prefixLift 152348
  have htrace : WordTrace (prefixWord ++ tailWord_152348) baseStart_152348 baseEnd_152348 := by
    simpa [prefixWord, tailWord_152348, baseEnd_152348] using wordTrace_append hprefix tailTrace_152348
  have hstable : (prefixWord ++ tailWord_152348).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_152348).length < 2 ^ (prefixWord ++ tailWord_152348).sum := by decide
  have hdescent : baseEnd_152348 < baseStart_152348 := by decide
  rcases family_descends (prefixWord ++ tailWord_152348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_152365 : List Nat := [1, 5, 3, 2, 1, 1, 8]
def baseStart_152365 : Nat := 118140960795 + 152365 * 2 ^ 59
def prefixEnd_152365 : Nat := 4983230072969 + 3 ^ 40 * 152365 * 2
def baseEnd_152365 : Nat := 3863529872711190367249

theorem tailTrace_152365 : CollatzResearch.WordTrace tailWord_152365 prefixEnd_152365 3863529872711190367249 := by
  unfold tailWord_152365
  simp only [CollatzResearch.WordTrace]
  refine ⟨5557208093015101715402549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3704805395343401143601699 5557208093015101715402549)
  ·
    refine ⟨520988258720165785818989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 5557208093015101715402549 520988258720165785818989)
    ·
      refine ⟨195370597020062169682121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 520988258720165785818989 195370597020062169682121)
      ·
        refine ⟨146527947765046627261591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 195370597020062169682121 146527947765046627261591)
        ·
          refine ⟨219791921647569940892387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 146527947765046627261591 219791921647569940892387)
          ·
            refine ⟨329687882471354911338581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 219791921647569940892387 329687882471354911338581)
            ·
              refine ⟨3863529872711190367249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 329687882471354911338581 3863529872711190367249)
              ·
                rfl

theorem cell21_152365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 1, 8].length) (baseStart_152365 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_152365 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_152365 prefixEnd_152365 := by exact prefixLift 152365
  have htrace : WordTrace (prefixWord ++ tailWord_152365) baseStart_152365 baseEnd_152365 := by
    simpa [prefixWord, tailWord_152365, baseEnd_152365] using wordTrace_append hprefix tailTrace_152365
  have hstable : (prefixWord ++ tailWord_152365).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_152365).length < 2 ^ (prefixWord ++ tailWord_152365).sum := by decide
  have hdescent : baseEnd_152365 < baseStart_152365 := by decide
  rcases family_descends (prefixWord ++ tailWord_152365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_152376 : List Nat := [2, 1, 2, 1, 3, 2, 3, 1, 6]
def baseStart_152376 : Nat := 118140960795 + 152376 * 2 ^ 59
def prefixEnd_152376 : Nat := 4983230072969 + 3 ^ 40 * 152376 * 2
def baseEnd_152376 : Nat := 34774279204267138621885

theorem tailTrace_152376 : CollatzResearch.WordTrace tailWord_152376 prefixEnd_152376 34774279204267138621885 := by
  unfold tailWord_152376
  simp only [CollatzResearch.WordTrace]
  refine ⟨2778804647987625297026491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3705072863983500396035321 2778804647987625297026491)
  ·
    refine ⟨4168206971981437945539737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2778804647987625297026491 4168206971981437945539737)
    ·
      refine ⟨3126155228986078459154803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4168206971981437945539737 3126155228986078459154803)
      ·
        refine ⟨4689232843479117688732205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3126155228986078459154803 4689232843479117688732205)
        ·
          refine ⟨1758462316304669133274577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4689232843479117688732205 1758462316304669133274577)
          ·
            refine ⟨1318846737228501849955933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1758462316304669133274577 1318846737228501849955933)
            ·
              refine ⟨494567526460688193733475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1318846737228501849955933 494567526460688193733475)
              ·
                refine ⟨741851289691032290600213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 494567526460688193733475 741851289691032290600213)
                ·
                  refine ⟨34774279204267138621885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 741851289691032290600213 34774279204267138621885)
                  ·
                    rfl

theorem cell21_152376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 3, 1, 6].length) (baseStart_152376 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_152376 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_152376 prefixEnd_152376 := by exact prefixLift 152376
  have htrace : WordTrace (prefixWord ++ tailWord_152376) baseStart_152376 baseEnd_152376 := by
    simpa [prefixWord, tailWord_152376, baseEnd_152376] using wordTrace_append hprefix tailTrace_152376
  have hstable : (prefixWord ++ tailWord_152376).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_152376).length < 2 ^ (prefixWord ++ tailWord_152376).sum := by decide
  have hdescent : baseEnd_152376 < baseStart_152376 := by decide
  rcases family_descends (prefixWord ++ tailWord_152376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_152407 : List Nat := [1, 1, 3, 2, 4, 2, 1, 7]
def baseStart_152407 : Nat := 118140960795 + 152407 * 2 ^ 59
def prefixEnd_152407 : Nat := 4983230072969 + 3 ^ 40 * 152407 * 2
def baseEnd_152407 : Nat := 11593784608872657868385

theorem tailTrace_152407 : CollatzResearch.WordTrace tailWord_152407 prefixEnd_152407 11593784608872657868385 := by
  unfold tailWord_152407
  simp only [CollatzResearch.WordTrace]
  refine ⟨5558739958862942888431475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3705826639241961925620983 5558739958862942888431475)
  ·
    refine ⟨8338109938294414332647213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5558739958862942888431475 8338109938294414332647213)
    ·
      refine ⟨3126791226860405374742705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8338109938294414332647213 3126791226860405374742705)
      ·
        refine ⟨2345093420145304031057029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3126791226860405374742705 2345093420145304031057029)
        ·
          refine ⟨439705016277244505823193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2345093420145304031057029 439705016277244505823193)
          ·
            refine ⟨329778762207933379367395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 439705016277244505823193 329778762207933379367395)
            ·
              refine ⟨494668143311900069051093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 329778762207933379367395 494668143311900069051093)
              ·
                refine ⟨11593784608872657868385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 494668143311900069051093 11593784608872657868385)
                ·
                  rfl

theorem cell21_152407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 2, 1, 7].length) (baseStart_152407 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_152407 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_152407 prefixEnd_152407 := by exact prefixLift 152407
  have htrace : WordTrace (prefixWord ++ tailWord_152407) baseStart_152407 baseEnd_152407 := by
    simpa [prefixWord, tailWord_152407, baseEnd_152407] using wordTrace_append hprefix tailTrace_152407
  have hstable : (prefixWord ++ tailWord_152407).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_152407).length < 2 ^ (prefixWord ++ tailWord_152407).sum := by decide
  have hdescent : baseEnd_152407 < baseStart_152407 := by decide
  rcases family_descends (prefixWord ++ tailWord_152407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_152421 : List Nat := [1, 3, 1, 3, 1, 1, 2, 2, 7]
def baseStart_152421 : Nat := 118140960795 + 152421 * 2 ^ 59
def prefixEnd_152421 : Nat := 4983230072969 + 3 ^ 40 * 152421 * 2
def baseEnd_152421 : Nat := 34784548817357060371793

theorem tailTrace_152421 : CollatzResearch.WordTrace tailWord_152421 prefixEnd_152421 34784548817357060371793 := by
  unfold tailWord_152421
  simp only [CollatzResearch.WordTrace]
  refine ⟨5559250580812223279441117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3706167053874815519627411 5559250580812223279441117)
  ·
    refine ⟨2084718967804583729790419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5559250580812223279441117 2084718967804583729790419)
    ·
      refine ⟨3127078451706875594685629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2084718967804583729790419 3127078451706875594685629)
      ·
        refine ⟨1172654419390078348007111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3127078451706875594685629 1172654419390078348007111)
        ·
          refine ⟨1758981629085117522010667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1172654419390078348007111 1758981629085117522010667)
          ·
            refine ⟨2638472443627676283016001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1758981629085117522010667 2638472443627676283016001)
            ·
              refine ⟨1978854332720757212262001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2638472443627676283016001 1978854332720757212262001)
              ·
                refine ⟨1484140749540567909196501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1978854332720757212262001 1484140749540567909196501)
                ·
                  refine ⟨34784548817357060371793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1484140749540567909196501 34784548817357060371793)
                  ·
                    rfl

theorem cell21_152421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 2, 2, 7].length) (baseStart_152421 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_152421 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_152421 prefixEnd_152421 := by exact prefixLift 152421
  have htrace : WordTrace (prefixWord ++ tailWord_152421) baseStart_152421 baseEnd_152421 := by
    simpa [prefixWord, tailWord_152421, baseEnd_152421] using wordTrace_append hprefix tailTrace_152421
  have hstable : (prefixWord ++ tailWord_152421).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_152421).length < 2 ^ (prefixWord ++ tailWord_152421).sum := by decide
  have hdescent : baseEnd_152421 < baseStart_152421 := by decide
  rcases family_descends (prefixWord ++ tailWord_152421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_152669 : List Nat := [1, 4, 4, 1, 2, 2, 1, 6]
def baseStart_152669 : Nat := 118140960795 + 152669 * 2 ^ 59
def prefixEnd_152669 : Nat := 4983230072969 + 3 ^ 40 * 152669 * 2
def baseEnd_152669 : Nat := 11613715265387913412651

theorem tailTrace_152669 : CollatzResearch.WordTrace tailWord_152669 prefixEnd_152669 11613715265387913412651 := by
  unfold tailWord_152669
  simp only [CollatzResearch.WordTrace]
  refine ⟨5568295883913761634469061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3712197255942507756312707 5568295883913761634469061)
  ·
    refine ⟨1044055478233830306462949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5568295883913761634469061 1044055478233830306462949)
    ·
      refine ⟨195760402168843182461803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1044055478233830306462949 195760402168843182461803)
      ·
        refine ⟨293640603253264773692705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 195760402168843182461803 293640603253264773692705)
        ·
          refine ⟨220230452439948580269529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 293640603253264773692705 220230452439948580269529)
          ·
            refine ⟨165172839329961435202147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 220230452439948580269529 165172839329961435202147)
            ·
              refine ⟨247759258994942152803221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 165172839329961435202147 247759258994942152803221)
              ·
                refine ⟨11613715265387913412651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 247759258994942152803221 11613715265387913412651)
                ·
                  rfl

theorem cell21_152669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 2, 1, 6].length) (baseStart_152669 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_152669 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_152669 prefixEnd_152669 := by exact prefixLift 152669
  have htrace : WordTrace (prefixWord ++ tailWord_152669) baseStart_152669 baseEnd_152669 := by
    simpa [prefixWord, tailWord_152669, baseEnd_152669] using wordTrace_append hprefix tailTrace_152669
  have hstable : (prefixWord ++ tailWord_152669).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_152669).length < 2 ^ (prefixWord ++ tailWord_152669).sum := by decide
  have hdescent : baseEnd_152669 < baseStart_152669 := by decide
  rcases family_descends (prefixWord ++ tailWord_152669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_152835 : List Nat := [1, 1, 1, 3, 2, 4, 4, 2, 3]
def baseStart_152835 : Nat := 118140960795 + 152835 * 2 ^ 59
def prefixEnd_152835 : Nat := 4983230072969 + 3 ^ 40 * 152835 * 2
def baseEnd_152835 : Nat := 34879029257784340470947

theorem tailTrace_152835 : CollatzResearch.WordTrace tailWord_152835 prefixEnd_152835 34879029257784340470947 := by
  unfold tailWord_152835
  simp only [CollatzResearch.WordTrace]
  refine ⟨5574350401312371985011959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3716233600874914656674639 5574350401312371985011959)
  ·
    refine ⟨8361525601968557977517939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5574350401312371985011959 8361525601968557977517939)
    ·
      refine ⟨12542288402952836966276909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8361525601968557977517939 12542288402952836966276909)
      ·
        refine ⟨4703358151107313862353841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12542288402952836966276909 4703358151107313862353841)
        ·
          refine ⟨3527518613330485396765381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4703358151107313862353841 3527518613330485396765381)
          ·
            refine ⟨661409739999466011893509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3527518613330485396765381 661409739999466011893509)
            ·
              refine ⟨124014326249899877230033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 661409739999466011893509 124014326249899877230033)
              ·
                refine ⟨93010744687424907922525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 124014326249899877230033 93010744687424907922525)
                ·
                  refine ⟨34879029257784340470947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 93010744687424907922525 34879029257784340470947)
                  ·
                    rfl

theorem cell21_152835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 4, 2, 3].length) (baseStart_152835 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_152835 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_152835 prefixEnd_152835 := by exact prefixLift 152835
  have htrace : WordTrace (prefixWord ++ tailWord_152835) baseStart_152835 baseEnd_152835 := by
    simpa [prefixWord, tailWord_152835, baseEnd_152835] using wordTrace_append hprefix tailTrace_152835
  have hstable : (prefixWord ++ tailWord_152835).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_152835).length < 2 ^ (prefixWord ++ tailWord_152835).sum := by decide
  have hdescent : baseEnd_152835 < baseStart_152835 := by decide
  rcases family_descends (prefixWord ++ tailWord_152835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_152894 : List Nat := [4, 2, 1, 2, 1, 1, 4, 1, 5]
def baseStart_152894 : Nat := 118140960795 + 152894 * 2 ^ 59
def prefixEnd_152894 : Nat := 4983230072969 + 3 ^ 40 * 152894 * 2
def baseEnd_152894 : Nat := 34892493861613348987493

theorem tailTrace_152894 : CollatzResearch.WordTrace tailWord_152894 prefixEnd_152894 34892493861613348987493 := by
  unfold tailWord_152894
  simp only [CollatzResearch.WordTrace]
  refine ⟨697062788512328132676217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3717668205399083374273157 697062788512328132676217)
  ·
    refine ⟨522797091384246099507163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 697062788512328132676217 522797091384246099507163)
    ·
      refine ⟨784195637076369149260745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 522797091384246099507163 784195637076369149260745)
      ·
        refine ⟨588146727807276861945559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 784195637076369149260745 588146727807276861945559)
        ·
          refine ⟨882220091710915292918339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 588146727807276861945559 882220091710915292918339)
          ·
            refine ⟨1323330137566372939377509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 882220091710915292918339 1323330137566372939377509)
            ·
              refine ⟨248124400793694926133283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1323330137566372939377509 248124400793694926133283)
              ·
                refine ⟨372186601190542389199925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 248124400793694926133283 372186601190542389199925)
                ·
                  refine ⟨34892493861613348987493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 372186601190542389199925 34892493861613348987493)
                  ·
                    rfl

theorem cell21_152894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 4, 1, 5].length) (baseStart_152894 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_152894 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_152894 prefixEnd_152894 := by exact prefixLift 152894
  have htrace : WordTrace (prefixWord ++ tailWord_152894) baseStart_152894 baseEnd_152894 := by
    simpa [prefixWord, tailWord_152894, baseEnd_152894] using wordTrace_append hprefix tailTrace_152894
  have hstable : (prefixWord ++ tailWord_152894).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_152894).length < 2 ^ (prefixWord ++ tailWord_152894).sum := by decide
  have hdescent : baseEnd_152894 < baseStart_152894 := by decide
  rcases family_descends (prefixWord ++ tailWord_152894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_152953 : List Nat := [1, 2, 1, 3, 2, 1, 5, 1, 5]
def baseStart_152953 : Nat := 118140960795 + 152953 * 2 ^ 59
def prefixEnd_152953 : Nat := 4983230072969 + 3 ^ 40 * 152953 * 2
def baseEnd_152953 : Nat := 34905958465442357504039

theorem tailTrace_152953 : CollatzResearch.WordTrace tailWord_152953 prefixEnd_152953 34905958465442357504039 := by
  unfold tailWord_152953
  simp only [CollatzResearch.WordTrace]
  refine ⟨5578654214884878137807513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3719102809923252091871675 5578654214884878137807513)
  ·
    refine ⟨4183990661163658603355635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5578654214884878137807513 4183990661163658603355635)
    ·
      refine ⟨6275985991745487905033453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4183990661163658603355635 6275985991745487905033453)
      ·
        refine ⟨2353494746904557964387545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6275985991745487905033453 2353494746904557964387545)
        ·
          refine ⟨1765121060178418473290659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2353494746904557964387545 1765121060178418473290659)
          ·
            refine ⟨2647681590267627709935989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1765121060178418473290659 2647681590267627709935989)
            ·
              refine ⟨248220149087590097806499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2647681590267627709935989 248220149087590097806499)
              ·
                refine ⟨372330223631385146709749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 248220149087590097806499 372330223631385146709749)
                ·
                  refine ⟨34905958465442357504039, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 372330223631385146709749 34905958465442357504039)
                  ·
                    rfl

theorem cell21_152953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 5, 1, 5].length) (baseStart_152953 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_152953 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_152953 prefixEnd_152953 := by exact prefixLift 152953
  have htrace : WordTrace (prefixWord ++ tailWord_152953) baseStart_152953 baseEnd_152953 := by
    simpa [prefixWord, tailWord_152953, baseEnd_152953] using wordTrace_append hprefix tailTrace_152953
  have hstable : (prefixWord ++ tailWord_152953).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_152953).length < 2 ^ (prefixWord ++ tailWord_152953).sum := by decide
  have hdescent : baseEnd_152953 < baseStart_152953 := by decide
  rcases family_descends (prefixWord ++ tailWord_152953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_153108 : List Nat := [2, 4, 3, 1, 2, 2, 7]
def baseStart_153108 : Nat := 118140960795 + 153108 * 2 ^ 59
def prefixEnd_153108 : Nat := 4983230072969 + 3 ^ 40 * 153108 * 2
def baseEnd_153108 : Nat := 3882370175244059157821

theorem tailTrace_153108 : CollatzResearch.WordTrace tailWord_153108 prefixEnd_153108 3882370175244059157821 := by
  unfold tailWord_153108
  simp only [CollatzResearch.WordTrace]
  refine ⟨2792153764661669804849989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3722871686215559739799985 2792153764661669804849989)
  ·
    refine ⟨523528830874063088409373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2792153764661669804849989 523528830874063088409373)
    ·
      refine ⟨196323311577773658153515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 523528830874063088409373 196323311577773658153515)
      ·
        refine ⟨294484967366660487230273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 196323311577773658153515 294484967366660487230273)
        ·
          refine ⟨220863725524995365422705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 294484967366660487230273 220863725524995365422705)
          ·
            refine ⟨165647794143746524067029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 220863725524995365422705 165647794143746524067029)
            ·
              refine ⟨3882370175244059157821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 165647794143746524067029 3882370175244059157821)
              ·
                rfl

theorem cell21_153108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 2, 7].length) (baseStart_153108 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_153108 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_153108 prefixEnd_153108 := by exact prefixLift 153108
  have htrace : WordTrace (prefixWord ++ tailWord_153108) baseStart_153108 baseEnd_153108 := by
    simpa [prefixWord, tailWord_153108, baseEnd_153108] using wordTrace_append hprefix tailTrace_153108
  have hstable : (prefixWord ++ tailWord_153108).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_153108).length < 2 ^ (prefixWord ++ tailWord_153108).sum := by decide
  have hdescent : baseEnd_153108 < baseStart_153108 := by decide
  rcases family_descends (prefixWord ++ tailWord_153108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_153119 : List Nat := [1, 1, 2, 4, 1, 1, 4, 1, 6]
def baseStart_153119 : Nat := 118140960795 + 153119 * 2 ^ 59
def prefixEnd_153119 : Nat := 4983230072969 + 3 ^ 40 * 153119 * 2
def baseEnd_153119 : Nat := 34943841927062957737033

theorem tailTrace_153119 : CollatzResearch.WordTrace tailWord_153119 prefixEnd_153119 34943841927062957737033 := by
  unfold tailWord_153119
  simp only [CollatzResearch.WordTrace]
  refine ⟨5584708732283488488350411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3723139154855658992233607 5584708732283488488350411)
  ·
    refine ⟨8377063098425232732525617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5584708732283488488350411 8377063098425232732525617)
    ·
      refine ⟨6282797323818924549394213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8377063098425232732525617 6282797323818924549394213)
      ·
        refine ⟨1178024498216048353011415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6282797323818924549394213 1178024498216048353011415)
        ·
          refine ⟨1767036747324072529517123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1178024498216048353011415 1767036747324072529517123)
          ·
            refine ⟨2650555120986108794275685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1767036747324072529517123 2650555120986108794275685)
            ·
              refine ⟨496979085184895398926691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2650555120986108794275685 496979085184895398926691)
              ·
                refine ⟨745468627777343098390037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 496979085184895398926691 745468627777343098390037)
                ·
                  refine ⟨34943841927062957737033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 745468627777343098390037 34943841927062957737033)
                  ·
                    rfl

theorem cell21_153119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 4, 1, 6].length) (baseStart_153119 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_153119 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_153119 prefixEnd_153119 := by exact prefixLift 153119
  have htrace : WordTrace (prefixWord ++ tailWord_153119) baseStart_153119 baseEnd_153119 := by
    simpa [prefixWord, tailWord_153119, baseEnd_153119] using wordTrace_append hprefix tailTrace_153119
  have hstable : (prefixWord ++ tailWord_153119).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_153119).length < 2 ^ (prefixWord ++ tailWord_153119).sum := by decide
  have hdescent : baseEnd_153119 < baseStart_153119 := by decide
  rcases family_descends (prefixWord ++ tailWord_153119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_153122 : List Nat := [3, 3, 1, 1, 1, 1, 2, 6, 3]
def baseStart_153122 : Nat := 118140960795 + 153122 * 2 ^ 59
def prefixEnd_153122 : Nat := 4983230072969 + 3 ^ 40 * 153122 * 2
def baseEnd_153122 : Nat := 34944526567935619187027

theorem tailTrace_153122 : CollatzResearch.WordTrace tailWord_153122 prefixEnd_153122 34944526567935619187027 := by
  unfold tailWord_153122
  simp only [CollatzResearch.WordTrace]
  refine ⟨1396204537818155000177405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3723212100848413333806413 1396204537818155000177405)
  ·
    refine ⟨523576701681808125066527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1396204537818155000177405 523576701681808125066527)
    ·
      refine ⟨785365052522712187599791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 523576701681808125066527 785365052522712187599791)
      ·
        refine ⟨1178047578784068281399687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 785365052522712187599791 1178047578784068281399687)
        ·
          refine ⟨1767071368176102422099531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1178047578784068281399687 1767071368176102422099531)
          ·
            refine ⟨2650607052264153633149297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1767071368176102422099531 2650607052264153633149297)
            ·
              refine ⟨1987955289198115224861973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2650607052264153633149297 1987955289198115224861973)
              ·
                refine ⟨93185404181161651165405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1987955289198115224861973 93185404181161651165405)
                ·
                  refine ⟨34944526567935619187027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 93185404181161651165405 34944526567935619187027)
                  ·
                    rfl

theorem cell21_153122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 2, 6, 3].length) (baseStart_153122 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_153122 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_153122 prefixEnd_153122 := by exact prefixLift 153122
  have htrace : WordTrace (prefixWord ++ tailWord_153122) baseStart_153122 baseEnd_153122 := by
    simpa [prefixWord, tailWord_153122, baseEnd_153122] using wordTrace_append hprefix tailTrace_153122
  have hstable : (prefixWord ++ tailWord_153122).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_153122).length < 2 ^ (prefixWord ++ tailWord_153122).sum := by decide
  have hdescent : baseEnd_153122 < baseStart_153122 := by decide
  rcases family_descends (prefixWord ++ tailWord_153122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_153198 : List Nat := [4, 1, 2, 2, 3, 1, 1, 2, 5]
def baseStart_153198 : Nat := 118140960795 + 153198 * 2 ^ 59
def prefixEnd_153198 : Nat := 4983230072969 + 3 ^ 40 * 153198 * 2
def baseEnd_153198 : Nat := 34961870803376375920205

theorem tailTrace_153198 : CollatzResearch.WordTrace tailWord_153198 prefixEnd_153198 34961870803376375920205 := by
  unfold tailWord_153198
  simp only [CollatzResearch.WordTrace]
  refine ⟨698448762374660622559531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3725060065998189986984165 698448762374660622559531)
  ·
    refine ⟨1047673143561990933839297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 698448762374660622559531 1047673143561990933839297)
    ·
      refine ⟨785754857671493200379473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1047673143561990933839297 785754857671493200379473)
      ·
        refine ⟨589316143253619900284605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 785754857671493200379473 589316143253619900284605)
        ·
          refine ⟨220993553720107462606727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 589316143253619900284605 220993553720107462606727)
          ·
            refine ⟨331490330580161193910091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 220993553720107462606727 331490330580161193910091)
            ·
              refine ⟨497235495870241790865137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 331490330580161193910091 497235495870241790865137)
              ·
                refine ⟨372926621902681343148853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 497235495870241790865137 372926621902681343148853)
                ·
                  refine ⟨34961870803376375920205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 372926621902681343148853 34961870803376375920205)
                  ·
                    rfl

theorem cell21_153198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 1, 1, 2, 5].length) (baseStart_153198 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_153198 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_153198 prefixEnd_153198 := by exact prefixLift 153198
  have htrace : WordTrace (prefixWord ++ tailWord_153198) baseStart_153198 baseEnd_153198 := by
    simpa [prefixWord, tailWord_153198, baseEnd_153198] using wordTrace_append hprefix tailTrace_153198
  have hstable : (prefixWord ++ tailWord_153198).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_153198).length < 2 ^ (prefixWord ++ tailWord_153198).sum := by decide
  have hdescent : baseEnd_153198 < baseStart_153198 := by decide
  rcases family_descends (prefixWord ++ tailWord_153198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_153226 : List Nat := [3, 1, 2, 3, 2, 2, 8]
def baseStart_153226 : Nat := 118140960795 + 153226 * 2 ^ 59
def prefixEnd_153226 : Nat := 4983230072969 + 3 ^ 40 * 153226 * 2
def baseEnd_153226 : Nat := 3885362309428283272609

theorem tailTrace_153226 : CollatzResearch.WordTrace tailWord_153226 prefixEnd_153226 3885362309428283272609 := by
  unfold tailWord_153226
  simp only [CollatzResearch.WordTrace]
  refine ⟨1397152835723961440623883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3725740895263897174997021 1397152835723961440623883)
  ·
    refine ⟨2095729253585942160935825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1397152835723961440623883 2095729253585942160935825)
    ·
      refine ⟨1571796940189456620701869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2095729253585942160935825 1571796940189456620701869)
      ·
        refine ⟨589423852571046232763201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1571796940189456620701869 589423852571046232763201)
        ·
          refine ⟨442067889428284674572401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 589423852571046232763201 442067889428284674572401)
          ·
            refine ⟨331550917071213505929301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 442067889428284674572401 331550917071213505929301)
            ·
              refine ⟨3885362309428283272609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 331550917071213505929301 3885362309428283272609)
              ·
                rfl

theorem cell21_153226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 2, 8].length) (baseStart_153226 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_153226 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_153226 prefixEnd_153226 := by exact prefixLift 153226
  have htrace : WordTrace (prefixWord ++ tailWord_153226) baseStart_153226 baseEnd_153226 := by
    simpa [prefixWord, tailWord_153226, baseEnd_153226] using wordTrace_append hprefix tailTrace_153226
  have hstable : (prefixWord ++ tailWord_153226).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_153226).length < 2 ^ (prefixWord ++ tailWord_153226).sum := by decide
  have hdescent : baseEnd_153226 < baseStart_153226 := by decide
  rcases family_descends (prefixWord ++ tailWord_153226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_153246 : List Nat := [4, 3, 1, 1, 1, 3, 3, 1, 4]
def baseStart_153246 : Nat := 118140960795 + 153246 * 2 ^ 59
def prefixEnd_153246 : Nat := 4983230072969 + 3 ^ 40 * 153246 * 2
def baseEnd_153246 : Nat := 34972825057338959120107

theorem tailTrace_153246 : CollatzResearch.WordTrace tailWord_153246 prefixEnd_153246 34972825057338959120107 := by
  unfold tailWord_153246
  simp only [CollatzResearch.WordTrace]
  refine ⟨698667600352923647277949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3726227201882259452149061 698667600352923647277949)
  ·
    refine ⟨262000350132346367729231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 698667600352923647277949 262000350132346367729231)
    ·
      refine ⟨393000525198519551593847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 262000350132346367729231 393000525198519551593847)
      ·
        refine ⟨589500787797779327390771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 393000525198519551593847 589500787797779327390771)
        ·
          refine ⟨884251181696668991086157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 589500787797779327390771 884251181696668991086157)
          ·
            refine ⟨331594193136250871657309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 884251181696668991086157 331594193136250871657309)
            ·
              refine ⟨124347822426094076871491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 331594193136250871657309 124347822426094076871491)
              ·
                refine ⟨186521733639141115307237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 124347822426094076871491 186521733639141115307237)
                ·
                  refine ⟨34972825057338959120107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 186521733639141115307237 34972825057338959120107)
                  ·
                    rfl

theorem cell21_153246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 3, 3, 1, 4].length) (baseStart_153246 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_153246 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_153246 prefixEnd_153246 := by exact prefixLift 153246
  have htrace : WordTrace (prefixWord ++ tailWord_153246) baseStart_153246 baseEnd_153246 := by
    simpa [prefixWord, tailWord_153246, baseEnd_153246] using wordTrace_append hprefix tailTrace_153246
  have hstable : (prefixWord ++ tailWord_153246).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_153246).length < 2 ^ (prefixWord ++ tailWord_153246).sum := by decide
  have hdescent : baseEnd_153246 < baseStart_153246 := by decide
  rcases family_descends (prefixWord ++ tailWord_153246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_153271 : List Nat := [1, 1, 3, 1, 5, 1, 1, 2, 6]
def baseStart_153271 : Nat := 118140960795 + 153271 * 2 ^ 59
def prefixEnd_153271 : Nat := 4983230072969 + 3 ^ 40 * 153271 * 2
def baseEnd_153271 : Nat := 34978530397944471203389

theorem tailTrace_153271 : CollatzResearch.WordTrace tailWord_153271 prefixEnd_153271 34978530397944471203389 := by
  unfold tailWord_153271
  simp only [CollatzResearch.WordTrace]
  refine ⟨5590252627732818447883667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3726835085155212298589111 5590252627732818447883667)
  ·
    refine ⟨8385378941599227671825501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5590252627732818447883667 8385378941599227671825501)
    ·
      refine ⟨3144517103099710376934563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8385378941599227671825501 3144517103099710376934563)
      ·
        refine ⟨4716775654649565565401845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3144517103099710376934563 4716775654649565565401845)
        ·
          refine ⟨442197717623396771756423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 4716775654649565565401845 442197717623396771756423)
          ·
            refine ⟨663296576435095157634635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 442197717623396771756423 663296576435095157634635)
            ·
              refine ⟨994944864652642736451953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 663296576435095157634635 994944864652642736451953)
              ·
                refine ⟨746208648489482052338965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 994944864652642736451953 746208648489482052338965)
                ·
                  refine ⟨34978530397944471203389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 746208648489482052338965 34978530397944471203389)
                  ·
                    rfl

theorem cell21_153271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 1, 2, 6].length) (baseStart_153271 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_153271 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_153271 prefixEnd_153271 := by exact prefixLift 153271
  have htrace : WordTrace (prefixWord ++ tailWord_153271) baseStart_153271 baseEnd_153271 := by
    simpa [prefixWord, tailWord_153271, baseEnd_153271] using wordTrace_append hprefix tailTrace_153271
  have hstable : (prefixWord ++ tailWord_153271).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_153271).length < 2 ^ (prefixWord ++ tailWord_153271).sum := by decide
  have hdescent : baseEnd_153271 < baseStart_153271 := by decide
  rcases family_descends (prefixWord ++ tailWord_153271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_153274 : List Nat := [3, 1, 1, 1, 2, 4, 3, 3, 3]
def baseStart_153274 : Nat := 118140960795 + 153274 * 2 ^ 59
def prefixEnd_153274 : Nat := 4983230072969 + 3 ^ 40 * 153274 * 2
def baseEnd_153274 : Nat := 34979215038817132653383

theorem tailTrace_153274 : CollatzResearch.WordTrace tailWord_153274 prefixEnd_153274 34979215038817132653383 := by
  unfold tailWord_153274
  simp only [CollatzResearch.WordTrace]
  refine ⟨1397590511680487490060719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3726908031147966640161917 1397590511680487490060719)
  ·
    refine ⟨2096385767520731235091079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1397590511680487490060719 2096385767520731235091079)
    ·
      refine ⟨3144578651281096852636619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2096385767520731235091079 3144578651281096852636619)
      ·
        refine ⟨4716867976921645278954929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3144578651281096852636619 4716867976921645278954929)
        ·
          refine ⟨3537650982691233959216197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4716867976921645278954929 3537650982691233959216197)
          ·
            refine ⟨663309559254606367353037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3537650982691233959216197 663309559254606367353037)
            ·
              refine ⟨248741084720477387757389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 663309559254606367353037 248741084720477387757389)
              ·
                refine ⟨93277906770179020409021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 248741084720477387757389 93277906770179020409021)
                ·
                  refine ⟨34979215038817132653383, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 93277906770179020409021 34979215038817132653383)
                  ·
                    rfl

theorem cell21_153274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 3, 3, 3].length) (baseStart_153274 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_153274 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_153274 prefixEnd_153274 := by exact prefixLift 153274
  have htrace : WordTrace (prefixWord ++ tailWord_153274) baseStart_153274 baseEnd_153274 := by
    simpa [prefixWord, tailWord_153274, baseEnd_153274] using wordTrace_append hprefix tailTrace_153274
  have hstable : (prefixWord ++ tailWord_153274).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_153274).length < 2 ^ (prefixWord ++ tailWord_153274).sum := by decide
  have hdescent : baseEnd_153274 < baseStart_153274 := by decide
  rcases family_descends (prefixWord ++ tailWord_153274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_153305 : List Nat := [1, 2, 1, 2, 3, 5, 2, 1, 4]
def baseStart_153305 : Nat := 118140960795 + 153305 * 2 ^ 59
def prefixEnd_153305 : Nat := 4983230072969 + 3 ^ 40 * 153305 * 2
def baseEnd_153305 : Nat := 34986289661167967636653

theorem tailTrace_153305 : CollatzResearch.WordTrace tailWord_153305 prefixEnd_153305 34986289661167967636653 := by
  unfold tailWord_153305
  simp only [CollatzResearch.WordTrace]
  refine ⟨5591492709609642254621369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3727661806406428169747579 5591492709609642254621369)
  ·
    refine ⟨4193619532207231690966027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5591492709609642254621369 4193619532207231690966027)
    ·
      refine ⟨6290429298310847536449041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4193619532207231690966027 6290429298310847536449041)
      ·
        refine ⟨4717821973733135652336781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6290429298310847536449041 4717821973733135652336781)
        ·
          refine ⟨1769183240149925869626293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4717821973733135652336781 1769183240149925869626293)
          ·
            refine ⟨165860928764055550277465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1769183240149925869626293 165860928764055550277465)
            ·
              refine ⟨124395696573041662708099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 165860928764055550277465 124395696573041662708099)
              ·
                refine ⟨186593544859562494062149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 124395696573041662708099 186593544859562494062149)
                ·
                  refine ⟨34986289661167967636653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 186593544859562494062149 34986289661167967636653)
                  ·
                    rfl

theorem cell21_153305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 5, 2, 1, 4].length) (baseStart_153305 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_153305 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_153305 prefixEnd_153305 := by exact prefixLift 153305
  have htrace : WordTrace (prefixWord ++ tailWord_153305) baseStart_153305 baseEnd_153305 := by
    simpa [prefixWord, tailWord_153305, baseEnd_153305] using wordTrace_append hprefix tailTrace_153305
  have hstable : (prefixWord ++ tailWord_153305).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_153305).length < 2 ^ (prefixWord ++ tailWord_153305).sum := by decide
  have hdescent : baseEnd_153305 < baseStart_153305 := by decide
  rcases family_descends (prefixWord ++ tailWord_153305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_153316 : List Nat := [2, 3, 1, 1, 1, 3, 2, 1, 7]
def baseStart_153316 : Nat := 118140960795 + 153316 * 2 ^ 59
def prefixEnd_153316 : Nat := 4983230072969 + 3 ^ 40 * 153316 * 2
def baseEnd_153316 : Nat := 34988800011034392953297

theorem tailTrace_153316 : CollatzResearch.WordTrace tailWord_153316 prefixEnd_153316 34988800011034392953297 := by
  unfold tailWord_153316
  simp only [CollatzResearch.WordTrace]
  refine ⟨2795946956284895566635901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3727929275046527422181201 2795946956284895566635901)
  ·
    refine ⟨1048480108606835837488463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2795946956284895566635901 1048480108606835837488463)
    ·
      refine ⟨1572720162910253756232695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1048480108606835837488463 1572720162910253756232695)
      ·
        refine ⟨2359080244365380634349043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1572720162910253756232695 2359080244365380634349043)
        ·
          refine ⟨3538620366548070951523565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2359080244365380634349043 3538620366548070951523565)
          ·
            refine ⟨1326982637455526606821337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3538620366548070951523565 1326982637455526606821337)
            ·
              refine ⟨995236978091644955116003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1326982637455526606821337 995236978091644955116003)
              ·
                refine ⟨1492855467137467432674005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 995236978091644955116003 1492855467137467432674005)
                ·
                  refine ⟨34988800011034392953297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1492855467137467432674005 34988800011034392953297)
                  ·
                    rfl

theorem cell21_153316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 2, 1, 7].length) (baseStart_153316 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_153316 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_153316 prefixEnd_153316 := by exact prefixLift 153316
  have htrace : WordTrace (prefixWord ++ tailWord_153316) baseStart_153316 baseEnd_153316 := by
    simpa [prefixWord, tailWord_153316, baseEnd_153316] using wordTrace_append hprefix tailTrace_153316
  have hstable : (prefixWord ++ tailWord_153316).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_153316).length < 2 ^ (prefixWord ++ tailWord_153316).sum := by decide
  have hdescent : baseEnd_153316 < baseStart_153316 := by decide
  rcases family_descends (prefixWord ++ tailWord_153316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_153347 : List Nat := [1, 1, 1, 3, 2, 2, 3, 4, 4]
def baseStart_153347 : Nat := 118140960795 + 153347 * 2 ^ 59
def prefixEnd_153347 : Nat := 4983230072969 + 3 ^ 40 * 153347 * 2
def baseEnd_153347 : Nat := 34995874633385227936567

theorem tailTrace_153347 : CollatzResearch.WordTrace tailWord_153347 prefixEnd_153347 34995874633385227936567 := by
  unfold tailWord_153347
  simp only [CollatzResearch.WordTrace]
  refine ⟨5593024575457483427650295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3728683050304988951766863 5593024575457483427650295)
  ·
    refine ⟨8389536863186225141475443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5593024575457483427650295 8389536863186225141475443)
    ·
      refine ⟨12584305294779337712213165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8389536863186225141475443 12584305294779337712213165)
      ·
        refine ⟨4719114485542251642079937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12584305294779337712213165 4719114485542251642079937)
        ·
          refine ⟨3539335864156688731559953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4719114485542251642079937 3539335864156688731559953)
          ·
            refine ⟨2654501898117516548669965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3539335864156688731559953 2654501898117516548669965)
            ·
              refine ⟨995438211794068705751237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2654501898117516548669965 995438211794068705751237)
              ·
                refine ⟨186644664711387882328357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 995438211794068705751237 186644664711387882328357)
                ·
                  refine ⟨34995874633385227936567, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 186644664711387882328357 34995874633385227936567)
                  ·
                    rfl

theorem cell21_153347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 3, 4, 4].length) (baseStart_153347 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_153347 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_153347 prefixEnd_153347 := by exact prefixLift 153347
  have htrace : WordTrace (prefixWord ++ tailWord_153347) baseStart_153347 baseEnd_153347 := by
    simpa [prefixWord, tailWord_153347, baseEnd_153347] using wordTrace_append hprefix tailTrace_153347
  have hstable : (prefixWord ++ tailWord_153347).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_153347).length < 2 ^ (prefixWord ++ tailWord_153347).sum := by decide
  have hdescent : baseEnd_153347 < baseStart_153347 := by decide
  rcases family_descends (prefixWord ++ tailWord_153347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_153398 : List Nat := [5, 1, 2, 2, 1, 3, 1, 2, 4]
def baseStart_153398 : Nat := 118140960795 + 153398 * 2 ^ 59
def prefixEnd_153398 : Nat := 4983230072969 + 3 ^ 40 * 153398 * 2
def baseEnd_153398 : Nat := 35007513528220472586463

theorem tailTrace_153398 : CollatzResearch.WordTrace tailWord_153398 prefixEnd_153398 35007513528220472586463 := by
  unfold tailWord_153398
  simp only [CollatzResearch.WordTrace]
  refine ⟨349680293642044946109803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 3729923132181812758504565 349680293642044946109803)
  ·
    refine ⟨524520440463067419164705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 349680293642044946109803 524520440463067419164705)
    ·
      refine ⟨393390330347300564373529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 524520440463067419164705 393390330347300564373529)
      ·
        refine ⟨295042747760475423280147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 393390330347300564373529 295042747760475423280147)
        ·
          refine ⟨442564121640713134920221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 295042747760475423280147 442564121640713134920221)
          ·
            refine ⟨165961545615267425595083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 442564121640713134920221 165961545615267425595083)
            ·
              refine ⟨248942318422901138392625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 165961545615267425595083 248942318422901138392625)
              ·
                refine ⟨186706738817175853794469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 248942318422901138392625 186706738817175853794469)
                ·
                  refine ⟨35007513528220472586463, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 186706738817175853794469 35007513528220472586463)
                  ·
                    rfl

theorem cell21_153398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 3, 1, 2, 4].length) (baseStart_153398 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_153398 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_153398 prefixEnd_153398 := by exact prefixLift 153398
  have htrace : WordTrace (prefixWord ++ tailWord_153398) baseStart_153398 baseEnd_153398 := by
    simpa [prefixWord, tailWord_153398, baseEnd_153398] using wordTrace_append hprefix tailTrace_153398
  have hstable : (prefixWord ++ tailWord_153398).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_153398).length < 2 ^ (prefixWord ++ tailWord_153398).sum := by decide
  have hdescent : baseEnd_153398 < baseStart_153398 := by decide
  rcases family_descends (prefixWord ++ tailWord_153398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_153443 : List Nat := [1, 1, 1, 5, 4, 2, 1, 3, 3]
def baseStart_153443 : Nat := 118140960795 + 153443 * 2 ^ 59
def prefixEnd_153443 : Nat := 4983230072969 + 3 ^ 40 * 153443 * 2
def baseEnd_153443 : Nat := 35017783141310394336371

theorem tailTrace_153443 : CollatzResearch.WordTrace tailWord_153443 prefixEnd_153443 35017783141310394336371 := by
  unfold tailWord_153443
  simp only [CollatzResearch.WordTrace]
  refine ⟨5596525983109691823144983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3731017322073127882096655 5596525983109691823144983)
  ·
    refine ⟨8394788974664537734717475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5596525983109691823144983 8394788974664537734717475)
    ·
      refine ⟨12592183461996806602076213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8394788974664537734717475 12592183461996806602076213)
      ·
        refine ⟨1180517199562200618944645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 12592183461996806602076213 1180517199562200618944645)
        ·
          refine ⟨221346974917912616052121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1180517199562200618944645 221346974917912616052121)
          ·
            refine ⟨166010231188434462039091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 221346974917912616052121 166010231188434462039091)
            ·
              refine ⟨249015346782651693058637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 166010231188434462039091 249015346782651693058637)
              ·
                refine ⟨93380755043494384896989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 249015346782651693058637 93380755043494384896989)
                ·
                  refine ⟨35017783141310394336371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 93380755043494384896989 35017783141310394336371)
                  ·
                    rfl

theorem cell21_153443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 2, 1, 3, 3].length) (baseStart_153443 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_153443 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_153443 prefixEnd_153443 := by exact prefixLift 153443
  have htrace : WordTrace (prefixWord ++ tailWord_153443) baseStart_153443 baseEnd_153443 := by
    simpa [prefixWord, tailWord_153443, baseEnd_153443] using wordTrace_append hprefix tailTrace_153443
  have hstable : (prefixWord ++ tailWord_153443).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_153443).length < 2 ^ (prefixWord ++ tailWord_153443).sum := by decide
  have hdescent : baseEnd_153443 < baseStart_153443 := by decide
  rcases family_descends (prefixWord ++ tailWord_153443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_153454 : List Nat := [4, 1, 2, 3, 1, 1, 9]
def baseStart_153454 : Nat := 118140960795 + 153454 * 2 ^ 59
def prefixEnd_153454 : Nat := 4983230072969 + 3 ^ 40 * 153454 * 2
def baseEnd_153454 : Nat := 3891143721241868850335

theorem tailTrace_153454 : CollatzResearch.WordTrace tailWord_153454 prefixEnd_153454 3891143721241868850335 := by
  unfold tailWord_153454
  simp only [CollatzResearch.WordTrace]
  refine ⟨699615898258730087724427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3731284790713227134530277 699615898258730087724427)
  ·
    refine ⟨1049423847388095131586641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 699615898258730087724427 1049423847388095131586641)
    ·
      refine ⟨787067885541071348689981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1049423847388095131586641 787067885541071348689981)
      ·
        refine ⟨295150457077901755758743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 787067885541071348689981 295150457077901755758743)
        ·
          refine ⟨442725685616852633638115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 295150457077901755758743 442725685616852633638115)
          ·
            refine ⟨664088528425278950457173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 442725685616852633638115 664088528425278950457173)
            ·
              refine ⟨3891143721241868850335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 664088528425278950457173 3891143721241868850335)
              ·
                rfl

theorem cell21_153454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 9].length) (baseStart_153454 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_153454 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_153454 prefixEnd_153454 := by exact prefixLift 153454
  have htrace : WordTrace (prefixWord ++ tailWord_153454) baseStart_153454 baseEnd_153454 := by
    simpa [prefixWord, tailWord_153454, baseEnd_153454] using wordTrace_append hprefix tailTrace_153454
  have hstable : (prefixWord ++ tailWord_153454).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_153454).length < 2 ^ (prefixWord ++ tailWord_153454).sum := by decide
  have hdescent : baseEnd_153454 < baseStart_153454 := by decide
  rcases family_descends (prefixWord ++ tailWord_153454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_153544 : List Nat := [2, 1, 3, 1, 4, 1, 1, 1, 7]
def baseStart_153544 : Nat := 118140960795 + 153544 * 2 ^ 59
def prefixEnd_153544 : Nat := 4983230072969 + 3 ^ 40 * 153544 * 2
def baseEnd_153544 : Nat := 35040832717356663152831

theorem tailTrace_153544 : CollatzResearch.WordTrace tailWord_153544 prefixEnd_153544 35040832717356663152831 := by
  unfold tailWord_153544
  simp only [CollatzResearch.WordTrace]
  refine ⟨2800104877871893036285843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3733473170495857381714457 2800104877871893036285843)
  ·
    refine ⟨4200157316807839554428765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2800104877871893036285843 4200157316807839554428765)
    ·
      refine ⟨1575058993802939832910787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4200157316807839554428765 1575058993802939832910787)
      ·
        refine ⟨2362588490704409749366181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1575058993802939832910787 2362588490704409749366181)
        ·
          refine ⟨442985342007076828006159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2362588490704409749366181 442985342007076828006159)
          ·
            refine ⟨664478013010615242009239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 442985342007076828006159 664478013010615242009239)
            ·
              refine ⟨996717019515922863013859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 664478013010615242009239 996717019515922863013859)
              ·
                refine ⟨1495075529273884294520789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 996717019515922863013859 1495075529273884294520789)
                ·
                  refine ⟨35040832717356663152831, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1495075529273884294520789 35040832717356663152831)
                  ·
                    rfl

theorem cell21_153544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 1, 1, 7].length) (baseStart_153544 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_153544 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_153544 prefixEnd_153544 := by exact prefixLift 153544
  have htrace : WordTrace (prefixWord ++ tailWord_153544) baseStart_153544 baseEnd_153544 := by
    simpa [prefixWord, tailWord_153544, baseEnd_153544] using wordTrace_append hprefix tailTrace_153544
  have hstable : (prefixWord ++ tailWord_153544).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_153544).length < 2 ^ (prefixWord ++ tailWord_153544).sum := by decide
  have hdescent : baseEnd_153544 < baseStart_153544 := by decide
  rcases family_descends (prefixWord ++ tailWord_153544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_153564 : List Nat := [2, 2, 6, 1, 1, 1, 8]
def baseStart_153564 : Nat := 118140960795 + 153564 * 2 ^ 59
def prefixEnd_153564 : Nat := 4983230072969 + 3 ^ 40 * 153564 * 2
def baseEnd_153564 : Nat := 3893932998871230313273

theorem tailTrace_153564 : CollatzResearch.WordTrace tailWord_153564 prefixEnd_153564 3893932998871230313273 := by
  unfold tailWord_153564
  simp only [CollatzResearch.WordTrace]
  refine ⟨2800469607835664744149873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3733959477114219658866497 2800469607835664744149873)
  ·
    refine ⟨2100352205876748558112405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2800469607835664744149873 2100352205876748558112405)
    ·
      refine ⟨98454009650472588661519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 2100352205876748558112405 98454009650472588661519)
      ·
        refine ⟨147681014475708882992279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98454009650472588661519 147681014475708882992279)
        ·
          refine ⟨221521521713563324488419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 147681014475708882992279 221521521713563324488419)
          ·
            refine ⟨332282282570344986732629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 221521521713563324488419 332282282570344986732629)
            ·
              refine ⟨3893932998871230313273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 332282282570344986732629 3893932998871230313273)
              ·
                rfl

theorem cell21_153564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 1, 8].length) (baseStart_153564 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_153564 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_153564 prefixEnd_153564 := by exact prefixLift 153564
  have htrace : WordTrace (prefixWord ++ tailWord_153564) baseStart_153564 baseEnd_153564 := by
    simpa [prefixWord, tailWord_153564, baseEnd_153564] using wordTrace_append hprefix tailTrace_153564
  have hstable : (prefixWord ++ tailWord_153564).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_153564).length < 2 ^ (prefixWord ++ tailWord_153564).sum := by decide
  have hdescent : baseEnd_153564 < baseStart_153564 := by decide
  rcases family_descends (prefixWord ++ tailWord_153564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_153623 : List Nat := [1, 1, 3, 5, 3, 1, 7]
def baseStart_153623 : Nat := 118140960795 + 153623 * 2 ^ 59
def prefixEnd_153623 : Nat := 4983230072969 + 3 ^ 40 * 153623 * 2
def baseEnd_153623 : Nat := 3895429065963342370667

theorem tailTrace_153623 : CollatzResearch.WordTrace tailWord_153623 prefixEnd_153623 3895429065963342370667 := by
  unfold tailWord_153623
  simp only [CollatzResearch.WordTrace]
  refine ⟨5603091122457582564697523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3735394081638388376465015 5603091122457582564697523)
  ·
    refine ⟨8404636683686373847046285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5603091122457582564697523 8404636683686373847046285)
    ·
      refine ⟨3151738756382390192642357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8404636683686373847046285 3151738756382390192642357)
      ·
        refine ⟨295475508410849080560221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 3151738756382390192642357 295475508410849080560221)
        ·
          refine ⟨110803315654068405210083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 295475508410849080560221 110803315654068405210083)
          ·
            refine ⟨166204973481102607815125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 110803315654068405210083 166204973481102607815125)
            ·
              refine ⟨3895429065963342370667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 166204973481102607815125 3895429065963342370667)
              ·
                rfl

theorem cell21_153623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 3, 1, 7].length) (baseStart_153623 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_153623 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_153623 prefixEnd_153623 := by exact prefixLift 153623
  have htrace : WordTrace (prefixWord ++ tailWord_153623) baseStart_153623 baseEnd_153623 := by
    simpa [prefixWord, tailWord_153623, baseEnd_153623] using wordTrace_append hprefix tailTrace_153623
  have hstable : (prefixWord ++ tailWord_153623).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_153623).length < 2 ^ (prefixWord ++ tailWord_153623).sum := by decide
  have hdescent : baseEnd_153623 < baseStart_153623 := by decide
  rcases family_descends (prefixWord ++ tailWord_153623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_153637 : List Nat := [1, 3, 1, 2, 2, 5, 1, 1, 5]
def baseStart_153637 : Nat := 118140960795 + 153637 * 2 ^ 59
def prefixEnd_153637 : Nat := 4983230072969 + 3 ^ 40 * 153637 * 2
def baseEnd_153637 : Nat := 35062056584409168102641

theorem tailTrace_153637 : CollatzResearch.WordTrace tailWord_153637 prefixEnd_153637 35062056584409168102641 := by
  unfold tailWord_153637
  simp only [CollatzResearch.WordTrace]
  refine ⟨5603601744406862955707165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3735734496271241970471443 5603601744406862955707165)
  ·
    refine ⟨2101350654152573608390187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5603601744406862955707165 2101350654152573608390187)
    ·
      refine ⟨3152025981228860412585281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2101350654152573608390187 3152025981228860412585281)
      ·
        refine ⟨2364019485921645309438961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3152025981228860412585281 2364019485921645309438961)
        ·
          refine ⟨1773014614441233982079221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2364019485921645309438961 1773014614441233982079221)
          ·
            refine ⟨166220120103865685819927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1773014614441233982079221 166220120103865685819927)
            ·
              refine ⟨249330180155798528729891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 166220120103865685819927 249330180155798528729891)
              ·
                refine ⟨373995270233697793094837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 249330180155798528729891 373995270233697793094837)
                ·
                  refine ⟨35062056584409168102641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 373995270233697793094837 35062056584409168102641)
                  ·
                    rfl

theorem cell21_153637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 5, 1, 1, 5].length) (baseStart_153637 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_153637 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_153637 prefixEnd_153637 := by exact prefixLift 153637
  have htrace : WordTrace (prefixWord ++ tailWord_153637) baseStart_153637 baseEnd_153637 := by
    simpa [prefixWord, tailWord_153637, baseEnd_153637] using wordTrace_append hprefix tailTrace_153637
  have hstable : (prefixWord ++ tailWord_153637).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_153637).length < 2 ^ (prefixWord ++ tailWord_153637).sum := by decide
  have hdescent : baseEnd_153637 < baseStart_153637 := by decide
  rcases family_descends (prefixWord ++ tailWord_153637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_153679 : List Nat := [1, 1, 2, 1, 1, 2, 2, 4, 7]
def baseStart_153679 : Nat := 118140960795 + 153679 * 2 ^ 59
def prefixEnd_153679 : Nat := 4983230072969 + 3 ^ 40 * 153679 * 2
def baseEnd_153679 : Nat := 35071641556626428402555

theorem tailTrace_153679 : CollatzResearch.WordTrace tailWord_153679 prefixEnd_153679 35071641556626428402555 := by
  unfold tailWord_153679
  simp only [CollatzResearch.WordTrace]
  refine ⟨5605133610254704128736091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3736755740169802752490727 5605133610254704128736091)
  ·
    refine ⟨8407700415382056193104137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5605133610254704128736091 8407700415382056193104137)
    ·
      refine ⟨6305775311536542144828103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8407700415382056193104137 6305775311536542144828103)
      ·
        refine ⟨9458662967304813217242155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6305775311536542144828103 9458662967304813217242155)
        ·
          refine ⟨14187994450957219825863233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9458662967304813217242155 14187994450957219825863233)
          ·
            refine ⟨10640995838217914869397425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14187994450957219825863233 10640995838217914869397425)
            ·
              refine ⟨7980746878663436152048069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10640995838217914869397425 7980746878663436152048069)
              ·
                refine ⟨1496390039749394278509013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7980746878663436152048069 1496390039749394278509013)
                ·
                  refine ⟨35071641556626428402555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1496390039749394278509013 35071641556626428402555)
                  ·
                    rfl

theorem cell21_153679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 4, 7].length) (baseStart_153679 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_153679 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_153679 prefixEnd_153679 := by exact prefixLift 153679
  have htrace : WordTrace (prefixWord ++ tailWord_153679) baseStart_153679 baseEnd_153679 := by
    simpa [prefixWord, tailWord_153679, baseEnd_153679] using wordTrace_append hprefix tailTrace_153679
  have hstable : (prefixWord ++ tailWord_153679).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_153679).length < 2 ^ (prefixWord ++ tailWord_153679).sum := by decide
  have hdescent : baseEnd_153679 < baseStart_153679 := by decide
  rcases family_descends (prefixWord ++ tailWord_153679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_153682 : List Nat := [3, 2, 2, 1, 5, 8]
def baseStart_153682 : Nat := 118140960795 + 153682 * 2 ^ 59
def prefixEnd_153682 : Nat := 4983230072969 + 3 ^ 40 * 153682 * 2
def baseEnd_153682 : Nat := 1298975044351818142687

theorem tailTrace_153682 : CollatzResearch.WordTrace tailWord_153682 prefixEnd_153682 1298975044351818142687 := by
  unfold tailWord_153682
  simp only [CollatzResearch.WordTrace]
  refine ⟨1401310757310958910273825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3736828686162557094063533 1401310757310958910273825)
  ·
    refine ⟨1050983067983219182705369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1401310757310958910273825 1050983067983219182705369)
    ·
      refine ⟨788237300987414387029027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1050983067983219182705369 788237300987414387029027)
      ·
        refine ⟨1182355951481121580543541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 788237300987414387029027 1182355951481121580543541)
        ·
          refine ⟨110845870451355148175957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 1182355951481121580543541 110845870451355148175957)
          ·
            refine ⟨1298975044351818142687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 110845870451355148175957 1298975044351818142687)
            ·
              rfl

theorem cell21_153682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 5, 8].length) (baseStart_153682 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_153682 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_153682 prefixEnd_153682 := by exact prefixLift 153682
  have htrace : WordTrace (prefixWord ++ tailWord_153682) baseStart_153682 baseEnd_153682 := by
    simpa [prefixWord, tailWord_153682, baseEnd_153682] using wordTrace_append hprefix tailTrace_153682
  have hstable : (prefixWord ++ tailWord_153682).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_153682).length < 2 ^ (prefixWord ++ tailWord_153682).sum := by decide
  have hdescent : baseEnd_153682 < baseStart_153682 := by decide
  rcases family_descends (prefixWord ++ tailWord_153682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_153786 : List Nat := [3, 1, 1, 1, 2, 2, 3, 2, 6]
def baseStart_153786 : Nat := 118140960795 + 153786 * 2 ^ 59
def prefixEnd_153786 : Nat := 4983230072969 + 3 ^ 40 * 153786 * 2
def baseEnd_153786 : Nat := 35096060414418020119003

theorem tailTrace_153786 : CollatzResearch.WordTrace tailWord_153786 prefixEnd_153786 35096060414418020119003 := by
  unfold tailWord_153786
  simp only [CollatzResearch.WordTrace]
  refine ⟨1402259055216765350720303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3739357480578040935254141 1402259055216765350720303)
  ·
    refine ⟨2103388582825148026080455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1402259055216765350720303 2103388582825148026080455)
    ·
      refine ⟨3155082874237722039120683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2103388582825148026080455 3155082874237722039120683)
      ·
        refine ⟨4732624311356583058681025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3155082874237722039120683 4732624311356583058681025)
        ·
          refine ⟨3549468233517437294010769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4732624311356583058681025 3549468233517437294010769)
          ·
            refine ⟨2662101175138077970508077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3549468233517437294010769 2662101175138077970508077)
            ·
              refine ⟨998287940676779238940529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2662101175138077970508077 998287940676779238940529)
              ·
                refine ⟨748715955507584429205397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 998287940676779238940529 748715955507584429205397)
                ·
                  refine ⟨35096060414418020119003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 748715955507584429205397 35096060414418020119003)
                  ·
                    rfl

theorem cell21_153786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 3, 2, 6].length) (baseStart_153786 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_153786 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_153786 prefixEnd_153786 := by exact prefixLift 153786
  have htrace : WordTrace (prefixWord ++ tailWord_153786) baseStart_153786 baseEnd_153786 := by
    simpa [prefixWord, tailWord_153786, baseEnd_153786] using wordTrace_append hprefix tailTrace_153786
  have hstable : (prefixWord ++ tailWord_153786).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_153786).length < 2 ^ (prefixWord ++ tailWord_153786).sum := by decide
  have hdescent : baseEnd_153786 < baseStart_153786 := by decide
  rcases family_descends (prefixWord ++ tailWord_153786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_153865 : List Nat := [1, 2, 1, 1, 3, 5, 1, 4, 3]
def baseStart_153865 : Nat := 118140960795 + 153865 * 2 ^ 59
def prefixEnd_153865 : Nat := 4983230072969 + 3 ^ 40 * 153865 * 2
def baseEnd_153865 : Nat := 35114089290731438302175

theorem tailTrace_153865 : CollatzResearch.WordTrace tailWord_153865 prefixEnd_153865 35114089290731438302175 := by
  unfold tailWord_153865
  simp only [CollatzResearch.WordTrace]
  refine ⟨5611917587580857895007049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3741278391720571930004699 5611917587580857895007049)
  ·
    refine ⟨4208938190685643421255287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5611917587580857895007049 4208938190685643421255287)
    ·
      refine ⟨6313407286028465131882931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4208938190685643421255287 6313407286028465131882931)
      ·
        refine ⟨9470110929042697697824397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6313407286028465131882931 9470110929042697697824397)
        ·
          refine ⟨3551291598391011636684149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9470110929042697697824397 3551291598391011636684149)
          ·
            refine ⟨332933587349157340939139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 3551291598391011636684149 332933587349157340939139)
            ·
              refine ⟨499400381023736011408709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 332933587349157340939139 499400381023736011408709)
              ·
                refine ⟨93637571441950502139133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 499400381023736011408709 93637571441950502139133)
                ·
                  refine ⟨35114089290731438302175, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 93637571441950502139133 35114089290731438302175)
                  ·
                    rfl

theorem cell21_153865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 5, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 5, 1, 4, 3].length) (baseStart_153865 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_153865 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_153865 prefixEnd_153865 := by exact prefixLift 153865
  have htrace : WordTrace (prefixWord ++ tailWord_153865) baseStart_153865 baseEnd_153865 := by
    simpa [prefixWord, tailWord_153865, baseEnd_153865] using wordTrace_append hprefix tailTrace_153865
  have hstable : (prefixWord ++ tailWord_153865).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_153865).length < 2 ^ (prefixWord ++ tailWord_153865).sum := by decide
  have hdescent : baseEnd_153865 < baseStart_153865 := by decide
  rcases family_descends (prefixWord ++ tailWord_153865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_153879 : List Nat := [1, 1, 3, 4, 1, 2, 2, 3, 4]
def baseStart_153879 : Nat := 118140960795 + 153879 * 2 ^ 59
def prefixEnd_153879 : Nat := 4983230072969 + 3 ^ 40 * 153879 * 2
def baseEnd_153879 : Nat := 35117284281470525068813

theorem tailTrace_153879 : CollatzResearch.WordTrace tailWord_153879 prefixEnd_153879 35117284281470525068813 := by
  unfold tailWord_153879
  simp only [CollatzResearch.WordTrace]
  refine ⟨5612428209530138286016691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3741618806353425524011127 5612428209530138286016691)
  ·
    refine ⟨8418642314295207429025037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5612428209530138286016691 8418642314295207429025037)
    ·
      refine ⟨3156990867860702785884389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8418642314295207429025037 3156990867860702785884389)
      ·
        refine ⟨591935787723881772353323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3156990867860702785884389 591935787723881772353323)
        ·
          refine ⟨887903681585822658529985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 591935787723881772353323 887903681585822658529985)
          ·
            refine ⟨665927761189366993897489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 887903681585822658529985 665927761189366993897489)
            ·
              refine ⟨499445820892025245423117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 665927761189366993897489 499445820892025245423117)
              ·
                refine ⟨187292182834509467033669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 499445820892025245423117 187292182834509467033669)
                ·
                  refine ⟨35117284281470525068813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 187292182834509467033669 35117284281470525068813)
                  ·
                    rfl

theorem cell21_153879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 2, 3, 4].length) (baseStart_153879 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_153879 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_153879 prefixEnd_153879 := by exact prefixLift 153879
  have htrace : WordTrace (prefixWord ++ tailWord_153879) baseStart_153879 baseEnd_153879 := by
    simpa [prefixWord, tailWord_153879, baseEnd_153879] using wordTrace_append hprefix tailTrace_153879
  have hstable : (prefixWord ++ tailWord_153879).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_153879).length < 2 ^ (prefixWord ++ tailWord_153879).sum := by decide
  have hdescent : baseEnd_153879 < baseStart_153879 := by decide
  rcases family_descends (prefixWord ++ tailWord_153879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_153907 : List Nat := [1, 1, 1, 2, 5, 1, 1, 2, 7]
def baseStart_153907 : Nat := 118140960795 + 153907 * 2 ^ 59
def prefixEnd_153907 : Nat := 4983230072969 + 3 ^ 40 * 153907 * 2
def baseEnd_153907 : Nat := 35123674262948698602089

theorem tailTrace_153907 : CollatzResearch.WordTrace tailWord_153907 prefixEnd_153907 35123674262948698602089 := by
  unfold tailWord_153907
  simp only [CollatzResearch.WordTrace]
  refine ⟨5613449453428699068035975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3742299635619132712023983 5613449453428699068035975)
  ·
    refine ⟨8420174180143048602053963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5613449453428699068035975 8420174180143048602053963)
    ·
      refine ⟨12630261270214572903080945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8420174180143048602053963 12630261270214572903080945)
      ·
        refine ⟨9472695952660929677310709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12630261270214572903080945 9472695952660929677310709)
        ·
          refine ⟨888065245561962157247879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 9472695952660929677310709 888065245561962157247879)
          ·
            refine ⟨1332097868342943235871819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 888065245561962157247879 1332097868342943235871819)
            ·
              refine ⟨1998146802514414853807729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1332097868342943235871819 1998146802514414853807729)
              ·
                refine ⟨1498610101885811140355797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1998146802514414853807729 1498610101885811140355797)
                ·
                  refine ⟨35123674262948698602089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1498610101885811140355797 35123674262948698602089)
                  ·
                    rfl

theorem cell21_153907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 1, 2, 7].length) (baseStart_153907 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_153907 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_153907 prefixEnd_153907 := by exact prefixLift 153907
  have htrace : WordTrace (prefixWord ++ tailWord_153907) baseStart_153907 baseEnd_153907 := by
    simpa [prefixWord, tailWord_153907, baseEnd_153907] using wordTrace_append hprefix tailTrace_153907
  have hstable : (prefixWord ++ tailWord_153907).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_153907).length < 2 ^ (prefixWord ++ tailWord_153907).sum := by decide
  have hdescent : baseEnd_153907 < baseStart_153907 := by decide
  rcases family_descends (prefixWord ++ tailWord_153907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_153950 : List Nat := [4, 4, 2, 1, 1, 2, 1, 3, 3]
def baseStart_153950 : Nat := 118140960795 + 153950 * 2 ^ 59
def prefixEnd_153950 : Nat := 4983230072969 + 3 ^ 40 * 153950 * 2
def baseEnd_153950 : Nat := 35133487448790179385335

theorem tailTrace_153950 : CollatzResearch.WordTrace tailWord_153950 prefixEnd_153950 35133487448790179385335 := by
  unfold tailWord_153950
  simp only [CollatzResearch.WordTrace]
  refine ⟨701877224034114676481413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3743345194848611607900869 701877224034114676481413)
  ·
    refine ⟨131601979506396501840265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 701877224034114676481413 131601979506396501840265)
    ·
      refine ⟨98701484629797376380199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 131601979506396501840265 98701484629797376380199)
      ·
        refine ⟨148052226944696064570299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98701484629797376380199 148052226944696064570299)
        ·
          refine ⟨222078340417044096855449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 148052226944696064570299 222078340417044096855449)
          ·
            refine ⟨166558755312783072641587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 222078340417044096855449 166558755312783072641587)
            ·
              refine ⟨249838132969174608962381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 166558755312783072641587 249838132969174608962381)
              ·
                refine ⟨93689299863440478360893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 249838132969174608962381 93689299863440478360893)
                ·
                  refine ⟨35133487448790179385335, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 93689299863440478360893 35133487448790179385335)
                  ·
                    rfl

theorem cell21_153950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 2, 1, 3, 3].length) (baseStart_153950 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_153950 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_153950 prefixEnd_153950 := by exact prefixLift 153950
  have htrace : WordTrace (prefixWord ++ tailWord_153950) baseStart_153950 baseEnd_153950 := by
    simpa [prefixWord, tailWord_153950, baseEnd_153950] using wordTrace_append hprefix tailTrace_153950
  have hstable : (prefixWord ++ tailWord_153950).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_153950).length < 2 ^ (prefixWord ++ tailWord_153950).sum := by decide
  have hdescent : baseEnd_153950 < baseStart_153950 := by decide
  rcases family_descends (prefixWord ++ tailWord_153950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_154026 : List Nat := [3, 1, 6, 1, 2, 1, 2, 2, 3]
def baseStart_154026 : Nat := 118140960795 + 154026 * 2 ^ 59
def prefixEnd_154026 : Nat := 4983230072969 + 3 ^ 40 * 154026 * 2
def baseEnd_154026 : Nat := 35150831684230936118513

theorem tailTrace_154026 : CollatzResearch.WordTrace tailWord_154026 prefixEnd_154026 35150831684230936118513 := by
  unfold tailWord_154026
  simp only [CollatzResearch.WordTrace]
  refine ⟨1404447434999395597904483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3745193159998388261078621 1404447434999395597904483)
  ·
    refine ⟨2106671152499093396856725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1404447434999395597904483 2106671152499093396856725)
    ·
      refine ⟨98750210273395002977659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 2106671152499093396856725 98750210273395002977659)
      ·
        refine ⟨148125315410092504466489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98750210273395002977659 148125315410092504466489)
        ·
          refine ⟨111093986557569378349867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 148125315410092504466489 111093986557569378349867)
          ·
            refine ⟨166640979836354067524801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 111093986557569378349867 166640979836354067524801)
            ·
              refine ⟨124980734877265550643601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 166640979836354067524801 124980734877265550643601)
              ·
                refine ⟨93735551157949162982701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 124980734877265550643601 93735551157949162982701)
                ·
                  refine ⟨35150831684230936118513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 93735551157949162982701 35150831684230936118513)
                  ·
                    rfl

theorem cell21_154026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 2, 1, 2, 2, 3].length) (baseStart_154026 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_154026 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_154026 prefixEnd_154026 := by exact prefixLift 154026
  have htrace : WordTrace (prefixWord ++ tailWord_154026) baseStart_154026 baseEnd_154026 := by
    simpa [prefixWord, tailWord_154026, baseEnd_154026] using wordTrace_append hprefix tailTrace_154026
  have hstable : (prefixWord ++ tailWord_154026).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_154026).length < 2 ^ (prefixWord ++ tailWord_154026).sum := by decide
  have hdescent : baseEnd_154026 < baseStart_154026 := by decide
  rcases family_descends (prefixWord ++ tailWord_154026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_154045 : List Nat := [1, 4, 1, 2, 2, 2, 3, 6]
def baseStart_154045 : Nat := 118140960795 + 154045 * 2 ^ 59
def prefixEnd_154045 : Nat := 4983230072969 + 3 ^ 40 * 154045 * 2
def baseEnd_154045 : Nat := 11718389247697041767269

theorem tailTrace_154045 : CollatzResearch.WordTrace tailWord_154045 prefixEnd_154045 11718389247697041767269 := by
  unfold tailWord_154045
  simp only [CollatzResearch.WordTrace]
  refine ⟨5618482726928748636559589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3745655151285832424373059 5618482726928748636559589)
  ·
    refine ⟨1053465511299140369354923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5618482726928748636559589 1053465511299140369354923)
    ·
      refine ⟨1580198266948710554032385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1053465511299140369354923 1580198266948710554032385)
      ·
        refine ⟨1185148700211532915524289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1580198266948710554032385 1185148700211532915524289)
        ·
          refine ⟨888861525158649686643217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1185148700211532915524289 888861525158649686643217)
          ·
            refine ⟨666646143868987264982413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 888861525158649686643217 666646143868987264982413)
            ·
              refine ⟨249992303950870224368405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 666646143868987264982413 249992303950870224368405)
              ·
                refine ⟨11718389247697041767269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 249992303950870224368405 11718389247697041767269)
                ·
                  rfl

theorem cell21_154045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 3, 6].length) (baseStart_154045 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_154045 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_154045 prefixEnd_154045 := by exact prefixLift 154045
  have htrace : WordTrace (prefixWord ++ tailWord_154045) baseStart_154045 baseEnd_154045 := by
    simpa [prefixWord, tailWord_154045, baseEnd_154045] using wordTrace_append hprefix tailTrace_154045
  have hstable : (prefixWord ++ tailWord_154045).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_154045).length < 2 ^ (prefixWord ++ tailWord_154045).sum := by decide
  have hdescent : baseEnd_154045 < baseStart_154045 := by decide
  rcases family_descends (prefixWord ++ tailWord_154045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_154082 : List Nat := [3, 3, 3, 2, 1, 2, 1, 2, 4]
def baseStart_154082 : Nat := 118140960795 + 154082 * 2 ^ 59
def prefixEnd_154082 : Nat := 4983230072969 + 3 ^ 40 * 154082 * 2
def baseEnd_154082 : Nat := 35163611647187283185065

theorem tailTrace_154082 : CollatzResearch.WordTrace tailWord_154082 prefixEnd_154082 35163611647187283185065 := by
  unfold tailWord_154082
  simp only [CollatzResearch.WordTrace]
  refine ⟨1404958056948675988914125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3746554818529802637104333 1404958056948675988914125)
  ·
    refine ⟨526859271355753495842797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1404958056948675988914125 526859271355753495842797)
    ·
      refine ⟨197572226758407560941049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 526859271355753495842797 197572226758407560941049)
      ·
        refine ⟨148179170068805670705787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 197572226758407560941049 148179170068805670705787)
        ·
          refine ⟨222268755103208506058681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 148179170068805670705787 222268755103208506058681)
          ·
            refine ⟨166701566327406379544011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 222268755103208506058681 166701566327406379544011)
            ·
              refine ⟨250052349491109569316017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 166701566327406379544011 250052349491109569316017)
              ·
                refine ⟨187539262118332176987013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 250052349491109569316017 187539262118332176987013)
                ·
                  refine ⟨35163611647187283185065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 187539262118332176987013 35163611647187283185065)
                  ·
                    rfl

theorem cell21_154082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 2, 1, 2, 4].length) (baseStart_154082 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_154082 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_154082 prefixEnd_154082 := by exact prefixLift 154082
  have htrace : WordTrace (prefixWord ++ tailWord_154082) baseStart_154082 baseEnd_154082 := by
    simpa [prefixWord, tailWord_154082, baseEnd_154082] using wordTrace_append hprefix tailTrace_154082
  have hstable : (prefixWord ++ tailWord_154082).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_154082).length < 2 ^ (prefixWord ++ tailWord_154082).sum := by decide
  have hdescent : baseEnd_154082 < baseStart_154082 := by decide
  rcases family_descends (prefixWord ++ tailWord_154082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_154093 : List Nat := [1, 5, 1, 3, 1, 2, 2, 1, 5]
def baseStart_154093 : Nat := 118140960795 + 154093 * 2 ^ 59
def prefixEnd_154093 : Nat := 4983230072969 + 3 ^ 40 * 154093 * 2
def baseEnd_154093 : Nat := 35166121997053708501709

theorem tailTrace_154093 : CollatzResearch.WordTrace tailWord_154093 prefixEnd_154093 35166121997053708501709 := by
  unfold tailWord_154093
  simp only [CollatzResearch.WordTrace]
  refine ⟨5620233430754852834306933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3746822287169901889537955 5620233430754852834306933)
  ·
    refine ⟨526896884133267453216275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 5620233430754852834306933 526896884133267453216275)
    ·
      refine ⟨790345326199901179824413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 526896884133267453216275 790345326199901179824413)
      ·
        refine ⟨296379497324962942434155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 790345326199901179824413 296379497324962942434155)
        ·
          refine ⟨444569245987444413651233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 296379497324962942434155 444569245987444413651233)
          ·
            refine ⟨333426934490583310238425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 444569245987444413651233 333426934490583310238425)
            ·
              refine ⟨250070200867937482678819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 333426934490583310238425 250070200867937482678819)
              ·
                refine ⟨375105301301906224018229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 250070200867937482678819 375105301301906224018229)
                ·
                  refine ⟨35166121997053708501709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 375105301301906224018229 35166121997053708501709)
                  ·
                    rfl

theorem cell21_154093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 2, 2, 1, 5].length) (baseStart_154093 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_154093 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_154093 prefixEnd_154093 := by exact prefixLift 154093
  have htrace : WordTrace (prefixWord ++ tailWord_154093) baseStart_154093 baseEnd_154093 := by
    simpa [prefixWord, tailWord_154093, baseEnd_154093] using wordTrace_append hprefix tailTrace_154093
  have hstable : (prefixWord ++ tailWord_154093).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_154093).length < 2 ^ (prefixWord ++ tailWord_154093).sum := by decide
  have hdescent : baseEnd_154093 < baseStart_154093 := by decide
  rcases family_descends (prefixWord ++ tailWord_154093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_154104 : List Nat := [2, 1, 2, 1, 1, 4, 2, 8]
def baseStart_154104 : Nat := 118140960795 + 154104 * 2 ^ 59
def prefixEnd_154104 : Nat := 4983230072969 + 3 ^ 40 * 154104 * 2
def baseEnd_154104 : Nat := 11722877448973377939451

theorem tailTrace_154104 : CollatzResearch.WordTrace tailWord_154104 prefixEnd_154104 11722877448973377939451 := by
  unfold tailWord_154104
  simp only [CollatzResearch.WordTrace]
  refine ⟨2810317316857500856478683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3747089755810001141971577 2810317316857500856478683)
  ·
    refine ⟨4215475975286251284718025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2810317316857500856478683 4215475975286251284718025)
    ·
      refine ⟨3161606981464688463538519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4215475975286251284718025 3161606981464688463538519)
      ·
        refine ⟨4742410472197032695307779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3161606981464688463538519 4742410472197032695307779)
        ·
          refine ⟨7113615708295549042961669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4742410472197032695307779 7113615708295549042961669)
          ·
            refine ⟨1333802945305415445555313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7113615708295549042961669 1333802945305415445555313)
            ·
              refine ⟨1000352208979061584166485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1333802945305415445555313 1000352208979061584166485)
              ·
                refine ⟨11722877448973377939451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1000352208979061584166485 11722877448973377939451)
                ·
                  rfl

theorem cell21_154104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 2, 8].length) (baseStart_154104 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_154104 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_154104 prefixEnd_154104 := by exact prefixLift 154104
  have htrace : WordTrace (prefixWord ++ tailWord_154104) baseStart_154104 baseEnd_154104 := by
    simpa [prefixWord, tailWord_154104, baseEnd_154104] using wordTrace_append hprefix tailTrace_154104
  have hstable : (prefixWord ++ tailWord_154104).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_154104).length < 2 ^ (prefixWord ++ tailWord_154104).sum := by decide
  have hdescent : baseEnd_154104 < baseStart_154104 := by decide
  rcases family_descends (prefixWord ++ tailWord_154104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_154158 : List Nat := [4, 1, 3, 1, 4, 1, 2, 1, 4]
def baseStart_154158 : Nat := 118140960795 + 154158 * 2 ^ 59
def prefixEnd_154158 : Nat := 4983230072969 + 3 ^ 40 * 154158 * 2
def baseEnd_154158 : Nat := 35180955882628039918243

theorem tailTrace_154158 : CollatzResearch.WordTrace tailWord_154158 prefixEnd_154158 35180955882628039918243 := by
  unfold tailWord_154158
  simp only [CollatzResearch.WordTrace]
  refine ⟨702825521939921116927891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3748402783679579290282085 702825521939921116927891)
  ·
    refine ⟨1054238282909881675391837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 702825521939921116927891 1054238282909881675391837)
    ·
      refine ⟨395339356091205628271939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1054238282909881675391837 395339356091205628271939)
      ·
        refine ⟨593009034136808442407909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 395339356091205628271939 593009034136808442407909)
        ·
          refine ⟨111189193900651582951483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 593009034136808442407909 111189193900651582951483)
          ·
            refine ⟨166783790850977374427225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 111189193900651582951483 166783790850977374427225)
            ·
              refine ⟨125087843138233030820419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 166783790850977374427225 125087843138233030820419)
              ·
                refine ⟨187631764707349546230629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 125087843138233030820419 187631764707349546230629)
                ·
                  refine ⟨35180955882628039918243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 187631764707349546230629 35180955882628039918243)
                  ·
                    rfl

theorem cell21_154158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 4, 1, 2, 1, 4].length) (baseStart_154158 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_154158 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_154158 prefixEnd_154158 := by exact prefixLift 154158
  have htrace : WordTrace (prefixWord ++ tailWord_154158) baseStart_154158 baseEnd_154158 := by
    simpa [prefixWord, tailWord_154158, baseEnd_154158] using wordTrace_append hprefix tailTrace_154158
  have hstable : (prefixWord ++ tailWord_154158).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_154158).length < 2 ^ (prefixWord ++ tailWord_154158).sum := by decide
  have hdescent : baseEnd_154158 < baseStart_154158 := by decide
  rcases family_descends (prefixWord ++ tailWord_154158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_154211 : List Nat := [1, 1, 1, 5, 1, 2, 2, 3, 5]
def baseStart_154211 : Nat := 118140960795 + 154211 * 2 ^ 59
def prefixEnd_154211 : Nat := 4983230072969 + 3 ^ 40 * 154211 * 2
def baseEnd_154211 : Nat := 35193051204711725534801

theorem tailTrace_154211 : CollatzResearch.WordTrace tailWord_154211 prefixEnd_154211 35193051204711725534801 := by
  unfold tailWord_154211
  simp only [CollatzResearch.WordTrace]
  refine ⟨5624537244327358987102487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3749691496218239324734991 5624537244327358987102487)
  ·
    refine ⟨8436805866491038480653731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5624537244327358987102487 8436805866491038480653731)
    ·
      refine ⟨12655208799736557720980597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8436805866491038480653731 12655208799736557720980597)
      ·
        refine ⟨1186425824975302286341931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 12655208799736557720980597 1186425824975302286341931)
        ·
          refine ⟨1779638737462953429512897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1186425824975302286341931 1779638737462953429512897)
          ·
            refine ⟨1334729053097215072134673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1779638737462953429512897 1334729053097215072134673)
            ·
              refine ⟨1001046789822911304101005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1334729053097215072134673 1001046789822911304101005)
              ·
                refine ⟨375392546183591739037877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1001046789822911304101005 375392546183591739037877)
                ·
                  refine ⟨35193051204711725534801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 375392546183591739037877 35193051204711725534801)
                  ·
                    rfl

theorem cell21_154211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 2, 3, 5].length) (baseStart_154211 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_154211 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_154211 prefixEnd_154211 := by exact prefixLift 154211
  have htrace : WordTrace (prefixWord ++ tailWord_154211) baseStart_154211 baseEnd_154211 := by
    simpa [prefixWord, tailWord_154211, baseEnd_154211] using wordTrace_append hprefix tailTrace_154211
  have hstable : (prefixWord ++ tailWord_154211).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_154211).length < 2 ^ (prefixWord ++ tailWord_154211).sum := by decide
  have hdescent : baseEnd_154211 < baseStart_154211 := by decide
  rcases family_descends (prefixWord ++ tailWord_154211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_154225 : List Nat := [1, 2, 2, 2, 1, 1, 1, 1, 10]
def baseStart_154225 : Nat := 118140960795 + 154225 * 2 ^ 59
def prefixEnd_154225 : Nat := 4983230072969 + 3 ^ 40 * 154225 * 2
def baseEnd_154225 : Nat := 35196246195450812301439

theorem tailTrace_154225 : CollatzResearch.WordTrace tailWord_154225 prefixEnd_154225 35196246195450812301439 := by
  unfold tailWord_154225
  simp only [CollatzResearch.WordTrace]
  refine ⟨5625047866276639378112129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3750031910851092918741419 5625047866276639378112129)
  ·
    refine ⟨4218785899707479533584097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5625047866276639378112129 4218785899707479533584097)
    ·
      refine ⟨3164089424780609650188073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4218785899707479533584097 3164089424780609650188073)
      ·
        refine ⟨2373067068585457237641055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3164089424780609650188073 2373067068585457237641055)
        ·
          refine ⟨3559600602878185856461583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2373067068585457237641055 3559600602878185856461583)
          ·
            refine ⟨5339400904317278784692375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3559600602878185856461583 5339400904317278784692375)
            ·
              refine ⟨8009101356475918177038563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5339400904317278784692375 8009101356475918177038563)
              ·
                refine ⟨12013652034713877265557845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8009101356475918177038563 12013652034713877265557845)
                ·
                  refine ⟨35196246195450812301439, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 12013652034713877265557845 35196246195450812301439)
                  ·
                    rfl

theorem cell21_154225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 1, 10].length) (baseStart_154225 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_154225 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_154225 prefixEnd_154225 := by exact prefixLift 154225
  have htrace : WordTrace (prefixWord ++ tailWord_154225) baseStart_154225 baseEnd_154225 := by
    simpa [prefixWord, tailWord_154225, baseEnd_154225] using wordTrace_append hprefix tailTrace_154225
  have hstable : (prefixWord ++ tailWord_154225).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_154225).length < 2 ^ (prefixWord ++ tailWord_154225).sum := by decide
  have hdescent : baseEnd_154225 < baseStart_154225 := by decide
  rcases family_descends (prefixWord ++ tailWord_154225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_154245 : List Nat := [1, 3, 1, 1, 4, 3, 2, 3, 3]
def baseStart_154245 : Nat := 118140960795 + 154245 * 2 ^ 59
def prefixEnd_154245 : Nat := 4983230072969 + 3 ^ 40 * 154245 * 2
def baseEnd_154245 : Nat := 35200810467935221968065

theorem tailTrace_154245 : CollatzResearch.WordTrace tailWord_154245 prefixEnd_154245 35200810467935221968065 := by
  unfold tailWord_154245
  simp only [CollatzResearch.WordTrace]
  refine ⟨5625777326204182793840189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3750518217469455195893459 5625777326204182793840189)
  ·
    refine ⟨2109666497326568547690071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5625777326204182793840189 2109666497326568547690071)
    ·
      refine ⟨3164499745989852821535107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2109666497326568547690071 3164499745989852821535107)
      ·
        refine ⟨4746749618984779232302661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3164499745989852821535107 4746749618984779232302661)
        ·
          refine ⟨890015553559646106056749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4746749618984779232302661 890015553559646106056749)
          ·
            refine ⟨333755832584867289771281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 890015553559646106056749 333755832584867289771281)
            ·
              refine ⟨250316874438650467328461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 333755832584867289771281 250316874438650467328461)
              ·
                refine ⟨93868827914493925248173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 250316874438650467328461 93868827914493925248173)
                ·
                  refine ⟨35200810467935221968065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 93868827914493925248173 35200810467935221968065)
                  ·
                    rfl

theorem cell21_154245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 3, 2, 3, 3].length) (baseStart_154245 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_154245 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_154245 prefixEnd_154245 := by exact prefixLift 154245
  have htrace : WordTrace (prefixWord ++ tailWord_154245) baseStart_154245 baseEnd_154245 := by
    simpa [prefixWord, tailWord_154245, baseEnd_154245] using wordTrace_append hprefix tailTrace_154245
  have hstable : (prefixWord ++ tailWord_154245).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_154245).length < 2 ^ (prefixWord ++ tailWord_154245).sum := by decide
  have hdescent : baseEnd_154245 < baseStart_154245 := by decide
  rcases family_descends (prefixWord ++ tailWord_154245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_154287 : List Nat := [1, 1, 2, 1, 2, 5, 2, 2, 5]
def baseStart_154287 : Nat := 118140960795 + 154287 * 2 ^ 59
def prefixEnd_154287 : Nat := 4983230072969 + 3 ^ 40 * 154287 * 2
def baseEnd_154287 : Nat := 35210395440152482267979

theorem tailTrace_154287 : CollatzResearch.WordTrace tailWord_154287 prefixEnd_154287 35210395440152482267979 := by
  unfold tailWord_154287
  simp only [CollatzResearch.WordTrace]
  refine ⟨5627309192052023966869115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3751539461368015977912743 5627309192052023966869115)
  ·
    refine ⟨8440963788078035950303673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5627309192052023966869115 8440963788078035950303673)
    ·
      refine ⟨6330722841058526962727755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8440963788078035950303673 6330722841058526962727755)
      ·
        refine ⟨9496084261587790444091633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6330722841058526962727755 9496084261587790444091633)
        ·
          refine ⟨7122063196190842833068725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9496084261587790444091633 7122063196190842833068725)
          ·
            refine ⟨667693424642891515600193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 7122063196190842833068725 667693424642891515600193)
            ·
              refine ⟨500770068482168636700145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 667693424642891515600193 500770068482168636700145)
              ·
                refine ⟨375577551361626477525109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 500770068482168636700145 375577551361626477525109)
                ·
                  refine ⟨35210395440152482267979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 375577551361626477525109 35210395440152482267979)
                  ·
                    rfl

theorem cell21_154287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 2, 2, 5].length) (baseStart_154287 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_154287 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_154287 prefixEnd_154287 := by exact prefixLift 154287
  have htrace : WordTrace (prefixWord ++ tailWord_154287) baseStart_154287 baseEnd_154287 := by
    simpa [prefixWord, tailWord_154287, baseEnd_154287] using wordTrace_append hprefix tailTrace_154287
  have hstable : (prefixWord ++ tailWord_154287).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_154287).length < 2 ^ (prefixWord ++ tailWord_154287).sum := by decide
  have hdescent : baseEnd_154287 < baseStart_154287 := by decide
  rcases family_descends (prefixWord ++ tailWord_154287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_154318 : List Nat := [4, 1, 1, 1, 3, 2, 2, 1, 6]
def baseStart_154318 : Nat := 118140960795 + 154318 * 2 ^ 59
def prefixEnd_154318 : Nat := 4983230072969 + 3 ^ 40 * 154318 * 2
def baseEnd_154318 : Nat := 35217470062503317251249

theorem tailTrace_154318 : CollatzResearch.WordTrace tailWord_154318 prefixEnd_154318 35217470062503317251249 := by
  unfold tailWord_154318
  simp only [CollatzResearch.WordTrace]
  refine ⟨703554981867464532655951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3752293236626477507498405 703554981867464532655951)
  ·
    refine ⟨1055332472801196798983927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 703554981867464532655951 1055332472801196798983927)
    ·
      refine ⟨1582998709201795198475891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1055332472801196798983927 1582998709201795198475891)
      ·
        refine ⟨2374498063802692797713837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1582998709201795198475891 2374498063802692797713837)
        ·
          refine ⟨890436773926009799142689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2374498063802692797713837 890436773926009799142689)
          ·
            refine ⟨667827580444507349357017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 890436773926009799142689 667827580444507349357017)
            ·
              refine ⟨500870685333380512017763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 667827580444507349357017 500870685333380512017763)
              ·
                refine ⟨751306028000070768026645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 500870685333380512017763 751306028000070768026645)
                ·
                  refine ⟨35217470062503317251249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 751306028000070768026645 35217470062503317251249)
                  ·
                    rfl

theorem cell21_154318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 2, 1, 6].length) (baseStart_154318 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_154318 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_154318 prefixEnd_154318 := by exact prefixLift 154318
  have htrace : WordTrace (prefixWord ++ tailWord_154318) baseStart_154318 baseEnd_154318 := by
    simpa [prefixWord, tailWord_154318, baseEnd_154318] using wordTrace_append hprefix tailTrace_154318
  have hstable : (prefixWord ++ tailWord_154318).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_154318).length < 2 ^ (prefixWord ++ tailWord_154318).sum := by decide
  have hdescent : baseEnd_154318 < baseStart_154318 := by decide
  rcases family_descends (prefixWord ++ tailWord_154318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_154321 : List Nat := [1, 2, 2, 1, 2, 3, 5, 2, 3]
def baseStart_154321 : Nat := 118140960795 + 154321 * 2 ^ 59
def prefixEnd_154321 : Nat := 4983230072969 + 3 ^ 40 * 154321 * 2
def baseEnd_154321 : Nat := 35218154703375978701243

theorem tailTrace_154321 : CollatzResearch.WordTrace tailWord_154321 prefixEnd_154321 35218154703375978701243 := by
  unfold tailWord_154321
  simp only [CollatzResearch.WordTrace]
  refine ⟨5628549273928847773606817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3752366182619231849071211 5628549273928847773606817)
  ·
    refine ⟨4221411955446635830205113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5628549273928847773606817 4221411955446635830205113)
    ·
      refine ⟨3166058966584976872653835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4221411955446635830205113 3166058966584976872653835)
      ·
        refine ⟨4749088449877465308980753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3166058966584976872653835 4749088449877465308980753)
        ·
          refine ⟨3561816337408098981735565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4749088449877465308980753 3561816337408098981735565)
          ·
            refine ⟨1335681126528037118150837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3561816337408098981735565 1335681126528037118150837)
            ·
              refine ⟨125220105612003479826641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1335681126528037118150837 125220105612003479826641)
              ·
                refine ⟨93915079209002609869981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 125220105612003479826641 93915079209002609869981)
                ·
                  refine ⟨35218154703375978701243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 93915079209002609869981 35218154703375978701243)
                  ·
                    rfl

theorem cell21_154321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 5, 2, 3].length) (baseStart_154321 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_154321 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_154321 prefixEnd_154321 := by exact prefixLift 154321
  have htrace : WordTrace (prefixWord ++ tailWord_154321) baseStart_154321 baseEnd_154321 := by
    simpa [prefixWord, tailWord_154321, baseEnd_154321] using wordTrace_append hprefix tailTrace_154321
  have hstable : (prefixWord ++ tailWord_154321).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_154321).length < 2 ^ (prefixWord ++ tailWord_154321).sum := by decide
  have hdescent : baseEnd_154321 < baseStart_154321 := by decide
  rcases family_descends (prefixWord ++ tailWord_154321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_154335 : List Nat := [1, 1, 2, 3, 2, 3, 4, 1, 4]
def baseStart_154335 : Nat := 118140960795 + 154335 * 2 ^ 59
def prefixEnd_154335 : Nat := 4983230072969 + 3 ^ 40 * 154335 * 2
def baseEnd_154335 : Nat := 35221349694115065467881

theorem tailTrace_154335 : CollatzResearch.WordTrace tailWord_154335 prefixEnd_154335 35221349694115065467881 := by
  unfold tailWord_154335
  simp only [CollatzResearch.WordTrace]
  refine ⟨5629059895878128164616459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3752706597252085443077639 5629059895878128164616459)
  ·
    refine ⟨8443589843817192246924689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5629059895878128164616459 8443589843817192246924689)
    ·
      refine ⟨6332692382862894185193517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8443589843817192246924689 6332692382862894185193517)
      ·
        refine ⟨2374759643573585319447569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6332692382862894185193517 2374759643573585319447569)
        ·
          refine ⟨1781069732680188989585677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2374759643573585319447569 1781069732680188989585677)
          ·
            refine ⟨667901149755070871094629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1781069732680188989585677 667901149755070871094629)
            ·
              refine ⟨125231465579075788330243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 667901149755070871094629 125231465579075788330243)
              ·
                refine ⟨187847198368613682495365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 125231465579075788330243 187847198368613682495365)
                ·
                  refine ⟨35221349694115065467881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 187847198368613682495365 35221349694115065467881)
                  ·
                    rfl

theorem cell21_154335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 4, 1, 4].length) (baseStart_154335 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_154335 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_154335 prefixEnd_154335 := by exact prefixLift 154335
  have htrace : WordTrace (prefixWord ++ tailWord_154335) baseStart_154335 baseEnd_154335 := by
    simpa [prefixWord, tailWord_154335, baseEnd_154335] using wordTrace_append hprefix tailTrace_154335
  have hstable : (prefixWord ++ tailWord_154335).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_154335).length < 2 ^ (prefixWord ++ tailWord_154335).sum := by decide
  have hdescent : baseEnd_154335 < baseStart_154335 := by decide
  rcases family_descends (prefixWord ++ tailWord_154335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_154377 : List Nat := [1, 2, 1, 1, 3, 2, 2, 3, 6]
def baseStart_154377 : Nat := 118140960795 + 154377 * 2 ^ 59
def prefixEnd_154377 : Nat := 4983230072969 + 3 ^ 40 * 154377 * 2
def baseEnd_154377 : Nat := 35230934666332325767795

theorem tailTrace_154377 : CollatzResearch.WordTrace tailWord_154377 prefixEnd_154377 35230934666332325767795 := by
  unfold tailWord_154377
  simp only [CollatzResearch.WordTrace]
  refine ⟨5630591761725969337645385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3753727841150646225096923 5630591761725969337645385)
  ·
    refine ⟨4222943821294477003234039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5630591761725969337645385 4222943821294477003234039)
    ·
      refine ⟨6334415731941715504851059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4222943821294477003234039 6334415731941715504851059)
      ·
        refine ⟨9501623597912573257276589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6334415731941715504851059 9501623597912573257276589)
        ·
          refine ⟨3563108849217214971478721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9501623597912573257276589 3563108849217214971478721)
          ·
            refine ⟨2672331636912911228609041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3563108849217214971478721 2672331636912911228609041)
            ·
              refine ⟨2004248727684683421456781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2672331636912911228609041 2004248727684683421456781)
              ·
                refine ⟨751593272881756283046293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2004248727684683421456781 751593272881756283046293)
                ·
                  refine ⟨35230934666332325767795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 751593272881756283046293 35230934666332325767795)
                  ·
                    rfl

theorem cell21_154377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 2, 3, 6].length) (baseStart_154377 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_154377 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_154377 prefixEnd_154377 := by exact prefixLift 154377
  have htrace : WordTrace (prefixWord ++ tailWord_154377) baseStart_154377 baseEnd_154377 := by
    simpa [prefixWord, tailWord_154377, baseEnd_154377] using wordTrace_append hprefix tailTrace_154377
  have hstable : (prefixWord ++ tailWord_154377).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_154377).length < 2 ^ (prefixWord ++ tailWord_154377).sum := by decide
  have hdescent : baseEnd_154377 < baseStart_154377 := by decide
  rcases family_descends (prefixWord ++ tailWord_154377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_154394 : List Nat := [3, 1, 1, 3, 2, 1, 1, 5, 4]
def baseStart_154394 : Nat := 118140960795 + 154394 * 2 ^ 59
def prefixEnd_154394 : Nat := 4983230072969 + 3 ^ 40 * 154394 * 2
def baseEnd_154394 : Nat := 35234814297944073984427

theorem tailTrace_154394 : CollatzResearch.WordTrace tailWord_154394 prefixEnd_154394 35234814297944073984427 := by
  unfold tailWord_154394
  simp only [CollatzResearch.WordTrace]
  refine ⟨1407802950666095310253559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3754141201776254160676157 1407802950666095310253559)
  ·
    refine ⟨2111704425999142965380339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1407802950666095310253559 2111704425999142965380339)
    ·
      refine ⟨3167556638998714448070509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2111704425999142965380339 3167556638998714448070509)
      ·
        refine ⟨1187833739624517918026441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3167556638998714448070509 1187833739624517918026441)
        ·
          refine ⟨890875304718388438519831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1187833739624517918026441 890875304718388438519831)
          ·
            refine ⟨1336312957077582657779747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 890875304718388438519831 1336312957077582657779747)
            ·
              refine ⟨2004469435616373986669621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1336312957077582657779747 2004469435616373986669621)
              ·
                refine ⟨187919009589035061250277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2004469435616373986669621 187919009589035061250277)
                ·
                  refine ⟨35234814297944073984427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 187919009589035061250277 35234814297944073984427)
                  ·
                    rfl

theorem cell21_154394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 1, 5, 4].length) (baseStart_154394 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_154394 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_154394 prefixEnd_154394 := by exact prefixLift 154394
  have htrace : WordTrace (prefixWord ++ tailWord_154394) baseStart_154394 baseEnd_154394 := by
    simpa [prefixWord, tailWord_154394, baseEnd_154394] using wordTrace_append hprefix tailTrace_154394
  have hstable : (prefixWord ++ tailWord_154394).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_154394).length < 2 ^ (prefixWord ++ tailWord_154394).sum := by decide
  have hdescent : baseEnd_154394 < baseStart_154394 := by decide
  rcases family_descends (prefixWord ++ tailWord_154394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_154397 : List Nat := [1, 4, 2, 4, 1, 1, 1, 2, 5]
def baseStart_154397 : Nat := 118140960795 + 154397 * 2 ^ 59
def prefixEnd_154397 : Nat := 4983230072969 + 3 ^ 40 * 154397 * 2
def baseEnd_154397 : Nat := 35235498938816735434421

theorem tailTrace_154397 : CollatzResearch.WordTrace tailWord_154397 prefixEnd_154397 35235498938816735434421 := by
  unfold tailWord_154397
  simp only [CollatzResearch.WordTrace]
  refine ⟨5631321221653512753373445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3754214147769008502248963 5631321221653512753373445)
  ·
    refine ⟨1055872729060033641257521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5631321221653512753373445 1055872729060033641257521)
    ·
      refine ⟨791904546795025230943141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1055872729060033641257521 791904546795025230943141)
      ·
        refine ⟨148482102524067230801839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 791904546795025230943141 148482102524067230801839)
        ·
          refine ⟨222723153786100846202759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 148482102524067230801839 222723153786100846202759)
          ·
            refine ⟨334084730679151269304139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 222723153786100846202759 334084730679151269304139)
            ·
              refine ⟨501127096018726903956209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 334084730679151269304139 501127096018726903956209)
              ·
                refine ⟨375845322014045177967157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 501127096018726903956209 375845322014045177967157)
                ·
                  refine ⟨35235498938816735434421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 375845322014045177967157 35235498938816735434421)
                  ·
                    rfl

theorem cell21_154397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 1, 1, 2, 5].length) (baseStart_154397 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_154397 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_154397 prefixEnd_154397 := by exact prefixLift 154397
  have htrace : WordTrace (prefixWord ++ tailWord_154397) baseStart_154397 baseEnd_154397 := by
    simpa [prefixWord, tailWord_154397, baseEnd_154397] using wordTrace_append hprefix tailTrace_154397
  have hstable : (prefixWord ++ tailWord_154397).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_154397).length < 2 ^ (prefixWord ++ tailWord_154397).sum := by decide
  have hdescent : baseEnd_154397 < baseStart_154397 := by decide
  rcases family_descends (prefixWord ++ tailWord_154397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_154414 : List Nat := [4, 1, 3, 2, 1, 2, 2, 3, 3]
def baseStart_154414 : Nat := 118140960795 + 154414 * 2 ^ 59
def prefixEnd_154414 : Nat := 4983230072969 + 3 ^ 40 * 154414 * 2
def baseEnd_154414 : Nat := 35239378570428483651053

theorem tailTrace_154414 : CollatzResearch.WordTrace tailWord_154414 prefixEnd_154414 35239378570428483651053 := by
  unfold tailWord_154414
  simp only [CollatzResearch.WordTrace]
  refine ⟨703992657823990582092787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3754627508394616437828197 703992657823990582092787)
  ·
    refine ⟨1055988986735985873139181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 703992657823990582092787 1055988986735985873139181)
    ·
      refine ⟨395995870025994702427193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1055988986735985873139181 395995870025994702427193)
      ·
        refine ⟨296996902519496026820395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 395995870025994702427193 296996902519496026820395)
        ·
          refine ⟨445495353779244040230593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 296996902519496026820395 445495353779244040230593)
          ·
            refine ⟨334121515334433030172945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 445495353779244040230593 334121515334433030172945)
            ·
              refine ⟨250591136500824772629709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 334121515334433030172945 250591136500824772629709)
              ·
                refine ⟨93971676187809289736141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 250591136500824772629709 93971676187809289736141)
                ·
                  refine ⟨35239378570428483651053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 93971676187809289736141 35239378570428483651053)
                  ·
                    rfl

theorem cell21_154414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 2, 2, 3, 3].length) (baseStart_154414 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_154414 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_154414 prefixEnd_154414 := by exact prefixLift 154414
  have htrace : WordTrace (prefixWord ++ tailWord_154414) baseStart_154414 baseEnd_154414 := by
    simpa [prefixWord, tailWord_154414, baseEnd_154414] using wordTrace_append hprefix tailTrace_154414
  have hstable : (prefixWord ++ tailWord_154414).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_154414).length < 2 ^ (prefixWord ++ tailWord_154414).sum := by decide
  have hdescent : baseEnd_154414 < baseStart_154414 := by decide
  rcases family_descends (prefixWord ++ tailWord_154414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_154445 : List Nat := [1, 6, 1, 2, 2, 1, 3, 1, 4]
def baseStart_154445 : Nat := 118140960795 + 154445 * 2 ^ 59
def prefixEnd_154445 : Nat := 4983230072969 + 3 ^ 40 * 154445 * 2
def baseEnd_154445 : Nat := 35246453192779318634323

theorem tailTrace_154445 : CollatzResearch.WordTrace tailWord_154445 prefixEnd_154445 35246453192779318634323 := by
  unfold tailWord_154445
  simp only [CollatzResearch.WordTrace]
  refine ⟨5633071925479616951120789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3755381283653077967413859 5633071925479616951120789)
  ·
    refine ⟨264050246506857044583787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 5633071925479616951120789 264050246506857044583787)
    ·
      refine ⟨396075369760285566875681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 264050246506857044583787 396075369760285566875681)
      ·
        refine ⟨297056527320214175156761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 396075369760285566875681 297056527320214175156761)
        ·
          refine ⟨222792395490160631367571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 297056527320214175156761 222792395490160631367571)
          ·
            refine ⟨334188593235240947051357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 222792395490160631367571 334188593235240947051357)
            ·
              refine ⟨125320722463215355144259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 334188593235240947051357 125320722463215355144259)
              ·
                refine ⟨187981083694823032716389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 125320722463215355144259 187981083694823032716389)
                ·
                  refine ⟨35246453192779318634323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 187981083694823032716389 35246453192779318634323)
                  ·
                    rfl

theorem cell21_154445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 1, 3, 1, 4].length) (baseStart_154445 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_154445 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_154445 prefixEnd_154445 := by exact prefixLift 154445
  have htrace : WordTrace (prefixWord ++ tailWord_154445) baseStart_154445 baseEnd_154445 := by
    simpa [prefixWord, tailWord_154445, baseEnd_154445] using wordTrace_append hprefix tailTrace_154445
  have hstable : (prefixWord ++ tailWord_154445).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_154445).length < 2 ^ (prefixWord ++ tailWord_154445).sum := by decide
  have hdescent : baseEnd_154445 < baseStart_154445 := by decide
  rcases family_descends (prefixWord ++ tailWord_154445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_154504 : List Nat := [2, 1, 3, 3, 2, 3, 2, 1, 4]
def baseStart_154504 : Nat := 118140960795 + 154504 * 2 ^ 59
def prefixEnd_154504 : Nat := 4983230072969 + 3 ^ 40 * 154504 * 2
def baseEnd_154504 : Nat := 35259917796608327150869

theorem tailTrace_154504 : CollatzResearch.WordTrace tailWord_154504 prefixEnd_154504 35259917796608327150869 := by
  unfold tailWord_154504
  simp only [CollatzResearch.WordTrace]
  refine ⟨2817611916132935013759283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3756815888177246685012377 2817611916132935013759283)
  ·
    refine ⟨4226417874199402520638925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2817611916132935013759283 4226417874199402520638925)
    ·
      refine ⟨1584906702824775945239597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4226417874199402520638925 1584906702824775945239597)
      ·
        refine ⟨594340013559290979464849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1584906702824775945239597 594340013559290979464849)
        ·
          refine ⟨445755010169468234598637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 594340013559290979464849 445755010169468234598637)
          ·
            refine ⟨167158128813550587974489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 445755010169468234598637 167158128813550587974489)
            ·
              refine ⟨125368596610162940980867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 167158128813550587974489 125368596610162940980867)
              ·
                refine ⟨188052894915244411471301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 125368596610162940980867 188052894915244411471301)
                ·
                  refine ⟨35259917796608327150869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 188052894915244411471301 35259917796608327150869)
                  ·
                    rfl

theorem cell21_154504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 3, 2, 1, 4].length) (baseStart_154504 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_154504 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_154504 prefixEnd_154504 := by exact prefixLift 154504
  have htrace : WordTrace (prefixWord ++ tailWord_154504) baseStart_154504 baseEnd_154504 := by
    simpa [prefixWord, tailWord_154504, baseEnd_154504] using wordTrace_append hprefix tailTrace_154504
  have hstable : (prefixWord ++ tailWord_154504).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_154504).length < 2 ^ (prefixWord ++ tailWord_154504).sum := by decide
  have hdescent : baseEnd_154504 < baseStart_154504 := by decide
  rcases family_descends (prefixWord ++ tailWord_154504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_154532 : List Nat := [2, 3, 1, 2, 1, 2, 2, 5, 3]
def baseStart_154532 : Nat := 118140960795 + 154532 * 2 ^ 59
def prefixEnd_154532 : Nat := 4983230072969 + 3 ^ 40 * 154532 * 2
def baseEnd_154532 : Nat := 35266307778086500684145

theorem tailTrace_154532 : CollatzResearch.WordTrace tailWord_154532 prefixEnd_154532 35266307778086500684145 := by
  unfold tailWord_154532
  simp only [CollatzResearch.WordTrace]
  refine ⟨2818122538082215404768925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3757496717442953873025233 2818122538082215404768925)
  ·
    refine ⟨1056795951780830776788347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2818122538082215404768925 1056795951780830776788347)
    ·
      refine ⟨1585193927671246165182521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1056795951780830776788347 1585193927671246165182521)
      ·
        refine ⟨1188895445753434623886891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1585193927671246165182521 1188895445753434623886891)
        ·
          refine ⟨1783343168630151935830337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1188895445753434623886891 1783343168630151935830337)
          ·
            refine ⟨1337507376472613951872753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1783343168630151935830337 1337507376472613951872753)
            ·
              refine ⟨1003130532354460463904565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1337507376472613951872753 1003130532354460463904565)
              ·
                refine ⟨94043487408230668491053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1003130532354460463904565 94043487408230668491053)
                ·
                  refine ⟨35266307778086500684145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 94043487408230668491053 35266307778086500684145)
                  ·
                    rfl

theorem cell21_154532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 2, 5, 3].length) (baseStart_154532 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_154532 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_154532 prefixEnd_154532 := by exact prefixLift 154532
  have htrace : WordTrace (prefixWord ++ tailWord_154532) baseStart_154532 baseEnd_154532 := by
    simpa [prefixWord, tailWord_154532, baseEnd_154532] using wordTrace_append hprefix tailTrace_154532
  have hstable : (prefixWord ++ tailWord_154532).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_154532).length < 2 ^ (prefixWord ++ tailWord_154532).sum := by decide
  have hdescent : baseEnd_154532 < baseStart_154532 := by decide
  rcases family_descends (prefixWord ++ tailWord_154532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_154560 : List Nat := [2, 1, 1, 2, 3, 3, 3, 6]
def baseStart_154560 : Nat := 118140960795 + 154560 * 2 ^ 59
def prefixEnd_154560 : Nat := 4983230072969 + 3 ^ 40 * 154560 * 2
def baseEnd_154560 : Nat := 11757565919854891405807

theorem tailTrace_154560 : CollatzResearch.WordTrace tailWord_154560 prefixEnd_154560 11757565919854891405807 := by
  unfold tailWord_154560
  simp only [CollatzResearch.WordTrace]
  refine ⟨2818633160031495795778567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3758177546708661061038089 2818633160031495795778567)
  ·
    refine ⟨4227949740047243693667851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2818633160031495795778567 4227949740047243693667851)
    ·
      refine ⟨6341924610070865540501777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4227949740047243693667851 6341924610070865540501777)
      ·
        refine ⟨4756443457553149155376333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6341924610070865540501777 4756443457553149155376333)
        ·
          refine ⟨1783666296582430933266125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4756443457553149155376333 1783666296582430933266125)
          ·
            refine ⟨668874861218411599974797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1783666296582430933266125 668874861218411599974797)
            ·
              refine ⟨250828072956904349990549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 668874861218411599974797 250828072956904349990549)
              ·
                refine ⟨11757565919854891405807, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 250828072956904349990549 11757565919854891405807)
                ·
                  rfl

theorem cell21_154560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 3, 6].length) (baseStart_154560 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_154560 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_154560 prefixEnd_154560 := by exact prefixLift 154560
  have htrace : WordTrace (prefixWord ++ tailWord_154560) baseStart_154560 baseEnd_154560 := by
    simpa [prefixWord, tailWord_154560, baseEnd_154560] using wordTrace_append hprefix tailTrace_154560
  have hstable : (prefixWord ++ tailWord_154560).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_154560).length < 2 ^ (prefixWord ++ tailWord_154560).sum := by decide
  have hdescent : baseEnd_154560 < baseStart_154560 := by decide
  rcases family_descends (prefixWord ++ tailWord_154560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_154597 : List Nat := [1, 3, 1, 6, 2, 1, 1, 2, 4]
def baseStart_154597 : Nat := 118140960795 + 154597 * 2 ^ 59
def prefixEnd_154597 : Nat := 4983230072969 + 3 ^ 40 * 154597 * 2
def baseEnd_154597 : Nat := 35281141663660832100679

theorem tailTrace_154597 : CollatzResearch.WordTrace tailWord_154597 prefixEnd_154597 35281141663660832100679 := by
  unfold tailWord_154597
  simp only [CollatzResearch.WordTrace]
  refine ⟨5638615820928946910654045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3759077213952631273769363 5638615820928946910654045)
  ·
    refine ⟨2114480932848355091495267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5638615820928946910654045 2114480932848355091495267)
    ·
      refine ⟨3171721399272532637242901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2114480932848355091495267 3171721399272532637242901)
      ·
        refine ⟨148674440590899967370761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 3171721399272532637242901 148674440590899967370761)
        ·
          refine ⟨111505830443174975528071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 148674440590899967370761 111505830443174975528071)
          ·
            refine ⟨167258745664762463292107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 111505830443174975528071 167258745664762463292107)
            ·
              refine ⟨250888118497143694938161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 167258745664762463292107 250888118497143694938161)
              ·
                refine ⟨188166088872857771203621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 250888118497143694938161 188166088872857771203621)
                ·
                  refine ⟨35281141663660832100679, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 188166088872857771203621 35281141663660832100679)
                  ·
                    rfl

theorem cell21_154597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 2, 1, 1, 2, 4].length) (baseStart_154597 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_154597 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_154597 prefixEnd_154597 := by exact prefixLift 154597
  have htrace : WordTrace (prefixWord ++ tailWord_154597) baseStart_154597 baseEnd_154597 := by
    simpa [prefixWord, tailWord_154597, baseEnd_154597] using wordTrace_append hprefix tailTrace_154597
  have hstable : (prefixWord ++ tailWord_154597).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_154597).length < 2 ^ (prefixWord ++ tailWord_154597).sum := by decide
  have hdescent : baseEnd_154597 < baseStart_154597 := by decide
  rcases family_descends (prefixWord ++ tailWord_154597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_154619 : List Nat := [1, 1, 1, 1, 1, 3, 3, 10]
def baseStart_154619 : Nat := 118140960795 + 154619 * 2 ^ 59
def prefixEnd_154619 : Nat := 4983230072969 + 3 ^ 40 * 154619 * 2
def baseEnd_154619 : Nat := 11762054121131227577989

theorem tailTrace_154619 : CollatzResearch.WordTrace tailWord_154619 prefixEnd_154619 11762054121131227577989 := by
  unfold tailWord_154619
  simp only [CollatzResearch.WordTrace]
  refine ⟨5639418226849244667954911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3759612151232829778636607 5639418226849244667954911)
  ·
    refine ⟨8459127340273867001932367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5639418226849244667954911 8459127340273867001932367)
    ·
      refine ⟨12688691010410800502898551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8459127340273867001932367 12688691010410800502898551)
      ·
        refine ⟨19033036515616200754347827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12688691010410800502898551 19033036515616200754347827)
        ·
          refine ⟨28549554773424301131521741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19033036515616200754347827 28549554773424301131521741)
          ·
            refine ⟨10706083040034112924320653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28549554773424301131521741 10706083040034112924320653)
            ·
              refine ⟨4014781140012792346620245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10706083040034112924320653 4014781140012792346620245)
              ·
                refine ⟨11762054121131227577989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 4014781140012792346620245 11762054121131227577989)
                ·
                  rfl

theorem cell21_154619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 10].length) (baseStart_154619 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_154619 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_154619 prefixEnd_154619 := by exact prefixLift 154619
  have htrace : WordTrace (prefixWord ++ tailWord_154619) baseStart_154619 baseEnd_154619 := by
    simpa [prefixWord, tailWord_154619, baseEnd_154619] using wordTrace_append hprefix tailTrace_154619
  have hstable : (prefixWord ++ tailWord_154619).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_154619).length < 2 ^ (prefixWord ++ tailWord_154619).sum := by decide
  have hdescent : baseEnd_154619 < baseStart_154619 := by decide
  rcases family_descends (prefixWord ++ tailWord_154619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_154636 : List Nat := [2, 2, 1, 2, 3, 3, 1, 7]
def baseStart_154636 : Nat := 118140960795 + 154636 * 2 ^ 59
def prefixEnd_154636 : Nat := 4983230072969 + 3 ^ 40 * 154636 * 2
def baseEnd_154636 : Nat := 11763347331668476983533

theorem tailTrace_154636 : CollatzResearch.WordTrace tailWord_154636 prefixEnd_154636 11763347331668476983533 := by
  unfold tailWord_154636
  simp only [CollatzResearch.WordTrace]
  refine ⟨2820019133893828285661881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3760025511858437714215841 2820019133893828285661881)
  ·
    refine ⟨2115014350420371214246411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2820019133893828285661881 2115014350420371214246411)
    ·
      refine ⟨3172521525630556821369617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2115014350420371214246411 3172521525630556821369617)
      ·
        refine ⟨2379391144222917616027213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3172521525630556821369617 2379391144222917616027213)
        ·
          refine ⟨892271679083594106010205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2379391144222917616027213 892271679083594106010205)
          ·
            refine ⟨334601879656347789753827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 892271679083594106010205 334601879656347789753827)
            ·
              refine ⟨501902819484521684630741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 334601879656347789753827 501902819484521684630741)
              ·
                refine ⟨11763347331668476983533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 501902819484521684630741 11763347331668476983533)
                ·
                  rfl

theorem cell21_154636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 3, 1, 7].length) (baseStart_154636 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_154636 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_154636 prefixEnd_154636 := by exact prefixLift 154636
  have htrace : WordTrace (prefixWord ++ tailWord_154636) baseStart_154636 baseEnd_154636 := by
    simpa [prefixWord, tailWord_154636, baseEnd_154636] using wordTrace_append hprefix tailTrace_154636
  have hstable : (prefixWord ++ tailWord_154636).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_154636).length < 2 ^ (prefixWord ++ tailWord_154636).sum := by decide
  have hdescent : baseEnd_154636 < baseStart_154636 := by decide
  rcases family_descends (prefixWord ++ tailWord_154636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_154653 : List Nat := [1, 4, 2, 2, 3, 2, 7]
def baseStart_154653 : Nat := 118140960795 + 154653 * 2 ^ 59
def prefixEnd_154653 : Nat := 4983230072969 + 3 ^ 40 * 154653 * 2
def baseEnd_154653 : Nat := 3921546847401908796359

theorem tailTrace_154653 : CollatzResearch.WordTrace tailWord_154653 prefixEnd_154653 3921546847401908796359 := by
  unfold tailWord_154653
  simp only [CollatzResearch.WordTrace]
  refine ⟨5640658308726068474692613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3760438872484045649795075 5640658308726068474692613)
  ·
    refine ⟨1057623432886137839004865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5640658308726068474692613 1057623432886137839004865)
    ·
      refine ⟨793217574664603379253649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1057623432886137839004865 793217574664603379253649)
      ·
        refine ⟨594913180998452534440237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 793217574664603379253649 594913180998452534440237)
        ·
          refine ⟨223092442874419700415089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 594913180998452534440237 223092442874419700415089)
          ·
            refine ⟨167319332155814775311317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 223092442874419700415089 167319332155814775311317)
            ·
              refine ⟨3921546847401908796359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 167319332155814775311317 3921546847401908796359)
              ·
                rfl

theorem cell21_154653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 2, 7].length) (baseStart_154653 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_154653 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_154653 prefixEnd_154653 := by exact prefixLift 154653
  have htrace : WordTrace (prefixWord ++ tailWord_154653) baseStart_154653 baseEnd_154653 := by
    simpa [prefixWord, tailWord_154653, baseEnd_154653] using wordTrace_append hprefix tailTrace_154653
  have hstable : (prefixWord ++ tailWord_154653).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_154653).length < 2 ^ (prefixWord ++ tailWord_154653).sum := by decide
  have hdescent : baseEnd_154653 < baseStart_154653 := by decide
  rcases family_descends (prefixWord ++ tailWord_154653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_154819 : List Nat := [1, 1, 1, 3, 1, 1, 1, 9, 3]
def baseStart_154819 : Nat := 118140960795 + 154819 * 2 ^ 59
def prefixEnd_154819 : Nat := 4983230072969 + 3 ^ 40 * 154819 * 2
def baseEnd_154819 : Nat := 35331805088237779400225

theorem tailTrace_154819 : CollatzResearch.WordTrace tailWord_154819 prefixEnd_154819 35331805088237779400225 := by
  unfold tailWord_154819
  simp only [CollatzResearch.WordTrace]
  refine ⟨5646712826124678825235511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3764475217416452550157007 5646712826124678825235511)
  ·
    refine ⟨8470069239187018237853267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5646712826124678825235511 8470069239187018237853267)
    ·
      refine ⟨12705103858780527356779901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8470069239187018237853267 12705103858780527356779901)
      ·
        refine ⟨4764413947042697758792463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12705103858780527356779901 4764413947042697758792463)
        ·
          refine ⟨7146620920564046638188695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4764413947042697758792463 7146620920564046638188695)
          ·
            refine ⟨10719931380846069957283043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7146620920564046638188695 10719931380846069957283043)
            ·
              refine ⟨16079897071269104935924565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10719931380846069957283043 16079897071269104935924565)
              ·
                refine ⟨94218146901967411733933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 16079897071269104935924565 94218146901967411733933)
                ·
                  refine ⟨35331805088237779400225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 94218146901967411733933 35331805088237779400225)
                  ·
                    rfl

theorem cell21_154819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 9, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 9, 3].length) (baseStart_154819 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_154819 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_154819 prefixEnd_154819 := by exact prefixLift 154819
  have htrace : WordTrace (prefixWord ++ tailWord_154819) baseStart_154819 baseEnd_154819 := by
    simpa [prefixWord, tailWord_154819, baseEnd_154819] using wordTrace_append hprefix tailTrace_154819
  have hstable : (prefixWord ++ tailWord_154819).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_154819).length < 2 ^ (prefixWord ++ tailWord_154819).sum := by decide
  have hdescent : baseEnd_154819 < baseStart_154819 := by decide
  rcases family_descends (prefixWord ++ tailWord_154819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_154833 : List Nat := [1, 2, 2, 1, 2, 2, 1, 6, 4]
def baseStart_154833 : Nat := 118140960795 + 154833 * 2 ^ 59
def prefixEnd_154833 : Nat := 4983230072969 + 3 ^ 40 * 154833 * 2
def baseEnd_154833 : Nat := 35335000078976866166863

theorem tailTrace_154833 : CollatzResearch.WordTrace tailWord_154833 prefixEnd_154833 35335000078976866166863 := by
  unfold tailWord_154833
  simp only [CollatzResearch.WordTrace]
  refine ⟨5647223448073959216245153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3764815632049306144163435 5647223448073959216245153)
  ·
    refine ⟨4235417586055469412183865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5647223448073959216245153 4235417586055469412183865)
    ·
      refine ⟨3176563189541602059137899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4235417586055469412183865 3176563189541602059137899)
      ·
        refine ⟨4764844784312403088706849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3176563189541602059137899 4764844784312403088706849)
        ·
          refine ⟨3573633588234302316530137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4764844784312403088706849 3573633588234302316530137)
          ·
            refine ⟨2680225191175726737397603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3573633588234302316530137 2680225191175726737397603)
            ·
              refine ⟨4020337786763590106096405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2680225191175726737397603 4020337786763590106096405)
              ·
                refine ⟨188453333754543286223269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 4020337786763590106096405 188453333754543286223269)
                ·
                  refine ⟨35335000078976866166863, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 188453333754543286223269 35335000078976866166863)
                  ·
                    rfl

theorem cell21_154833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 6, 4].length) (baseStart_154833 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_154833 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_154833 prefixEnd_154833 := by exact prefixLift 154833
  have htrace : WordTrace (prefixWord ++ tailWord_154833) baseStart_154833 baseEnd_154833 := by
    simpa [prefixWord, tailWord_154833, baseEnd_154833] using wordTrace_append hprefix tailTrace_154833
  have hstable : (prefixWord ++ tailWord_154833).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_154833).length < 2 ^ (prefixWord ++ tailWord_154833).sum := by decide
  have hdescent : baseEnd_154833 < baseStart_154833 := by decide
  rcases family_descends (prefixWord ++ tailWord_154833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_154847 : List Nat := [1, 1, 2, 3, 2, 1, 3, 8]
def baseStart_154847 : Nat := 118140960795 + 154847 * 2 ^ 59
def prefixEnd_154847 : Nat := 4983230072969 + 3 ^ 40 * 154847 * 2
def baseEnd_154847 : Nat := 11779398356571984311167

theorem tailTrace_154847 : CollatzResearch.WordTrace tailWord_154847 prefixEnd_154847 11779398356571984311167 := by
  unfold tailWord_154847
  simp only [CollatzResearch.WordTrace]
  refine ⟨5647734070023239607254795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3765156046682159738169863 5647734070023239607254795)
  ·
    refine ⟨8471601105034859410882193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5647734070023239607254795 8471601105034859410882193)
    ·
      refine ⟨6353700828776144558161645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8471601105034859410882193 6353700828776144558161645)
      ·
        refine ⟨2382637810791054209310617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6353700828776144558161645 2382637810791054209310617)
        ·
          refine ⟨1786978358093290656982963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2382637810791054209310617 1786978358093290656982963)
          ·
            refine ⟨2680467537139935985474445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1786978358093290656982963 2680467537139935985474445)
            ·
              refine ⟨1005175326427475994552917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2680467537139935985474445 1005175326427475994552917)
              ·
                refine ⟨11779398356571984311167, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1005175326427475994552917 11779398356571984311167)
                ·
                  rfl

theorem cell21_154847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 3, 8].length) (baseStart_154847 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_154847 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_154847 prefixEnd_154847 := by exact prefixLift 154847
  have htrace : WordTrace (prefixWord ++ tailWord_154847) baseStart_154847 baseEnd_154847 := by
    simpa [prefixWord, tailWord_154847, baseEnd_154847] using wordTrace_append hprefix tailTrace_154847
  have hstable : (prefixWord ++ tailWord_154847).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_154847).length < 2 ^ (prefixWord ++ tailWord_154847).sum := by decide
  have hdescent : baseEnd_154847 < baseStart_154847 := by decide
  rcases family_descends (prefixWord ++ tailWord_154847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_154988 : List Nat := [2, 2, 1, 1, 5, 1, 3, 3, 3]
def baseStart_154988 : Nat := 118140960795 + 154988 * 2 ^ 59
def prefixEnd_154988 : Nat := 4983230072969 + 3 ^ 40 * 154988 * 2
def baseEnd_154988 : Nat := 35370373190731041083213

theorem tailTrace_154988 : CollatzResearch.WordTrace tailWord_154988 prefixEnd_154988 35370373190731041083213 := by
  unfold tailWord_154988
  simp only [CollatzResearch.WordTrace]
  refine ⟨2826438381256210344068809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3768584508341613792091745 2826438381256210344068809)
  ·
    refine ⟨2119828785942157758051607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2826438381256210344068809 2119828785942157758051607)
    ·
      refine ⟨3179743178913236637077411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2119828785942157758051607 3179743178913236637077411)
      ·
        refine ⟨4769614768369854955616117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3179743178913236637077411 4769614768369854955616117)
        ·
          refine ⟨447151384534673902089011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 4769614768369854955616117 447151384534673902089011)
          ·
            refine ⟨670727076802010853133517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 447151384534673902089011 670727076802010853133517)
            ·
              refine ⟨251522653800754069925069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 670727076802010853133517 251522653800754069925069)
              ·
                refine ⟨94320995175282776221901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 251522653800754069925069 94320995175282776221901)
                ·
                  refine ⟨35370373190731041083213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 94320995175282776221901 35370373190731041083213)
                  ·
                    rfl

theorem cell21_154988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 3, 3, 3].length) (baseStart_154988 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_154988 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_154988 prefixEnd_154988 := by exact prefixLift 154988
  have htrace : WordTrace (prefixWord ++ tailWord_154988) baseStart_154988 baseEnd_154988 := by
    simpa [prefixWord, tailWord_154988, baseEnd_154988] using wordTrace_append hprefix tailTrace_154988
  have hstable : (prefixWord ++ tailWord_154988).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_154988).length < 2 ^ (prefixWord ++ tailWord_154988).sum := by decide
  have hdescent : baseEnd_154988 < baseStart_154988 := by decide
  rcases family_descends (prefixWord ++ tailWord_154988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_155016 : List Nat := [2, 1, 3, 3, 1, 3, 2, 6]
def baseStart_155016 : Nat := 118140960795 + 155016 * 2 ^ 59
def prefixEnd_155016 : Nat := 4983230072969 + 3 ^ 40 * 155016 * 2
def baseEnd_155016 : Nat := 11792254390736404872163

theorem tailTrace_155016 : CollatzResearch.WordTrace tailWord_155016 prefixEnd_155016 11792254390736404872163 := by
  unfold tailWord_155016
  simp only [CollatzResearch.WordTrace]
  refine ⟨2826949003205490735078451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3769265337607320980104601 2826949003205490735078451)
  ·
    refine ⟨4240423504808236102617677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2826949003205490735078451 4240423504808236102617677)
    ·
      refine ⟨1590158814303088538481629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4240423504808236102617677 1590158814303088538481629)
      ·
        refine ⟨596309555363658201930611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1590158814303088538481629 596309555363658201930611)
        ·
          refine ⟨894464333045487302895917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 596309555363658201930611 894464333045487302895917)
          ·
            refine ⟨335424124892057738585969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 894464333045487302895917 335424124892057738585969)
            ·
              refine ⟨251568093669043303939477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 335424124892057738585969 251568093669043303939477)
              ·
                refine ⟨11792254390736404872163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 251568093669043303939477 11792254390736404872163)
                ·
                  rfl

theorem cell21_155016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 3, 2, 6].length) (baseStart_155016 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_155016 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_155016 prefixEnd_155016 := by exact prefixLift 155016
  have htrace : WordTrace (prefixWord ++ tailWord_155016) baseStart_155016 baseEnd_155016 := by
    simpa [prefixWord, tailWord_155016, baseEnd_155016] using wordTrace_append hprefix tailTrace_155016
  have hstable : (prefixWord ++ tailWord_155016).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_155016).length < 2 ^ (prefixWord ++ tailWord_155016).sum := by decide
  have hdescent : baseEnd_155016 < baseStart_155016 := by decide
  rcases family_descends (prefixWord ++ tailWord_155016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_155064 : List Nat := [2, 1, 2, 1, 2, 2, 6, 2, 3]
def baseStart_155064 : Nat := 118140960795 + 155064 * 2 ^ 59
def prefixEnd_155064 : Nat := 4983230072969 + 3 ^ 40 * 155064 * 2
def baseEnd_155064 : Nat := 35387717426171797816391

theorem tailTrace_155064 : CollatzResearch.WordTrace tailWord_155064 prefixEnd_155064 35387717426171797816391 := by
  unfold tailWord_155064
  simp only [CollatzResearch.WordTrace]
  refine ⟨2827824355118542833952123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3770432473491390445269497 2827824355118542833952123)
  ·
    refine ⟨4241736532677814250928185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2827824355118542833952123 4241736532677814250928185)
    ·
      refine ⟨3181302399508360688196139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4241736532677814250928185 3181302399508360688196139)
      ·
        refine ⟨4771953599262541032294209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3181302399508360688196139 4771953599262541032294209)
        ·
          refine ⟨3578965199446905774220657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4771953599262541032294209 3578965199446905774220657)
          ·
            refine ⟨2684223899585179330665493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3578965199446905774220657 2684223899585179330665493)
            ·
              refine ⟨125822995293055281124945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 2684223899585179330665493 125822995293055281124945)
              ·
                refine ⟨94367246469791460843709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 125822995293055281124945 94367246469791460843709)
                ·
                  refine ⟨35387717426171797816391, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 94367246469791460843709 35387717426171797816391)
                  ·
                    rfl

theorem cell21_155064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 6, 2, 3].length) (baseStart_155064 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_155064 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_155064 prefixEnd_155064 := by exact prefixLift 155064
  have htrace : WordTrace (prefixWord ++ tailWord_155064) baseStart_155064 baseEnd_155064 := by
    simpa [prefixWord, tailWord_155064, baseEnd_155064] using wordTrace_append hprefix tailTrace_155064
  have hstable : (prefixWord ++ tailWord_155064).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_155064).length < 2 ^ (prefixWord ++ tailWord_155064).sum := by decide
  have hdescent : baseEnd_155064 < baseStart_155064 := by decide
  rcases family_descends (prefixWord ++ tailWord_155064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_155075 : List Nat := [1, 1, 1, 3, 1, 1, 7, 6]
def baseStart_155075 : Nat := 118140960795 + 155075 * 2 ^ 59
def prefixEnd_155075 : Nat := 4983230072969 + 3 ^ 40 * 155075 * 2
def baseEnd_155075 : Nat := 11796742592012741044345

theorem tailTrace_155075 : CollatzResearch.WordTrace tailWord_155075 prefixEnd_155075 11796742592012741044345 := by
  unfold tailWord_155075
  simp only [CollatzResearch.WordTrace]
  refine ⟨5656049913197234546554679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3770699942131489697703119 5656049913197234546554679)
  ·
    refine ⟨8484074869795851819832019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5656049913197234546554679 8484074869795851819832019)
    ·
      refine ⟨12726112304693777729748029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8484074869795851819832019 12726112304693777729748029)
      ·
        refine ⟨4772292114260166648655511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12726112304693777729748029 4772292114260166648655511)
        ·
          refine ⟨7158438171390249972983267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4772292114260166648655511 7158438171390249972983267)
          ·
            refine ⟨10737657257085374959474901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7158438171390249972983267 10737657257085374959474901)
            ·
              refine ⟨251663841962938475612693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 10737657257085374959474901 251663841962938475612693)
              ·
                refine ⟨11796742592012741044345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 251663841962938475612693 11796742592012741044345)
                ·
                  rfl

theorem cell21_155075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 7, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 7, 6].length) (baseStart_155075 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_155075 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_155075 prefixEnd_155075 := by exact prefixLift 155075
  have htrace : WordTrace (prefixWord ++ tailWord_155075) baseStart_155075 baseEnd_155075 := by
    simpa [prefixWord, tailWord_155075, baseEnd_155075] using wordTrace_append hprefix tailTrace_155075
  have hstable : (prefixWord ++ tailWord_155075).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_155075).length < 2 ^ (prefixWord ++ tailWord_155075).sum := by decide
  have hdescent : baseEnd_155075 < baseStart_155075 := by decide
  rcases family_descends (prefixWord ++ tailWord_155075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_155168 : List Nat := [2, 1, 1, 6, 1, 3, 7]
def baseStart_155168 : Nat := 118140960795 + 155168 * 2 ^ 59
def prefixEnd_155168 : Nat := 4983230072969 + 3 ^ 40 * 155168 * 2
def baseEnd_155168 : Nat := 3934605738121192009205

theorem tailTrace_155168 : CollatzResearch.WordTrace tailWord_155168 prefixEnd_155168 3934605738121192009205 := by
  unfold tailWord_155168
  simp only [CollatzResearch.WordTrace]
  refine ⟨2829720950930155714845079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3772961267906874286460105 2829720950930155714845079)
  ·
    refine ⟨4244581426395233572267619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2829720950930155714845079 4244581426395233572267619)
    ·
      refine ⟨6366872139592850358401429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4244581426395233572267619 6366872139592850358401429)
      ·
        refine ⟨298447131543414860550067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 6366872139592850358401429 298447131543414860550067)
        ·
          refine ⟨447670697315122290825101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 298447131543414860550067 447670697315122290825101)
          ·
            refine ⟨167876511493170859059413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 447670697315122290825101 167876511493170859059413)
            ·
              refine ⟨3934605738121192009205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 167876511493170859059413 3934605738121192009205)
              ·
                rfl

theorem cell21_155168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 3, 7].length) (baseStart_155168 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_155168 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_155168 prefixEnd_155168 := by exact prefixLift 155168
  have htrace : WordTrace (prefixWord ++ tailWord_155168) baseStart_155168 baseEnd_155168 := by
    simpa [prefixWord, tailWord_155168, baseEnd_155168] using wordTrace_append hprefix tailTrace_155168
  have hstable : (prefixWord ++ tailWord_155168).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_155168).length < 2 ^ (prefixWord ++ tailWord_155168).sum := by decide
  have hdescent : baseEnd_155168 < baseStart_155168 := by decide
  rcases family_descends (prefixWord ++ tailWord_155168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_155275 : List Nat := [1, 1, 1, 1, 4, 1, 6, 3, 3]
def baseStart_155275 : Nat := 118140960795 + 155275 * 2 ^ 59
def prefixEnd_155275 : Nat := 4983230072969 + 3 ^ 40 * 155275 * 2
def baseEnd_155275 : Nat := 35435870500882319799293

theorem tailTrace_155275 : CollatzResearch.WordTrace tailWord_155275 prefixEnd_155275 35435870500882319799293 := by
  unfold tailWord_155275
  simp only [CollatzResearch.WordTrace]
  refine ⟨5663344512472668703835279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3775563008315112469223519 5663344512472668703835279)
  ·
    refine ⟨8495016768709003055752919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5663344512472668703835279 8495016768709003055752919)
    ·
      refine ⟨12742525153063504583629379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8495016768709003055752919 12742525153063504583629379)
      ·
        refine ⟨19113787729595256875444069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12742525153063504583629379 19113787729595256875444069)
        ·
          refine ⟨3583835199299110664145763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19113787729595256875444069 3583835199299110664145763)
          ·
            refine ⟨5375752798948665996218645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3583835199299110664145763 5375752798948665996218645)
            ·
              refine ⟨251988412450718718572749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 5375752798948665996218645 251988412450718718572749)
              ·
                refine ⟨94495654669019519464781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 251988412450718718572749 94495654669019519464781)
                ·
                  refine ⟨35435870500882319799293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 94495654669019519464781 35435870500882319799293)
                  ·
                    rfl

theorem cell21_155275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 6, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 6, 3, 3].length) (baseStart_155275 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_155275 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_155275 prefixEnd_155275 := by exact prefixLift 155275
  have htrace : WordTrace (prefixWord ++ tailWord_155275) baseStart_155275 baseEnd_155275 := by
    simpa [prefixWord, tailWord_155275, baseEnd_155275] using wordTrace_append hprefix tailTrace_155275
  have hstable : (prefixWord ++ tailWord_155275).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_155275).length < 2 ^ (prefixWord ++ tailWord_155275).sum := by decide
  have hdescent : baseEnd_155275 < baseStart_155275 := by decide
  rcases family_descends (prefixWord ++ tailWord_155275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_155357 : List Nat := [1, 4, 3, 3, 2, 1, 2, 1, 4]
def baseStart_155357 : Nat := 118140960795 + 155357 * 2 ^ 59
def prefixEnd_155357 : Nat := 4983230072969 + 3 ^ 40 * 155357 * 2
def baseEnd_155357 : Nat := 35454584018068399432459

theorem tailTrace_155357 : CollatzResearch.WordTrace tailWord_155357 prefixEnd_155357 35454584018068399432459 := by
  unfold tailWord_155357
  simp only [CollatzResearch.WordTrace]
  refine ⟨5666335298175596708320325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3777556865450397805546883 5666335298175596708320325)
  ·
    refine ⟨1062437868407924382810061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5666335298175596708320325 1062437868407924382810061)
    ·
      refine ⟨398414200652971643553773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1062437868407924382810061 398414200652971643553773)
      ·
        refine ⟨149405325244864366332665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 398414200652971643553773 149405325244864366332665)
        ·
          refine ⟨112053993933648274749499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 149405325244864366332665 112053993933648274749499)
          ·
            refine ⟨168080990900472412124249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 112053993933648274749499 168080990900472412124249)
            ·
              refine ⟨126060743175354309093187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 168080990900472412124249 126060743175354309093187)
              ·
                refine ⟨189091114763031463639781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 126060743175354309093187 189091114763031463639781)
                ·
                  refine ⟨35454584018068399432459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 189091114763031463639781 35454584018068399432459)
                  ·
                    rfl

theorem cell21_155357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 2, 1, 2, 1, 4].length) (baseStart_155357 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_155357 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_155357 prefixEnd_155357 := by exact prefixLift 155357
  have htrace : WordTrace (prefixWord ++ tailWord_155357) baseStart_155357 baseEnd_155357 := by
    simpa [prefixWord, tailWord_155357, baseEnd_155357] using wordTrace_append hprefix tailTrace_155357
  have hstable : (prefixWord ++ tailWord_155357).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_155357).length < 2 ^ (prefixWord ++ tailWord_155357).sum := by decide
  have hdescent : baseEnd_155357 < baseStart_155357 := by decide
  rcases family_descends (prefixWord ++ tailWord_155357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_155365 : List Nat := [1, 3, 1, 4, 1, 1, 3, 3, 4]
def baseStart_155365 : Nat := 118140960795 + 155365 * 2 ^ 59
def prefixEnd_155365 : Nat := 4983230072969 + 3 ^ 40 * 155365 * 2
def baseEnd_155365 : Nat := 35456409727062163299109

theorem tailTrace_155365 : CollatzResearch.WordTrace tailWord_155365 prefixEnd_155365 35456409727062163299109 := by
  unfold tailWord_155365
  simp only [CollatzResearch.WordTrace]
  refine ⟨5666627082146614074611549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3777751388097742716407699 5666627082146614074611549)
  ·
    refine ⟨2124985155804980277979331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5666627082146614074611549 2124985155804980277979331)
    ·
      refine ⟨3187477733707470416968997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2124985155804980277979331 3187477733707470416968997)
      ·
        refine ⟨597652075070150703181687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3187477733707470416968997 597652075070150703181687)
        ·
          refine ⟨896478112605226054772531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 597652075070150703181687 896478112605226054772531)
          ·
            refine ⟨1344717168907839082158797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 896478112605226054772531 1344717168907839082158797)
            ·
              refine ⟨504268938340439655809549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1344717168907839082158797 504268938340439655809549)
              ·
                refine ⟨189100851877664870928581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 504268938340439655809549 189100851877664870928581)
                ·
                  refine ⟨35456409727062163299109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 189100851877664870928581 35456409727062163299109)
                  ·
                    rfl

theorem cell21_155365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 3, 3, 4].length) (baseStart_155365 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_155365 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_155365 prefixEnd_155365 := by exact prefixLift 155365
  have htrace : WordTrace (prefixWord ++ tailWord_155365) baseStart_155365 baseEnd_155365 := by
    simpa [prefixWord, tailWord_155365, baseEnd_155365] using wordTrace_append hprefix tailTrace_155365
  have hstable : (prefixWord ++ tailWord_155365).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_155365).length < 2 ^ (prefixWord ++ tailWord_155365).sum := by decide
  have hdescent : baseEnd_155365 < baseStart_155365 := by decide
  rcases family_descends (prefixWord ++ tailWord_155365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_155444 : List Nat := [2, 5, 1, 1, 2, 1, 1, 5, 3]
def baseStart_155444 : Nat := 118140960795 + 155444 * 2 ^ 59
def prefixEnd_155444 : Nat := 4983230072969 + 3 ^ 40 * 155444 * 2
def baseEnd_155444 : Nat := 35474438603375581482281

theorem tailTrace_155444 : CollatzResearch.WordTrace tailWord_155444 prefixEnd_155444 35474438603375581482281 := by
  unfold tailWord_155444
  simp only [CollatzResearch.WordTrace]
  refine ⟨2834754224430205283368693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3779672299240273711158257 2834754224430205283368693)
  ·
    refine ⟨265758208540331745315815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 2834754224430205283368693 265758208540331745315815)
    ·
      refine ⟨398637312810497617973723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 265758208540331745315815 398637312810497617973723)
      ·
        refine ⟨597955969215746426960585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 398637312810497617973723 597955969215746426960585)
        ·
          refine ⟨448466976911809820220439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 597955969215746426960585 448466976911809820220439)
          ·
            refine ⟨672700465367714730330659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 448466976911809820220439 672700465367714730330659)
            ·
              refine ⟨1009050698051572095495989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 672700465367714730330659 1009050698051572095495989)
              ·
                refine ⟨94598502942334883952749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1009050698051572095495989 94598502942334883952749)
                ·
                  refine ⟨35474438603375581482281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 94598502942334883952749 35474438603375581482281)
                  ·
                    rfl

theorem cell21_155444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 1, 5, 3].length) (baseStart_155444 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_155444 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_155444 prefixEnd_155444 := by exact prefixLift 155444
  have htrace : WordTrace (prefixWord ++ tailWord_155444) baseStart_155444 baseEnd_155444 := by
    simpa [prefixWord, tailWord_155444, baseEnd_155444] using wordTrace_append hprefix tailTrace_155444
  have hstable : (prefixWord ++ tailWord_155444).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_155444).length < 2 ^ (prefixWord ++ tailWord_155444).sum := by decide
  have hdescent : baseEnd_155444 < baseStart_155444 := by decide
  rcases family_descends (prefixWord ++ tailWord_155444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_155455 : List Nat := [1, 1, 2, 2, 6, 1, 8]
def baseStart_155455 : Nat := 118140960795 + 155455 * 2 ^ 59
def prefixEnd_155455 : Nat := 4983230072969 + 3 ^ 40 * 155455 * 2
def baseEnd_155455 : Nat := 3941883217026889644325

theorem tailTrace_155455 : CollatzResearch.WordTrace tailWord_155455 prefixEnd_155455 3941883217026889644325 := by
  unfold tailWord_155455
  simp only [CollatzResearch.WordTrace]
  refine ⟨5669909651820559445387819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3779939767880372963591879 5669909651820559445387819)
  ·
    refine ⟨8504864477730839168081729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5669909651820559445387819 8504864477730839168081729)
    ·
      refine ⟨6378648358298129376061297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8504864477730839168081729 6378648358298129376061297)
      ·
        refine ⟨4783986268723597032045973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6378648358298129376061297 4783986268723597032045973)
        ·
          refine ⟨224249356346418610877155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 4783986268723597032045973 224249356346418610877155)
          ·
            refine ⟨336374034519627916315733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 224249356346418610877155 336374034519627916315733)
            ·
              refine ⟨3941883217026889644325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 336374034519627916315733 3941883217026889644325)
              ·
                rfl

theorem cell21_155455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 1, 8].length) (baseStart_155455 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_155455 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_155455 prefixEnd_155455 := by exact prefixLift 155455
  have htrace : WordTrace (prefixWord ++ tailWord_155455) baseStart_155455 baseEnd_155455 := by
    simpa [prefixWord, tailWord_155455, baseEnd_155455] using wordTrace_append hprefix tailTrace_155455
  have hstable : (prefixWord ++ tailWord_155455).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_155455).length < 2 ^ (prefixWord ++ tailWord_155455).sum := by decide
  have hdescent : baseEnd_155455 < baseStart_155455 := by decide
  rcases family_descends (prefixWord ++ tailWord_155455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_155500 : List Nat := [2, 2, 1, 1, 4, 2, 1, 2, 6]
def baseStart_155500 : Nat := 118140960795 + 155500 * 2 ^ 59
def prefixEnd_155500 : Nat := 4983230072969 + 3 ^ 40 * 155500 * 2
def baseEnd_155500 : Nat := 35487218566331928548833

theorem tailTrace_155500 : CollatzResearch.WordTrace tailWord_155500 prefixEnd_155500 35487218566331928548833 := by
  unfold tailWord_155500
  simp only [CollatzResearch.WordTrace]
  refine ⟨2835775468328766065387977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3781033957771688087183969 2835775468328766065387977)
  ·
    refine ⟨2126831601246574549040983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2835775468328766065387977 2126831601246574549040983)
    ·
      refine ⟨3190247401869861823561475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2126831601246574549040983 3190247401869861823561475)
      ·
        refine ⟨4785371102804792735342213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3190247401869861823561475 4785371102804792735342213)
        ·
          refine ⟨897257081775898637876665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4785371102804792735342213 897257081775898637876665)
          ·
            refine ⟨672942811331923978407499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 897257081775898637876665 672942811331923978407499)
            ·
              refine ⟨1009414216997885967611249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 672942811331923978407499 1009414216997885967611249)
              ·
                refine ⟨757060662748414475708437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1009414216997885967611249 757060662748414475708437)
                ·
                  refine ⟨35487218566331928548833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 757060662748414475708437 35487218566331928548833)
                  ·
                    rfl

theorem cell21_155500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 6].length) (baseStart_155500 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_155500 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_155500 prefixEnd_155500 := by exact prefixLift 155500
  have htrace : WordTrace (prefixWord ++ tailWord_155500) baseStart_155500 baseEnd_155500 := by
    simpa [prefixWord, tailWord_155500, baseEnd_155500] using wordTrace_append hprefix tailTrace_155500
  have hstable : (prefixWord ++ tailWord_155500).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_155500).length < 2 ^ (prefixWord ++ tailWord_155500).sum := by decide
  have hdescent : baseEnd_155500 < baseStart_155500 := by decide
  rcases family_descends (prefixWord ++ tailWord_155500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_155514 : List Nat := [3, 1, 1, 1, 1, 1, 13]
def baseStart_155514 : Nat := 118140960795 + 155514 * 2 ^ 59
def prefixEnd_155514 : Nat := 4983230072969 + 3 ^ 40 * 155514 * 2
def baseEnd_155514 : Nat := 3943379284119001701719

theorem tailTrace_155514 : CollatzResearch.WordTrace tailWord_155514 prefixEnd_155514 3943379284119001701719 := by
  unfold tailWord_155514
  simp only [CollatzResearch.WordTrace]
  refine ⟨1418015389651703130446399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3781374372404541681190397 1418015389651703130446399)
  ·
    refine ⟨2127023084477554695669599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1418015389651703130446399 2127023084477554695669599)
    ·
      refine ⟨3190534626716332043504399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2127023084477554695669599 3190534626716332043504399)
      ·
        refine ⟨4785801940074498065256599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3190534626716332043504399 4785801940074498065256599)
        ·
          refine ⟨7178702910111747097884899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4785801940074498065256599 7178702910111747097884899)
          ·
            refine ⟨10768054365167620646827349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7178702910111747097884899 10768054365167620646827349)
            ·
              refine ⟨3943379284119001701719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 13 10768054365167620646827349 3943379284119001701719)
              ·
                rfl

theorem cell21_155514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 13].length) (baseStart_155514 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_155514 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_155514 prefixEnd_155514 := by exact prefixLift 155514
  have htrace : WordTrace (prefixWord ++ tailWord_155514) baseStart_155514 baseEnd_155514 := by
    simpa [prefixWord, tailWord_155514, baseEnd_155514] using wordTrace_append hprefix tailTrace_155514
  have hstable : (prefixWord ++ tailWord_155514).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_155514).length < 2 ^ (prefixWord ++ tailWord_155514).sum := by decide
  have hdescent : baseEnd_155514 < baseStart_155514 := by decide
  rcases family_descends (prefixWord ++ tailWord_155514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_155545 : List Nat := [1, 2, 1, 2, 1, 3, 2, 4, 5]
def baseStart_155545 : Nat := 118140960795 + 155545 * 2 ^ 59
def prefixEnd_155545 : Nat := 4983230072969 + 3 ^ 40 * 155545 * 2
def baseEnd_155545 : Nat := 35497488179421850298741

theorem tailTrace_155545 : CollatzResearch.WordTrace tailWord_155545 prefixEnd_155545 35497488179421850298741 := by
  unfold tailWord_155545
  simp only [CollatzResearch.WordTrace]
  refine ⟨5673192221494504816164089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3782128147663003210776059 5673192221494504816164089)
  ·
    refine ⟨4254894166120878612123067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5673192221494504816164089 4254894166120878612123067)
    ·
      refine ⟨6382341249181317918184601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4254894166120878612123067 6382341249181317918184601)
      ·
        refine ⟨4786755936885988438638451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6382341249181317918184601 4786755936885988438638451)
        ·
          refine ⟨7180133905328982657957677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4786755936885988438638451 7180133905328982657957677)
          ·
            refine ⟨2692550214498368496734129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7180133905328982657957677 2692550214498368496734129)
            ·
              refine ⟨2019412660873776372550597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2692550214498368496734129 2019412660873776372550597)
              ·
                refine ⟨378639873913833069853237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2019412660873776372550597 378639873913833069853237)
                ·
                  refine ⟨35497488179421850298741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 378639873913833069853237 35497488179421850298741)
                  ·
                    rfl

theorem cell21_155545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 2, 4, 5].length) (baseStart_155545 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_155545 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_155545 prefixEnd_155545 := by exact prefixLift 155545
  have htrace : WordTrace (prefixWord ++ tailWord_155545) baseStart_155545 baseEnd_155545 := by
    simpa [prefixWord, tailWord_155545, baseEnd_155545] using wordTrace_append hprefix tailTrace_155545
  have hstable : (prefixWord ++ tailWord_155545).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_155545).length < 2 ^ (prefixWord ++ tailWord_155545).sum := by decide
  have hdescent : baseEnd_155545 < baseStart_155545 := by decide
  rcases family_descends (prefixWord ++ tailWord_155545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_155607 : List Nat := [1, 1, 3, 2, 1, 1, 7, 5]
def baseStart_155607 : Nat := 118140960795 + 155607 * 2 ^ 59
def prefixEnd_155607 : Nat := 4983230072969 + 3 ^ 40 * 155607 * 2
def baseEnd_155607 : Nat := 11837212474707840088427

theorem tailTrace_155607 : CollatzResearch.WordTrace tailWord_155607 prefixEnd_155607 11837212474707840088427 := by
  unfold tailWord_155607
  simp only [CollatzResearch.WordTrace]
  refine ⟨5675453547269889404921075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3783635698179926269947383 5675453547269889404921075)
  ·
    refine ⟨8513180320904834107381613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5675453547269889404921075 8513180320904834107381613)
    ·
      refine ⟨3192442620339312790268105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8513180320904834107381613 3192442620339312790268105)
      ·
        refine ⟨2394331965254484592701079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3192442620339312790268105 2394331965254484592701079)
        ·
          refine ⟨3591497947881726889051619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2394331965254484592701079 3591497947881726889051619)
          ·
            refine ⟨5387246921822590333577429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3591497947881726889051619 5387246921822590333577429)
            ·
              refine ⟨126263599730216960943221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 5387246921822590333577429 126263599730216960943221)
              ·
                refine ⟨11837212474707840088427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 126263599730216960943221 11837212474707840088427)
                ·
                  rfl

theorem cell21_155607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 7, 5].length) (baseStart_155607 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_155607 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_155607 prefixEnd_155607 := by exact prefixLift 155607
  have htrace : WordTrace (prefixWord ++ tailWord_155607) baseStart_155607 baseEnd_155607 := by
    simpa [prefixWord, tailWord_155607, baseEnd_155607] using wordTrace_append hprefix tailTrace_155607
  have hstable : (prefixWord ++ tailWord_155607).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_155607).length < 2 ^ (prefixWord ++ tailWord_155607).sum := by decide
  have hdescent : baseEnd_155607 < baseStart_155607 := by decide
  rcases family_descends (prefixWord ++ tailWord_155607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_155759 : List Nat := [1, 1, 2, 1, 3, 6, 1, 6]
def baseStart_155759 : Nat := 118140960795 + 155759 * 2 ^ 59
def prefixEnd_155759 : Nat := 4983230072969 + 3 ^ 40 * 155759 * 2
def baseEnd_155759 : Nat := 11848775298335011243879

theorem tailTrace_155759 : CollatzResearch.WordTrace tailWord_155759 prefixEnd_155759 11848775298335011243879 := by
  unfold tailWord_155759
  simp only [CollatzResearch.WordTrace]
  refine ⟨5680997442719219364454331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3787331628479479576302887 5680997442719219364454331)
  ·
    refine ⟨8521496164078829046681497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5680997442719219364454331 8521496164078829046681497)
    ·
      refine ⟨6391122123059121785011123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8521496164078829046681497 6391122123059121785011123)
      ·
        refine ⟨9586683184588682677516685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6391122123059121785011123 9586683184588682677516685)
        ·
          refine ⟨3595006194220756004068757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9586683184588682677516685 3595006194220756004068757)
          ·
            refine ⟨168515915354097937690723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 3595006194220756004068757 168515915354097937690723)
            ·
              refine ⟨252773873031146906536085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 168515915354097937690723 252773873031146906536085)
              ·
                refine ⟨11848775298335011243879, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 252773873031146906536085 11848775298335011243879)
                ·
                  rfl

theorem cell21_155759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 6, 1, 6].length) (baseStart_155759 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_155759 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_155759 prefixEnd_155759 := by exact prefixLift 155759
  have htrace : WordTrace (prefixWord ++ tailWord_155759) baseStart_155759 baseEnd_155759 := by
    simpa [prefixWord, tailWord_155759, baseEnd_155759] using wordTrace_append hprefix tailTrace_155759
  have hstable : (prefixWord ++ tailWord_155759).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_155759).length < 2 ^ (prefixWord ++ tailWord_155759).sum := by decide
  have hdescent : baseEnd_155759 < baseStart_155759 := by decide
  rcases family_descends (prefixWord ++ tailWord_155759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_155773 : List Nat := [1, 4, 1, 1, 3, 2, 1, 1, 7]
def baseStart_155773 : Nat := 118140960795 + 155773 * 2 ^ 59
def prefixEnd_155773 : Nat := 4983230072969 + 3 ^ 40 * 155773 * 2
def baseEnd_155773 : Nat := 35549520885744120498275

theorem tailTrace_155773 : CollatzResearch.WordTrace tailWord_155773 prefixEnd_155773 35549520885744120498275 := by
  unfold tailWord_155773
  simp only [CollatzResearch.WordTrace]
  refine ⟨5681508064668499755463973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3787672043112333170309315 5681508064668499755463973)
  ·
    refine ⟨1065282762125343704149495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5681508064668499755463973 1065282762125343704149495)
    ·
      refine ⟨1597924143188015556224243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1065282762125343704149495 1597924143188015556224243)
      ·
        refine ⟨2396886214782023334336365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1597924143188015556224243 2396886214782023334336365)
        ·
          refine ⟨898832330543258750376137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2396886214782023334336365 898832330543258750376137)
          ·
            refine ⟨674124247907444062782103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 898832330543258750376137 674124247907444062782103)
            ·
              refine ⟨1011186371861166094173155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 674124247907444062782103 1011186371861166094173155)
              ·
                refine ⟨1516779557791749141259733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1011186371861166094173155 1516779557791749141259733)
                ·
                  refine ⟨35549520885744120498275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1516779557791749141259733 35549520885744120498275)
                  ·
                    rfl

theorem cell21_155773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 1, 1, 7].length) (baseStart_155773 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_155773 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_155773 prefixEnd_155773 := by exact prefixLift 155773
  have htrace : WordTrace (prefixWord ++ tailWord_155773) baseStart_155773 baseEnd_155773 := by
    simpa [prefixWord, tailWord_155773, baseEnd_155773] using wordTrace_append hprefix tailTrace_155773
  have hstable : (prefixWord ++ tailWord_155773).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_155773).length < 2 ^ (prefixWord ++ tailWord_155773).sum := by decide
  have hdescent : baseEnd_155773 < baseStart_155773 := by decide
  rcases family_descends (prefixWord ++ tailWord_155773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_155796 : List Nat := [2, 4, 2, 3, 2, 1, 1, 2, 4]
def baseStart_155796 : Nat := 118140960795 + 155796 * 2 ^ 59
def prefixEnd_155796 : Nat := 4983230072969 + 3 ^ 40 * 155796 * 2
def baseEnd_155796 : Nat := 35554769799101191614895

theorem tailTrace_155796 : CollatzResearch.WordTrace tailWord_155796 prefixEnd_155796 35554769799101191614895 := by
  unfold tailWord_155796
  simp only [CollatzResearch.WordTrace]
  refine ⟨2841173471792587341775621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3788231295723449789034161 2841173471792587341775621)
  ·
    refine ⟨532720025961110126582929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2841173471792587341775621 532720025961110126582929)
    ·
      refine ⟨399540019470832594937197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 532720025961110126582929 399540019470832594937197)
      ·
        refine ⟨149827507301562223101449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 399540019470832594937197 149827507301562223101449)
        ·
          refine ⟨112370630476171667326087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 149827507301562223101449 112370630476171667326087)
          ·
            refine ⟨168555945714257500989131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 112370630476171667326087 168555945714257500989131)
            ·
              refine ⟨252833918571386251483697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 168555945714257500989131 252833918571386251483697)
              ·
                refine ⟨189625438928539688612773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 252833918571386251483697 189625438928539688612773)
                ·
                  refine ⟨35554769799101191614895, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 189625438928539688612773 35554769799101191614895)
                  ·
                    rfl

theorem cell21_155796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 2, 1, 1, 2, 4].length) (baseStart_155796 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_155796 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_155796 prefixEnd_155796 := by exact prefixLift 155796
  have htrace : WordTrace (prefixWord ++ tailWord_155796) baseStart_155796 baseEnd_155796 := by
    simpa [prefixWord, tailWord_155796, baseEnd_155796] using wordTrace_append hprefix tailTrace_155796
  have hstable : (prefixWord ++ tailWord_155796).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_155796).length < 2 ^ (prefixWord ++ tailWord_155796).sum := by decide
  have hdescent : baseEnd_155796 < baseStart_155796 := by decide
  rcases family_descends (prefixWord ++ tailWord_155796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_155804 : List Nat := [2, 2, 3, 2, 1, 1, 3, 1, 6]
def baseStart_155804 : Nat := 118140960795 + 155804 * 2 ^ 59
def prefixEnd_155804 : Nat := 4983230072969 + 3 ^ 40 * 155804 * 2
def baseEnd_155804 : Nat := 35556595508094955481545

theorem tailTrace_155804 : CollatzResearch.WordTrace tailWord_155804 prefixEnd_155804 35556595508094955481545 := by
  unfold tailWord_155804
  simp only [CollatzResearch.WordTrace]
  refine ⟨2841319363778096024921233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3788425818370794699894977 2841319363778096024921233)
  ·
    refine ⟨2130989522833572018690925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2841319363778096024921233 2130989522833572018690925)
    ·
      refine ⟨799121071062589507009097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2130989522833572018690925 799121071062589507009097)
      ·
        refine ⟨599340803296942130256823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 799121071062589507009097 599340803296942130256823)
        ·
          refine ⟨899011204945413195385235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 599340803296942130256823 899011204945413195385235)
          ·
            refine ⟨1348516807418119793077853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 899011204945413195385235 1348516807418119793077853)
            ·
              refine ⟨505693802781794922404195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1348516807418119793077853 505693802781794922404195)
              ·
                refine ⟨758540704172692383606293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 505693802781794922404195 758540704172692383606293)
                ·
                  refine ⟨35556595508094955481545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 758540704172692383606293 35556595508094955481545)
                  ·
                    rfl

theorem cell21_155804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 3, 1, 6].length) (baseStart_155804 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_155804 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_155804 prefixEnd_155804 := by exact prefixLift 155804
  have htrace : WordTrace (prefixWord ++ tailWord_155804) baseStart_155804 baseEnd_155804 := by
    simpa [prefixWord, tailWord_155804, baseEnd_155804] using wordTrace_append hprefix tailTrace_155804
  have hstable : (prefixWord ++ tailWord_155804).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_155804).length < 2 ^ (prefixWord ++ tailWord_155804).sum := by decide
  have hdescent : baseEnd_155804 < baseStart_155804 := by decide
  rcases family_descends (prefixWord ++ tailWord_155804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_155807 : List Nat := [1, 1, 2, 6, 1, 1, 2, 4, 3]
def baseStart_155807 : Nat := 118140960795 + 155807 * 2 ^ 59
def prefixEnd_155807 : Nat := 4983230072969 + 3 ^ 40 * 155807 * 2
def baseEnd_155807 : Nat := 35557280148967616931539

theorem tailTrace_155807 : CollatzResearch.WordTrace tailWord_155807 prefixEnd_155807 35557280148967616931539 := by
  unfold tailWord_155807
  simp only [CollatzResearch.WordTrace]
  refine ⟨5682748146545323562201675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3788498764363549041467783 5682748146545323562201675)
  ·
    refine ⟨8524122219817985343302513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5682748146545323562201675 8524122219817985343302513)
    ·
      refine ⟨6393091664863489007476885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8524122219817985343302513 6393091664863489007476885)
      ·
        refine ⟨299676171790476047225479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 6393091664863489007476885 299676171790476047225479)
        ·
          refine ⟨449514257685714070838219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 299676171790476047225479 449514257685714070838219)
          ·
            refine ⟨674271386528571106257329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 449514257685714070838219 674271386528571106257329)
            ·
              refine ⟨505703539896428329692997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 674271386528571106257329 505703539896428329692997)
              ·
                refine ⟨94819413730580311817437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 505703539896428329692997 94819413730580311817437)
                ·
                  refine ⟨35557280148967616931539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 94819413730580311817437 35557280148967616931539)
                  ·
                    rfl

theorem cell21_155807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 2, 4, 3].length) (baseStart_155807 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_155807 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_155807 prefixEnd_155807 := by exact prefixLift 155807
  have htrace : WordTrace (prefixWord ++ tailWord_155807) baseStart_155807 baseEnd_155807 := by
    simpa [prefixWord, tailWord_155807, baseEnd_155807] using wordTrace_append hprefix tailTrace_155807
  have hstable : (prefixWord ++ tailWord_155807).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_155807).length < 2 ^ (prefixWord ++ tailWord_155807).sum := by decide
  have hdescent : baseEnd_155807 < baseStart_155807 := by decide
  rcases family_descends (prefixWord ++ tailWord_155807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan21Incremental
