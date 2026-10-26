import V185TrunkScan20Chunk080

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental

namespace V185TrunkScan20Incremental

def tailWord_493027 : List Nat := [1, 1, 1, 6, 2, 1, 1, 5, 2]
def baseStart_493027 : Nat := 118140960795 + 493027 * 2 ^ 59
def prefixEnd_493027 : Nat := 4983230072969 + 3 ^ 40 * 493027 * 2
def baseEnd_493027 : Nat := 225030957017198011817881

theorem tailTrace_493027 : CollatzResearch.WordTrace tailWord_493027 prefixEnd_493027 225030957017198011817881 := by
  unfold tailWord_493027
  simp only [CollatzResearch.WordTrace]
  refine ⟨17982171984854856153021335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11988114656569904102014223 17982171984854856153021335)
  ·
    refine ⟨26973257977282284229532003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17982171984854856153021335 26973257977282284229532003)
    ·
      refine ⟨40459886965923426344298005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26973257977282284229532003 40459886965923426344298005)
      ·
        refine ⟨1896557201527660609888969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 40459886965923426344298005 1896557201527660609888969)
        ·
          refine ⟨1422417901145745457416727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1896557201527660609888969 1422417901145745457416727)
          ·
            refine ⟨2133626851718618186125091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1422417901145745457416727 2133626851718618186125091)
            ·
              refine ⟨3200440277577927279187637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2133626851718618186125091 3200440277577927279187637)
              ·
                refine ⟨300041276022930682423841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3200440277577927279187637 300041276022930682423841)
                ·
                  refine ⟨225030957017198011817881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 300041276022930682423841 225030957017198011817881)
                  ·
                    rfl

theorem cell20_493027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 1, 5, 2].length) (baseStart_493027 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_493027 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_493027 prefixEnd_493027 := by exact prefixLift 493027
  have htrace : WordTrace (prefixWord ++ tailWord_493027) baseStart_493027 baseEnd_493027 := by
    simpa [prefixWord, tailWord_493027, baseEnd_493027] using wordTrace_append hprefix tailTrace_493027
  have hstable : (prefixWord ++ tailWord_493027).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_493027).length < 2 ^ (prefixWord ++ tailWord_493027).sum := by decide
  have hdescent : baseEnd_493027 < baseStart_493027 := by decide
  rcases family_descends (prefixWord ++ tailWord_493027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_493037 : List Nat := [1, 5, 1, 3, 2, 2, 1, 2, 3]
def baseStart_493037 : Nat := 118140960795 + 493037 * 2 ^ 59
def prefixEnd_493037 : Nat := 4983230072969 + 3 ^ 40 * 493037 * 2
def baseEnd_493037 : Nat := 225035521289682421484507

theorem tailTrace_493037 : CollatzResearch.WordTrace tailWord_493037 prefixEnd_493037 225035521289682421484507 := by
  unfold tailWord_493037
  simp only [CollatzResearch.WordTrace]
  refine ⟨17982536714818627860885365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11988357809879085240590243 17982536714818627860885365)
  ·
    refine ⟨1685862817014246361958003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 17982536714818627860885365 1685862817014246361958003)
    ·
      refine ⟨2528794225521369542937005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1685862817014246361958003 2528794225521369542937005)
      ·
        refine ⟨948297834570513578601377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2528794225521369542937005 948297834570513578601377)
        ·
          refine ⟨711223375927885183951033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 948297834570513578601377 711223375927885183951033)
          ·
            refine ⟨533417531945913887963275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 711223375927885183951033 533417531945913887963275)
            ·
              refine ⟨800126297918870831944913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 533417531945913887963275 800126297918870831944913)
              ·
                refine ⟨600094723439153123958685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 800126297918870831944913 600094723439153123958685)
                ·
                  refine ⟨225035521289682421484507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 600094723439153123958685 225035521289682421484507)
                  ·
                    rfl

theorem cell20_493037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 2, 1, 2, 3].length) (baseStart_493037 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_493037 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_493037 prefixEnd_493037 := by exact prefixLift 493037
  have htrace : WordTrace (prefixWord ++ tailWord_493037) baseStart_493037 baseEnd_493037 := by
    simpa [prefixWord, tailWord_493037, baseEnd_493037] using wordTrace_append hprefix tailTrace_493037
  have hstable : (prefixWord ++ tailWord_493037).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_493037).length < 2 ^ (prefixWord ++ tailWord_493037).sum := by decide
  have hdescent : baseEnd_493037 < baseStart_493037 := by decide
  rcases family_descends (prefixWord ++ tailWord_493037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_493041 : List Nat := [1, 2, 2, 2, 3, 2, 3, 2, 3]
def baseStart_493041 : Nat := 118140960795 + 493041 * 2 ^ 59
def prefixEnd_493041 : Nat := 4983230072969 + 3 ^ 40 * 493041 * 2
def baseEnd_493041 : Nat := 225037346998676185351157

theorem tailTrace_493041 : CollatzResearch.WordTrace tailWord_493041 prefixEnd_493041 225037346998676185351157 := by
  unfold tailWord_493041
  simp only [CollatzResearch.WordTrace]
  refine ⟨17982682606804136544030977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11988455071202757696020651 17982682606804136544030977)
  ·
    refine ⟨13487011955103102408023233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17982682606804136544030977 13487011955103102408023233)
    ·
      refine ⟨10115258966327326806017425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13487011955103102408023233 10115258966327326806017425)
      ·
        refine ⟨7586444224745495104513069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10115258966327326806017425 7586444224745495104513069)
        ·
          refine ⟨2844916584279560664192401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7586444224745495104513069 2844916584279560664192401)
          ·
            refine ⟨2133687438209670498144301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2844916584279560664192401 2133687438209670498144301)
            ·
              refine ⟨800132789328626436804113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2133687438209670498144301 800132789328626436804113)
              ·
                refine ⟨600099591996469827603085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 800132789328626436804113 600099591996469827603085)
                ·
                  refine ⟨225037346998676185351157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 600099591996469827603085 225037346998676185351157)
                  ·
                    rfl

theorem cell20_493041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 3, 2, 3].length) (baseStart_493041 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_493041 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_493041 prefixEnd_493041 := by exact prefixLift 493041
  have htrace : WordTrace (prefixWord ++ tailWord_493041) baseStart_493041 baseEnd_493041 := by
    simpa [prefixWord, tailWord_493041, baseEnd_493041] using wordTrace_append hprefix tailTrace_493041
  have hstable : (prefixWord ++ tailWord_493041).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_493041).length < 2 ^ (prefixWord ++ tailWord_493041).sum := by decide
  have hdescent : baseEnd_493041 < baseStart_493041 := by decide
  rcases family_descends (prefixWord ++ tailWord_493041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_493048 : List Nat := [2, 1, 2, 1, 1, 6, 2, 1, 4]
def baseStart_493048 : Nat := 118140960795 + 493048 * 2 ^ 59
def prefixEnd_493048 : Nat := 4983230072969 + 3 ^ 40 * 493048 * 2
def baseEnd_493048 : Nat := 225040541989415272117795

theorem tailTrace_493048 : CollatzResearch.WordTrace tailWord_493048 prefixEnd_493048 225040541989415272117795 := by
  unfold tailWord_493048
  simp only [CollatzResearch.WordTrace]
  refine ⟨8991468958889388369767899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11988625278519184493023865 8991468958889388369767899)
  ·
    refine ⟨13487203438334082554651849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8991468958889388369767899 13487203438334082554651849)
    ·
      refine ⟨10115402578750561915988887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13487203438334082554651849 10115402578750561915988887)
      ·
        refine ⟨15173103868125842873983331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10115402578750561915988887 15173103868125842873983331)
        ·
          refine ⟨22759655802188764310974997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15173103868125842873983331 22759655802188764310974997)
          ·
            refine ⟨1066858865727598327076953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 22759655802188764310974997 1066858865727598327076953)
            ·
              refine ⟨800144149295698745307715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1066858865727598327076953 800144149295698745307715)
              ·
                refine ⟨1200216223943548117961573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 800144149295698745307715 1200216223943548117961573)
                ·
                  refine ⟨225040541989415272117795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1200216223943548117961573 225040541989415272117795)
                  ·
                    rfl

theorem cell20_493048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 6, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 6, 2, 1, 4].length) (baseStart_493048 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_493048 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_493048 prefixEnd_493048 := by exact prefixLift 493048
  have htrace : WordTrace (prefixWord ++ tailWord_493048) baseStart_493048 baseEnd_493048 := by
    simpa [prefixWord, tailWord_493048, baseEnd_493048] using wordTrace_append hprefix tailTrace_493048
  have hstable : (prefixWord ++ tailWord_493048).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_493048).length < 2 ^ (prefixWord ++ tailWord_493048).sum := by decide
  have hdescent : baseEnd_493048 < baseStart_493048 := by decide
  rcases family_descends (prefixWord ++ tailWord_493048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_493054 : List Nat := [4, 2, 2, 3, 1, 1, 3, 1, 3]
def baseStart_493054 : Nat := 118140960795 + 493054 * 2 ^ 59
def prefixEnd_493054 : Nat := 4983230072969 + 3 ^ 40 * 493054 * 2
def baseEnd_493054 : Nat := 225043280552905917917771

theorem tailTrace_493054 : CollatzResearch.WordTrace tailWord_493054 prefixEnd_493054 225043280552905917917771 := by
  unfold tailWord_493054
  simp only [CollatzResearch.WordTrace]
  refine ⟨2247894594469629970531777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 11988771170504693176169477 2247894594469629970531777)
  ·
    refine ⟨1685920945852222477898833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2247894594469629970531777 1685920945852222477898833)
    ·
      refine ⟨1264440709389166858424125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1685920945852222477898833 1264440709389166858424125)
      ·
        refine ⟨474165266020937571909047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1264440709389166858424125 474165266020937571909047)
        ·
          refine ⟨711247899031406357863571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 474165266020937571909047 711247899031406357863571)
          ·
            refine ⟨1066871848547109536795357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 711247899031406357863571 1066871848547109536795357)
            ·
              refine ⟨400076943205166076298259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1066871848547109536795357 400076943205166076298259)
              ·
                refine ⟨600115414807749114447389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 400076943205166076298259 600115414807749114447389)
                ·
                  refine ⟨225043280552905917917771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 600115414807749114447389 225043280552905917917771)
                  ·
                    rfl

theorem cell20_493054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 1, 3, 1, 3].length) (baseStart_493054 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_493054 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_493054 prefixEnd_493054 := by exact prefixLift 493054
  have htrace : WordTrace (prefixWord ++ tailWord_493054) baseStart_493054 baseEnd_493054 := by
    simpa [prefixWord, tailWord_493054, baseEnd_493054] using wordTrace_append hprefix tailTrace_493054
  have hstable : (prefixWord ++ tailWord_493054).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_493054).length < 2 ^ (prefixWord ++ tailWord_493054).sum := by decide
  have hdescent : baseEnd_493054 < baseStart_493054 := by decide
  rcases family_descends (prefixWord ++ tailWord_493054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_493155 : List Nat := [1, 1, 1, 5, 1, 4, 2, 2, 3]
def baseStart_493155 : Nat := 118140960795 + 493155 * 2 ^ 59
def prefixEnd_493155 : Nat := 4983230072969 + 3 ^ 40 * 493155 * 2
def baseEnd_493155 : Nat := 225089379704998455550691

theorem tailTrace_493155 : CollatzResearch.WordTrace tailWord_493155 prefixEnd_493155 225089379704998455550691 := by
  unfold tailWord_493155
  simp only [CollatzResearch.WordTrace]
  refine ⟨17986840528391134013680919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11991227018927422675787279 17986840528391134013680919)
  ·
    refine ⟨26980260792586701020521379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17986840528391134013680919 26980260792586701020521379)
    ·
      refine ⟨40470391188880051530782069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26980260792586701020521379 40470391188880051530782069)
      ·
        refine ⟨3794099173957504831010819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 40470391188880051530782069 3794099173957504831010819)
        ·
          refine ⟨5691148760936257246516229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3794099173957504831010819 5691148760936257246516229)
          ·
            refine ⟨1067090392675548233721793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5691148760936257246516229 1067090392675548233721793)
            ·
              refine ⟨800317794506661175291345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1067090392675548233721793 800317794506661175291345)
              ·
                refine ⟨600238345879995881468509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 800317794506661175291345 600238345879995881468509)
                ·
                  refine ⟨225089379704998455550691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 600238345879995881468509 225089379704998455550691)
                  ·
                    rfl

theorem cell20_493155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 4, 2, 2, 3].length) (baseStart_493155 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_493155 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_493155 prefixEnd_493155 := by exact prefixLift 493155
  have htrace : WordTrace (prefixWord ++ tailWord_493155) baseStart_493155 baseEnd_493155 := by
    simpa [prefixWord, tailWord_493155, baseEnd_493155] using wordTrace_append hprefix tailTrace_493155
  have hstable : (prefixWord ++ tailWord_493155).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_493155).length < 2 ^ (prefixWord ++ tailWord_493155).sum := by decide
  have hdescent : baseEnd_493155 < baseStart_493155 := by decide
  rcases family_descends (prefixWord ++ tailWord_493155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_493165 : List Nat := [1, 5, 1, 1, 5, 1, 1, 5]
def baseStart_493165 : Nat := 118140960795 + 493165 * 2 ^ 59
def prefixEnd_493165 : Nat := 4983230072969 + 3 ^ 40 * 493165 * 2
def baseEnd_493165 : Nat := 75031314659160955072439

theorem tailTrace_493165 : CollatzResearch.WordTrace tailWord_493165 prefixEnd_493165 75031314659160955072439 := by
  unfold tailWord_493165
  simp only [CollatzResearch.WordTrace]
  refine ⟨17987205258354905721544949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11991470172236603814363299 17987205258354905721544949)
  ·
    refine ⟨1686300492970772411394839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 17987205258354905721544949 1686300492970772411394839)
    ·
      refine ⟨2529450739456158617092259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1686300492970772411394839 2529450739456158617092259)
      ·
        refine ⟨3794176109184237925638389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2529450739456158617092259 3794176109184237925638389)
        ·
          refine ⟨355704010236022305528599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 3794176109184237925638389 355704010236022305528599)
          ·
            refine ⟨533556015354033458292899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 355704010236022305528599 533556015354033458292899)
            ·
              refine ⟨800334023031050187439349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 533556015354033458292899 800334023031050187439349)
              ·
                refine ⟨75031314659160955072439, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 800334023031050187439349 75031314659160955072439)
                ·
                  rfl

theorem cell20_493165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 5, 1, 1, 5].length) (baseStart_493165 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_493165 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_493165 prefixEnd_493165 := by exact prefixLift 493165
  have htrace : WordTrace (prefixWord ++ tailWord_493165) baseStart_493165 baseEnd_493165 := by
    simpa [prefixWord, tailWord_493165, baseEnd_493165] using wordTrace_append hprefix tailTrace_493165
  have hstable : (prefixWord ++ tailWord_493165).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_493165).length < 2 ^ (prefixWord ++ tailWord_493165).sum := by decide
  have hdescent : baseEnd_493165 < baseStart_493165 := by decide
  rcases family_descends (prefixWord ++ tailWord_493165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_493217 : List Nat := [1, 2, 3, 3, 2, 1, 2, 4, 2]
def baseStart_493217 : Nat := 118140960795 + 493217 * 2 ^ 59
def prefixEnd_493217 : Nat := 4983230072969 + 3 ^ 40 * 493217 * 2
def baseEnd_493217 : Nat := 225117678194401795483771

theorem tailTrace_493217 : CollatzResearch.WordTrace tailWord_493217 prefixEnd_493217 225117678194401795483771 := by
  unfold tailWord_493217
  simp only [CollatzResearch.WordTrace]
  refine ⟨17989101854166518602437905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11992734569444345734958603 17989101854166518602437905)
  ·
    refine ⟨13491826390624888951828429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17989101854166518602437905 13491826390624888951828429)
    ·
      refine ⟨5059434896484333356935661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13491826390624888951828429 5059434896484333356935661)
      ·
        refine ⟨1897288086181625008850873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5059434896484333356935661 1897288086181625008850873)
        ·
          refine ⟨1422966064636218756638155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1897288086181625008850873 1422966064636218756638155)
          ·
            refine ⟨2134449096954328134957233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1422966064636218756638155 2134449096954328134957233)
            ·
              refine ⟨1600836822715746101217925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2134449096954328134957233 1600836822715746101217925)
              ·
                refine ⟨300156904259202393978361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1600836822715746101217925 300156904259202393978361)
                ·
                  refine ⟨225117678194401795483771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 300156904259202393978361 225117678194401795483771)
                  ·
                    rfl

theorem cell20_493217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 2, 4, 2].length) (baseStart_493217 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_493217 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_493217 prefixEnd_493217 := by exact prefixLift 493217
  have htrace : WordTrace (prefixWord ++ tailWord_493217) baseStart_493217 baseEnd_493217 := by
    simpa [prefixWord, tailWord_493217, baseEnd_493217] using wordTrace_append hprefix tailTrace_493217
  have hstable : (prefixWord ++ tailWord_493217).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_493217).length < 2 ^ (prefixWord ++ tailWord_493217).sum := by decide
  have hdescent : baseEnd_493217 < baseStart_493217 := by decide
  rcases family_descends (prefixWord ++ tailWord_493217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_493221 : List Nat := [1, 3, 1, 2, 1, 2, 3, 3, 4]
def baseStart_493221 : Nat := 118140960795 + 493221 * 2 ^ 59
def prefixEnd_493221 : Nat := 4983230072969 + 3 ^ 40 * 493221 * 2
def baseEnd_493221 : Nat := 225119503903395559350421

theorem tailTrace_493221 : CollatzResearch.WordTrace tailWord_493221 prefixEnd_493221 225119503903395559350421 := by
  unfold tailWord_493221
  simp only [CollatzResearch.WordTrace]
  refine ⟨17989247746152027285583517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11992831830768018190389011 17989247746152027285583517)
  ·
    refine ⟨6745967904807010232093819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17989247746152027285583517 6745967904807010232093819)
    ·
      refine ⟨10118951857210515348140729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6745967904807010232093819 10118951857210515348140729)
      ·
        refine ⟨7589213892907886511105547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10118951857210515348140729 7589213892907886511105547)
        ·
          refine ⟨11383820839361829766658321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7589213892907886511105547 11383820839361829766658321)
          ·
            refine ⟨8537865629521372324993741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11383820839361829766658321 8537865629521372324993741)
            ·
              refine ⟨3201699611070514621872653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8537865629521372324993741 3201699611070514621872653)
              ·
                refine ⟨1200637354151442983202245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3201699611070514621872653 1200637354151442983202245)
                ·
                  refine ⟨225119503903395559350421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1200637354151442983202245 225119503903395559350421)
                  ·
                    rfl

theorem cell20_493221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 3, 3, 4].length) (baseStart_493221 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_493221 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_493221 prefixEnd_493221 := by exact prefixLift 493221
  have htrace : WordTrace (prefixWord ++ tailWord_493221) baseStart_493221 baseEnd_493221 := by
    simpa [prefixWord, tailWord_493221, baseEnd_493221] using wordTrace_append hprefix tailTrace_493221
  have hstable : (prefixWord ++ tailWord_493221).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_493221).length < 2 ^ (prefixWord ++ tailWord_493221).sum := by decide
  have hdescent : baseEnd_493221 < baseStart_493221 := by decide
  rcases family_descends (prefixWord ++ tailWord_493221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_493231 : List Nat := [1, 1, 2, 1, 2, 4, 5, 1, 3]
def baseStart_493231 : Nat := 118140960795 + 493231 * 2 ^ 59
def prefixEnd_493231 : Nat := 4983230072969 + 3 ^ 40 * 493231 * 2
def baseEnd_493231 : Nat := 225124068175879969017047

theorem tailTrace_493231 : CollatzResearch.WordTrace tailWord_493231 prefixEnd_493231 225124068175879969017047 := by
  unfold tailWord_493231
  simp only [CollatzResearch.WordTrace]
  refine ⟨17989612476115798993447547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11993074984077199328965031 17989612476115798993447547)
  ·
    refine ⟨26984418714173698490171321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17989612476115798993447547 26984418714173698490171321)
    ·
      refine ⟨20238314035630273867628491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26984418714173698490171321 20238314035630273867628491)
      ·
        refine ⟨30357471053445410801442737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20238314035630273867628491 30357471053445410801442737)
        ·
          refine ⟨22768103290084058101082053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30357471053445410801442737 22768103290084058101082053)
          ·
            refine ⟨4269019366890760893952885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22768103290084058101082053 4269019366890760893952885)
            ·
              refine ⟨400220565646008833808083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4269019366890760893952885 400220565646008833808083)
              ·
                refine ⟨600330848469013250712125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 400220565646008833808083 600330848469013250712125)
                ·
                  refine ⟨225124068175879969017047, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 600330848469013250712125 225124068175879969017047)
                  ·
                    rfl

theorem cell20_493231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 5, 1, 3].length) (baseStart_493231 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_493231 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_493231 prefixEnd_493231 := by exact prefixLift 493231
  have htrace : WordTrace (prefixWord ++ tailWord_493231) baseStart_493231 baseEnd_493231 := by
    simpa [prefixWord, tailWord_493231, baseEnd_493231] using wordTrace_append hprefix tailTrace_493231
  have hstable : (prefixWord ++ tailWord_493231).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_493231).length < 2 ^ (prefixWord ++ tailWord_493231).sum := by decide
  have hdescent : baseEnd_493231 < baseStart_493231 := by decide
  rcases family_descends (prefixWord ++ tailWord_493231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_493252 : List Nat := [2, 3, 3, 1, 1, 1, 1, 1, 7]
def baseStart_493252 : Nat := 118140960795 + 493252 * 2 ^ 59
def prefixEnd_493252 : Nat := 4983230072969 + 3 ^ 40 * 493252 * 2
def baseEnd_493252 : Nat := 225133653148097229316961

theorem tailTrace_493252 : CollatzResearch.WordTrace tailWord_493252 prefixEnd_493252 225133653148097229316961 := by
  unfold tailWord_493252
  simp only [CollatzResearch.WordTrace]
  refine ⟨8995189204519859789981005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11993585606026479719974673 8995189204519859789981005)
  ·
    refine ⟨3373195951694947421242877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8995189204519859789981005 3373195951694947421242877)
    ·
      refine ⟨1264948481885605282966079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3373195951694947421242877 1264948481885605282966079)
      ·
        refine ⟨1897422722828407924449119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1264948481885605282966079 1897422722828407924449119)
        ·
          refine ⟨2846134084242611886673679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1897422722828407924449119 2846134084242611886673679)
          ·
            refine ⟨4269201126363917830010519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2846134084242611886673679 4269201126363917830010519)
            ·
              refine ⟨6403801689545876745015779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4269201126363917830010519 6403801689545876745015779)
              ·
                refine ⟨9605702534318815117523669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6403801689545876745015779 9605702534318815117523669)
                ·
                  refine ⟨225133653148097229316961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9605702534318815117523669 225133653148097229316961)
                  ·
                    rfl

theorem cell20_493252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 1, 1, 7].length) (baseStart_493252 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_493252 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_493252 prefixEnd_493252 := by exact prefixLift 493252
  have htrace : WordTrace (prefixWord ++ tailWord_493252) baseStart_493252 baseEnd_493252 := by
    simpa [prefixWord, tailWord_493252, baseEnd_493252] using wordTrace_append hprefix tailTrace_493252
  have hstable : (prefixWord ++ tailWord_493252).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_493252).length < 2 ^ (prefixWord ++ tailWord_493252).sum := by decide
  have hdescent : baseEnd_493252 < baseStart_493252 := by decide
  rcases family_descends (prefixWord ++ tailWord_493252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_493311 : List Nat := [1, 1, 2, 2, 1, 3, 2, 1, 7]
def baseStart_493311 : Nat := 118140960795 + 493311 * 2 ^ 59
def prefixEnd_493311 : Nat := 4983230072969 + 3 ^ 40 * 493311 * 2
def baseEnd_493311 : Nat := 225160582355755246350053

theorem tailTrace_493311 : CollatzResearch.WordTrace tailWord_493311 prefixEnd_493311 225160582355755246350053 := by
  unfold tailWord_493311
  simp only [CollatzResearch.WordTrace]
  refine ⟨17992530315825972656359787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11995020210550648437573191 17992530315825972656359787)
  ·
    refine ⟨26988795473738958984539681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17992530315825972656359787 26988795473738958984539681)
    ·
      refine ⟨20241596605304219238404761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26988795473738958984539681 20241596605304219238404761)
      ·
        refine ⟨15181197453978164428803571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20241596605304219238404761 15181197453978164428803571)
        ·
          refine ⟨22771796180967246643205357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15181197453978164428803571 22771796180967246643205357)
          ·
            refine ⟨8539423567862717491202009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22771796180967246643205357 8539423567862717491202009)
            ·
              refine ⟨6404567675897038118401507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8539423567862717491202009 6404567675897038118401507)
              ·
                refine ⟨9606851513845557177602261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6404567675897038118401507 9606851513845557177602261)
                ·
                  refine ⟨225160582355755246350053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9606851513845557177602261 225160582355755246350053)
                  ·
                    rfl

theorem cell20_493311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 2, 1, 7].length) (baseStart_493311 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_493311 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_493311 prefixEnd_493311 := by exact prefixLift 493311
  have htrace : WordTrace (prefixWord ++ tailWord_493311) baseStart_493311 baseEnd_493311 := by
    simpa [prefixWord, tailWord_493311, baseEnd_493311] using wordTrace_append hprefix tailTrace_493311
  have hstable : (prefixWord ++ tailWord_493311).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_493311).length < 2 ^ (prefixWord ++ tailWord_493311).sum := by decide
  have hdescent : baseEnd_493311 < baseStart_493311 := by decide
  rcases family_descends (prefixWord ++ tailWord_493311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_493352 : List Nat := [2, 1, 5, 1, 1, 3, 1, 2, 4]
def baseStart_493352 : Nat := 118140960795 + 493352 * 2 ^ 59
def prefixEnd_493352 : Nat := 4983230072969 + 3 ^ 40 * 493352 * 2
def baseEnd_493352 : Nat := 225179295872941325983219

theorem tailTrace_493352 : CollatzResearch.WordTrace tailWord_493352 prefixEnd_493352 225179295872941325983219 := by
  unfold tailWord_493352
  simp only [CollatzResearch.WordTrace]
  refine ⟨8997012854338718329301155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11996017139118291105734873 8997012854338718329301155)
  ·
    refine ⟨13495519281508077493951733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8997012854338718329301155 13495519281508077493951733)
    ·
      refine ⟨1265204932641382265057975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 13495519281508077493951733 1265204932641382265057975)
      ·
        refine ⟨1897807398962073397586963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1265204932641382265057975 1897807398962073397586963)
        ·
          refine ⟨2846711098443110096380445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1897807398962073397586963 2846711098443110096380445)
          ·
            refine ⟨1067516661916166286142667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2846711098443110096380445 1067516661916166286142667)
            ·
              refine ⟨1601274992874249429214001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1067516661916166286142667 1601274992874249429214001)
              ·
                refine ⟨1200956244655687071910501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1601274992874249429214001 1200956244655687071910501)
                ·
                  refine ⟨225179295872941325983219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1200956244655687071910501 225179295872941325983219)
                  ·
                    rfl

theorem cell20_493352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 3, 1, 2, 4].length) (baseStart_493352 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_493352 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_493352 prefixEnd_493352 := by exact prefixLift 493352
  have htrace : WordTrace (prefixWord ++ tailWord_493352) baseStart_493352 baseEnd_493352 := by
    simpa [prefixWord, tailWord_493352, baseEnd_493352] using wordTrace_append hprefix tailTrace_493352
  have hstable : (prefixWord ++ tailWord_493352).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_493352).length < 2 ^ (prefixWord ++ tailWord_493352).sum := by decide
  have hdescent : baseEnd_493352 < baseStart_493352 := by decide
  rcases family_descends (prefixWord ++ tailWord_493352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_493425 : List Nat := [1, 2, 2, 2, 1, 3, 1, 1, 7]
def baseStart_493425 : Nat := 118140960795 + 493425 * 2 ^ 59
def prefixEnd_493425 : Nat := 4983230072969 + 3 ^ 40 * 493425 * 2
def baseEnd_493425 : Nat := 225212615062077516549587

theorem tailTrace_493425 : CollatzResearch.WordTrace tailWord_493425 prefixEnd_493425 225212615062077516549587 := by
  unfold tailWord_493425
  simp only [CollatzResearch.WordTrace]
  refine ⟨17996688237412970126009729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11997792158275313417339819 17996688237412970126009729)
  ·
    refine ⟨13497516178059727594507297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17996688237412970126009729 13497516178059727594507297)
    ·
      refine ⟨10123137133544795695880473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13497516178059727594507297 10123137133544795695880473)
      ·
        refine ⟨7592352850158596771910355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10123137133544795695880473 7592352850158596771910355)
        ·
          refine ⟨11388529275237895157865533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7592352850158596771910355 11388529275237895157865533)
          ·
            refine ⟨4270698478214210684199575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11388529275237895157865533 4270698478214210684199575)
            ·
              refine ⟨6406047717321316026299363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4270698478214210684199575 6406047717321316026299363)
              ·
                refine ⟨9609071575981974039449045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6406047717321316026299363 9609071575981974039449045)
                ·
                  refine ⟨225212615062077516549587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9609071575981974039449045 225212615062077516549587)
                  ·
                    rfl

theorem cell20_493425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 1, 1, 7].length) (baseStart_493425 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_493425 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_493425 prefixEnd_493425 := by exact prefixLift 493425
  have htrace : WordTrace (prefixWord ++ tailWord_493425) baseStart_493425 baseEnd_493425 := by
    simpa [prefixWord, tailWord_493425, baseEnd_493425] using wordTrace_append hprefix tailTrace_493425
  have hstable : (prefixWord ++ tailWord_493425).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_493425).length < 2 ^ (prefixWord ++ tailWord_493425).sum := by decide
  have hdescent : baseEnd_493425 < baseStart_493425 := by decide
  rcases family_descends (prefixWord ++ tailWord_493425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_493441 : List Nat := [1, 2, 4, 4, 1, 1, 3, 2, 2]
def baseStart_493441 : Nat := 118140960795 + 493441 * 2 ^ 59
def prefixEnd_493441 : Nat := 4983230072969 + 3 ^ 40 * 493441 * 2
def baseEnd_493441 : Nat := 225219917898052572016189

theorem tailTrace_493441 : CollatzResearch.WordTrace tailWord_493441 prefixEnd_493441 225219917898052572016189 := by
  unfold tailWord_493441
  simp only [CollatzResearch.WordTrace]
  refine ⟨17997271805355004858592177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11998181203570003239061451 17997271805355004858592177)
  ·
    refine ⟨13497953854016253643944133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17997271805355004858592177 13497953854016253643944133)
    ·
      refine ⟨2530866347628047558239525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13497953854016253643944133 2530866347628047558239525)
      ·
        refine ⟨474537440180258917169911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2530866347628047558239525 474537440180258917169911)
        ·
          refine ⟨711806160270388375754867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 474537440180258917169911 711806160270388375754867)
          ·
            refine ⟨1067709240405582563632301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 711806160270388375754867 1067709240405582563632301)
            ·
              refine ⟨400390965152093461362113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1067709240405582563632301 400390965152093461362113)
              ·
                refine ⟨300293223864070096021585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 400390965152093461362113 300293223864070096021585)
                ·
                  refine ⟨225219917898052572016189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 300293223864070096021585 225219917898052572016189)
                  ·
                    rfl

theorem cell20_493441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 1, 3, 2, 2].length) (baseStart_493441 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_493441 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_493441 prefixEnd_493441 := by exact prefixLift 493441
  have htrace : WordTrace (prefixWord ++ tailWord_493441) baseStart_493441 baseEnd_493441 := by
    simpa [prefixWord, tailWord_493441, baseEnd_493441] using wordTrace_append hprefix tailTrace_493441
  have hstable : (prefixWord ++ tailWord_493441).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_493441).length < 2 ^ (prefixWord ++ tailWord_493441).sum := by decide
  have hdescent : baseEnd_493441 < baseStart_493441 := by decide
  rcases family_descends (prefixWord ++ tailWord_493441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_493445 : List Nat := [1, 3, 1, 1, 3, 2, 5, 2, 2]
def baseStart_493445 : Nat := 118140960795 + 493445 * 2 ^ 59
def prefixEnd_493445 : Nat := 4983230072969 + 3 ^ 40 * 493445 * 2
def baseEnd_493445 : Nat := 225221743607046335882839

theorem tailTrace_493445 : CollatzResearch.WordTrace tailWord_493445 prefixEnd_493445 225221743607046335882839 := by
  unfold tailWord_493445
  simp only [CollatzResearch.WordTrace]
  refine ⟨17997417697340513541737789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 11998278464893675694491859 17997417697340513541737789)
  ·
    refine ⟨6749031636502692578151671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17997417697340513541737789 6749031636502692578151671)
    ·
      refine ⟨10123547454754038867227507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6749031636502692578151671 10123547454754038867227507)
      ·
        refine ⟨15185321182131058300841261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10123547454754038867227507 15185321182131058300841261)
        ·
          refine ⟨5694495443299146862815473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15185321182131058300841261 5694495443299146862815473)
          ·
            refine ⟨4270871582474360147111605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5694495443299146862815473 4270871582474360147111605)
            ·
              refine ⟨400394210856971263791713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4270871582474360147111605 400394210856971263791713)
              ·
                refine ⟨300295658142728447843785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 400394210856971263791713 300295658142728447843785)
                ·
                  refine ⟨225221743607046335882839, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 300295658142728447843785 225221743607046335882839)
                  ·
                    rfl

theorem cell20_493445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 5, 2, 2].length) (baseStart_493445 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_493445 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_493445 prefixEnd_493445 := by exact prefixLift 493445
  have htrace : WordTrace (prefixWord ++ tailWord_493445) baseStart_493445 baseEnd_493445 := by
    simpa [prefixWord, tailWord_493445, baseEnd_493445] using wordTrace_append hprefix tailTrace_493445
  have hstable : (prefixWord ++ tailWord_493445).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_493445).length < 2 ^ (prefixWord ++ tailWord_493445).sum := by decide
  have hdescent : baseEnd_493445 < baseStart_493445 := by decide
  rcases family_descends (prefixWord ++ tailWord_493445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_493500 : List Nat := [2, 2, 2, 5, 1, 1, 1, 4, 2]
def baseStart_493500 : Nat := 118140960795 + 493500 * 2 ^ 59
def prefixEnd_493500 : Nat := 4983230072969 + 3 ^ 40 * 493500 * 2
def baseEnd_493500 : Nat := 225246847105710589049281

theorem tailTrace_493500 : CollatzResearch.WordTrace tailWord_493500 prefixEnd_493500 225246847105710589049281 := by
  unfold tailWord_493500
  simp only [CollatzResearch.WordTrace]
  refine ⟨8999711856070628967494977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11999615808094171956659969 8999711856070628967494977)
  ·
    refine ⟨6749783892052971725621233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8999711856070628967494977 6749783892052971725621233)
    ·
      refine ⟨5062337919039728794215925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6749783892052971725621233 5062337919039728794215925)
      ·
        refine ⟨474594179909974574457743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 5062337919039728794215925 474594179909974574457743)
        ·
          refine ⟨711891269864961861686615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 474594179909974574457743 711891269864961861686615)
          ·
            refine ⟨1067836904797442792529923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 711891269864961861686615 1067836904797442792529923)
            ·
              refine ⟨1601755357196164188794885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1067836904797442792529923 1601755357196164188794885)
              ·
                refine ⟨300329129474280785399041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1601755357196164188794885 300329129474280785399041)
                ·
                  refine ⟨225246847105710589049281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 300329129474280785399041 225246847105710589049281)
                  ·
                    rfl

theorem cell20_493500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 1, 1, 4, 2].length) (baseStart_493500 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_493500 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_493500 prefixEnd_493500 := by exact prefixLift 493500
  have htrace : WordTrace (prefixWord ++ tailWord_493500) baseStart_493500 baseEnd_493500 := by
    simpa [prefixWord, tailWord_493500, baseEnd_493500] using wordTrace_append hprefix tailTrace_493500
  have hstable : (prefixWord ++ tailWord_493500).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_493500).length < 2 ^ (prefixWord ++ tailWord_493500).sum := by decide
  have hdescent : baseEnd_493500 < baseStart_493500 := by decide
  rcases family_descends (prefixWord ++ tailWord_493500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_493504 : List Nat := [2, 1, 1, 2, 3, 2, 3, 4, 2]
def baseStart_493504 : Nat := 118140960795 + 493504 * 2 ^ 59
def prefixEnd_493504 : Nat := 4983230072969 + 3 ^ 40 * 493504 * 2
def baseEnd_493504 : Nat := 225248672814704352915931

theorem tailTrace_493504 : CollatzResearch.WordTrace tailWord_493504 prefixEnd_493504 225248672814704352915931 := by
  unfold tailWord_493504
  simp only [CollatzResearch.WordTrace]
  refine ⟨8999784802063383309067783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 11999713069417844412090377 8999784802063383309067783)
  ·
    refine ⟨13499677203095074963601675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8999784802063383309067783 13499677203095074963601675)
    ·
      refine ⟨20249515804642612445402513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13499677203095074963601675 20249515804642612445402513)
      ·
        refine ⟨15187136853481959334051885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20249515804642612445402513 15187136853481959334051885)
        ·
          refine ⟨5695176320055734750269457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15187136853481959334051885 5695176320055734750269457)
          ·
            refine ⟨4271382240041801062702093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5695176320055734750269457 4271382240041801062702093)
            ·
              refine ⟨1601768340015675398513285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4271382240041801062702093 1601768340015675398513285)
              ·
                refine ⟨300331563752939137221241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1601768340015675398513285 300331563752939137221241)
                ·
                  refine ⟨225248672814704352915931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 300331563752939137221241 225248672814704352915931)
                  ·
                    rfl

theorem cell20_493504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 3, 4, 2].length) (baseStart_493504 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_493504 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_493504 prefixEnd_493504 := by exact prefixLift 493504
  have htrace : WordTrace (prefixWord ++ tailWord_493504) baseStart_493504 baseEnd_493504 := by
    simpa [prefixWord, tailWord_493504, baseEnd_493504] using wordTrace_append hprefix tailTrace_493504
  have hstable : (prefixWord ++ tailWord_493504).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_493504).length < 2 ^ (prefixWord ++ tailWord_493504).sum := by decide
  have hdescent : baseEnd_493504 < baseStart_493504 := by decide
  rcases family_descends (prefixWord ++ tailWord_493504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_493518 : List Nat := [4, 1, 1, 1, 2, 2, 1, 5, 3]
def baseStart_493518 : Nat := 118140960795 + 493518 * 2 ^ 59
def prefixEnd_493518 : Nat := 4983230072969 + 3 ^ 40 * 493518 * 2
def baseEnd_493518 : Nat := 225255062796182526449207

theorem tailTrace_493518 : CollatzResearch.WordTrace tailWord_493518 prefixEnd_493518 225255062796182526449207 := by
  unfold tailWord_493518
  simp only [CollatzResearch.WordTrace]
  refine ⟨2250010028259505876143151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12000053484050698006096805 2250010028259505876143151)
  ·
    refine ⟨3375015042389258814214727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2250010028259505876143151 3375015042389258814214727)
    ·
      refine ⟨5062522563583888221322091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3375015042389258814214727 5062522563583888221322091)
      ·
        refine ⟨7593783845375832331983137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5062522563583888221322091 7593783845375832331983137)
        ·
          refine ⟨5695337884031874248987353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7593783845375832331983137 5695337884031874248987353)
          ·
            refine ⟨4271503413023905686740515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5695337884031874248987353 4271503413023905686740515)
            ·
              refine ⟨6407255119535858530110773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4271503413023905686740515 6407255119535858530110773)
              ·
                refine ⟨600680167456486737197885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6407255119535858530110773 600680167456486737197885)
                ·
                  refine ⟨225255062796182526449207, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 600680167456486737197885 225255062796182526449207)
                  ·
                    rfl

theorem cell20_493518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 1, 5, 3].length) (baseStart_493518 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_493518 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_493518 prefixEnd_493518 := by exact prefixLift 493518
  have htrace : WordTrace (prefixWord ++ tailWord_493518) baseStart_493518 baseEnd_493518 := by
    simpa [prefixWord, tailWord_493518, baseEnd_493518] using wordTrace_append hprefix tailTrace_493518
  have hstable : (prefixWord ++ tailWord_493518).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_493518).length < 2 ^ (prefixWord ++ tailWord_493518).sum := by decide
  have hdescent : baseEnd_493518 < baseStart_493518 := by decide
  rcases family_descends (prefixWord ++ tailWord_493518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_493525 : List Nat := [1, 3, 2, 3, 2, 1, 1, 1, 6]
def baseStart_493525 : Nat := 118140960795 + 493525 * 2 ^ 59
def prefixEnd_493525 : Nat := 4983230072969 + 3 ^ 40 * 493525 * 2
def baseEnd_493525 : Nat := 225258257786921613215845

theorem tailTrace_493525 : CollatzResearch.WordTrace tailWord_493525 prefixEnd_493525 225258257786921613215845 := by
  unfold tailWord_493525
  simp only [CollatzResearch.WordTrace]
  refine ⟨18000335537050687204650029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12000223691367124803100019 18000335537050687204650029)
  ·
    refine ⟨6750125826394007701743761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18000335537050687204650029 6750125826394007701743761)
    ·
      refine ⟨5062594369795505776307821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6750125826394007701743761 5062594369795505776307821)
      ·
        refine ⟨1898472888673314666115433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5062594369795505776307821 1898472888673314666115433)
        ·
          refine ⟨1423854666504985999586575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1898472888673314666115433 1423854666504985999586575)
          ·
            refine ⟨2135781999757478999379863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1423854666504985999586575 2135781999757478999379863)
            ·
              refine ⟨3203672999636218499069795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2135781999757478999379863 3203672999636218499069795)
              ·
                refine ⟨4805509499454327748604693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3203672999636218499069795 4805509499454327748604693)
                ·
                  refine ⟨225258257786921613215845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4805509499454327748604693 225258257786921613215845)
                  ·
                    rfl

theorem cell20_493525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 1, 1, 6].length) (baseStart_493525 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_493525 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_493525 prefixEnd_493525 := by exact prefixLift 493525
  have htrace : WordTrace (prefixWord ++ tailWord_493525) baseStart_493525 baseEnd_493525 := by
    simpa [prefixWord, tailWord_493525, baseEnd_493525] using wordTrace_append hprefix tailTrace_493525
  have hstable : (prefixWord ++ tailWord_493525).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_493525).length < 2 ^ (prefixWord ++ tailWord_493525).sum := by decide
  have hdescent : baseEnd_493525 < baseStart_493525 := by decide
  rcases family_descends (prefixWord ++ tailWord_493525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_493573 : List Nat := [1, 3, 1, 1, 2, 5, 3, 1, 3]
def baseStart_493573 : Nat := 118140960795 + 493573 * 2 ^ 59
def prefixEnd_493573 : Nat := 4983230072969 + 3 ^ 40 * 493573 * 2
def baseEnd_493573 : Nat := 225280166294846779615649

theorem tailTrace_493573 : CollatzResearch.WordTrace tailWord_493573 prefixEnd_493573 225280166294846779615649 := by
  unfold tailWord_493573
  simp only [CollatzResearch.WordTrace]
  refine ⟨18002086240876791402397373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12001390827251194268264915 18002086240876791402397373)
  ·
    refine ⟨6750782340328796775899015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18002086240876791402397373 6750782340328796775899015)
    ·
      refine ⟨10126173510493195163848523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6750782340328796775899015 10126173510493195163848523)
      ·
        refine ⟨15189260265739792745772785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10126173510493195163848523 15189260265739792745772785)
        ·
          refine ⟨11391945199304844559329589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15189260265739792745772785 11391945199304844559329589)
          ·
            refine ⟨1067994862434829177437149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 11391945199304844559329589 1067994862434829177437149)
            ·
              refine ⟨400498073413060941538931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1067994862434829177437149 400498073413060941538931)
              ·
                refine ⟨600747110119591412308397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 400498073413060941538931 600747110119591412308397)
                ·
                  refine ⟨225280166294846779615649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 600747110119591412308397 225280166294846779615649)
                  ·
                    rfl

theorem cell20_493573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 5, 3, 1, 3].length) (baseStart_493573 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_493573 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_493573 prefixEnd_493573 := by exact prefixLift 493573
  have htrace : WordTrace (prefixWord ++ tailWord_493573) baseStart_493573 baseEnd_493573 := by
    simpa [prefixWord, tailWord_493573, baseEnd_493573] using wordTrace_append hprefix tailTrace_493573
  have hstable : (prefixWord ++ tailWord_493573).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_493573).length < 2 ^ (prefixWord ++ tailWord_493573).sum := by decide
  have hdescent : baseEnd_493573 < baseStart_493573 := by decide
  rcases family_descends (prefixWord ++ tailWord_493573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_493597 : List Nat := [1, 4, 2, 2, 2, 1, 3, 3, 2]
def baseStart_493597 : Nat := 118140960795 + 493597 * 2 ^ 59
def prefixEnd_493597 : Nat := 4983230072969 + 3 ^ 40 * 493597 * 2
def baseEnd_493597 : Nat := 225291120548809362815551

theorem tailTrace_493597 : CollatzResearch.WordTrace tailWord_493597 prefixEnd_493597 225291120548809362815551 := by
  unfold tailWord_493597
  simp only [CollatzResearch.WordTrace]
  refine ⟨18002961592789843501271045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12001974395193229000847363 18002961592789843501271045)
  ·
    refine ⟨3375555298648095656488321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18002961592789843501271045 3375555298648095656488321)
    ·
      refine ⟨2531666473986071742366241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3375555298648095656488321 2531666473986071742366241)
      ·
        refine ⟨1898749855489553806774681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2531666473986071742366241 1898749855489553806774681)
        ·
          refine ⟨1424062391617165355081011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1898749855489553806774681 1424062391617165355081011)
          ·
            refine ⟨2136093587425748032621517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1424062391617165355081011 2136093587425748032621517)
            ·
              refine ⟨801035095284655512233069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2136093587425748032621517 801035095284655512233069)
              ·
                refine ⟨300388160731745817087401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 801035095284655512233069 300388160731745817087401)
                ·
                  refine ⟨225291120548809362815551, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 300388160731745817087401 225291120548809362815551)
                  ·
                    rfl

theorem cell20_493597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 3, 3, 2].length) (baseStart_493597 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_493597 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_493597 prefixEnd_493597 := by exact prefixLift 493597
  have htrace : WordTrace (prefixWord ++ tailWord_493597) baseStart_493597 baseEnd_493597 := by
    simpa [prefixWord, tailWord_493597, baseEnd_493597] using wordTrace_append hprefix tailTrace_493597
  have hstable : (prefixWord ++ tailWord_493597).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_493597).length < 2 ^ (prefixWord ++ tailWord_493597).sum := by decide
  have hdescent : baseEnd_493597 < baseStart_493597 := by decide
  rcases family_descends (prefixWord ++ tailWord_493597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_493604 : List Nat := [2, 3, 1, 4, 3, 1, 6]
def baseStart_493604 : Nat := 118140960795 + 493604 * 2 ^ 59
def prefixEnd_493604 : Nat := 4983230072969 + 3 ^ 40 * 493604 * 2
def baseEnd_493604 : Nat := 25032701726616494398021

theorem tailTrace_493604 : CollatzResearch.WordTrace tailWord_493604 prefixEnd_493604 25032701726616494398021 := by
  unfold tailWord_493604
  simp only [CollatzResearch.WordTrace]
  refine ⟨9001608451882241848387933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12002144602509655797850577 9001608451882241848387933)
  ·
    refine ⟨3375603169455840693145475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9001608451882241848387933 3375603169455840693145475)
    ·
      refine ⟨5063404754183761039718213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3375603169455840693145475 5063404754183761039718213)
      ·
        refine ⟨949388391409455194947165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5063404754183761039718213 949388391409455194947165)
        ·
          refine ⟨356020646778545698105187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 949388391409455194947165 356020646778545698105187)
          ·
            refine ⟨534030970167818547157781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 356020646778545698105187 534030970167818547157781)
            ·
              refine ⟨25032701726616494398021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 534030970167818547157781 25032701726616494398021)
              ·
                rfl

theorem cell20_493604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 3, 1, 6].length) (baseStart_493604 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_493604 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_493604 prefixEnd_493604 := by exact prefixLift 493604
  have htrace : WordTrace (prefixWord ++ tailWord_493604) baseStart_493604 baseEnd_493604 := by
    simpa [prefixWord, tailWord_493604, baseEnd_493604] using wordTrace_append hprefix tailTrace_493604
  have hstable : (prefixWord ++ tailWord_493604).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_493604).length < 2 ^ (prefixWord ++ tailWord_493604).sum := by decide
  have hdescent : baseEnd_493604 < baseStart_493604 := by decide
  rcases family_descends (prefixWord ++ tailWord_493604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_493614 : List Nat := [4, 1, 3, 1, 1, 3, 3, 2, 2]
def baseStart_493614 : Nat := 118140960795 + 493614 * 2 ^ 59
def prefixEnd_493614 : Nat := 4983230072969 + 3 ^ 40 * 493614 * 2
def baseEnd_493614 : Nat := 225298879812032859248815

theorem tailTrace_493614 : CollatzResearch.WordTrace tailWord_493614 prefixEnd_493614 225298879812032859248815 := by
  unfold tailWord_493614
  simp only [CollatzResearch.WordTrace]
  refine ⟨2250447704216031925579987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12002387755818836936426597 2250447704216031925579987)
  ·
    refine ⟨3375671556324047888369981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2250447704216031925579987 3375671556324047888369981)
    ·
      refine ⟨1265876833621517958138743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3375671556324047888369981 1265876833621517958138743)
      ·
        refine ⟨1898815250432276937208115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1265876833621517958138743 1898815250432276937208115)
        ·
          refine ⟨2848222875648415405812173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1898815250432276937208115 2848222875648415405812173)
          ·
            refine ⟨1068083578368155777179565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2848222875648415405812173 1068083578368155777179565)
            ·
              refine ⟨400531341888058416442337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1068083578368155777179565 400531341888058416442337)
              ·
                refine ⟨300398506416043812331753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 400531341888058416442337 300398506416043812331753)
                ·
                  refine ⟨225298879812032859248815, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 300398506416043812331753 225298879812032859248815)
                  ·
                    rfl

theorem cell20_493614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 3, 3, 2, 2].length) (baseStart_493614 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_493614 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_493614 prefixEnd_493614 := by exact prefixLift 493614
  have htrace : WordTrace (prefixWord ++ tailWord_493614) baseStart_493614 baseEnd_493614 := by
    simpa [prefixWord, tailWord_493614, baseEnd_493614] using wordTrace_append hprefix tailTrace_493614
  have hstable : (prefixWord ++ tailWord_493614).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_493614).length < 2 ^ (prefixWord ++ tailWord_493614).sum := by decide
  have hdescent : baseEnd_493614 < baseStart_493614 := by decide
  rcases family_descends (prefixWord ++ tailWord_493614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_493618 : List Nat := [3, 2, 1, 1, 2, 5, 1, 1, 4]
def baseStart_493618 : Nat := 118140960795 + 493618 * 2 ^ 59
def prefixEnd_493618 : Nat := 4983230072969 + 3 ^ 40 * 493618 * 2
def baseEnd_493618 : Nat := 225300705521026623115465

theorem tailTrace_493618 : CollatzResearch.WordTrace tailWord_493618 prefixEnd_493618 225300705521026623115465 := by
  unfold tailWord_493618
  simp only [CollatzResearch.WordTrace]
  refine ⟨4500931881428441021946377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12002485017142509391857005 4500931881428441021946377)
  ·
    refine ⟨3375698911071330766459783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4500931881428441021946377 3375698911071330766459783)
    ·
      refine ⟨5063548366606996149689675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3375698911071330766459783 5063548366606996149689675)
      ·
        refine ⟨7595322549910494224534513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5063548366606996149689675 7595322549910494224534513)
        ·
          refine ⟨5696491912432870668400885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7595322549910494224534513 5696491912432870668400885)
          ·
            refine ⟨534046116790581625162583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 5696491912432870668400885 534046116790581625162583)
            ·
              refine ⟨801069175185872437743875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 534046116790581625162583 801069175185872437743875)
              ·
                refine ⟨1201603762778808656615813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 801069175185872437743875 1201603762778808656615813)
                ·
                  refine ⟨225300705521026623115465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1201603762778808656615813 225300705521026623115465)
                  ·
                    rfl

theorem cell20_493618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 5, 1, 1, 4].length) (baseStart_493618 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_493618 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_493618 prefixEnd_493618 := by exact prefixLift 493618
  have htrace : WordTrace (prefixWord ++ tailWord_493618) baseStart_493618 baseEnd_493618 := by
    simpa [prefixWord, tailWord_493618, baseEnd_493618] using wordTrace_append hprefix tailTrace_493618
  have hstable : (prefixWord ++ tailWord_493618).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_493618).length < 2 ^ (prefixWord ++ tailWord_493618).sum := by decide
  have hdescent : baseEnd_493618 < baseStart_493618 := by decide
  rcases family_descends (prefixWord ++ tailWord_493618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_493625 : List Nat := [1, 2, 1, 5, 3, 1, 2, 5]
def baseStart_493625 : Nat := 118140960795 + 493625 * 2 ^ 59
def prefixEnd_493625 : Nat := 4983230072969 + 3 ^ 40 * 493625 * 2
def baseEnd_493625 : Nat := 75101300170588569960701

theorem tailTrace_493625 : CollatzResearch.WordTrace tailWord_493625 prefixEnd_493625 75101300170588569960701 := by
  unfold tailWord_493625
  simp only [CollatzResearch.WordTrace]
  refine ⟨18003982836688404283290329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12002655224458936188860219 18003982836688404283290329)
  ·
    refine ⟨13502987127516303212467747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18003982836688404283290329 13502987127516303212467747)
    ·
      refine ⟨20254480691274454818701621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13502987127516303212467747 20254480691274454818701621)
      ·
        refine ⟨1898857564806980139253277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 20254480691274454818701621 1898857564806980139253277)
        ·
          refine ⟨712071586802617552219979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1898857564806980139253277 712071586802617552219979)
          ·
            refine ⟨1068107380203926328329969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 712071586802617552219979 1068107380203926328329969)
            ·
              refine ⟨801080535152944746247477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1068107380203926328329969 801080535152944746247477)
              ·
                refine ⟨75101300170588569960701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 801080535152944746247477 75101300170588569960701)
                ·
                  rfl

theorem cell20_493625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 1, 2, 5].length) (baseStart_493625 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_493625 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_493625 prefixEnd_493625 := by exact prefixLift 493625
  have htrace : WordTrace (prefixWord ++ tailWord_493625) baseStart_493625 baseEnd_493625 := by
    simpa [prefixWord, tailWord_493625, baseEnd_493625] using wordTrace_append hprefix tailTrace_493625
  have hstable : (prefixWord ++ tailWord_493625).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_493625).length < 2 ^ (prefixWord ++ tailWord_493625).sum := by decide
  have hdescent : baseEnd_493625 < baseStart_493625 := by decide
  rcases family_descends (prefixWord ++ tailWord_493625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_493632 : List Nat := [2, 1, 1, 2, 2, 5, 1, 3, 3]
def baseStart_493632 : Nat := 118140960795 + 493632 * 2 ^ 59
def prefixEnd_493632 : Nat := 4983230072969 + 3 ^ 40 * 493632 * 2
def baseEnd_493632 : Nat := 225307095502504796648741

theorem tailTrace_493632 : CollatzResearch.WordTrace tailWord_493632 prefixEnd_493632 225307095502504796648741 := by
  unfold tailWord_493632
  simp only [CollatzResearch.WordTrace]
  refine ⟨9002119073831522239397575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12002825431775362985863433 9002119073831522239397575)
  ·
    refine ⟨13503178610747283359096363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9002119073831522239397575 13503178610747283359096363)
    ·
      refine ⟨20254767916120925038644545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13503178610747283359096363 20254767916120925038644545)
      ·
        refine ⟨15191075937090693778983409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20254767916120925038644545 15191075937090693778983409)
        ·
          refine ⟨11393306952818020334237557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15191075937090693778983409 11393306952818020334237557)
          ·
            refine ⟨1068122526826689406334771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 11393306952818020334237557 1068122526826689406334771)
            ·
              refine ⟨1602183790240034109502157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1068122526826689406334771 1602183790240034109502157)
              ·
                refine ⟨600818921340012791063309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1602183790240034109502157 600818921340012791063309)
                ·
                  refine ⟨225307095502504796648741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 600818921340012791063309 225307095502504796648741)
                  ·
                    rfl

theorem cell20_493632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 5, 1, 3, 3].length) (baseStart_493632 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_493632 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_493632 prefixEnd_493632 := by exact prefixLift 493632
  have htrace : WordTrace (prefixWord ++ tailWord_493632) baseStart_493632 baseEnd_493632 := by
    simpa [prefixWord, tailWord_493632, baseEnd_493632] using wordTrace_append hprefix tailTrace_493632
  have hstable : (prefixWord ++ tailWord_493632).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_493632).length < 2 ^ (prefixWord ++ tailWord_493632).sum := by decide
  have hdescent : baseEnd_493632 < baseStart_493632 := by decide
  rcases family_descends (prefixWord ++ tailWord_493632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_493646 : List Nat := [4, 1, 1, 1, 1, 4, 2, 6]
def baseStart_493646 : Nat := 118140960795 + 493646 * 2 ^ 59
def prefixEnd_493646 : Nat := 4983230072969 + 3 ^ 40 * 493646 * 2
def baseEnd_493646 : Nat := 75104495161327656727339

theorem tailTrace_493646 : CollatzResearch.WordTrace tailWord_493646 prefixEnd_493646 75104495161327656727339 := by
  unfold tailWord_493646
  simp only [CollatzResearch.WordTrace]
  refine ⟨2250593596201540608725599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12003165846408216579869861 2250593596201540608725599)
  ·
    refine ⟨3375890394302310913088399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2250593596201540608725599 3375890394302310913088399)
    ·
      refine ⟨5063835591453466369632599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3375890394302310913088399 5063835591453466369632599)
      ·
        refine ⟨7595753387180199554448899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5063835591453466369632599 7595753387180199554448899)
        ·
          refine ⟨11393630080770299331673349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7595753387180199554448899 11393630080770299331673349)
          ·
            refine ⟨2136305640144431124688753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11393630080770299331673349 2136305640144431124688753)
            ·
              refine ⟨1602229230108323343516565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2136305640144431124688753 1602229230108323343516565)
              ·
                refine ⟨75104495161327656727339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1602229230108323343516565 75104495161327656727339)
                ·
                  rfl

theorem cell20_493646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 2, 6].length) (baseStart_493646 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_493646 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_493646 prefixEnd_493646 := by exact prefixLift 493646
  have htrace : WordTrace (prefixWord ++ tailWord_493646) baseStart_493646 baseEnd_493646 := by
    simpa [prefixWord, tailWord_493646, baseEnd_493646] using wordTrace_append hprefix tailTrace_493646
  have hstable : (prefixWord ++ tailWord_493646).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_493646).length < 2 ^ (prefixWord ++ tailWord_493646).sum := by decide
  have hdescent : baseEnd_493646 < baseStart_493646 := by decide
  rcases family_descends (prefixWord ++ tailWord_493646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_493666 : List Nat := [3, 3, 2, 2, 2, 1, 2, 2, 3]
def baseStart_493666 : Nat := 118140960795 + 493666 * 2 ^ 59
def prefixEnd_493666 : Nat := 4983230072969 + 3 ^ 40 * 493666 * 2
def baseEnd_493666 : Nat := 225322614028951789515269

theorem tailTrace_493666 : CollatzResearch.WordTrace tailWord_493666 prefixEnd_493666 225322614028951789515269 := by
  unfold tailWord_493666
  simp only [CollatzResearch.WordTrace]
  refine ⟨4501369557384967071383213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12003652153026578857021901 4501369557384967071383213)
  ·
    refine ⟨1688013584019362651768705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4501369557384967071383213 1688013584019362651768705)
    ·
      refine ⟨1266010188014521988826529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1688013584019362651768705 1266010188014521988826529)
      ·
        refine ⟨949507641010891491619897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1266010188014521988826529 949507641010891491619897)
        ·
          refine ⟨712130730758168618714923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 949507641010891491619897 712130730758168618714923)
          ·
            refine ⟨1068196096137252928072385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 712130730758168618714923 1068196096137252928072385)
            ·
              refine ⟨801147072102939696054289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1068196096137252928072385 801147072102939696054289)
              ·
                refine ⟨600860304077204772040717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 801147072102939696054289 600860304077204772040717)
                ·
                  refine ⟨225322614028951789515269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 600860304077204772040717 225322614028951789515269)
                  ·
                    rfl

theorem cell20_493666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 1, 2, 2, 3].length) (baseStart_493666 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_493666 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_493666 prefixEnd_493666 := by exact prefixLift 493666
  have htrace : WordTrace (prefixWord ++ tailWord_493666) baseStart_493666 baseEnd_493666 := by
    simpa [prefixWord, tailWord_493666, baseEnd_493666] using wordTrace_append hprefix tailTrace_493666
  have hstable : (prefixWord ++ tailWord_493666).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_493666).length < 2 ^ (prefixWord ++ tailWord_493666).sum := by decide
  have hdescent : baseEnd_493666 < baseStart_493666 := by decide
  rcases family_descends (prefixWord ++ tailWord_493666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_493677 : List Nat := [1, 5, 1, 1, 2, 1, 2, 3, 4]
def baseStart_493677 : Nat := 118140960795 + 493677 * 2 ^ 59
def prefixEnd_493677 : Nat := 4983230072969 + 3 ^ 40 * 493677 * 2
def baseEnd_493677 : Nat := 225327634728684640148557

theorem tailTrace_493677 : CollatzResearch.WordTrace tailWord_493677 prefixEnd_493677 225327634728684640148557 := by
  unfold tailWord_493677
  simp only [CollatzResearch.WordTrace]
  refine ⟨18005879432500017164183285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12003919621666678109455523 18005879432500017164183285)
  ·
    refine ⟨1688051196796876609142183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 18005879432500017164183285 1688051196796876609142183)
    ·
      refine ⟨2532076795195314913713275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1688051196796876609142183 2532076795195314913713275)
      ·
        refine ⟨3798115192792972370569913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2532076795195314913713275 3798115192792972370569913)
        ·
          refine ⟨2848586394594729277927435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3798115192792972370569913 2848586394594729277927435)
          ·
            refine ⟨4272879591892093916891153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2848586394594729277927435 4272879591892093916891153)
            ·
              refine ⟨3204659693919070437668365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4272879591892093916891153 3204659693919070437668365)
              ·
                refine ⟨1201747385219651414125637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3204659693919070437668365 1201747385219651414125637)
                ·
                  refine ⟨225327634728684640148557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1201747385219651414125637 225327634728684640148557)
                  ·
                    rfl

theorem cell20_493677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 2, 3, 4].length) (baseStart_493677 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_493677 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_493677 prefixEnd_493677 := by exact prefixLift 493677
  have htrace : WordTrace (prefixWord ++ tailWord_493677) baseStart_493677 baseEnd_493677 := by
    simpa [prefixWord, tailWord_493677, baseEnd_493677] using wordTrace_append hprefix tailTrace_493677
  have hstable : (prefixWord ++ tailWord_493677).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_493677).length < 2 ^ (prefixWord ++ tailWord_493677).sum := by decide
  have hdescent : baseEnd_493677 < baseStart_493677 := by decide
  rcases family_descends (prefixWord ++ tailWord_493677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_493701 : List Nat := [1, 3, 1, 1, 5, 2, 3, 4]
def baseStart_493701 : Nat := 118140960795 + 493701 * 2 ^ 59
def prefixEnd_493701 : Nat := 4983230072969 + 3 ^ 40 * 493701 * 2
def baseEnd_493701 : Nat := 75112862994215741116153

theorem tailTrace_493701 : CollatzResearch.WordTrace tailWord_493701 prefixEnd_493701 75112862994215741116153 := by
  unfold tailWord_493701
  simp only [CollatzResearch.WordTrace]
  refine ⟨18006754784413069263056957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12004503189608712842037971 18006754784413069263056957)
  ·
    refine ⟨6752533044154900973646359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18006754784413069263056957 6752533044154900973646359)
    ·
      refine ⟨10128799566232351460469539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6752533044154900973646359 10128799566232351460469539)
      ·
        refine ⟨15193199349348527190704309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10128799566232351460469539 15193199349348527190704309)
        ·
          refine ⟨1424362439001424424128529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 15193199349348527190704309 1424362439001424424128529)
          ·
            refine ⟨1068271829251068318096397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1424362439001424424128529 1068271829251068318096397)
            ·
              refine ⟨400601935969150619286149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1068271829251068318096397 400601935969150619286149)
              ·
                refine ⟨75112862994215741116153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 400601935969150619286149 75112862994215741116153)
                ·
                  rfl

theorem cell20_493701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 2, 3, 4].length) (baseStart_493701 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_493701 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_493701 prefixEnd_493701 := by exact prefixLift 493701
  have htrace : WordTrace (prefixWord ++ tailWord_493701) baseStart_493701 baseEnd_493701 := by
    simpa [prefixWord, tailWord_493701, baseEnd_493701] using wordTrace_append hprefix tailTrace_493701
  have hstable : (prefixWord ++ tailWord_493701).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_493701).length < 2 ^ (prefixWord ++ tailWord_493701).sum := by decide
  have hdescent : baseEnd_493701 < baseStart_493701 := by decide
  rcases family_descends (prefixWord ++ tailWord_493701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_493725 : List Nat := [1, 4, 2, 1, 1, 5, 1, 2, 3]
def baseStart_493725 : Nat := 118140960795 + 493725 * 2 ^ 59
def prefixEnd_493725 : Nat := 4983230072969 + 3 ^ 40 * 493725 * 2
def baseEnd_493725 : Nat := 225349543236609806548361

theorem tailTrace_493725 : CollatzResearch.WordTrace tailWord_493725 prefixEnd_493725 225349543236609806548361 := by
  unfold tailWord_493725
  simp only [CollatzResearch.WordTrace]
  refine ⟨18007630136326121361930629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12005086757550747574620419 18007630136326121361930629)
  ·
    refine ⟨3376430650561147755361993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18007630136326121361930629 3376430650561147755361993)
    ·
      refine ⟨2532322987920860816521495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3376430650561147755361993 2532322987920860816521495)
      ·
        refine ⟨3798484481881291224782243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2532322987920860816521495 3798484481881291224782243)
        ·
          refine ⟨5697726722821936837173365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3798484481881291224782243 5697726722821936837173365)
          ·
            refine ⟨534161880264556578485003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 5697726722821936837173365 534161880264556578485003)
            ·
              refine ⟨801242820396834867727505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 534161880264556578485003 801242820396834867727505)
              ·
                refine ⟨600932115297626150795629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 801242820396834867727505 600932115297626150795629)
                ·
                  refine ⟨225349543236609806548361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 600932115297626150795629 225349543236609806548361)
                  ·
                    rfl

theorem cell20_493725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 5, 1, 2, 3].length) (baseStart_493725 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_493725 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_493725 prefixEnd_493725 := by exact prefixLift 493725
  have htrace : WordTrace (prefixWord ++ tailWord_493725) baseStart_493725 baseEnd_493725 := by
    simpa [prefixWord, tailWord_493725, baseEnd_493725] using wordTrace_append hprefix tailTrace_493725
  have hstable : (prefixWord ++ tailWord_493725).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_493725).length < 2 ^ (prefixWord ++ tailWord_493725).sum := by decide
  have hdescent : baseEnd_493725 < baseStart_493725 := by decide
  rcases family_descends (prefixWord ++ tailWord_493725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_493732 : List Nat := [2, 3, 1, 2, 4, 1, 2, 1, 4]
def baseStart_493732 : Nat := 118140960795 + 493732 * 2 ^ 59
def prefixEnd_493732 : Nat := 4983230072969 + 3 ^ 40 * 493732 * 2
def baseEnd_493732 : Nat := 225352738227348893314999

theorem tailTrace_493732 : CollatzResearch.WordTrace tailWord_493732 prefixEnd_493732 225352738227348893314999 := by
  unfold tailWord_493732
  simp only [CollatzResearch.WordTrace]
  refine ⟨9003942723650380778717725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12005256964867174371623633 9003942723650380778717725)
  ·
    refine ⟨3376478521368892792019147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9003942723650380778717725 3376478521368892792019147)
    ·
      refine ⟨5064717782053339188028721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3376478521368892792019147 5064717782053339188028721)
      ·
        refine ⟨3798538336540004391021541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5064717782053339188028721 3798538336540004391021541)
        ·
          refine ⟨712225938101250823316539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3798538336540004391021541 712225938101250823316539)
          ·
            refine ⟨1068338907151876234974809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 712225938101250823316539 1068338907151876234974809)
            ·
              refine ⟨801254180363907176231107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1068338907151876234974809 801254180363907176231107)
              ·
                refine ⟨1201881270545860764346661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 801254180363907176231107 1201881270545860764346661)
                ·
                  refine ⟨225352738227348893314999, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1201881270545860764346661 225352738227348893314999)
                  ·
                    rfl

theorem cell20_493732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 1, 2, 1, 4].length) (baseStart_493732 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_493732 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_493732 prefixEnd_493732 := by exact prefixLift 493732
  have htrace : WordTrace (prefixWord ++ tailWord_493732) baseStart_493732 baseEnd_493732 := by
    simpa [prefixWord, tailWord_493732, baseEnd_493732] using wordTrace_append hprefix tailTrace_493732
  have hstable : (prefixWord ++ tailWord_493732).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_493732).length < 2 ^ (prefixWord ++ tailWord_493732).sum := by decide
  have hdescent : baseEnd_493732 < baseStart_493732 := by decide
  rcases family_descends (prefixWord ++ tailWord_493732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_493743 : List Nat := [1, 1, 2, 1, 2, 3, 1, 9]
def baseStart_493743 : Nat := 118140960795 + 493743 * 2 ^ 59
def prefixEnd_493743 : Nat := 4983230072969 + 3 ^ 40 * 493743 * 2
def baseEnd_493743 : Nat := 75119252975693914649429

theorem tailTrace_493743 : CollatzResearch.WordTrace tailWord_493743 prefixEnd_493743 75119252975693914649429 := by
  unfold tailWord_493743
  simp only [CollatzResearch.WordTrace]
  refine ⟨18008286650260910436085883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12005524433507273624057255 18008286650260910436085883)
  ·
    refine ⟨27012429975391365654128825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18008286650260910436085883 27012429975391365654128825)
    ·
      refine ⟨20259322481543524240596619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27012429975391365654128825 20259322481543524240596619)
      ·
        refine ⟨30388983722315286360894929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20259322481543524240596619 30388983722315286360894929)
        ·
          refine ⟨22791737791736464770671197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30388983722315286360894929 22791737791736464770671197)
          ·
            refine ⟨8546901671901174289001699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22791737791736464770671197 8546901671901174289001699)
            ·
              refine ⟨12820352507851761433502549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8546901671901174289001699 12820352507851761433502549)
              ·
                refine ⟨75119252975693914649429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 12820352507851761433502549 75119252975693914649429)
                ·
                  rfl

theorem cell20_493743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 9].length) (baseStart_493743 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_493743 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_493743 prefixEnd_493743 := by exact prefixLift 493743
  have htrace : WordTrace (prefixWord ++ tailWord_493743) baseStart_493743 baseEnd_493743 := by
    simpa [prefixWord, tailWord_493743, baseEnd_493743] using wordTrace_append hprefix tailTrace_493743
  have hstable : (prefixWord ++ tailWord_493743).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_493743).length < 2 ^ (prefixWord ++ tailWord_493743).sum := by decide
  have hdescent : baseEnd_493743 < baseStart_493743 := by decide
  rcases family_descends (prefixWord ++ tailWord_493743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_493756 : List Nat := [2, 2, 2, 3, 3, 2, 2, 4]
def baseStart_493756 : Nat := 118140960795 + 493756 * 2 ^ 59
def prefixEnd_493756 : Nat := 4983230072969 + 3 ^ 40 * 493756 * 2
def baseEnd_493756 : Nat := 75121230827103825504967

theorem tailTrace_493756 : CollatzResearch.WordTrace tailWord_493756 prefixEnd_493756 75121230827103825504967 := by
  unfold tailWord_493756
  simp only [CollatzResearch.WordTrace]
  refine ⟨9004380399606906828154561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12005840532809209104206081 9004380399606906828154561)
  ·
    refine ⟨6753285299705180121115921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9004380399606906828154561 6753285299705180121115921)
    ·
      refine ⟨5064963974778885090836941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6753285299705180121115921 5064963974778885090836941)
      ·
        refine ⟨1899361490542081909063853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5064963974778885090836941 1899361490542081909063853)
        ·
          refine ⟨712260558953280715898945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1899361490542081909063853 712260558953280715898945)
          ·
            refine ⟨534195419214960536924209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 712260558953280715898945 534195419214960536924209)
            ·
              refine ⟨400646564411220402693157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 534195419214960536924209 400646564411220402693157)
              ·
                refine ⟨75121230827103825504967, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 400646564411220402693157 75121230827103825504967)
                ·
                  rfl

theorem cell20_493756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 2, 2, 4].length) (baseStart_493756 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_493756 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_493756 prefixEnd_493756 := by exact prefixLift 493756
  have htrace : WordTrace (prefixWord ++ tailWord_493756) baseStart_493756 baseEnd_493756 := by
    simpa [prefixWord, tailWord_493756, baseEnd_493756] using wordTrace_append hprefix tailTrace_493756
  have hstable : (prefixWord ++ tailWord_493756).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_493756).length < 2 ^ (prefixWord ++ tailWord_493756).sum := by decide
  have hdescent : baseEnd_493756 < baseStart_493756 := by decide
  rcases family_descends (prefixWord ++ tailWord_493756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_493760 : List Nat := [2, 1, 1, 2, 5, 2, 1, 6]
def baseStart_493760 : Nat := 118140960795 + 493760 * 2 ^ 59
def prefixEnd_493760 : Nat := 4983230072969 + 3 ^ 40 * 493760 * 2
def baseEnd_493760 : Nat := 75121839396768413460517

theorem tailTrace_493760 : CollatzResearch.WordTrace tailWord_493760 prefixEnd_493760 75121839396768413460517 := by
  unfold tailWord_493760
  simp only [CollatzResearch.WordTrace]
  refine ⟨9004453345599661169727367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12005937794132881559636489 9004453345599661169727367)
  ·
    refine ⟨13506680018399491754591051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9004453345599661169727367 13506680018399491754591051)
    ·
      refine ⟨20260020027599237631886577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13506680018399491754591051 20260020027599237631886577)
      ·
        refine ⟨15195015020699428223914933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20260020027599237631886577 15195015020699428223914933)
        ·
          refine ⟨1424532658190571395992025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 15195015020699428223914933 1424532658190571395992025)
          ·
            refine ⟨1068399493642928546994019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1424532658190571395992025 1068399493642928546994019)
            ·
              refine ⟨1602599240464392820491029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1068399493642928546994019 1602599240464392820491029)
              ·
                refine ⟨75121839396768413460517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1602599240464392820491029 75121839396768413460517)
                ·
                  rfl

theorem cell20_493760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 2, 1, 6].length) (baseStart_493760 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_493760 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_493760 prefixEnd_493760 := by exact prefixLift 493760
  have htrace : WordTrace (prefixWord ++ tailWord_493760) baseStart_493760 baseEnd_493760 := by
    simpa [prefixWord, tailWord_493760, baseEnd_493760] using wordTrace_append hprefix tailTrace_493760
  have hstable : (prefixWord ++ tailWord_493760).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_493760).length < 2 ^ (prefixWord ++ tailWord_493760).sum := by decide
  have hdescent : baseEnd_493760 < baseStart_493760 := by decide
  rcases family_descends (prefixWord ++ tailWord_493760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_493860 : List Nat := [2, 3, 1, 3, 1, 2, 2, 3, 3]
def baseStart_493860 : Nat := 118140960795 + 493860 * 2 ^ 59
def prefixEnd_493860 : Nat := 4983230072969 + 3 ^ 40 * 493860 * 2
def baseEnd_493860 : Nat := 225411160915149337047809

theorem tailTrace_493860 : CollatzResearch.WordTrace tailWord_493860 prefixEnd_493860 225411160915149337047809 := by
  unfold tailWord_493860
  simp only [CollatzResearch.WordTrace]
  refine ⟨9006276995418519709047517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12008369327224692945396689 9006276995418519709047517)
  ·
    refine ⟨3377353873281944890892819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9006276995418519709047517 3377353873281944890892819)
    ·
      refine ⟨5066030809922917336339229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3377353873281944890892819 5066030809922917336339229)
      ·
        refine ⟨1899761553721094001127211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5066030809922917336339229 1899761553721094001127211)
        ·
          refine ⟨2849642330581641001690817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1899761553721094001127211 2849642330581641001690817)
          ·
            refine ⟨2137231747936230751268113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2849642330581641001690817 2137231747936230751268113)
            ·
              refine ⟨1602923810952173063451085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2137231747936230751268113 1602923810952173063451085)
              ·
                refine ⟨601096429107064898794157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1602923810952173063451085 601096429107064898794157)
                ·
                  refine ⟨225411160915149337047809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 601096429107064898794157 225411160915149337047809)
                  ·
                    rfl

theorem cell20_493860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 2, 3, 3].length) (baseStart_493860 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_493860 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_493860 prefixEnd_493860 := by exact prefixLift 493860
  have htrace : WordTrace (prefixWord ++ tailWord_493860) baseStart_493860 baseEnd_493860 := by
    simpa [prefixWord, tailWord_493860, baseEnd_493860] using wordTrace_append hprefix tailTrace_493860
  have hstable : (prefixWord ++ tailWord_493860).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_493860).length < 2 ^ (prefixWord ++ tailWord_493860).sum := by decide
  have hdescent : baseEnd_493860 < baseStart_493860 := by decide
  rcases family_descends (prefixWord ++ tailWord_493860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_493884 : List Nat := [2, 2, 2, 2, 1, 2, 4, 3, 2]
def baseStart_493884 : Nat := 118140960795 + 493884 * 2 ^ 59
def prefixEnd_493884 : Nat := 4983230072969 + 3 ^ 40 * 493884 * 2
def baseEnd_493884 : Nat := 225422115169111920247711

theorem tailTrace_493884 : CollatzResearch.WordTrace tailWord_493884 prefixEnd_493884 225422115169111920247711 := by
  unfold tailWord_493884
  simp only [CollatzResearch.WordTrace]
  refine ⟨9006714671375045758484353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12008952895166727677979137 9006714671375045758484353)
  ·
    refine ⟨6755036003531284318863265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9006714671375045758484353 6755036003531284318863265)
    ·
      refine ⟨5066277002648463239147449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6755036003531284318863265 5066277002648463239147449)
      ·
        refine ⟨3799707751986347429360587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5066277002648463239147449 3799707751986347429360587)
        ·
          refine ⟨5699561627979521144040881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3799707751986347429360587 5699561627979521144040881)
          ·
            refine ⟨4274671220984640858030661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5699561627979521144040881 4274671220984640858030661)
            ·
              refine ⟨801500853934620160880749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4274671220984640858030661 801500853934620160880749)
              ·
                refine ⟨300562820225482560330281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 801500853934620160880749 300562820225482560330281)
                ·
                  refine ⟨225422115169111920247711, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 300562820225482560330281 225422115169111920247711)
                  ·
                    rfl

theorem cell20_493884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 4, 3, 2].length) (baseStart_493884 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_493884 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_493884 prefixEnd_493884 := by exact prefixLift 493884
  have htrace : WordTrace (prefixWord ++ tailWord_493884) baseStart_493884 baseEnd_493884 := by
    simpa [prefixWord, tailWord_493884, baseEnd_493884] using wordTrace_append hprefix tailTrace_493884
  have hstable : (prefixWord ++ tailWord_493884).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_493884).length < 2 ^ (prefixWord ++ tailWord_493884).sum := by decide
  have hdescent : baseEnd_493884 < baseStart_493884 := by decide
  rcases family_descends (prefixWord ++ tailWord_493884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_493895 : List Nat := [1, 1, 4, 1, 2, 2, 9]
def baseStart_493895 : Nat := 118140960795 + 493895 * 2 ^ 59
def prefixEnd_493895 : Nat := 4983230072969 + 3 ^ 40 * 493895 * 2
def baseEnd_493895 : Nat := 25047459540982752320111

theorem tailTrace_493895 : CollatzResearch.WordTrace tailWord_493895 prefixEnd_493895 25047459540982752320111 := by
  unfold tailWord_493895
  simp only [CollatzResearch.WordTrace]
  refine ⟨18013830545710240395619139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12009220363806826930412759 18013830545710240395619139)
  ·
    refine ⟨27020745818565360593428709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18013830545710240395619139 27020745818565360593428709)
    ·
      refine ⟨5066389840981005111267883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27020745818565360593428709 5066389840981005111267883)
      ·
        refine ⟨7599584761471507666901825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5066389840981005111267883 7599584761471507666901825)
        ·
          refine ⟨5699688571103630750176369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7599584761471507666901825 5699688571103630750176369)
          ·
            refine ⟨4274766428327723062632277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5699688571103630750176369 4274766428327723062632277)
            ·
              refine ⟨25047459540982752320111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 4274766428327723062632277 25047459540982752320111)
              ·
                rfl

theorem cell20_493895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 9].length) (baseStart_493895 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_493895 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_493895 prefixEnd_493895 := by exact prefixLift 493895
  have htrace : WordTrace (prefixWord ++ tailWord_493895) baseStart_493895 baseEnd_493895 := by
    simpa [prefixWord, tailWord_493895, baseEnd_493895] using wordTrace_append hprefix tailTrace_493895
  have hstable : (prefixWord ++ tailWord_493895).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_493895).length < 2 ^ (prefixWord ++ tailWord_493895).sum := by decide
  have hdescent : baseEnd_493895 < baseStart_493895 := by decide
  rcases family_descends (prefixWord ++ tailWord_493895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_493905 : List Nat := [1, 2, 2, 1, 4, 3, 2, 1, 4]
def baseStart_493905 : Nat := 118140960795 + 493905 * 2 ^ 59
def prefixEnd_493905 : Nat := 4983230072969 + 3 ^ 40 * 493905 * 2
def baseEnd_493905 : Nat := 225431700141329180547625

theorem tailTrace_493905 : CollatzResearch.WordTrace tailWord_493905 prefixEnd_493905 225431700141329180547625 := by
  unfold tailWord_493905
  simp only [CollatzResearch.WordTrace]
  refine ⟨18014195275674012103483169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12009463517116008068988779 18014195275674012103483169)
  ·
    refine ⟨13510646456755509077612377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18014195275674012103483169 13510646456755509077612377)
    ·
      refine ⟨10132984842566631808209283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13510646456755509077612377 10132984842566631808209283)
      ·
        refine ⟨15199477263849947712313925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10132984842566631808209283 15199477263849947712313925)
        ·
          refine ⟨2849901986971865196058861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15199477263849947712313925 2849901986971865196058861)
          ·
            refine ⟨1068713245114449448522073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2849901986971865196058861 1068713245114449448522073)
            ·
              refine ⟨801534933835837086391555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1068713245114449448522073 801534933835837086391555)
              ·
                refine ⟨1202302400753755629587333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 801534933835837086391555 1202302400753755629587333)
                ·
                  refine ⟨225431700141329180547625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1202302400753755629587333 225431700141329180547625)
                  ·
                    rfl

theorem cell20_493905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 3, 2, 1, 4].length) (baseStart_493905 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_493905 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_493905 prefixEnd_493905 := by exact prefixLift 493905
  have htrace : WordTrace (prefixWord ++ tailWord_493905) baseStart_493905 baseEnd_493905 := by
    simpa [prefixWord, tailWord_493905, baseEnd_493905] using wordTrace_append hprefix tailTrace_493905
  have hstable : (prefixWord ++ tailWord_493905).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_493905).length < 2 ^ (prefixWord ++ tailWord_493905).sum := by decide
  have hdescent : baseEnd_493905 < baseStart_493905 := by decide
  rcases family_descends (prefixWord ++ tailWord_493905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_493919 : List Nat := [1, 1, 2, 3, 1, 2, 2, 5, 3]
def baseStart_493919 : Nat := 118140960795 + 493919 * 2 ^ 59
def prefixEnd_493919 : Nat := 4983230072969 + 3 ^ 40 * 493919 * 2
def baseEnd_493919 : Nat := 225438090122807354080901

theorem tailTrace_493919 : CollatzResearch.WordTrace tailWord_493919 prefixEnd_493919 225438090122807354080901 := by
  unfold tailWord_493919
  simp only [CollatzResearch.WordTrace]
  refine ⟨18014705897623292494492811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12009803931748861662995207 18014705897623292494492811)
  ·
    refine ⟨27022058846434938741739217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18014705897623292494492811 27022058846434938741739217)
    ·
      refine ⟨20266544134826204056304413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27022058846434938741739217 20266544134826204056304413)
      ·
        refine ⟨7599954050559826521114155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20266544134826204056304413 7599954050559826521114155)
        ·
          refine ⟨11399931075839739781671233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7599954050559826521114155 11399931075839739781671233)
          ·
            refine ⟨8549948306879804836253425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11399931075839739781671233 8549948306879804836253425)
            ·
              refine ⟨6412461230159853627190069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8549948306879804836253425 6412461230159853627190069)
              ·
                refine ⟨601168240327486277549069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6412461230159853627190069 601168240327486277549069)
                ·
                  refine ⟨225438090122807354080901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 601168240327486277549069 225438090122807354080901)
                  ·
                    rfl

theorem cell20_493919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 2, 5, 3].length) (baseStart_493919 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_493919 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_493919 prefixEnd_493919 := by exact prefixLift 493919
  have htrace : WordTrace (prefixWord ++ tailWord_493919) baseStart_493919 baseEnd_493919 := by
    simpa [prefixWord, tailWord_493919, baseEnd_493919] using wordTrace_append hprefix tailTrace_493919
  have hstable : (prefixWord ++ tailWord_493919).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_493919).length < 2 ^ (prefixWord ++ tailWord_493919).sum := by decide
  have hdescent : baseEnd_493919 < baseStart_493919 := by decide
  rcases family_descends (prefixWord ++ tailWord_493919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_493943 : List Nat := [1, 1, 3, 1, 1, 2, 2, 7, 2]
def baseStart_493943 : Nat := 118140960795 + 493943 * 2 ^ 59
def prefixEnd_493943 : Nat := 4983230072969 + 3 ^ 40 * 493943 * 2
def baseEnd_493943 : Nat := 225449044376769937280803

theorem tailTrace_493943 : CollatzResearch.WordTrace tailWord_493943 prefixEnd_493943 225449044376769937280803 := by
  unfold tailWord_493943
  simp only [CollatzResearch.WordTrace]
  refine ⟨18015581249536344593366483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12010387499690896395577655 18015581249536344593366483)
  ·
    refine ⟨27023371874304516890049725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18015581249536344593366483 27023371874304516890049725)
    ·
      refine ⟨10133764452864193833768647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27023371874304516890049725 10133764452864193833768647)
      ·
        refine ⟨15200646679296290750652971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10133764452864193833768647 15200646679296290750652971)
        ·
          refine ⟨22800970018944436125979457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15200646679296290750652971 22800970018944436125979457)
          ·
            refine ⟨17100727514208327094484593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22800970018944436125979457 17100727514208327094484593)
            ·
              refine ⟨12825545635656245320863445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17100727514208327094484593 12825545635656245320863445)
              ·
                refine ⟨300598725835693249707737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 12825545635656245320863445 300598725835693249707737)
                ·
                  refine ⟨225449044376769937280803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 300598725835693249707737 225449044376769937280803)
                  ·
                    rfl

theorem cell20_493943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 7, 2].length) (baseStart_493943 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_493943 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_493943 prefixEnd_493943 := by exact prefixLift 493943
  have htrace : WordTrace (prefixWord ++ tailWord_493943) baseStart_493943 baseEnd_493943 := by
    simpa [prefixWord, tailWord_493943, baseEnd_493943] using wordTrace_append hprefix tailTrace_493943
  have hstable : (prefixWord ++ tailWord_493943).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_493943).length < 2 ^ (prefixWord ++ tailWord_493943).sum := by decide
  have hdescent : baseEnd_493943 < baseStart_493943 := by decide
  rcases family_descends (prefixWord ++ tailWord_493943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_493957 : List Nat := [1, 3, 1, 1, 3, 1, 1, 6, 3]
def baseStart_493957 : Nat := 118140960795 + 493957 * 2 ^ 59
def prefixEnd_493957 : Nat := 4983230072969 + 3 ^ 40 * 493957 * 2
def baseEnd_493957 : Nat := 225455434358248110814079

theorem tailTrace_493957 : CollatzResearch.WordTrace tailWord_493957 prefixEnd_493957 225455434358248110814079 := by
  unfold tailWord_493957
  simp only [CollatzResearch.WordTrace]
  refine ⟨18016091871485624984376125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12010727914323749989584083 18016091871485624984376125)
  ·
    refine ⟨6756034451807109369141047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18016091871485624984376125 6756034451807109369141047)
    ·
      refine ⟨10134051677710664053711571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6756034451807109369141047 10134051677710664053711571)
      ·
        refine ⟨15201077516565996080567357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10134051677710664053711571 15201077516565996080567357)
        ·
          refine ⟨5700404068712248530212759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15201077516565996080567357 5700404068712248530212759)
          ·
            refine ⟨8550606103068372795319139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5700404068712248530212759 8550606103068372795319139)
            ·
              refine ⟨12825909154602559192978709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8550606103068372795319139 12825909154602559192978709)
              ·
                refine ⟨601214491621994962170877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 12825909154602559192978709 601214491621994962170877)
                ·
                  refine ⟨225455434358248110814079, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 601214491621994962170877 225455434358248110814079)
                  ·
                    rfl

theorem cell20_493957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 6, 3].length) (baseStart_493957 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_493957 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_493957 prefixEnd_493957 := by exact prefixLift 493957
  have htrace : WordTrace (prefixWord ++ tailWord_493957) baseStart_493957 baseEnd_493957 := by
    simpa [prefixWord, tailWord_493957, baseEnd_493957] using wordTrace_append hprefix tailTrace_493957
  have hstable : (prefixWord ++ tailWord_493957).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_493957).length < 2 ^ (prefixWord ++ tailWord_493957).sum := by decide
  have hdescent : baseEnd_493957 < baseStart_493957 := by decide
  rcases family_descends (prefixWord ++ tailWord_493957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_494009 : List Nat := [1, 2, 1, 4, 3, 9]
def baseStart_494009 : Nat := 118140960795 + 494009 * 2 ^ 59
def prefixEnd_494009 : Nat := 4983230072969 + 3 ^ 40 * 494009 * 2
def baseEnd_494009 : Nat := 8351080317598779299279

theorem tailTrace_494009 : CollatzResearch.WordTrace tailWord_494009 prefixEnd_494009 8351080317598779299279 := by
  unfold tailWord_494009
  simp only [CollatzResearch.WordTrace]
  refine ⟨18017988467297237865269081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12011992311531491910179387 18017988467297237865269081)
  ·
    refine ⟨13513491350472928398951811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18017988467297237865269081 13513491350472928398951811)
    ·
      refine ⟨20270237025709392598427717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13513491350472928398951811 20270237025709392598427717)
      ·
        refine ⟨3800669442320511112205197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20270237025709392598427717 3800669442320511112205197)
        ·
          refine ⟨1425251040870191667076949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3800669442320511112205197 1425251040870191667076949)
          ·
            refine ⟨8351080317598779299279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 1425251040870191667076949 8351080317598779299279)
            ·
              rfl

theorem cell20_494009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 9].length) (baseStart_494009 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_494009 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_494009 prefixEnd_494009 := by exact prefixLift 494009
  have htrace : WordTrace (prefixWord ++ tailWord_494009) baseStart_494009 baseEnd_494009 := by
    simpa [prefixWord, tailWord_494009, baseEnd_494009] using wordTrace_append hprefix tailTrace_494009
  have hstable : (prefixWord ++ tailWord_494009).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_494009).length < 2 ^ (prefixWord ++ tailWord_494009).sum := by decide
  have hdescent : baseEnd_494009 < baseStart_494009 := by decide
  rcases family_descends (prefixWord ++ tailWord_494009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_494012 : List Nat := [2, 2, 2, 4, 1, 1, 1, 4, 3]
def baseStart_494012 : Nat := 118140960795 + 494012 * 2 ^ 59
def prefixEnd_494012 : Nat := 4983230072969 + 3 ^ 40 * 494012 * 2
def baseEnd_494012 : Nat := 225480537856912363980521

theorem tailTrace_494012 : CollatzResearch.WordTrace tailWord_494012 prefixEnd_494012 225480537856912363980521 := by
  unfold tailWord_494012
  simp only [CollatzResearch.WordTrace]
  refine ⟨9009048943143184688814145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12012065257524246251752193 9009048943143184688814145)
  ·
    refine ⟨6756786707357388516610609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9009048943143184688814145 6756786707357388516610609)
    ·
      refine ⟨5067590030518041387457957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6756786707357388516610609 5067590030518041387457957)
      ·
        refine ⟨950173130722132760148367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5067590030518041387457957 950173130722132760148367)
        ·
          refine ⟨1425259696083199140222551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 950173130722132760148367 1425259696083199140222551)
          ·
            refine ⟨2137889544124798710333827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1425259696083199140222551 2137889544124798710333827)
            ·
              refine ⟨3206834316187198065500741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2137889544124798710333827 3206834316187198065500741)
              ·
                refine ⟨601281434285099637281389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3206834316187198065500741 601281434285099637281389)
                ·
                  refine ⟨225480537856912363980521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 601281434285099637281389 225480537856912363980521)
                  ·
                    rfl

theorem cell20_494012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 1, 4, 3].length) (baseStart_494012 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_494012 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_494012 prefixEnd_494012 := by exact prefixLift 494012
  have htrace : WordTrace (prefixWord ++ tailWord_494012) baseStart_494012 baseEnd_494012 := by
    simpa [prefixWord, tailWord_494012, baseEnd_494012] using wordTrace_append hprefix tailTrace_494012
  have hstable : (prefixWord ++ tailWord_494012).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_494012).length < 2 ^ (prefixWord ++ tailWord_494012).sum := by decide
  have hdescent : baseEnd_494012 < baseStart_494012 := by decide
  rcases family_descends (prefixWord ++ tailWord_494012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_494053 : List Nat := [1, 3, 1, 5, 2, 1, 2, 3, 2]
def baseStart_494053 : Nat := 118140960795 + 494053 * 2 ^ 59
def prefixEnd_494053 : Nat := 4983230072969 + 3 ^ 40 * 494053 * 2
def baseEnd_494053 : Nat := 225499251374098443613687

theorem tailTrace_494053 : CollatzResearch.WordTrace tailWord_494053 prefixEnd_494053 225499251374098443613687 := by
  unfold tailWord_494053
  simp only [CollatzResearch.WordTrace]
  refine ⟨18019593279137833379870813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12013062186091888919913875 18019593279137833379870813)
  ·
    refine ⟨6757347479676687517451555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18019593279137833379870813 6757347479676687517451555)
    ·
      refine ⟨10136021219515031276177333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6757347479676687517451555 10136021219515031276177333)
      ·
        refine ⟨950251989329534182141625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 10136021219515031276177333 950251989329534182141625)
        ·
          refine ⟨712688991997150636606219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 950251989329534182141625 712688991997150636606219)
          ·
            refine ⟨1069033487995725954909329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 712688991997150636606219 1069033487995725954909329)
            ·
              refine ⟨801775115996794466181997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1069033487995725954909329 801775115996794466181997)
              ·
                refine ⟨300665668498797924818249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 801775115996794466181997 300665668498797924818249)
                ·
                  refine ⟨225499251374098443613687, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 300665668498797924818249 225499251374098443613687)
                  ·
                    rfl

theorem cell20_494053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 1, 2, 3, 2].length) (baseStart_494053 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_494053 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_494053 prefixEnd_494053 := by exact prefixLift 494053
  have htrace : WordTrace (prefixWord ++ tailWord_494053) baseStart_494053 baseEnd_494053 := by
    simpa [prefixWord, tailWord_494053, baseEnd_494053] using wordTrace_append hprefix tailTrace_494053
  have hstable : (prefixWord ++ tailWord_494053).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_494053).length < 2 ^ (prefixWord ++ tailWord_494053).sum := by decide
  have hdescent : baseEnd_494053 < baseStart_494053 := by decide
  rcases family_descends (prefixWord ++ tailWord_494053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_494109 : List Nat := [1, 4, 2, 2, 1, 2, 1, 2, 5]
def baseStart_494109 : Nat := 118140960795 + 494109 * 2 ^ 59
def prefixEnd_494109 : Nat := 4983230072969 + 3 ^ 40 * 494109 * 2
def baseEnd_494109 : Nat := 225524811300011137746791

theorem tailTrace_494109 : CollatzResearch.WordTrace tailWord_494109 prefixEnd_494109 225524811300011137746791 := by
  unfold tailWord_494109
  simp only [CollatzResearch.WordTrace]
  refine ⟨18021635766934954943909381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12014423844623303295939587 18021635766934954943909381)
  ·
    refine ⟨3379056706300304051983009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18021635766934954943909381 3379056706300304051983009)
    ·
      refine ⟨2534292529725228038987257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3379056706300304051983009 2534292529725228038987257)
      ·
        refine ⟨1900719397293921029240443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2534292529725228038987257 1900719397293921029240443)
        ·
          refine ⟨2851079095940881543860665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1900719397293921029240443 2851079095940881543860665)
          ·
            refine ⟨2138309321955661157895499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2851079095940881543860665 2138309321955661157895499)
            ·
              refine ⟨3207463982933491736843249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2138309321955661157895499 3207463982933491736843249)
              ·
                refine ⟨2405597987200118802632437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3207463982933491736843249 2405597987200118802632437)
                ·
                  refine ⟨225524811300011137746791, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2405597987200118802632437 225524811300011137746791)
                  ·
                    rfl

theorem cell20_494109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 1, 2, 5].length) (baseStart_494109 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_494109 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_494109 prefixEnd_494109 := by exact prefixLift 494109
  have htrace : WordTrace (prefixWord ++ tailWord_494109) baseStart_494109 baseEnd_494109 := by
    simpa [prefixWord, tailWord_494109, baseEnd_494109] using wordTrace_append hprefix tailTrace_494109
  have hstable : (prefixWord ++ tailWord_494109).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_494109).length < 2 ^ (prefixWord ++ tailWord_494109).sum := by decide
  have hdescent : baseEnd_494109 < baseStart_494109 := by decide
  rcases family_descends (prefixWord ++ tailWord_494109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_494125 : List Nat := [1, 5, 4, 1, 2, 1, 1, 1, 4]
def baseStart_494125 : Nat := 118140960795 + 494125 * 2 ^ 59
def prefixEnd_494125 : Nat := 4983230072969 + 3 ^ 40 * 494125 * 2
def baseEnd_494125 : Nat := 225532114135986193213393

theorem tailTrace_494125 : CollatzResearch.WordTrace tailWord_494125 prefixEnd_494125 225532114135986193213393 := by
  unfold tailWord_494125
  simp only [CollatzResearch.WordTrace]
  refine ⟨18022219334876989676491829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12014812889917993117661219 18022219334876989676491829)
  ·
    refine ⟨1689583062644717782171109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 18022219334876989676491829 1689583062644717782171109)
    ·
      refine ⟨316796824245884584157083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1689583062644717782171109 316796824245884584157083)
      ·
        refine ⟨475195236368826876235625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 316796824245884584157083 475195236368826876235625)
        ·
          refine ⟨356396427276620157176719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 475195236368826876235625 356396427276620157176719)
          ·
            refine ⟨534594640914930235765079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 356396427276620157176719 534594640914930235765079)
            ·
              refine ⟨801891961372395353647619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 534594640914930235765079 801891961372395353647619)
              ·
                refine ⟨1202837942058593030471429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 801891961372395353647619 1202837942058593030471429)
                ·
                  refine ⟨225532114135986193213393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1202837942058593030471429 225532114135986193213393)
                  ·
                    rfl

theorem cell20_494125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 2, 1, 1, 1, 4].length) (baseStart_494125 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_494125 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_494125 prefixEnd_494125 := by exact prefixLift 494125
  have htrace : WordTrace (prefixWord ++ tailWord_494125) baseStart_494125 baseEnd_494125 := by
    simpa [prefixWord, tailWord_494125, baseEnd_494125] using wordTrace_append hprefix tailTrace_494125
  have hstable : (prefixWord ++ tailWord_494125).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_494125).length < 2 ^ (prefixWord ++ tailWord_494125).sum := by decide
  have hdescent : baseEnd_494125 < baseStart_494125 := by decide
  rcases family_descends (prefixWord ++ tailWord_494125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_494140 : List Nat := [2, 2, 2, 2, 3, 2, 2, 5]
def baseStart_494140 : Nat := 118140960795 + 494140 * 2 ^ 59
def prefixEnd_494140 : Nat := 4983230072969 + 3 ^ 40 * 494140 * 2
def baseEnd_494140 : Nat := 75179653514904269237777

theorem tailTrace_494140 : CollatzResearch.WordTrace tailWord_494140 prefixEnd_494140 75179653514904269237777 := by
  unfold tailWord_494140
  simp only [CollatzResearch.WordTrace]
  refine ⟨9011383214911323619143937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12015177619881764825525249 9011383214911323619143937)
  ·
    refine ⟨6758537411183492714357953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9011383214911323619143937 6758537411183492714357953)
    ·
      refine ⟨5068903058387619535768465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6758537411183492714357953 5068903058387619535768465)
      ·
        refine ⟨3801677293790714651826349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5068903058387619535768465 3801677293790714651826349)
        ·
          refine ⟨1425628985171517994434881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3801677293790714651826349 1425628985171517994434881)
          ·
            refine ⟨1069221738878638495826161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1425628985171517994434881 1069221738878638495826161)
            ·
              refine ⟨801916304158978871869621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1069221738878638495826161 801916304158978871869621)
              ·
                refine ⟨75179653514904269237777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 801916304158978871869621 75179653514904269237777)
                ·
                  rfl

theorem cell20_494140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 2, 2, 5].length) (baseStart_494140 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_494140 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_494140 prefixEnd_494140 := by exact prefixLift 494140
  have htrace : WordTrace (prefixWord ++ tailWord_494140) baseStart_494140 baseEnd_494140 := by
    simpa [prefixWord, tailWord_494140, baseEnd_494140] using wordTrace_append hprefix tailTrace_494140
  have hstable : (prefixWord ++ tailWord_494140).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_494140).length < 2 ^ (prefixWord ++ tailWord_494140).sum := by decide
  have hdescent : baseEnd_494140 < baseStart_494140 := by decide
  rcases family_descends (prefixWord ++ tailWord_494140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_494161 : List Nat := [1, 2, 2, 1, 3, 3, 2, 6]
def baseStart_494161 : Nat := 118140960795 + 494161 * 2 ^ 59
def prefixEnd_494161 : Nat := 4983230072969 + 3 ^ 40 * 494161 * 2
def baseEnd_494161 : Nat := 75182848505643356004415

theorem tailTrace_494161 : CollatzResearch.WordTrace tailWord_494161 prefixEnd_494161 75182848505643356004415 := by
  unfold tailWord_494161
  simp only [CollatzResearch.WordTrace]
  refine ⟨18023532362746567824802337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12015688241831045216534891 18023532362746567824802337)
  ·
    refine ⟨13517649272059925868601753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18023532362746567824802337 13517649272059925868601753)
    ·
      refine ⟨10138236954044944401451315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13517649272059925868601753 10138236954044944401451315)
      ·
        refine ⟨15207355431067416602176973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10138236954044944401451315 15207355431067416602176973)
        ·
          refine ⟨5702758286650281225816365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15207355431067416602176973 5702758286650281225816365)
          ·
            refine ⟨2138534357493855459681137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5702758286650281225816365 2138534357493855459681137)
            ·
              refine ⟨1603900768120391594760853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2138534357493855459681137 1603900768120391594760853)
              ·
                refine ⟨75182848505643356004415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1603900768120391594760853 75182848505643356004415)
                ·
                  rfl

theorem cell20_494161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 2, 6].length) (baseStart_494161 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_494161 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_494161 prefixEnd_494161 := by exact prefixLift 494161
  have htrace : WordTrace (prefixWord ++ tailWord_494161) baseStart_494161 baseEnd_494161 := by
    simpa [prefixWord, tailWord_494161, baseEnd_494161] using wordTrace_append hprefix tailTrace_494161
  have hstable : (prefixWord ++ tailWord_494161).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_494161).length < 2 ^ (prefixWord ++ tailWord_494161).sum := by decide
  have hdescent : baseEnd_494161 < baseStart_494161 := by decide
  rcases family_descends (prefixWord ++ tailWord_494161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_494168 : List Nat := [2, 1, 2, 2, 1, 2, 2, 1, 7]
def baseStart_494168 : Nat := 118140960795 + 494168 * 2 ^ 59
def prefixEnd_494168 : Nat := 4983230072969 + 3 ^ 40 * 494168 * 2
def baseEnd_494168 : Nat := 225551740507669154779883

theorem tailTrace_494168 : CollatzResearch.WordTrace tailWord_494168 prefixEnd_494168 225551740507669154779883 := by
  unfold tailWord_494168
  simp only [CollatzResearch.WordTrace]
  refine ⟨9011893836860604010153579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12015858449147472013538105 9011893836860604010153579)
  ·
    refine ⟨13517840755290906015230369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9011893836860604010153579 13517840755290906015230369)
    ·
      refine ⟨10138380566468179511422777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13517840755290906015230369 10138380566468179511422777)
      ·
        refine ⟨7603785424851134633567083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10138380566468179511422777 7603785424851134633567083)
        ·
          refine ⟨11405678137276701950350625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7603785424851134633567083 11405678137276701950350625)
          ·
            refine ⟨8554258602957526462762969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11405678137276701950350625 8554258602957526462762969)
            ·
              refine ⟨6415693952218144847072227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8554258602957526462762969 6415693952218144847072227)
              ·
                refine ⟨9623540928327217270608341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6415693952218144847072227 9623540928327217270608341)
                ·
                  refine ⟨225551740507669154779883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9623540928327217270608341 225551740507669154779883)
                  ·
                    rfl

theorem cell20_494168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 2, 1, 7].length) (baseStart_494168 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_494168 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_494168 prefixEnd_494168 := by exact prefixLift 494168
  have htrace : WordTrace (prefixWord ++ tailWord_494168) baseStart_494168 baseEnd_494168 := by
    simpa [prefixWord, tailWord_494168, baseEnd_494168] using wordTrace_append hprefix tailTrace_494168
  have hstable : (prefixWord ++ tailWord_494168).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_494168).length < 2 ^ (prefixWord ++ tailWord_494168).sum := by decide
  have hdescent : baseEnd_494168 < baseStart_494168 := by decide
  rcases family_descends (prefixWord ++ tailWord_494168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_494174 : List Nat := [4, 4, 1, 2, 1, 8]
def baseStart_494174 : Nat := 118140960795 + 494174 * 2 ^ 59
def prefixEnd_494174 : Nat := 4983230072969 + 3 ^ 40 * 494174 * 2
def baseEnd_494174 : Nat := 8353869595228140762217

theorem tailTrace_494174 : CollatzResearch.WordTrace tailWord_494174 prefixEnd_494174 8353869595228140762217 := by
  unfold tailWord_494174
  simp only [CollatzResearch.WordTrace]
  refine ⟨2253000813962433880628197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12016004341132980696683717 2253000813962433880628197)
  ·
    refine ⟨422437652617956352617787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2253000813962433880628197 422437652617956352617787)
    ·
      refine ⟨633656478926934528926681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 422437652617956352617787 633656478926934528926681)
      ·
        refine ⟨475242359195200896695011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 633656478926934528926681 475242359195200896695011)
        ·
          refine ⟨712863538792801345042517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 475242359195200896695011 712863538792801345042517)
          ·
            refine ⟨8353869595228140762217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 712863538792801345042517 8353869595228140762217)
            ·
              rfl

theorem cell20_494174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 8].length) (baseStart_494174 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_494174 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_494174 prefixEnd_494174 := by exact prefixLift 494174
  have htrace : WordTrace (prefixWord ++ tailWord_494174) baseStart_494174 baseEnd_494174 := by
    simpa [prefixWord, tailWord_494174, baseEnd_494174] using wordTrace_append hprefix tailTrace_494174
  have hstable : (prefixWord ++ tailWord_494174).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_494174).length < 2 ^ (prefixWord ++ tailWord_494174).sum := by decide
  have hdescent : baseEnd_494174 < baseStart_494174 := by decide
  rcases family_descends (prefixWord ++ tailWord_494174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_494178 : List Nat := [3, 3, 2, 3, 9]
def baseStart_494178 : Nat := 118140960795 + 494178 * 2 ^ 59
def prefixEnd_494178 : Nat := 4983230072969 + 3 ^ 40 * 494178 * 2
def baseEnd_494178 : Nat := 2784645738026587215389

theorem tailTrace_494178 : CollatzResearch.WordTrace tailWord_494178 prefixEnd_494178 2784645738026587215389 := by
  unfold tailWord_494178
  simp only [CollatzResearch.WordTrace]
  refine ⟨4506038100921244932042797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12016101602456653152114125 4506038100921244932042797)
  ·
    refine ⟨1689764287845466849516049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4506038100921244932042797 1689764287845466849516049)
    ·
      refine ⟨1267323215884100137137037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1689764287845466849516049 1267323215884100137137037)
      ·
        refine ⟨475246205956537551426389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1267323215884100137137037 475246205956537551426389)
        ·
          refine ⟨2784645738026587215389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 9 475246205956537551426389 2784645738026587215389)
          ·
            rfl

theorem cell20_494178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 9].length) (baseStart_494178 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_494178 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_494178 prefixEnd_494178 := by exact prefixLift 494178
  have htrace : WordTrace (prefixWord ++ tailWord_494178) baseStart_494178 baseEnd_494178 := by
    simpa [prefixWord, tailWord_494178, baseEnd_494178] using wordTrace_append hprefix tailTrace_494178
  have hstable : (prefixWord ++ tailWord_494178).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_494178).length < 2 ^ (prefixWord ++ tailWord_494178).sum := by decide
  have hdescent : baseEnd_494178 < baseStart_494178 := by decide
  rcases family_descends (prefixWord ++ tailWord_494178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_494184 : List Nat := [2, 1, 4, 3, 2, 2, 2, 2, 2]
def baseStart_494184 : Nat := 118140960795 + 494184 * 2 ^ 59
def prefixEnd_494184 : Nat := 4983230072969 + 3 ^ 40 * 494184 * 2
def baseEnd_494184 : Nat := 225559043343644210246485

theorem tailTrace_494184 : CollatzResearch.WordTrace tailWord_494184 prefixEnd_494184 225559043343644210246485 := by
  unfold tailWord_494184
  simp only [CollatzResearch.WordTrace]
  refine ⟨9012185620831621376444803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12016247494442161835259737 9012185620831621376444803)
  ·
    refine ⟨13518278431247432064667205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9012185620831621376444803 13518278431247432064667205)
    ·
      refine ⟨2534677205858893512125101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13518278431247432064667205 2534677205858893512125101)
      ·
        refine ⟨950503952197085067046913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2534677205858893512125101 950503952197085067046913)
        ·
          refine ⟨712877964147813800285185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 950503952197085067046913 712877964147813800285185)
          ·
            refine ⟨534658473110860350213889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 712877964147813800285185 534658473110860350213889)
            ·
              refine ⟨400993854833145262660417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 534658473110860350213889 400993854833145262660417)
              ·
                refine ⟨300745391124858946995313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 400993854833145262660417 300745391124858946995313)
                ·
                  refine ⟨225559043343644210246485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 300745391124858946995313 225559043343644210246485)
                  ·
                    rfl

theorem cell20_494184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 2, 2, 2, 2].length) (baseStart_494184 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_494184 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_494184 prefixEnd_494184 := by exact prefixLift 494184
  have htrace : WordTrace (prefixWord ++ tailWord_494184) baseStart_494184 baseEnd_494184 := by
    simpa [prefixWord, tailWord_494184, baseEnd_494184] using wordTrace_append hprefix tailTrace_494184
  have hstable : (prefixWord ++ tailWord_494184).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_494184).length < 2 ^ (prefixWord ++ tailWord_494184).sum := by decide
  have hdescent : baseEnd_494184 < baseStart_494184 := by decide
  rcases family_descends (prefixWord ++ tailWord_494184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_494188 : List Nat := [2, 2, 1, 1, 3, 1, 6, 2, 2]
def baseStart_494188 : Nat := 118140960795 + 494188 * 2 ^ 59
def prefixEnd_494188 : Nat := 4983230072969 + 3 ^ 40 * 494188 * 2
def baseEnd_494188 : Nat := 225560869052637974113135

theorem tailTrace_494188 : CollatzResearch.WordTrace tailWord_494188 prefixEnd_494188 225560869052637974113135 := by
  unfold tailWord_494188
  simp only [CollatzResearch.WordTrace]
  refine ⟨9012258566824375718017609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12016344755765834290690145 9012258566824375718017609)
  ·
    refine ⟨6759193925118281788513207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9012258566824375718017609 6759193925118281788513207)
    ·
      refine ⟨10138790887677422682769811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6759193925118281788513207 10138790887677422682769811)
      ·
        refine ⟨15208186331516134024154717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10138790887677422682769811 15208186331516134024154717)
        ·
          refine ⟨5703069874318550259058019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15208186331516134024154717 5703069874318550259058019)
          ·
            refine ⟨8554604811477825388587029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5703069874318550259058019 8554604811477825388587029)
            ·
              refine ⟨400997100538023065090017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 8554604811477825388587029 400997100538023065090017)
              ·
                refine ⟨300747825403517298817513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 400997100538023065090017 300747825403517298817513)
                ·
                  refine ⟨225560869052637974113135, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 300747825403517298817513 225560869052637974113135)
                  ·
                    rfl

theorem cell20_494188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 6, 2, 2].length) (baseStart_494188 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_494188 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_494188 prefixEnd_494188 := by exact prefixLift 494188
  have htrace : WordTrace (prefixWord ++ tailWord_494188) baseStart_494188 baseEnd_494188 := by
    simpa [prefixWord, tailWord_494188, baseEnd_494188] using wordTrace_append hprefix tailTrace_494188
  have hstable : (prefixWord ++ tailWord_494188).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_494188).length < 2 ^ (prefixWord ++ tailWord_494188).sum := by decide
  have hdescent : baseEnd_494188 < baseStart_494188 := by decide
  rcases family_descends (prefixWord ++ tailWord_494188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_494199 : List Nat := [1, 1, 3, 1, 1, 3, 5, 5]
def baseStart_494199 : Nat := 118140960795 + 494199 * 2 ^ 59
def prefixEnd_494199 : Nat := 4983230072969 + 3 ^ 40 * 494199 * 2
def baseEnd_494199 : Nat := 75188629917456941582141

theorem tailTrace_494199 : CollatzResearch.WordTrace tailWord_494199 prefixEnd_494199 75188629917456941582141 := by
  unfold tailWord_494199
  simp only [CollatzResearch.WordTrace]
  refine ⟨18024918336608900314685651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12016612224405933543123767 18024918336608900314685651)
  ·
    refine ⟨27037377504913350472028477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18024918336608900314685651 27037377504913350472028477)
    ·
      refine ⟨10139016564342506427010679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27037377504913350472028477 10139016564342506427010679)
      ·
        refine ⟨15208524846513759640516019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10139016564342506427010679 15208524846513759640516019)
        ·
          refine ⟨22812787269770639460774029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15208524846513759640516019 22812787269770639460774029)
          ·
            refine ⟨8554795226163989797790261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22812787269770639460774029 8554795226163989797790261)
            ·
              refine ⟨802012052452874043542837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 8554795226163989797790261 802012052452874043542837)
              ·
                refine ⟨75188629917456941582141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 802012052452874043542837 75188629917456941582141)
                ·
                  rfl

theorem cell20_494199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 5, 5].length) (baseStart_494199 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_494199 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_494199 prefixEnd_494199 := by exact prefixLift 494199
  have htrace : WordTrace (prefixWord ++ tailWord_494199) baseStart_494199 baseEnd_494199 := by
    simpa [prefixWord, tailWord_494199, baseEnd_494199] using wordTrace_append hprefix tailTrace_494199
  have hstable : (prefixWord ++ tailWord_494199).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_494199).length < 2 ^ (prefixWord ++ tailWord_494199).sum := by decide
  have hdescent : baseEnd_494199 < baseStart_494199 := by decide
  rcases family_descends (prefixWord ++ tailWord_494199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_494226 : List Nat := [3, 2, 3, 1, 2, 1, 1, 5, 2]
def baseStart_494226 : Nat := 118140960795 + 494226 * 2 ^ 59
def prefixEnd_494226 : Nat := 4983230072969 + 3 ^ 40 * 494226 * 2
def baseEnd_494226 : Nat := 225578213288078730846313

theorem tailTrace_494226 : CollatzResearch.WordTrace tailWord_494226 prefixEnd_494226 225578213288078730846313 := by
  unfold tailWord_494226
  simp only [CollatzResearch.WordTrace]
  refine ⟨4506475776877770981479633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12017268738340722617279021 4506475776877770981479633)
  ·
    refine ⟨3379856832658328236109725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4506475776877770981479633 3379856832658328236109725)
    ·
      refine ⟨1267446312246873088541147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3379856832658328236109725 1267446312246873088541147)
      ·
        refine ⟨1901169468370309632811721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1267446312246873088541147 1901169468370309632811721)
        ·
          refine ⟨1425877101277732224608791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1901169468370309632811721 1425877101277732224608791)
          ·
            refine ⟨2138815651916598336913187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1425877101277732224608791 2138815651916598336913187)
            ·
              refine ⟨3208223477874897505369781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2138815651916598336913187 3208223477874897505369781)
              ·
                refine ⟨300770951050771641128417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3208223477874897505369781 300770951050771641128417)
                ·
                  refine ⟨225578213288078730846313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 300770951050771641128417 225578213288078730846313)
                  ·
                    rfl

theorem cell20_494226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 1, 5, 2].length) (baseStart_494226 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_494226 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_494226 prefixEnd_494226 := by exact prefixLift 494226
  have htrace : WordTrace (prefixWord ++ tailWord_494226) baseStart_494226 baseEnd_494226 := by
    simpa [prefixWord, tailWord_494226, baseEnd_494226] using wordTrace_append hprefix tailTrace_494226
  have hstable : (prefixWord ++ tailWord_494226).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_494226).length < 2 ^ (prefixWord ++ tailWord_494226).sum := by decide
  have hdescent : baseEnd_494226 < baseStart_494226 := by decide
  rcases family_descends (prefixWord ++ tailWord_494226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_494268 : List Nat := [2, 2, 2, 3, 1, 1, 1, 4, 4]
def baseStart_494268 : Nat := 118140960795 + 494268 * 2 ^ 59
def prefixEnd_494268 : Nat := 4983230072969 + 3 ^ 40 * 494268 * 2
def baseEnd_494268 : Nat := 225597383232513251446141

theorem tailTrace_494268 : CollatzResearch.WordTrace tailWord_494268 prefixEnd_494268 225597383232513251446141 := by
  unfold tailWord_494268
  simp only [CollatzResearch.WordTrace]
  refine ⟨9013717486679462549473729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12018289982239283399298305 9013717486679462549473729)
  ·
    refine ⟨6760288115009596912105297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9013717486679462549473729 6760288115009596912105297)
    ·
      refine ⟨5070216086257197684078973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6760288115009596912105297 5070216086257197684078973)
      ·
        refine ⟨1901331032346449131529615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5070216086257197684078973 1901331032346449131529615)
        ·
          refine ⟨2851996548519673697294423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1901331032346449131529615 2851996548519673697294423)
          ·
            refine ⟨4277994822779510545941635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2851996548519673697294423 4277994822779510545941635)
            ·
              refine ⟨6416992234169265818912453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4277994822779510545941635 6416992234169265818912453)
              ·
                refine ⟨1203186043906737341046085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6416992234169265818912453 1203186043906737341046085)
                ·
                  refine ⟨225597383232513251446141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1203186043906737341046085 225597383232513251446141)
                  ·
                    rfl

theorem cell20_494268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 1, 4, 4].length) (baseStart_494268 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_494268 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_494268 prefixEnd_494268 := by exact prefixLift 494268
  have htrace : WordTrace (prefixWord ++ tailWord_494268) baseStart_494268 baseEnd_494268 := by
    simpa [prefixWord, tailWord_494268, baseEnd_494268] using wordTrace_append hprefix tailTrace_494268
  have hstable : (prefixWord ++ tailWord_494268).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_494268).length < 2 ^ (prefixWord ++ tailWord_494268).sum := by decide
  have hdescent : baseEnd_494268 < baseStart_494268 := by decide
  rcases family_descends (prefixWord ++ tailWord_494268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_494312 : List Nat := [2, 1, 4, 1, 5, 1, 2, 1, 3]
def baseStart_494312 : Nat := 118140960795 + 494312 * 2 ^ 59
def prefixEnd_494312 : Nat := 4983230072969 + 3 ^ 40 * 494312 * 2
def baseEnd_494312 : Nat := 225617466031444653979295

theorem tailTrace_494312 : CollatzResearch.WordTrace tailWord_494312 prefixEnd_494312 225617466031444653979295 := by
  unfold tailWord_494312
  simp only [CollatzResearch.WordTrace]
  refine ⟨9014519892599760306774595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12019359856799680409032793 9014519892599760306774595)
  ·
    refine ⟨13521779838899640460161893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9014519892599760306774595 13521779838899640460161893)
    ·
      refine ⟨2535333719793682586280355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13521779838899640460161893 2535333719793682586280355)
      ·
        refine ⟨3803000579690523879420533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2535333719793682586280355 3803000579690523879420533)
        ·
          refine ⟨356531304345986613695675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 3803000579690523879420533 356531304345986613695675)
          ·
            refine ⟨534796956518979920543513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 356531304345986613695675 534796956518979920543513)
            ·
              refine ⟨401097717389234940407635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 534796956518979920543513 401097717389234940407635)
              ·
                refine ⟨601646576083852410611453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 401097717389234940407635 601646576083852410611453)
                ·
                  refine ⟨225617466031444653979295, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 601646576083852410611453 225617466031444653979295)
                  ·
                    rfl

theorem cell20_494312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 5, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 5, 1, 2, 1, 3].length) (baseStart_494312 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_494312 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_494312 prefixEnd_494312 := by exact prefixLift 494312
  have htrace : WordTrace (prefixWord ++ tailWord_494312) baseStart_494312 baseEnd_494312 := by
    simpa [prefixWord, tailWord_494312, baseEnd_494312] using wordTrace_append hprefix tailTrace_494312
  have hstable : (prefixWord ++ tailWord_494312).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_494312).length < 2 ^ (prefixWord ++ tailWord_494312).sum := by decide
  have hdescent : baseEnd_494312 < baseStart_494312 := by decide
  rcases family_descends (prefixWord ++ tailWord_494312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_494327 : List Nat := [1, 1, 3, 1, 1, 1, 3, 3, 6]
def baseStart_494327 : Nat := 118140960795 + 494327 * 2 ^ 59
def prefixEnd_494327 : Nat := 4983230072969 + 3 ^ 40 * 494327 * 2
def baseEnd_494327 : Nat := 225624312440171268479233

theorem tailTrace_494327 : CollatzResearch.WordTrace tailWord_494327 prefixEnd_494327 225624312440171268479233 := by
  unfold tailWord_494327
  simp only [CollatzResearch.WordTrace]
  refine ⟨18029586880145178175345235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12019724586763452116896823 18029586880145178175345235)
  ·
    refine ⟨27044380320217767263017853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18029586880145178175345235 27044380320217767263017853)
    ·
      refine ⟨10141642620081662723631695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27044380320217767263017853 10141642620081662723631695)
      ·
        refine ⟨15212463930122494085447543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10141642620081662723631695 15212463930122494085447543)
        ·
          refine ⟨22818695895183741128171315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15212463930122494085447543 22818695895183741128171315)
          ·
            refine ⟨34228043842775611692256973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22818695895183741128171315 34228043842775611692256973)
            ·
              refine ⟨12835516441040854384596365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34228043842775611692256973 12835516441040854384596365)
              ·
                refine ⟨4813318665390320394223637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12835516441040854384596365 4813318665390320394223637)
                ·
                  refine ⟨225624312440171268479233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4813318665390320394223637 225624312440171268479233)
                  ·
                    rfl

theorem cell20_494327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 3, 6].length) (baseStart_494327 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_494327 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_494327 prefixEnd_494327 := by exact prefixLift 494327
  have htrace : WordTrace (prefixWord ++ tailWord_494327) baseStart_494327 baseEnd_494327 := by
    simpa [prefixWord, tailWord_494327, baseEnd_494327] using wordTrace_append hprefix tailTrace_494327
  have hstable : (prefixWord ++ tailWord_494327).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_494327).length < 2 ^ (prefixWord ++ tailWord_494327).sum := by decide
  have hdescent : baseEnd_494327 < baseStart_494327 := by decide
  rcases family_descends (prefixWord ++ tailWord_494327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_494368 : List Nat := [2, 1, 1, 5, 1, 4, 1, 5]
def baseStart_494368 : Nat := 118140960795 + 494368 * 2 ^ 59
def prefixEnd_494368 : Nat := 4983230072969 + 3 ^ 40 * 494368 * 2
def baseEnd_494368 : Nat := 75214341985785782704133

theorem tailTrace_494368 : CollatzResearch.WordTrace tailWord_494368 prefixEnd_494368 75214341985785782704133 := by
  unfold tailWord_494368
  simp only [CollatzResearch.WordTrace]
  refine ⟨9015541136498321088793879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12020721515331094785058505 9015541136498321088793879)
  ·
    refine ⟨13523311704747481633190819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9015541136498321088793879 13523311704747481633190819)
    ·
      refine ⟨20284967557121222449786229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13523311704747481633190819 20284967557121222449786229)
      ·
        refine ⟨1901715708480114604667459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 20284967557121222449786229 1901715708480114604667459)
        ·
          refine ⟨2852573562720171907001189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1901715708480114604667459 2852573562720171907001189)
          ·
            refine ⟨534857543010032232562723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2852573562720171907001189 534857543010032232562723)
            ·
              refine ⟨802286314515048348844085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 534857543010032232562723 802286314515048348844085)
              ·
                refine ⟨75214341985785782704133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 802286314515048348844085 75214341985785782704133)
                ·
                  rfl

theorem cell20_494368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 4, 1, 5].length) (baseStart_494368 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_494368 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_494368 prefixEnd_494368 := by exact prefixLift 494368
  have htrace : WordTrace (prefixWord ++ tailWord_494368) baseStart_494368 baseEnd_494368 := by
    simpa [prefixWord, tailWord_494368, baseEnd_494368] using wordTrace_append hprefix tailTrace_494368
  have hstable : (prefixWord ++ tailWord_494368).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_494368).length < 2 ^ (prefixWord ++ tailWord_494368).sum := by decide
  have hdescent : baseEnd_494368 < baseStart_494368 := by decide
  rcases family_descends (prefixWord ++ tailWord_494368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_494378 : List Nat := [3, 1, 4, 3, 1, 1, 1, 2, 4]
def baseStart_494378 : Nat := 118140960795 + 494378 * 2 ^ 59
def prefixEnd_494378 : Nat := 4983230072969 + 3 ^ 40 * 494378 * 2
def baseEnd_494378 : Nat := 225647590229841757779025

theorem tailTrace_494378 : CollatzResearch.WordTrace tailWord_494378 prefixEnd_494378 225647590229841757779025 := by
  unfold tailWord_494378
  simp only [CollatzResearch.WordTrace]
  refine ⟨4507861750740103471362947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12020964668640275923634525 4507861750740103471362947)
  ·
    refine ⟨6761792626110155207044421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4507861750740103471362947 6761792626110155207044421)
    ·
      refine ⟨1267836117395654101320829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6761792626110155207044421 1267836117395654101320829)
      ·
        refine ⟨475438544023370287995311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1267836117395654101320829 475438544023370287995311)
        ·
          refine ⟨713157816035055431992967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 475438544023370287995311 713157816035055431992967)
          ·
            refine ⟨1069736724052583147989451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 713157816035055431992967 1069736724052583147989451)
            ·
              refine ⟨1604605086078874721984177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1069736724052583147989451 1604605086078874721984177)
              ·
                refine ⟨1203453814559156041488133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1604605086078874721984177 1203453814559156041488133)
                ·
                  refine ⟨225647590229841757779025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1203453814559156041488133 225647590229841757779025)
                  ·
                    rfl

theorem cell20_494378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 1, 1, 2, 4].length) (baseStart_494378 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_494378 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_494378 prefixEnd_494378 := by exact prefixLift 494378
  have htrace : WordTrace (prefixWord ++ tailWord_494378) baseStart_494378 baseEnd_494378 := by
    simpa [prefixWord, tailWord_494378, baseEnd_494378] using wordTrace_append hprefix tailTrace_494378
  have hstable : (prefixWord ++ tailWord_494378).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_494378).length < 2 ^ (prefixWord ++ tailWord_494378).sum := by decide
  have hdescent : baseEnd_494378 < baseStart_494378 := by decide
  rcases family_descends (prefixWord ++ tailWord_494378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_494396 : List Nat := [2, 2, 2, 2, 1, 1, 1, 4, 5]
def baseStart_494396 : Nat := 118140960795 + 494396 * 2 ^ 59
def prefixEnd_494396 : Nat := 4983230072969 + 3 ^ 40 * 494396 * 2
def baseEnd_494396 : Nat := 225655805920313695178951

theorem tailTrace_494396 : CollatzResearch.WordTrace tailWord_494396 prefixEnd_494396 225655805920313695178951 := by
  unfold tailWord_494396
  simp only [CollatzResearch.WordTrace]
  refine ⟨9016051758447601479803521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12021402344596801973071361 9016051758447601479803521)
  ·
    refine ⟨6762038818835701109852641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9016051758447601479803521 6762038818835701109852641)
    ·
      refine ⟨5071529114126775832389481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6762038818835701109852641 5071529114126775832389481)
      ·
        refine ⟨3803646835595081874292111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5071529114126775832389481 3803646835595081874292111)
        ·
          refine ⟨5705470253392622811438167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3803646835595081874292111 5705470253392622811438167)
          ·
            refine ⟨8558205380088934217157251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5705470253392622811438167 8558205380088934217157251)
            ·
              refine ⟨12837308070133401325735877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8558205380088934217157251 12837308070133401325735877)
              ·
                refine ⟨2406995263150012748575477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12837308070133401325735877 2406995263150012748575477)
                ·
                  refine ⟨225655805920313695178951, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2406995263150012748575477 225655805920313695178951)
                  ·
                    rfl

theorem cell20_494396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 4, 5].length) (baseStart_494396 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_494396 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_494396 prefixEnd_494396 := by exact prefixLift 494396
  have htrace : WordTrace (prefixWord ++ tailWord_494396) baseStart_494396 baseEnd_494396 := by
    simpa [prefixWord, tailWord_494396, baseEnd_494396] using wordTrace_append hprefix tailTrace_494396
  have hstable : (prefixWord ++ tailWord_494396).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_494396).length < 2 ^ (prefixWord ++ tailWord_494396).sum := by decide
  have hdescent : baseEnd_494396 < baseStart_494396 := by decide
  rcases family_descends (prefixWord ++ tailWord_494396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_494399 : List Nat := [1, 1, 2, 2, 5, 1, 1, 5, 2]
def baseStart_494399 : Nat := 118140960795 + 494399 * 2 ^ 59
def prefixEnd_494399 : Nat := 4983230072969 + 3 ^ 40 * 494399 * 2
def baseEnd_494399 : Nat := 225657175202059018078939

theorem tailTrace_494399 : CollatzResearch.WordTrace tailWord_494399 prefixEnd_494399 225657175202059018078939 := by
  unfold tailWord_494399
  simp only [CollatzResearch.WordTrace]
  refine ⟨18032212935884334471966251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12021475290589556314644167 18032212935884334471966251)
  ·
    refine ⟨27048319403826501707949377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18032212935884334471966251 27048319403826501707949377)
    ·
      refine ⟨20286239552869876280962033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27048319403826501707949377 20286239552869876280962033)
      ·
        refine ⟨15214679664652407210721525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20286239552869876280962033 15214679664652407210721525)
        ·
          refine ⟨1426376218561163176005143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 15214679664652407210721525 1426376218561163176005143)
          ·
            refine ⟨2139564327841744764007715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1426376218561163176005143 2139564327841744764007715)
            ·
              refine ⟨3209346491762617146011573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2139564327841744764007715 3209346491762617146011573)
              ·
                refine ⟨300876233602745357438585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3209346491762617146011573 300876233602745357438585)
                ·
                  refine ⟨225657175202059018078939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 300876233602745357438585 225657175202059018078939)
                  ·
                    rfl

theorem cell20_494399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 1, 5, 2].length) (baseStart_494399 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_494399 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_494399 prefixEnd_494399 := by exact prefixLift 494399
  have htrace : WordTrace (prefixWord ++ tailWord_494399) baseStart_494399 baseEnd_494399 := by
    simpa [prefixWord, tailWord_494399, baseEnd_494399] using wordTrace_append hprefix tailTrace_494399
  have hstable : (prefixWord ++ tailWord_494399).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_494399).length < 2 ^ (prefixWord ++ tailWord_494399).sum := by decide
  have hdescent : baseEnd_494399 < baseStart_494399 := by decide
  rcases family_descends (prefixWord ++ tailWord_494399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_494403 : List Nat := [1, 1, 1, 3, 1, 4, 1, 2, 6]
def baseStart_494403 : Nat := 118140960795 + 494403 * 2 ^ 59
def prefixEnd_494403 : Nat := 4983230072969 + 3 ^ 40 * 494403 * 2
def baseEnd_494403 : Nat := 225659000911052781945589

theorem tailTrace_494403 : CollatzResearch.WordTrace tailWord_494403 prefixEnd_494403 225659000911052781945589 := by
  unfold tailWord_494403
  simp only [CollatzResearch.WordTrace]
  refine ⟨18032358827869843155111863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12021572551913228770074575 18032358827869843155111863)
  ·
    refine ⟨27048538241804764732667795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18032358827869843155111863 27048538241804764732667795)
    ·
      refine ⟨40572807362707147099001693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27048538241804764732667795 40572807362707147099001693)
      ·
        refine ⟨15214802761015180162125635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40572807362707147099001693 15214802761015180162125635)
        ·
          refine ⟨22822204141522770243188453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15214802761015180162125635 22822204141522770243188453)
          ·
            refine ⟨4279163276535519420597835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22822204141522770243188453 4279163276535519420597835)
            ·
              refine ⟨6418744914803279130896753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4279163276535519420597835 6418744914803279130896753)
              ·
                refine ⟨4814058686102459348172565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6418744914803279130896753 4814058686102459348172565)
                ·
                  refine ⟨225659000911052781945589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4814058686102459348172565 225659000911052781945589)
                  ·
                    rfl

theorem cell20_494403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 1, 2, 6].length) (baseStart_494403 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_494403 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_494403 prefixEnd_494403 := by exact prefixLift 494403
  have htrace : WordTrace (prefixWord ++ tailWord_494403) baseStart_494403 baseEnd_494403 := by
    simpa [prefixWord, tailWord_494403, baseEnd_494403] using wordTrace_append hprefix tailTrace_494403
  have hstable : (prefixWord ++ tailWord_494403).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_494403).length < 2 ^ (prefixWord ++ tailWord_494403).sum := by decide
  have hdescent : baseEnd_494403 < baseStart_494403 := by decide
  rcases family_descends (prefixWord ++ tailWord_494403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_494524 : List Nat := [2, 2, 2, 14]
def baseStart_494524 : Nat := 118140960795 + 494524 * 2 ^ 59
def prefixEnd_494524 : Nat := 4983230072969 + 3 ^ 40 * 494524 * 2
def baseEnd_494524 : Nat := 928865138304996456427

theorem tailTrace_494524 : CollatzResearch.WordTrace tailWord_494524 prefixEnd_494524 928865138304996456427 := by
  unfold tailWord_494524
  simp only [CollatzResearch.WordTrace]
  refine ⟨9018386030215740410133313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12024514706954320546844417 9018386030215740410133313)
  ·
    refine ⟨6763789522661805307599985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9018386030215740410133313 6763789522661805307599985)
    ·
      refine ⟨5072842141996353980699989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6763789522661805307599985 5072842141996353980699989)
      ·
        refine ⟨928865138304996456427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 14 5072842141996353980699989 928865138304996456427)
        ·
          rfl

theorem cell20_494524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 14].length) (baseStart_494524 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_494524 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_494524 prefixEnd_494524 := by exact prefixLift 494524
  have htrace : WordTrace (prefixWord ++ tailWord_494524) baseStart_494524 baseEnd_494524 := by
    simpa [prefixWord, tailWord_494524, baseEnd_494524] using wordTrace_append hprefix tailTrace_494524
  have hstable : (prefixWord ++ tailWord_494524).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_494524).length < 2 ^ (prefixWord ++ tailWord_494524).sum := by decide
  have hdescent : baseEnd_494524 < baseStart_494524 := by decide
  rcases family_descends (prefixWord ++ tailWord_494524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_494578 : List Nat := [3, 2, 1, 5, 2, 1, 1, 2, 3]
def baseStart_494578 : Nat := 118140960795 + 494578 * 2 ^ 59
def prefixEnd_494578 : Nat := 4983230072969 + 3 ^ 40 * 494578 * 2
def baseEnd_494578 : Nat := 225738875679529951111541

theorem tailTrace_494578 : CollatzResearch.WordTrace tailWord_494578 prefixEnd_494578 225738875679529951111541 := by
  unfold tailWord_494578
  simp only [CollatzResearch.WordTrace]
  refine ⟨4509685400558962010683097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12025827734823898695154925 4509685400558962010683097)
  ·
    refine ⟨3382264050419221508012323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4509685400558962010683097 3382264050419221508012323)
    ·
      refine ⟨5073396075628832262018485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3382264050419221508012323 5073396075628832262018485)
      ·
        refine ⟨475630882090203024564233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 5073396075628832262018485 475630882090203024564233)
        ·
          refine ⟨356723161567652268423175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 475630882090203024564233 356723161567652268423175)
          ·
            refine ⟨535084742351478402634763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 356723161567652268423175 535084742351478402634763)
            ·
              refine ⟨802627113527217603952145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 535084742351478402634763 802627113527217603952145)
              ·
                refine ⟨601970335145413202964109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 802627113527217603952145 601970335145413202964109)
                ·
                  refine ⟨225738875679529951111541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 601970335145413202964109 225738875679529951111541)
                  ·
                    rfl

theorem cell20_494578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 2, 1, 1, 2, 3].length) (baseStart_494578 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_494578 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_494578 prefixEnd_494578 := by exact prefixLift 494578
  have htrace : WordTrace (prefixWord ++ tailWord_494578) baseStart_494578 baseEnd_494578 := by
    simpa [prefixWord, tailWord_494578, baseEnd_494578] using wordTrace_append hprefix tailTrace_494578
  have hstable : (prefixWord ++ tailWord_494578).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_494578).length < 2 ^ (prefixWord ++ tailWord_494578).sum := by decide
  have hdescent : baseEnd_494578 < baseStart_494578 := by decide
  rcases family_descends (prefixWord ++ tailWord_494578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_494582 : List Nat := [5, 1, 1, 1, 3, 1, 3, 2, 3]
def baseStart_494582 : Nat := 118140960795 + 494582 * 2 ^ 59
def prefixEnd_494582 : Nat := 4983230072969 + 3 ^ 40 * 494582 * 2
def baseEnd_494582 : Nat := 225740701388523714978191

theorem tailTrace_494582 : CollatzResearch.WordTrace tailWord_494582 prefixEnd_494582 225740701388523714978191 := by
  unfold tailWord_494582
  simp only [CollatzResearch.WordTrace]
  refine ⟨1127430468388834795367375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 12025924996147571150585333 1127430468388834795367375)
  ·
    refine ⟨1691145702583252193051063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1127430468388834795367375 1691145702583252193051063)
    ·
      refine ⟨2536718553874878289576595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1691145702583252193051063 2536718553874878289576595)
      ·
        refine ⟨3805077830812317434364893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2536718553874878289576595 3805077830812317434364893)
        ·
          refine ⟨1426904186554619037886835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3805077830812317434364893 1426904186554619037886835)
          ·
            refine ⟨2140356279831928556830253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1426904186554619037886835 2140356279831928556830253)
            ·
              refine ⟨802633604936973208811345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2140356279831928556830253 802633604936973208811345)
              ·
                refine ⟨601975203702729906608509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 802633604936973208811345 601975203702729906608509)
                ·
                  refine ⟨225740701388523714978191, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 601975203702729906608509 225740701388523714978191)
                  ·
                    rfl

theorem cell20_494582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 3, 2, 3].length) (baseStart_494582 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_494582 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_494582 prefixEnd_494582 := by exact prefixLift 494582
  have htrace : WordTrace (prefixWord ++ tailWord_494582) baseStart_494582 baseEnd_494582 := by
    simpa [prefixWord, tailWord_494582, baseEnd_494582] using wordTrace_append hprefix tailTrace_494582
  have hstable : (prefixWord ++ tailWord_494582).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_494582).length < 2 ^ (prefixWord ++ tailWord_494582).sum := by decide
  have hdescent : baseEnd_494582 < baseStart_494582 := by decide
  rcases family_descends (prefixWord ++ tailWord_494582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_494617 : List Nat := [1, 2, 1, 2, 1, 1, 8, 4]
def baseStart_494617 : Nat := 118140960795 + 494617 * 2 ^ 59
def prefixEnd_494617 : Nat := 4983230072969 + 3 ^ 40 * 494617 * 2
def baseEnd_494617 : Nat := 75252225447406382937127

theorem tailTrace_494617 : CollatzResearch.WordTrace tailWord_494617 prefixEnd_494617 75252225447406382937127 := by
  unfold tailWord_494617
  simp only [CollatzResearch.WordTrace]
  refine ⟨18040164049094557703402105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12026776032729705135601403 18040164049094557703402105)
  ·
    refine ⟨13530123036820918277551579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18040164049094557703402105 13530123036820918277551579)
    ·
      refine ⟨20295184555231377416327369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13530123036820918277551579 20295184555231377416327369)
      ·
        refine ⟨15221388416423533062245527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20295184555231377416327369 15221388416423533062245527)
        ·
          refine ⟨22832082624635299593368291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15221388416423533062245527 22832082624635299593368291)
          ·
            refine ⟨34248123936952949390052437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22832082624635299593368291 34248123936952949390052437)
            ·
              refine ⟨401345202386167375664677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 34248123936952949390052437 401345202386167375664677)
              ·
                refine ⟨75252225447406382937127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 401345202386167375664677 75252225447406382937127)
                ·
                  rfl

theorem cell20_494617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 8, 4].length) (baseStart_494617 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_494617 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_494617 prefixEnd_494617 := by exact prefixLift 494617
  have htrace : WordTrace (prefixWord ++ tailWord_494617) baseStart_494617 baseEnd_494617 := by
    simpa [prefixWord, tailWord_494617, baseEnd_494617] using wordTrace_append hprefix tailTrace_494617
  have hstable : (prefixWord ++ tailWord_494617).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_494617).length < 2 ^ (prefixWord ++ tailWord_494617).sum := by decide
  have hdescent : baseEnd_494617 < baseStart_494617 := by decide
  rcases family_descends (prefixWord ++ tailWord_494617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_494627 : List Nat := [1, 1, 1, 4, 3, 2, 3, 3, 2]
def baseStart_494627 : Nat := 118140960795 + 494627 * 2 ^ 59
def prefixEnd_494627 : Nat := 4983230072969 + 3 ^ 40 * 494627 * 2
def baseEnd_494627 : Nat := 225761240614703558478007

theorem tailTrace_494627 : CollatzResearch.WordTrace tailWord_494627 prefixEnd_494627 225761240614703558478007 := by
  unfold tailWord_494627
  simp only [CollatzResearch.WordTrace]
  refine ⟨18040528779058329411266135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12027019186038886274177423 18040528779058329411266135)
  ·
    refine ⟨27060793168587494116899203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18040528779058329411266135 27060793168587494116899203)
    ·
      refine ⟨40591189752881241175348805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27060793168587494116899203 40591189752881241175348805)
      ·
        refine ⟨7610848078665232720377901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 40591189752881241175348805 7610848078665232720377901)
        ·
          refine ⟨2854068029499462270141713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7610848078665232720377901 2854068029499462270141713)
          ·
            refine ⟨2140551022124596702606285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2854068029499462270141713 2140551022124596702606285)
            ·
              refine ⟨802706633296723763477357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2140551022124596702606285 802706633296723763477357)
              ·
                refine ⟨301014987486271411304009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 802706633296723763477357 301014987486271411304009)
                ·
                  refine ⟨225761240614703558478007, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 301014987486271411304009 225761240614703558478007)
                  ·
                    rfl

theorem cell20_494627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 3, 3, 2].length) (baseStart_494627 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_494627 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_494627 prefixEnd_494627 := by exact prefixLift 494627
  have htrace : WordTrace (prefixWord ++ tailWord_494627) baseStart_494627 baseEnd_494627 := by
    simpa [prefixWord, tailWord_494627, baseEnd_494627] using wordTrace_append hprefix tailTrace_494627
  have hstable : (prefixWord ++ tailWord_494627).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_494627).length < 2 ^ (prefixWord ++ tailWord_494627).sum := by decide
  have hdescent : baseEnd_494627 < baseStart_494627 := by decide
  rcases family_descends (prefixWord ++ tailWord_494627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_494634 : List Nat := [3, 1, 4, 1, 3, 2, 6]
def baseStart_494634 : Nat := 118140960795 + 494634 * 2 ^ 59
def prefixEnd_494634 : Nat := 4983230072969 + 3 ^ 40 * 494634 * 2
def baseEnd_494634 : Nat := 25084937289493627249405

theorem tailTrace_494634 : CollatzResearch.WordTrace tailWord_494634 prefixEnd_494634 25084937289493627249405 := by
  unfold tailWord_494634
  simp only [CollatzResearch.WordTrace]
  refine ⟨4510196022508242401692739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12027189393355313071180637 4510196022508242401692739)
  ·
    refine ⟨6765294033762363602539109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4510196022508242401692739 6765294033762363602539109)
    ·
      refine ⟨1268492631330443175476083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6765294033762363602539109 1268492631330443175476083)
      ·
        refine ⟨1902738946995664763214125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1268492631330443175476083 1902738946995664763214125)
        ·
          refine ⟨713527105123374286205297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1902738946995664763214125 713527105123374286205297)
          ·
            refine ⟨535145328842530714653973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 713527105123374286205297 535145328842530714653973)
            ·
              refine ⟨25084937289493627249405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 535145328842530714653973 25084937289493627249405)
              ·
                rfl

theorem cell20_494634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 2, 6].length) (baseStart_494634 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_494634 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_494634 prefixEnd_494634 := by exact prefixLift 494634
  have htrace : WordTrace (prefixWord ++ tailWord_494634) baseStart_494634 baseEnd_494634 := by
    simpa [prefixWord, tailWord_494634, baseEnd_494634] using wordTrace_append hprefix tailTrace_494634
  have hstable : (prefixWord ++ tailWord_494634).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_494634).length < 2 ^ (prefixWord ++ tailWord_494634).sum := by decide
  have hdescent : baseEnd_494634 < baseStart_494634 := by decide
  rcases family_descends (prefixWord ++ tailWord_494634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_494644 : List Nat := [2, 5, 1, 2, 1, 3, 1, 1, 4]
def baseStart_494644 : Nat := 118140960795 + 494644 * 2 ^ 59
def prefixEnd_494644 : Nat := 4983230072969 + 3 ^ 40 * 494644 * 2
def baseEnd_494644 : Nat := 225768999877927054911271

theorem tailTrace_494644 : CollatzResearch.WordTrace tailWord_494644 prefixEnd_494644 225768999877927054911271 := by
  unfold tailWord_494644
  simp only [CollatzResearch.WordTrace]
  refine ⟨9020574409998370657317493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12027432546664494209756657 9020574409998370657317493)
  ·
    refine ⟨845678850937347249123515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 9020574409998370657317493 845678850937347249123515)
    ·
      refine ⟨1268518276406020873685273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 845678850937347249123515 1268518276406020873685273)
      ·
        refine ⟨951388707304515655263955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1268518276406020873685273 951388707304515655263955)
        ·
          refine ⟨1427083060956773482895933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 951388707304515655263955 1427083060956773482895933)
          ·
            refine ⟨535156147858790056085975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1427083060956773482895933 535156147858790056085975)
            ·
              refine ⟨802734221788185084128963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 535156147858790056085975 802734221788185084128963)
              ·
                refine ⟨1204101332682277626193445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 802734221788185084128963 1204101332682277626193445)
                ·
                  refine ⟨225768999877927054911271, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1204101332682277626193445 225768999877927054911271)
                  ·
                    rfl

theorem cell20_494644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 3, 1, 1, 4].length) (baseStart_494644 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_494644 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_494644 prefixEnd_494644 := by exact prefixLift 494644
  have htrace : WordTrace (prefixWord ++ tailWord_494644) baseStart_494644 baseEnd_494644 := by
    simpa [prefixWord, tailWord_494644, baseEnd_494644] using wordTrace_append hprefix tailTrace_494644
  have hstable : (prefixWord ++ tailWord_494644).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_494644).length < 2 ^ (prefixWord ++ tailWord_494644).sum := by decide
  have hdescent : baseEnd_494644 < baseStart_494644 := by decide
  rcases family_descends (prefixWord ++ tailWord_494644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_494648 : List Nat := [2, 1, 2, 1, 5, 1, 3, 1, 4]
def baseStart_494648 : Nat := 118140960795 + 494648 * 2 ^ 59
def prefixEnd_494648 : Nat := 4983230072969 + 3 ^ 40 * 494648 * 2
def baseEnd_494648 : Nat := 225770825586920818777921

theorem tailTrace_494648 : CollatzResearch.WordTrace tailWord_494648 prefixEnd_494648 225770825586920818777921 := by
  unfold tailWord_494648
  simp only [CollatzResearch.WordTrace]
  refine ⟨9020647355991124998890299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12027529807988166665187065 9020647355991124998890299)
  ·
    refine ⟨13530971033986687498335449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9020647355991124998890299 13530971033986687498335449)
    ·
      refine ⟨10148228275490015623751587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13530971033986687498335449 10148228275490015623751587)
      ·
        refine ⟨15222342413235023435627381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10148228275490015623751587 15222342413235023435627381)
        ·
          refine ⟨1427094601240783447090067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 15222342413235023435627381 1427094601240783447090067)
          ·
            refine ⟨2140641901861175170635101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1427094601240783447090067 2140641901861175170635101)
            ·
              refine ⟨802740713197940688988163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2140641901861175170635101 802740713197940688988163)
              ·
                refine ⟨1204111069796911033482245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 802740713197940688988163 1204111069796911033482245)
                ·
                  refine ⟨225770825586920818777921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1204111069796911033482245 225770825586920818777921)
                  ·
                    rfl

theorem cell20_494648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 3, 1, 4].length) (baseStart_494648 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_494648 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_494648 prefixEnd_494648 := by exact prefixLift 494648
  have htrace : WordTrace (prefixWord ++ tailWord_494648) baseStart_494648 baseEnd_494648 := by
    simpa [prefixWord, tailWord_494648, baseEnd_494648] using wordTrace_append hprefix tailTrace_494648
  have hstable : (prefixWord ++ tailWord_494648).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_494648).length < 2 ^ (prefixWord ++ tailWord_494648).sum := by decide
  have hdescent : baseEnd_494648 < baseStart_494648 := by decide
  rcases family_descends (prefixWord ++ tailWord_494648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_494724 : List Nat := [2, 3, 2, 1, 2, 3, 1, 2, 4]
def baseStart_494724 : Nat := 118140960795 + 494724 * 2 ^ 59
def prefixEnd_494724 : Nat := 4983230072969 + 3 ^ 40 * 494724 * 2
def baseEnd_494724 : Nat := 225805514057802332244277

theorem tailTrace_494724 : CollatzResearch.WordTrace tailWord_494724 prefixEnd_494724 225805514057802332244277 := by
  unfold tailWord_494724
  simp only [CollatzResearch.WordTrace]
  refine ⟨9022033329853457488773613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12029377773137943318364817 9022033329853457488773613)
  ·
    refine ⟨3383262498695046558290105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9022033329853457488773613 3383262498695046558290105)
    ·
      refine ⟨2537446874021284918717579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3383262498695046558290105 2537446874021284918717579)
      ·
        refine ⟨3806170311031927378076369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2537446874021284918717579 3806170311031927378076369)
        ·
          refine ⟨2854627733273945533557277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3806170311031927378076369 2854627733273945533557277)
          ·
            refine ⟨1070485399977729575083979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2854627733273945533557277 1070485399977729575083979)
            ·
              refine ⟨1605728099966594362625969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1070485399977729575083979 1605728099966594362625969)
              ·
                refine ⟨1204296074974945771969477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1605728099966594362625969 1204296074974945771969477)
                ·
                  refine ⟨225805514057802332244277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1204296074974945771969477 225805514057802332244277)
                  ·
                    rfl

theorem cell20_494724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 3, 1, 2, 4].length) (baseStart_494724 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_494724 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_494724 prefixEnd_494724 := by exact prefixLift 494724
  have htrace : WordTrace (prefixWord ++ tailWord_494724) baseStart_494724 baseEnd_494724 := by
    simpa [prefixWord, tailWord_494724, baseEnd_494724] using wordTrace_append hprefix tailTrace_494724
  have hstable : (prefixWord ++ tailWord_494724).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_494724).length < 2 ^ (prefixWord ++ tailWord_494724).sum := by decide
  have hdescent : baseEnd_494724 < baseStart_494724 := by decide
  rcases family_descends (prefixWord ++ tailWord_494724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_494751 : List Nat := [1, 1, 2, 6, 3, 1, 1, 2, 3]
def baseStart_494751 : Nat := 118140960795 + 494751 * 2 ^ 59
def prefixEnd_494751 : Nat := 4983230072969 + 3 ^ 40 * 494751 * 2
def baseEnd_494751 : Nat := 225817837593510238344167

theorem tailTrace_494751 : CollatzResearch.WordTrace tailWord_494751 prefixEnd_494751 225817837593510238344167 := by
  unfold tailWord_494751
  simp only [CollatzResearch.WordTrace]
  refine ⟨18045051430609098588780107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12030034287072732392520071 18045051430609098588780107)
  ·
    refine ⟨27067577145913647883170161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18045051430609098588780107 27067577145913647883170161)
    ·
      refine ⟨20300682859435235912377621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27067577145913647883170161 20300682859435235912377621)
      ·
        refine ⟨951594509036026683392701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 20300682859435235912377621 951594509036026683392701)
        ·
          refine ⟨356847940888510006272263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 951594509036026683392701 356847940888510006272263)
          ·
            refine ⟨535271911332765009408395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 356847940888510006272263 535271911332765009408395)
            ·
              refine ⟨802907866999147514112593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 535271911332765009408395 802907866999147514112593)
              ·
                refine ⟨602180900249360635584445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 802907866999147514112593 602180900249360635584445)
                ·
                  refine ⟨225817837593510238344167, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 602180900249360635584445 225817837593510238344167)
                  ·
                    rfl

theorem cell20_494751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 3, 1, 1, 2, 3].length) (baseStart_494751 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_494751 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_494751 prefixEnd_494751 := by exact prefixLift 494751
  have htrace : WordTrace (prefixWord ++ tailWord_494751) baseStart_494751 baseEnd_494751 := by
    simpa [prefixWord, tailWord_494751, baseEnd_494751] using wordTrace_append hprefix tailTrace_494751
  have hstable : (prefixWord ++ tailWord_494751).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_494751).length < 2 ^ (prefixWord ++ tailWord_494751).sum := by decide
  have hdescent : baseEnd_494751 < baseStart_494751 := by decide
  rcases family_descends (prefixWord ++ tailWord_494751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_494752 : List Nat := [2, 1, 1, 4, 2, 1, 9]
def baseStart_494752 : Nat := 118140960795 + 494752 * 2 ^ 59
def prefixEnd_494752 : Nat := 4983230072969 + 3 ^ 40 * 494752 * 2
def baseEnd_494752 : Nat := 25090921557862075478981

theorem tailTrace_494752 : CollatzResearch.WordTrace tailWord_494752 prefixEnd_494752 25090921557862075478981 := by
  unfold tailWord_494752
  simp only [CollatzResearch.WordTrace]
  refine ⟨9022543951802737879783255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12030058602403650506377673 9022543951802737879783255)
  ·
    refine ⟨13533815927704106819674883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9022543951802737879783255 13533815927704106819674883)
    ·
      refine ⟨20300723891556160229512325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13533815927704106819674883 20300723891556160229512325)
      ·
        refine ⟨3806385729666780043033561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20300723891556160229512325 3806385729666780043033561)
        ·
          refine ⟨2854789297250085032275171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3806385729666780043033561 2854789297250085032275171)
          ·
            refine ⟨4282183945875127548412757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2854789297250085032275171 4282183945875127548412757)
            ·
              refine ⟨25090921557862075478981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 4282183945875127548412757 25090921557862075478981)
              ·
                rfl

theorem cell20_494752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 9].length) (baseStart_494752 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_494752 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_494752 prefixEnd_494752 := by exact prefixLift 494752
  have htrace : WordTrace (prefixWord ++ tailWord_494752) baseStart_494752 baseEnd_494752 := by
    simpa [prefixWord, tailWord_494752, baseEnd_494752] using wordTrace_append hprefix tailTrace_494752
  have hstable : (prefixWord ++ tailWord_494752).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_494752).length < 2 ^ (prefixWord ++ tailWord_494752).sum := by decide
  have hdescent : baseEnd_494752 < baseStart_494752 := by decide
  rcases family_descends (prefixWord ++ tailWord_494752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_494783 : List Nat := [1, 1, 2, 2, 2, 2, 4, 2, 4]
def baseStart_494783 : Nat := 118140960795 + 494783 * 2 ^ 59
def prefixEnd_494783 : Nat := 4983230072969 + 3 ^ 40 * 494783 * 2
def baseEnd_494783 : Nat := 225832443265460349277369

theorem tailTrace_494783 : CollatzResearch.WordTrace tailWord_494783 prefixEnd_494783 225832443265460349277369 := by
  unfold tailWord_494783
  simp only [CollatzResearch.WordTrace]
  refine ⟨18046218566493168053945003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12030812377662112035963335 18046218566493168053945003)
  ·
    refine ⟨27069327849739752080917505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18046218566493168053945003 27069327849739752080917505)
    ·
      refine ⟨20301995887304814060688129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27069327849739752080917505 20301995887304814060688129)
      ·
        refine ⟨15226496915478610545516097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20301995887304814060688129 15226496915478610545516097)
        ·
          refine ⟨11419872686608957909137073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15226496915478610545516097 11419872686608957909137073)
          ·
            refine ⟨8564904514956718431852805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11419872686608957909137073 8564904514956718431852805)
            ·
              refine ⟨1605919596554384705972401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8564904514956718431852805 1605919596554384705972401)
              ·
                refine ⟨1204439697415788529479301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1605919596554384705972401 1204439697415788529479301)
                ·
                  refine ⟨225832443265460349277369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1204439697415788529479301 225832443265460349277369)
                  ·
                    rfl

theorem cell20_494783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 4, 2, 4].length) (baseStart_494783 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_494783 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_494783 prefixEnd_494783 := by exact prefixLift 494783
  have htrace : WordTrace (prefixWord ++ tailWord_494783) baseStart_494783 baseEnd_494783 := by
    simpa [prefixWord, tailWord_494783, baseEnd_494783] using wordTrace_append hprefix tailTrace_494783
  have hstable : (prefixWord ++ tailWord_494783).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_494783).length < 2 ^ (prefixWord ++ tailWord_494783).sum := by decide
  have hdescent : baseEnd_494783 < baseStart_494783 := by decide
  rcases family_descends (prefixWord ++ tailWord_494783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_494813 : List Nat := [1, 4, 3, 2, 2, 1, 3, 2, 2]
def baseStart_494813 : Nat := 118140960795 + 494813 * 2 ^ 59
def prefixEnd_494813 : Nat := 4983230072969 + 3 ^ 40 * 494813 * 2
def baseEnd_494813 : Nat := 225846136082913578277247

theorem tailTrace_494813 : CollatzResearch.WordTrace tailWord_494813 prefixEnd_494813 225846136082913578277247 := by
  unfold tailWord_494813
  simp only [CollatzResearch.WordTrace]
  refine ⟨18047312756384483177537093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12031541837589655451691395 18047312756384483177537093)
  ·
    refine ⟨3383871141822090595788205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18047312756384483177537093 3383871141822090595788205)
    ·
      refine ⟨1268951678183283973420577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3383871141822090595788205 1268951678183283973420577)
      ·
        refine ⟨951713758637462980065433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1268951678183283973420577 951713758637462980065433)
        ·
          refine ⟨713785318978097235049075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 951713758637462980065433 713785318978097235049075)
          ·
            refine ⟨1070677978467145852573613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 713785318978097235049075 1070677978467145852573613)
            ·
              refine ⟨401504241925179694715105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1070677978467145852573613 401504241925179694715105)
              ·
                refine ⟨301128181443884771036329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 401504241925179694715105 301128181443884771036329)
                ·
                  refine ⟨225846136082913578277247, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 301128181443884771036329 225846136082913578277247)
                  ·
                    rfl

theorem cell20_494813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 1, 3, 2, 2].length) (baseStart_494813 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_494813 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_494813 prefixEnd_494813 := by exact prefixLift 494813
  have htrace : WordTrace (prefixWord ++ tailWord_494813) baseStart_494813 baseEnd_494813 := by
    simpa [prefixWord, tailWord_494813, baseEnd_494813] using wordTrace_append hprefix tailTrace_494813
  have hstable : (prefixWord ++ tailWord_494813).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_494813).length < 2 ^ (prefixWord ++ tailWord_494813).sum := by decide
  have hdescent : baseEnd_494813 < baseStart_494813 := by decide
  rcases family_descends (prefixWord ++ tailWord_494813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_494828 : List Nat := [2, 2, 1, 1, 2, 4, 1, 7]
def baseStart_494828 : Nat := 118140960795 + 494828 * 2 ^ 59
def prefixEnd_494828 : Nat := 4983230072969 + 3 ^ 40 * 494828 * 2
def baseEnd_494828 : Nat := 75284327497213397592395

theorem tailTrace_494828 : CollatzResearch.WordTrace tailWord_494828 prefixEnd_494828 75284327497213397592395 := by
  unfold tailWord_494828
  simp only [CollatzResearch.WordTrace]
  refine ⟨9023929925665070369666569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12031906567553427159555425 9023929925665070369666569)
  ·
    refine ⟨6767947444248802777249927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9023929925665070369666569 6767947444248802777249927)
    ·
      refine ⟨10151921166373204165874891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6767947444248802777249927 10151921166373204165874891)
      ·
        refine ⟨15227881749559806248812337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10151921166373204165874891 15227881749559806248812337)
        ·
          refine ⟨11420911312169854686609253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15227881749559806248812337 11420911312169854686609253)
          ·
            refine ⟨2141420871031847753739235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11420911312169854686609253 2141420871031847753739235)
            ·
              refine ⟨3212131306547771630608853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2141420871031847753739235 3212131306547771630608853)
              ·
                refine ⟨75284327497213397592395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3212131306547771630608853 75284327497213397592395)
                ·
                  rfl

theorem cell20_494828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 1, 7].length) (baseStart_494828 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_494828 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_494828 prefixEnd_494828 := by exact prefixLift 494828
  have htrace : WordTrace (prefixWord ++ tailWord_494828) baseStart_494828 baseEnd_494828 := by
    simpa [prefixWord, tailWord_494828, baseEnd_494828] using wordTrace_append hprefix tailTrace_494828
  have hstable : (prefixWord ++ tailWord_494828).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_494828).length < 2 ^ (prefixWord ++ tailWord_494828).sum := by decide
  have hdescent : baseEnd_494828 < baseStart_494828 := by decide
  rcases family_descends (prefixWord ++ tailWord_494828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_494831 : List Nat := [1, 1, 2, 1, 7, 1, 1, 3, 3]
def baseStart_494831 : Nat := 118140960795 + 494831 * 2 ^ 59
def prefixEnd_494831 : Nat := 4983230072969 + 3 ^ 40 * 494831 * 2
def baseEnd_494831 : Nat := 225854351773385515677173

theorem tailTrace_494831 : CollatzResearch.WordTrace tailWord_494831 prefixEnd_494831 225854351773385515677173 := by
  unfold tailWord_494831
  simp only [CollatzResearch.WordTrace]
  refine ⟨18047969270319272251692347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12031979513546181501128231 18047969270319272251692347)
  ·
    refine ⟨27071953905478908377538521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18047969270319272251692347 27071953905478908377538521)
    ·
      refine ⟨20303965429109181283153891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27071953905478908377538521 20303965429109181283153891)
      ·
        refine ⟨30455948143663771924730837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20303965429109181283153891 30455948143663771924730837)
        ·
          refine ⟨713811284617119654485879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 30455948143663771924730837 713811284617119654485879)
          ·
            refine ⟨1070716926925679481728819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 713811284617119654485879 1070716926925679481728819)
            ·
              refine ⟨1606075390388519222593229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1070716926925679481728819 1606075390388519222593229)
              ·
                refine ⟨602278271395694708472461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1606075390388519222593229 602278271395694708472461)
                ·
                  refine ⟨225854351773385515677173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 602278271395694708472461 225854351773385515677173)
                  ·
                    rfl

theorem cell20_494831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 1, 1, 3, 3].length) (baseStart_494831 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_494831 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_494831 prefixEnd_494831 := by exact prefixLift 494831
  have htrace : WordTrace (prefixWord ++ tailWord_494831) baseStart_494831 baseEnd_494831 := by
    simpa [prefixWord, tailWord_494831, baseEnd_494831] using wordTrace_append hprefix tailTrace_494831
  have hstable : (prefixWord ++ tailWord_494831).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_494831).length < 2 ^ (prefixWord ++ tailWord_494831).sum := by decide
  have hdescent : baseEnd_494831 < baseStart_494831 := by decide
  rcases family_descends (prefixWord ++ tailWord_494831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_494872 : List Nat := [2, 1, 2, 3, 1, 5, 2, 2, 2]
def baseStart_494872 : Nat := 118140960795 + 494872 * 2 ^ 59
def prefixEnd_494872 : Nat := 4983230072969 + 3 ^ 40 * 494872 * 2
def baseEnd_494872 : Nat := 225873065290571595310339

theorem tailTrace_494872 : CollatzResearch.WordTrace tailWord_494872 prefixEnd_494872 225873065290571595310339 := by
  unfold tailWord_494872
  simp only [CollatzResearch.WordTrace]
  refine ⟨9024732331585368126967435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12032976442113824169289913 9024732331585368126967435)
  ·
    refine ⟨13537098497378052190451153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9024732331585368126967435 13537098497378052190451153)
    ·
      refine ⟨10152823873033539142838365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13537098497378052190451153 10152823873033539142838365)
      ·
        refine ⟨3807308952387577178564387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10152823873033539142838365 3807308952387577178564387)
        ·
          refine ⟨5710963428581365767846581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3807308952387577178564387 5710963428581365767846581)
          ·
            refine ⟨535402821429503040735617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 5710963428581365767846581 535402821429503040735617)
            ·
              refine ⟨401552116072127280551713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 535402821429503040735617 401552116072127280551713)
              ·
                refine ⟨301164087054095460413785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 401552116072127280551713 301164087054095460413785)
                ·
                  refine ⟨225873065290571595310339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 301164087054095460413785 225873065290571595310339)
                  ·
                    rfl

theorem cell20_494872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 5, 2, 2, 2].length) (baseStart_494872 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_494872 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_494872 prefixEnd_494872 := by exact prefixLift 494872
  have htrace : WordTrace (prefixWord ++ tailWord_494872) baseStart_494872 baseEnd_494872 := by
    simpa [prefixWord, tailWord_494872, baseEnd_494872] using wordTrace_append hprefix tailTrace_494872
  have hstable : (prefixWord ++ tailWord_494872).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_494872).length < 2 ^ (prefixWord ++ tailWord_494872).sum := by decide
  have hdescent : baseEnd_494872 < baseStart_494872 := by decide
  rcases family_descends (prefixWord ++ tailWord_494872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_494883 : List Nat := [1, 1, 1, 4, 2, 5, 1, 5]
def baseStart_494883 : Nat := 118140960795 + 494883 * 2 ^ 59
def prefixEnd_494883 : Nat := 4983230072969 + 3 ^ 40 * 494883 * 2
def baseEnd_494883 : Nat := 75292695330101481981209

theorem tailTrace_494883 : CollatzResearch.WordTrace tailWord_494883 prefixEnd_494883 75292695330101481981209 := by
  unfold tailWord_494883
  simp only [CollatzResearch.WordTrace]
  refine ⟨18049865866130885132585303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12033243910753923421723535 18049865866130885132585303)
  ·
    refine ⟨27074798799196327698877955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18049865866130885132585303 27074798799196327698877955)
    ·
      refine ⟨40612198198794491548316933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27074798799196327698877955 40612198198794491548316933)
      ·
        refine ⟨7614787162273967165309425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 40612198198794491548316933 7614787162273967165309425)
        ·
          refine ⟨5711090371705475373982069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7614787162273967165309425 5711090371705475373982069)
          ·
            refine ⟨535414722347388316310819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 5711090371705475373982069 535414722347388316310819)
            ·
              refine ⟨803122083521082474466229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 535414722347388316310819 803122083521082474466229)
              ·
                refine ⟨75292695330101481981209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 803122083521082474466229 75292695330101481981209)
                ·
                  rfl

theorem cell20_494883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 5, 1, 5].length) (baseStart_494883 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_494883 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_494883 prefixEnd_494883 := by exact prefixLift 494883
  have htrace : WordTrace (prefixWord ++ tailWord_494883) baseStart_494883 baseEnd_494883 := by
    simpa [prefixWord, tailWord_494883, baseEnd_494883] using wordTrace_append hprefix tailTrace_494883
  have hstable : (prefixWord ++ tailWord_494883).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_494883).length < 2 ^ (prefixWord ++ tailWord_494883).sum := by decide
  have hdescent : baseEnd_494883 < baseStart_494883 := by decide
  rcases family_descends (prefixWord ++ tailWord_494883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_494893 : List Nat := [1, 5, 3, 1, 1, 2, 1, 2, 4]
def baseStart_494893 : Nat := 118140960795 + 494893 * 2 ^ 59
def prefixEnd_494893 : Nat := 4983230072969 + 3 ^ 40 * 494893 * 2
def baseEnd_494893 : Nat := 225882650262788855610253

theorem tailTrace_494893 : CollatzResearch.WordTrace tailWord_494893 prefixEnd_494893 225882650262788855610253 := by
  unfold tailWord_494893
  simp only [CollatzResearch.WordTrace]
  refine ⟨18050230596094656840449333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12033487064063104560299555 18050230596094656840449333)
  ·
    refine ⟨1692209118383874078792125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 18050230596094656840449333 1692209118383874078792125)
    ·
      refine ⟨634578419393952779547047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1692209118383874078792125 634578419393952779547047)
      ·
        refine ⟨951867629090929169320571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 634578419393952779547047 951867629090929169320571)
        ·
          refine ⟨1427801443636393753980857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 951867629090929169320571 1427801443636393753980857)
          ·
            refine ⟨1070851082727295315485643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1427801443636393753980857 1070851082727295315485643)
            ·
              refine ⟨1606276624090942973228465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1070851082727295315485643 1606276624090942973228465)
              ·
                refine ⟨1204707468068207229921349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1606276624090942973228465 1204707468068207229921349)
                ·
                  refine ⟨225882650262788855610253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1204707468068207229921349 225882650262788855610253)
                  ·
                    rfl

theorem cell20_494893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 2, 1, 2, 4].length) (baseStart_494893 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_494893 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_494893 prefixEnd_494893 := by exact prefixLift 494893
  have htrace : WordTrace (prefixWord ++ tailWord_494893) baseStart_494893 baseEnd_494893 := by
    simpa [prefixWord, tailWord_494893, baseEnd_494893] using wordTrace_append hprefix tailTrace_494893
  have hstable : (prefixWord ++ tailWord_494893).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_494893).length < 2 ^ (prefixWord ++ tailWord_494893).sum := by decide
  have hdescent : baseEnd_494893 < baseStart_494893 := by decide
  rcases family_descends (prefixWord ++ tailWord_494893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_494897 : List Nat := [1, 2, 2, 3, 3, 1, 1, 1, 6]
def baseStart_494897 : Nat := 118140960795 + 494897 * 2 ^ 59
def prefixEnd_494897 : Nat := 4983230072969 + 3 ^ 40 * 494897 * 2
def baseEnd_494897 : Nat := 225884475971782619476903

theorem tailTrace_494897 : CollatzResearch.WordTrace tailWord_494897 prefixEnd_494897 225884475971782619476903 := by
  unfold tailWord_494897
  simp only [CollatzResearch.WordTrace]
  refine ⟨18050376488080165523594945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12033584325386777015729963 18050376488080165523594945)
  ·
    refine ⟨13537782366060124142696209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18050376488080165523594945 13537782366060124142696209)
    ·
      refine ⟨10153336774545093107022157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13537782366060124142696209 10153336774545093107022157)
      ·
        refine ⟨3807501290454409915133309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10153336774545093107022157 3807501290454409915133309)
        ·
          refine ⟨1427812983920403718174991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3807501290454409915133309 1427812983920403718174991)
          ·
            refine ⟨2141719475880605577262487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1427812983920403718174991 2141719475880605577262487)
            ·
              refine ⟨3212579213820908365893731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2141719475880605577262487 3212579213820908365893731)
              ·
                refine ⟨4818868820731362548840597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3212579213820908365893731 4818868820731362548840597)
                ·
                  refine ⟨225884475971782619476903, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4818868820731362548840597 225884475971782619476903)
                  ·
                    rfl

theorem cell20_494897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 1, 1, 6].length) (baseStart_494897 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_494897 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_494897 prefixEnd_494897 := by exact prefixLift 494897
  have htrace : WordTrace (prefixWord ++ tailWord_494897) baseStart_494897 baseEnd_494897 := by
    simpa [prefixWord, tailWord_494897, baseEnd_494897] using wordTrace_append hprefix tailTrace_494897
  have hstable : (prefixWord ++ tailWord_494897).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_494897).length < 2 ^ (prefixWord ++ tailWord_494897).sum := by decide
  have hdescent : baseEnd_494897 < baseStart_494897 := by decide
  rcases family_descends (prefixWord ++ tailWord_494897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_494900 : List Nat := [2, 5, 1, 1, 1, 1, 5, 4]
def baseStart_494900 : Nat := 118140960795 + 494900 * 2 ^ 59
def prefixEnd_494900 : Nat := 4983230072969 + 3 ^ 40 * 494900 * 2
def baseEnd_494900 : Nat := 75295281751175980792297

theorem tailTrace_494900 : CollatzResearch.WordTrace tailWord_494900 prefixEnd_494900 75295281751175980792297 := by
  unfold tailWord_494900
  simp only [CollatzResearch.WordTrace]
  refine ⟨9025242953534648517977077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12033657271379531357302769 9025242953534648517977077)
  ·
    refine ⟨846116526893873298560351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 9025242953534648517977077 846116526893873298560351)
    ·
      refine ⟨1269174790340809947840527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 846116526893873298560351 1269174790340809947840527)
      ·
        refine ⟨1903762185511214921760791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1269174790340809947840527 1903762185511214921760791)
        ·
          refine ⟨2855643278266822382641187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1903762185511214921760791 2855643278266822382641187)
          ·
            refine ⟨4283464917400233573961781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2855643278266822382641187 4283464917400233573961781)
            ·
              refine ⟨401574836006271897558917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4283464917400233573961781 401574836006271897558917)
              ·
                refine ⟨75295281751175980792297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 401574836006271897558917 75295281751175980792297)
                ·
                  rfl

theorem cell20_494900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 5, 4].length) (baseStart_494900 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_494900 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_494900 prefixEnd_494900 := by exact prefixLift 494900
  have htrace : WordTrace (prefixWord ++ tailWord_494900) baseStart_494900 baseEnd_494900 := by
    simpa [prefixWord, tailWord_494900, baseEnd_494900] using wordTrace_append hprefix tailTrace_494900
  have hstable : (prefixWord ++ tailWord_494900).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_494900).length < 2 ^ (prefixWord ++ tailWord_494900).sum := by decide
  have hdescent : baseEnd_494900 < baseStart_494900 := by decide
  rcases family_descends (prefixWord ++ tailWord_494900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_494935 : List Nat := [1, 1, 3, 2, 3, 2, 1, 3, 4]
def baseStart_494935 : Nat := 118140960795 + 494935 * 2 ^ 59
def prefixEnd_494935 : Nat := 4983230072969 + 3 ^ 40 * 494935 * 2
def baseEnd_494935 : Nat := 225901820207223376210081

theorem tailTrace_494935 : CollatzResearch.WordTrace tailWord_494935 prefixEnd_494935 225901820207223376210081 := by
  unfold tailWord_494935
  simp only [CollatzResearch.WordTrace]
  refine ⟨18051762461942498013478259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12034508307961665342318839 18051762461942498013478259)
  ·
    refine ⟨27077643692913747020217389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18051762461942498013478259 27077643692913747020217389)
    ·
      refine ⟨10154116384842655132581521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27077643692913747020217389 10154116384842655132581521)
      ·
        refine ⟨7615587288631991349436141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10154116384842655132581521 7615587288631991349436141)
        ·
          refine ⟨2855845233236996756038553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7615587288631991349436141 2855845233236996756038553)
          ·
            refine ⟨2141883924927747567028915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2855845233236996756038553 2141883924927747567028915)
            ·
              refine ⟨3212825887391621350543373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2141883924927747567028915 3212825887391621350543373)
              ·
                refine ⟨1204809707771858006453765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3212825887391621350543373 1204809707771858006453765)
                ·
                  refine ⟨225901820207223376210081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1204809707771858006453765 225901820207223376210081)
                  ·
                    rfl

theorem cell20_494935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 1, 3, 4].length) (baseStart_494935 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_494935 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_494935 prefixEnd_494935 := by exact prefixLift 494935
  have htrace : WordTrace (prefixWord ++ tailWord_494935) baseStart_494935 baseEnd_494935 := by
    simpa [prefixWord, tailWord_494935, baseEnd_494935] using wordTrace_append hprefix tailTrace_494935
  have hstable : (prefixWord ++ tailWord_494935).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_494935).length < 2 ^ (prefixWord ++ tailWord_494935).sum := by decide
  have hdescent : baseEnd_494935 < baseStart_494935 := by decide
  rcases family_descends (prefixWord ++ tailWord_494935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_494965 : List Nat := [1, 3, 4, 1, 4, 1, 1, 3, 2]
def baseStart_494965 : Nat := 118140960795 + 494965 * 2 ^ 59
def prefixEnd_494965 : Nat := 4983230072969 + 3 ^ 40 * 494965 * 2
def baseEnd_494965 : Nat := 225915513024676605209959

theorem tailTrace_494965 : CollatzResearch.WordTrace tailWord_494965 prefixEnd_494965 225915513024676605209959 := by
  unfold tailWord_494965
  simp only [CollatzResearch.WordTrace]
  refine ⟨18052856651833813137070349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12035237767889208758046899 18052856651833813137070349)
  ·
    refine ⟨6769821244437679926401381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18052856651833813137070349 6769821244437679926401381)
    ·
      refine ⟨1269341483332064986200259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6769821244437679926401381 1269341483332064986200259)
      ·
        refine ⟨1904012224998097479300389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1269341483332064986200259 1904012224998097479300389)
        ·
          refine ⟨357002292187143277368823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1904012224998097479300389 357002292187143277368823)
          ·
            refine ⟨535503438280714916053235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 357002292187143277368823 535503438280714916053235)
            ·
              refine ⟨803255157421072374079853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 535503438280714916053235 803255157421072374079853)
              ·
                refine ⟨301220684032902140279945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 803255157421072374079853 301220684032902140279945)
                ·
                  refine ⟨225915513024676605209959, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 301220684032902140279945 225915513024676605209959)
                  ·
                    rfl

theorem cell20_494965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 4, 1, 1, 3, 2].length) (baseStart_494965 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_494965 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_494965 prefixEnd_494965 := by exact prefixLift 494965
  have htrace : WordTrace (prefixWord ++ tailWord_494965) baseStart_494965 baseEnd_494965 := by
    simpa [prefixWord, tailWord_494965, baseEnd_494965] using wordTrace_append hprefix tailTrace_494965
  have hstable : (prefixWord ++ tailWord_494965).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_494965).length < 2 ^ (prefixWord ++ tailWord_494965).sum := by decide
  have hdescent : baseEnd_494965 < baseStart_494965 := by decide
  rcases family_descends (prefixWord ++ tailWord_494965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_494980 : List Nat := [2, 3, 2, 1, 1, 3, 8]
def baseStart_494980 : Nat := 118140960795 + 494980 * 2 ^ 59
def prefixEnd_494980 : Nat := 4983230072969 + 3 ^ 40 * 494980 * 2
def baseEnd_494980 : Nat := 25102484381489246634433

theorem tailTrace_494980 : CollatzResearch.WordTrace tailWord_494980 prefixEnd_494980 25102484381489246634433 := by
  unfold tailWord_494980
  simp only [CollatzResearch.WordTrace]
  refine ⟨9026701873389735349433197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12035602497852980465910929 9026701873389735349433197)
  ·
    refine ⟨3385013202521150756037449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9026701873389735349433197 3385013202521150756037449)
    ·
      refine ⟨2538759901890863067028087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3385013202521150756037449 2538759901890863067028087)
      ·
        refine ⟨3808139852836294600542131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2538759901890863067028087 3808139852836294600542131)
        ·
          refine ⟨5712209779254441900813197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3808139852836294600542131 5712209779254441900813197)
          ·
            refine ⟨2142078667220415712804949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5712209779254441900813197 2142078667220415712804949)
            ·
              refine ⟨25102484381489246634433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2142078667220415712804949 25102484381489246634433)
              ·
                rfl

theorem cell20_494980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 8].length) (baseStart_494980 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_494980 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_494980 prefixEnd_494980 := by exact prefixLift 494980
  have htrace : WordTrace (prefixWord ++ tailWord_494980) baseStart_494980 baseEnd_494980 := by
    simpa [prefixWord, tailWord_494980, baseEnd_494980] using wordTrace_append hprefix tailTrace_494980
  have hstable : (prefixWord ++ tailWord_494980).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_494980).length < 2 ^ (prefixWord ++ tailWord_494980).sum := by decide
  have hdescent : baseEnd_494980 < baseStart_494980 := by decide
  rcases family_descends (prefixWord ++ tailWord_494980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_494987 : List Nat := [1, 1, 1, 1, 4, 3, 1, 3, 5]
def baseStart_494987 : Nat := 118140960795 + 494987 * 2 ^ 59
def prefixEnd_494987 : Nat := 4983230072969 + 3 ^ 40 * 494987 * 2
def baseEnd_494987 : Nat := 225925554424142306476535

theorem tailTrace_494987 : CollatzResearch.WordTrace tailWord_494987 prefixEnd_494987 225925554424142306476535 := by
  unfold tailWord_494987
  simp only [CollatzResearch.WordTrace]
  refine ⟨18053659057754110894371215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12035772705169407262914143 18053659057754110894371215)
  ·
    refine ⟨27080488586631166341556823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18053659057754110894371215 27080488586631166341556823)
    ·
      refine ⟨40620732879946749512335235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27080488586631166341556823 40620732879946749512335235)
      ·
        refine ⟨60931099319920124268502853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40620732879946749512335235 60931099319920124268502853)
        ·
          refine ⟨11424581122485023300344285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 60931099319920124268502853 11424581122485023300344285)
          ·
            refine ⟨4284217920931883737629107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11424581122485023300344285 4284217920931883737629107)
            ·
              refine ⟨6426326881397825606443661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4284217920931883737629107 6426326881397825606443661)
              ·
                refine ⟨2409872580524184602416373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6426326881397825606443661 2409872580524184602416373)
                ·
                  refine ⟨225925554424142306476535, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2409872580524184602416373 225925554424142306476535)
                  ·
                    rfl

theorem cell20_494987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 1, 3, 5].length) (baseStart_494987 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_494987 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_494987 prefixEnd_494987 := by exact prefixLift 494987
  have htrace : WordTrace (prefixWord ++ tailWord_494987) baseStart_494987 baseEnd_494987 := by
    simpa [prefixWord, tailWord_494987, baseEnd_494987] using wordTrace_append hprefix tailTrace_494987
  have hstable : (prefixWord ++ tailWord_494987).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_494987).length < 2 ^ (prefixWord ++ tailWord_494987).sum := by decide
  have hdescent : baseEnd_494987 < baseStart_494987 := by decide
  rcases family_descends (prefixWord ++ tailWord_494987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_495073 : List Nat := [1, 2, 3, 1, 2, 4, 3, 4]
def baseStart_495073 : Nat := 118140960795 + 495073 * 2 ^ 59
def prefixEnd_495073 : Nat := 4983230072969 + 3 ^ 40 * 495073 * 2
def baseEnd_495073 : Nat := 75321602389169409869839

theorem tailTrace_495073 : CollatzResearch.WordTrace tailWord_495073 prefixEnd_495073 75321602389169409869839 := by
  unfold tailWord_495073
  simp only [CollatzResearch.WordTrace]
  refine ⟨18056795735442547582001873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12037863823628365054667915 18056795735442547582001873)
  ·
    refine ⟨13542596801581910686501405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18056795735442547582001873 13542596801581910686501405)
    ·
      refine ⟨5078473800593216507438027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13542596801581910686501405 5078473800593216507438027)
      ·
        refine ⟨7617710700889824761157041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5078473800593216507438027 7617710700889824761157041)
        ·
          refine ⟨5713283025667368570867781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7617710700889824761157041 5713283025667368570867781)
          ·
            refine ⟨1071240567312631607037709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5713283025667368570867781 1071240567312631607037709)
            ·
              refine ⟨401715212742236852639141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1071240567312631607037709 401715212742236852639141)
              ·
                refine ⟨75321602389169409869839, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 401715212742236852639141 75321602389169409869839)
                ·
                  rfl

theorem cell20_495073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 4, 3, 4].length) (baseStart_495073 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_495073 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_495073 prefixEnd_495073 := by exact prefixLift 495073
  have htrace : WordTrace (prefixWord ++ tailWord_495073) baseStart_495073 baseEnd_495073 := by
    simpa [prefixWord, tailWord_495073, baseEnd_495073] using wordTrace_append hprefix tailTrace_495073
  have hstable : (prefixWord ++ tailWord_495073).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_495073).length < 2 ^ (prefixWord ++ tailWord_495073).sum := by decide
  have hdescent : baseEnd_495073 < baseStart_495073 := by decide
  rcases family_descends (prefixWord ++ tailWord_495073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_495124 : List Nat := [2, 4, 3, 1, 3, 1, 2, 4]
def baseStart_495124 : Nat := 118140960795 + 495124 * 2 ^ 59
def prefixEnd_495124 : Nat := 4983230072969 + 3 ^ 40 * 495124 * 2
def baseEnd_495124 : Nat := 75329361652392906303103

theorem tailTrace_495124 : CollatzResearch.WordTrace tailWord_495124 prefixEnd_495124 75329361652392906303103 := by
  unfold tailWord_495124
  simp only [CollatzResearch.WordTrace]
  refine ⟨9029327929128891646054213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12039103905505188861405617 9029327929128891646054213)
  ·
    refine ⟨1692998986711667183635165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9029327929128891646054213 1692998986711667183635165)
    ·
      refine ⟨634874620016875193863187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1692998986711667183635165 634874620016875193863187)
      ·
        refine ⟨952311930025312790794781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 634874620016875193863187 952311930025312790794781)
        ·
          refine ⟨357116973759492296548043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 952311930025312790794781 357116973759492296548043)
          ·
            refine ⟨535675460639238444822065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 357116973759492296548043 535675460639238444822065)
            ·
              refine ⟨401756595479428833616549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 535675460639238444822065 401756595479428833616549)
              ·
                refine ⟨75329361652392906303103, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 401756595479428833616549 75329361652392906303103)
                ·
                  rfl

theorem cell20_495124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 3, 1, 2, 4].length) (baseStart_495124 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_495124 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_495124 prefixEnd_495124 := by exact prefixLift 495124
  have htrace : WordTrace (prefixWord ++ tailWord_495124) baseStart_495124 baseEnd_495124 := by
    simpa [prefixWord, tailWord_495124, baseEnd_495124] using wordTrace_append hprefix tailTrace_495124
  have hstable : (prefixWord ++ tailWord_495124).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_495124).length < 2 ^ (prefixWord ++ tailWord_495124).sum := by decide
  have hdescent : baseEnd_495124 < baseStart_495124 := by decide
  rcases family_descends (prefixWord ++ tailWord_495124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_495125 : List Nat := [1, 3, 2, 1, 3, 2, 2, 2, 4]
def baseStart_495125 : Nat := 118140960795 + 495125 * 2 ^ 59
def prefixEnd_495125 : Nat := 4983230072969 + 3 ^ 40 * 495125 * 2
def baseEnd_495125 : Nat := 225988541384427159875971

theorem tailTrace_495125 : CollatzResearch.WordTrace tailWord_495125 prefixEnd_495125 225988541384427159875971 := by
  unfold tailWord_495125
  simp only [CollatzResearch.WordTrace]
  refine ⟨18058692331254160462894829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12039128220836106975263219 18058692331254160462894829)
  ·
    refine ⟨6772009624220310173585561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18058692331254160462894829 6772009624220310173585561)
    ·
      refine ⟨5079007218165232630189171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6772009624220310173585561 5079007218165232630189171)
      ·
        refine ⟨7618510827247848945283757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5079007218165232630189171 7618510827247848945283757)
        ·
          refine ⟨2856941560217943354481409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7618510827247848945283757 2856941560217943354481409)
          ·
            refine ⟨2142706170163457515861057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2856941560217943354481409 2142706170163457515861057)
            ·
              refine ⟨1607029627622593136895793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2142706170163457515861057 1607029627622593136895793)
              ·
                refine ⟨1205272220716944852671845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1607029627622593136895793 1205272220716944852671845)
                ·
                  refine ⟨225988541384427159875971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1205272220716944852671845 225988541384427159875971)
                  ·
                    rfl

theorem cell20_495125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 2, 2, 4].length) (baseStart_495125 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_495125 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_495125 prefixEnd_495125 := by exact prefixLift 495125
  have htrace : WordTrace (prefixWord ++ tailWord_495125) baseStart_495125 baseEnd_495125 := by
    simpa [prefixWord, tailWord_495125, baseEnd_495125] using wordTrace_append hprefix tailTrace_495125
  have hstable : (prefixWord ++ tailWord_495125).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_495125).length < 2 ^ (prefixWord ++ tailWord_495125).sum := by decide
  have hdescent : baseEnd_495125 < baseStart_495125 := by decide
  rcases family_descends (prefixWord ++ tailWord_495125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_495128 : List Nat := [2, 1, 2, 3, 4, 2, 2, 4]
def baseStart_495128 : Nat := 118140960795 + 495128 * 2 ^ 59
def prefixEnd_495128 : Nat := 4983230072969 + 3 ^ 40 * 495128 * 2
def baseEnd_495128 : Nat := 75329970222057494258653

theorem tailTrace_495128 : CollatzResearch.WordTrace tailWord_495128 prefixEnd_495128 75329970222057494258653 := by
  unfold tailWord_495128
  simp only [CollatzResearch.WordTrace]
  refine ⟨9029400875121645987627019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12039201166828861316836025 9029400875121645987627019)
  ·
    refine ⟨13544101312682468981440529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9029400875121645987627019 13544101312682468981440529)
    ·
      refine ⟨10158075984511851736080397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13544101312682468981440529 10158075984511851736080397)
      ·
        refine ⟨3809278494191944401030149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10158075984511851736080397 3809278494191944401030149)
        ·
          refine ⟨714239717660989575193153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3809278494191944401030149 714239717660989575193153)
          ·
            refine ⟨535679788245742181394865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 714239717660989575193153 535679788245742181394865)
            ·
              refine ⟨401759841184306636046149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 535679788245742181394865 401759841184306636046149)
              ·
                refine ⟨75329970222057494258653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 401759841184306636046149 75329970222057494258653)
                ·
                  rfl

theorem cell20_495128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 2, 2, 4].length) (baseStart_495128 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_495128 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_495128 prefixEnd_495128 := by exact prefixLift 495128
  have htrace : WordTrace (prefixWord ++ tailWord_495128) baseStart_495128 baseEnd_495128 := by
    simpa [prefixWord, tailWord_495128, baseEnd_495128] using wordTrace_append hprefix tailTrace_495128
  have hstable : (prefixWord ++ tailWord_495128).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_495128).length < 2 ^ (prefixWord ++ tailWord_495128).sum := by decide
  have hdescent : baseEnd_495128 < baseStart_495128 := by decide
  rcases family_descends (prefixWord ++ tailWord_495128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_495132 : List Nat := [2, 2, 3, 1, 2, 1, 3, 6]
def baseStart_495132 : Nat := 118140960795 + 495132 * 2 ^ 59
def prefixEnd_495132 : Nat := 4983230072969 + 3 ^ 40 * 495132 * 2
def baseEnd_495132 : Nat := 75330578791722082214203

theorem tailTrace_495132 : CollatzResearch.WordTrace tailWord_495132 prefixEnd_495132 75330578791722082214203 := by
  unfold tailWord_495132
  simp only [CollatzResearch.WordTrace]
  refine ⟨9029473821114400329199825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12039298428152533772266433 9029473821114400329199825)
  ·
    refine ⟨6772105365835800246899869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9029473821114400329199825 6772105365835800246899869)
    ·
      refine ⟨2539539512188425092587451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6772105365835800246899869 2539539512188425092587451)
      ·
        refine ⟨3809309268282637638881177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2539539512188425092587451 3809309268282637638881177)
        ·
          refine ⟨2856981951211978229160883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3809309268282637638881177 2856981951211978229160883)
          ·
            refine ⟨4285472926817967343741325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2856981951211978229160883 4285472926817967343741325)
            ·
              refine ⟨1607052347556737753902997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4285472926817967343741325 1607052347556737753902997)
              ·
                refine ⟨75330578791722082214203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1607052347556737753902997 75330578791722082214203)
                ·
                  rfl

theorem cell20_495132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 3, 6].length) (baseStart_495132 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_495132 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_495132 prefixEnd_495132 := by exact prefixLift 495132
  have htrace : WordTrace (prefixWord ++ tailWord_495132) baseStart_495132 baseEnd_495132 := by
    simpa [prefixWord, tailWord_495132, baseEnd_495132] using wordTrace_append hprefix tailTrace_495132
  have hstable : (prefixWord ++ tailWord_495132).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_495132).length < 2 ^ (prefixWord ++ tailWord_495132).sum := by decide
  have hdescent : baseEnd_495132 < baseStart_495132 := by decide
  rcases family_descends (prefixWord ++ tailWord_495132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_495159 : List Nat := [1, 1, 3, 1, 2, 5, 3, 2, 2]
def baseStart_495159 : Nat := 118140960795 + 495159 * 2 ^ 59
def prefixEnd_495159 : Nat := 4983230072969 + 3 ^ 40 * 495159 * 2
def baseEnd_495159 : Nat := 226004059910874152742499

theorem tailTrace_495159 : CollatzResearch.WordTrace tailWord_495159 prefixEnd_495159 226004059910874152742499 := by
  unfold tailWord_495159
  simp only [CollatzResearch.WordTrace]
  refine ⟨18059932413130984269632531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12039954942087322846421687 18059932413130984269632531)
  ·
    refine ⟨27089898619696476404448797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18059932413130984269632531 27089898619696476404448797)
    ·
      refine ⟨10158711982386178651668299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27089898619696476404448797 10158711982386178651668299)
      ·
        refine ⟨15238067973579267977502449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10158711982386178651668299 15238067973579267977502449)
        ·
          refine ⟨11428550980184450983126837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15238067973579267977502449 11428550980184450983126837)
          ·
            refine ⟨1071426654392292279668141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 11428550980184450983126837 1071426654392292279668141)
            ·
              refine ⟨401784995397109604875553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1071426654392292279668141 401784995397109604875553)
              ·
                refine ⟨301338746547832203656665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 401784995397109604875553 301338746547832203656665)
                ·
                  refine ⟨226004059910874152742499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 301338746547832203656665 226004059910874152742499)
                  ·
                    rfl

theorem cell20_495159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 5, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 5, 3, 2, 2].length) (baseStart_495159 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_495159 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_495159 prefixEnd_495159 := by exact prefixLift 495159
  have htrace : WordTrace (prefixWord ++ tailWord_495159) baseStart_495159 baseEnd_495159 := by
    simpa [prefixWord, tailWord_495159, baseEnd_495159] using wordTrace_append hprefix tailTrace_495159
  have hstable : (prefixWord ++ tailWord_495159).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_495159).length < 2 ^ (prefixWord ++ tailWord_495159).sum := by decide
  have hdescent : baseEnd_495159 < baseStart_495159 := by decide
  rcases family_descends (prefixWord ++ tailWord_495159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_495184 : List Nat := [2, 1, 1, 1, 1, 3, 4, 1, 6]
def baseStart_495184 : Nat := 118140960795 + 495184 * 2 ^ 59
def prefixEnd_495184 : Nat := 4983230072969 + 3 ^ 40 * 495184 * 2
def baseEnd_495184 : Nat := 226015470592085176909063

theorem tailTrace_495184 : CollatzResearch.WordTrace tailWord_495184 prefixEnd_495184 226015470592085176909063 := by
  unfold tailWord_495184
  simp only [CollatzResearch.WordTrace]
  refine ⟨9030422119020206769646303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12040562825360275692861737 9030422119020206769646303)
  ·
    refine ⟨13545633178530310154469455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9030422119020206769646303 13545633178530310154469455)
    ·
      refine ⟨20318449767795465231704183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13545633178530310154469455 20318449767795465231704183)
      ·
        refine ⟨30477674651693197847556275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20318449767795465231704183 30477674651693197847556275)
        ·
          refine ⟨45716511977539796771334413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30477674651693197847556275 45716511977539796771334413)
          ·
            refine ⟨17143691991577423789250405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45716511977539796771334413 17143691991577423789250405)
            ·
              refine ⟨3214442248420766960484451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17143691991577423789250405 3214442248420766960484451)
              ·
                refine ⟨4821663372631150440726677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3214442248420766960484451 4821663372631150440726677)
                ·
                  refine ⟨226015470592085176909063, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4821663372631150440726677 226015470592085176909063)
                  ·
                    rfl

theorem cell20_495184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 4, 1, 6].length) (baseStart_495184 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_495184 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_495184 prefixEnd_495184 := by exact prefixLift 495184
  have htrace : WordTrace (prefixWord ++ tailWord_495184) baseStart_495184 baseEnd_495184 := by
    simpa [prefixWord, tailWord_495184, baseEnd_495184] using wordTrace_append hprefix tailTrace_495184
  have hstable : (prefixWord ++ tailWord_495184).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_495184).length < 2 ^ (prefixWord ++ tailWord_495184).sum := by decide
  have hdescent : baseEnd_495184 < baseStart_495184 := by decide
  rcases family_descends (prefixWord ++ tailWord_495184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_495208 : List Nat := [2, 1, 4, 3, 1, 9]
def baseStart_495208 : Nat := 118140960795 + 495208 * 2 ^ 59
def prefixEnd_495208 : Nat := 4983230072969 + 3 ^ 40 * 495208 * 2
def baseEnd_495208 : Nat := 8371349068372139263295

theorem tailTrace_495208 : CollatzResearch.WordTrace tailWord_495208 prefixEnd_495208 8371349068372139263295 := by
  unfold tailWord_495208
  simp only [CollatzResearch.WordTrace]
  refine ⟨9030859794976732819083139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12041146393302310425444185 9030859794976732819083139)
  ·
    refine ⟨13546289692465099228624709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9030859794976732819083139 13546289692465099228624709)
    ·
      refine ⟨2539929317337206105367133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13546289692465099228624709 2539929317337206105367133)
      ·
        refine ⟨952473494001452289512675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2539929317337206105367133 952473494001452289512675)
        ·
          refine ⟨1428710241002178434269013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 952473494001452289512675 1428710241002178434269013)
          ·
            refine ⟨8371349068372139263295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 1428710241002178434269013 8371349068372139263295)
            ·
              rfl

theorem cell20_495208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 9].length) (baseStart_495208 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_495208 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_495208 prefixEnd_495208 := by exact prefixLift 495208
  have htrace : WordTrace (prefixWord ++ tailWord_495208) baseStart_495208 baseEnd_495208 := by
    simpa [prefixWord, tailWord_495208, baseEnd_495208] using wordTrace_append hprefix tailTrace_495208
  have hstable : (prefixWord ++ tailWord_495208).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_495208).length < 2 ^ (prefixWord ++ tailWord_495208).sum := by decide
  have hdescent : baseEnd_495208 < baseStart_495208 := by decide
  rcases family_descends (prefixWord ++ tailWord_495208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_495239 : List Nat := [1, 1, 4, 2, 1, 4, 1, 2, 4]
def baseStart_495239 : Nat := 118140960795 + 495239 * 2 ^ 59
def prefixEnd_495239 : Nat := 4983230072969 + 3 ^ 40 * 495239 * 2
def baseEnd_495239 : Nat := 226040574090749430075505

theorem tailTrace_495239 : CollatzResearch.WordTrace tailWord_495239 prefixEnd_495239 226040574090749430075505 := by
  unfold tailWord_495239
  simp only [CollatzResearch.WordTrace]
  refine ⟨18062850252841157932544771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12041900168560771955029847 18062850252841157932544771)
  ·
    refine ⟨27094275379261736898817157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18062850252841157932544771 27094275379261736898817157)
    ·
      refine ⟨5080176633611575668528217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27094275379261736898817157 5080176633611575668528217)
      ·
        refine ⟨3810132475208681751396163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5080176633611575668528217 3810132475208681751396163)
        ·
          refine ⟨5715198712813022627094245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3810132475208681751396163 5715198712813022627094245)
          ·
            refine ⟨1071599758652441742580171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5715198712813022627094245 1071599758652441742580171)
            ·
              refine ⟨1607399637978662613870257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1071599758652441742580171 1607399637978662613870257)
              ·
                refine ⟨1205549728483996960402693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1607399637978662613870257 1205549728483996960402693)
                ·
                  refine ⟨226040574090749430075505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1205549728483996960402693 226040574090749430075505)
                  ·
                    rfl

theorem cell20_495239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 4, 1, 2, 4].length) (baseStart_495239 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_495239 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_495239 prefixEnd_495239 := by exact prefixLift 495239
  have htrace : WordTrace (prefixWord ++ tailWord_495239) baseStart_495239 baseEnd_495239 := by
    simpa [prefixWord, tailWord_495239, baseEnd_495239] using wordTrace_append hprefix tailTrace_495239
  have hstable : (prefixWord ++ tailWord_495239).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_495239).length < 2 ^ (prefixWord ++ tailWord_495239).sum := by decide
  have hdescent : baseEnd_495239 < baseStart_495239 := by decide
  rcases family_descends (prefixWord ++ tailWord_495239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_495252 : List Nat := [2, 4, 2, 2, 2, 1, 2, 3, 2]
def baseStart_495252 : Nat := 118140960795 + 495252 * 2 ^ 59
def prefixEnd_495252 : Nat := 4983230072969 + 3 ^ 40 * 495252 * 2
def baseEnd_495252 : Nat := 226046507644979162642119

theorem tailTrace_495252 : CollatzResearch.WordTrace tailWord_495252 prefixEnd_495252 226046507644979162642119 := by
  unfold tailWord_495252
  simp only [CollatzResearch.WordTrace]
  refine ⟨9031662200897030576384005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12042216267862707435178673 9031662200897030576384005)
  ·
    refine ⟨1693436662668193233072001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9031662200897030576384005 1693436662668193233072001)
    ·
      refine ⟨1270077497001144924804001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1693436662668193233072001 1270077497001144924804001)
      ·
        refine ⟨952558122750858693603001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1270077497001144924804001 952558122750858693603001)
        ·
          refine ⟨714418592063144020202251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 952558122750858693603001 714418592063144020202251)
          ·
            refine ⟨1071627888094716030303377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 714418592063144020202251 1071627888094716030303377)
            ·
              refine ⟨803720916071037022727533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1071627888094716030303377 803720916071037022727533)
              ·
                refine ⟨301395343526638883522825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 803720916071037022727533 301395343526638883522825)
                ·
                  refine ⟨226046507644979162642119, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 301395343526638883522825 226046507644979162642119)
                  ·
                    rfl

theorem cell20_495252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 1, 2, 3, 2].length) (baseStart_495252 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_495252 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_495252 prefixEnd_495252 := by exact prefixLift 495252
  have htrace : WordTrace (prefixWord ++ tailWord_495252) baseStart_495252 baseEnd_495252 := by
    simpa [prefixWord, tailWord_495252, baseEnd_495252] using wordTrace_append hprefix tailTrace_495252
  have hstable : (prefixWord ++ tailWord_495252).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_495252).length < 2 ^ (prefixWord ++ tailWord_495252).sum := by decide
  have hdescent : baseEnd_495252 < baseStart_495252 := by decide
  rcases family_descends (prefixWord ++ tailWord_495252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_495256 : List Nat := [2, 1, 2, 4, 1, 2, 1, 5, 2]
def baseStart_495256 : Nat := 118140960795 + 495256 * 2 ^ 59
def prefixEnd_495256 : Nat := 4983230072969 + 3 ^ 40 * 495256 * 2
def baseEnd_495256 : Nat := 226048333353972926508769

theorem tailTrace_495256 : CollatzResearch.WordTrace tailWord_495256 prefixEnd_495256 226048333353972926508769 := by
  unfold tailWord_495256
  simp only [CollatzResearch.WordTrace]
  refine ⟨9031735146889784917956811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12042313529186379890609081 9031735146889784917956811)
  ·
    refine ⟨13547602720334677376935217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9031735146889784917956811 13547602720334677376935217)
    ·
      refine ⟨10160702040251008032701413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13547602720334677376935217 10160702040251008032701413)
      ·
        refine ⟨1905131632547064006131515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10160702040251008032701413 1905131632547064006131515)
        ·
          refine ⟨2857697448820596009197273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1905131632547064006131515 2857697448820596009197273)
          ·
            refine ⟨2143273086615447006897955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2857697448820596009197273 2143273086615447006897955)
            ·
              refine ⟨3214909629923170510346933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2143273086615447006897955 3214909629923170510346933)
              ·
                refine ⟨301397777805297235345025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3214909629923170510346933 301397777805297235345025)
                ·
                  refine ⟨226048333353972926508769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 301397777805297235345025 226048333353972926508769)
                  ·
                    rfl

theorem cell20_495256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 1, 5, 2].length) (baseStart_495256 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_495256 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_495256 prefixEnd_495256 := by exact prefixLift 495256
  have htrace : WordTrace (prefixWord ++ tailWord_495256) baseStart_495256 baseEnd_495256 := by
    simpa [prefixWord, tailWord_495256, baseEnd_495256] using wordTrace_append hprefix tailTrace_495256
  have hstable : (prefixWord ++ tailWord_495256).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_495256).length < 2 ^ (prefixWord ++ tailWord_495256).sum := by decide
  have hdescent : baseEnd_495256 < baseStart_495256 := by decide
  rcases family_descends (prefixWord ++ tailWord_495256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_495263 : List Nat := [1, 1, 2, 7, 1, 1, 7]
def baseStart_495263 : Nat := 118140960795 + 495263 * 2 ^ 59
def prefixEnd_495263 : Nat := 4983230072969 + 3 ^ 40 * 495263 * 2
def baseEnd_495263 : Nat := 25116836482745779252823

theorem tailTrace_495263 : CollatzResearch.WordTrace tailWord_495263 prefixEnd_495263 25116836482745779252823 := by
  unfold tailWord_495263
  simp only [CollatzResearch.WordTrace]
  refine ⟨18063725604754210031418443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12042483736502806687612295 18063725604754210031418443)
  ·
    refine ⟨27095588407131315047127665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18063725604754210031418443 27095588407131315047127665)
    ·
      refine ⟨20321691305348486285345749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27095588407131315047127665 20321691305348486285345749)
      ·
        refine ⟨476289639969105147312791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 20321691305348486285345749 476289639969105147312791)
        ·
          refine ⟨714434459953657720969187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 476289639969105147312791 714434459953657720969187)
          ·
            refine ⟨1071651689930486581453781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 714434459953657720969187 1071651689930486581453781)
            ·
              refine ⟨25116836482745779252823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1071651689930486581453781 25116836482745779252823)
              ·
                rfl

theorem cell20_495263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 1, 7].length) (baseStart_495263 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_495263 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_495263 prefixEnd_495263 := by exact prefixLift 495263
  have htrace : WordTrace (prefixWord ++ tailWord_495263) baseStart_495263 baseEnd_495263 := by
    simpa [prefixWord, tailWord_495263, baseEnd_495263] using wordTrace_append hprefix tailTrace_495263
  have hstable : (prefixWord ++ tailWord_495263).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_495263).length < 2 ^ (prefixWord ++ tailWord_495263).sum := by decide
  have hdescent : baseEnd_495263 < baseStart_495263 := by decide
  rcases family_descends (prefixWord ++ tailWord_495263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_495267 : List Nat := [1, 1, 1, 4, 1, 1, 11]
def baseStart_495267 : Nat := 118140960795 + 495267 * 2 ^ 59
def prefixEnd_495267 : Nat := 4983230072969 + 3 ^ 40 * 495267 * 2
def baseEnd_495267 : Nat := 25117039339300641904673

theorem tailTrace_495267 : CollatzResearch.WordTrace tailWord_495267 prefixEnd_495267 25117039339300641904673 := by
  unfold tailWord_495267
  simp only [CollatzResearch.WordTrace]
  refine ⟨18063871496739718714564055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12042580997826479143042703 18063871496739718714564055)
  ·
    refine ⟨27095807245109578071846083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18063871496739718714564055 27095807245109578071846083)
    ·
      refine ⟨40643710867664367107769125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27095807245109578071846083 40643710867664367107769125)
      ·
        refine ⟨7620695787687068832706711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 40643710867664367107769125 7620695787687068832706711)
        ·
          refine ⟨11431043681530603249060067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7620695787687068832706711 11431043681530603249060067)
          ·
            refine ⟨17146565522295904873590101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11431043681530603249060067 17146565522295904873590101)
            ·
              refine ⟨25117039339300641904673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 17146565522295904873590101 25117039339300641904673)
              ·
                rfl

theorem cell20_495267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 11].length) (baseStart_495267 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_495267 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_495267 prefixEnd_495267 := by exact prefixLift 495267
  have htrace : WordTrace (prefixWord ++ tailWord_495267) baseStart_495267 baseEnd_495267 := by
    simpa [prefixWord, tailWord_495267, baseEnd_495267] using wordTrace_append hprefix tailTrace_495267
  have hstable : (prefixWord ++ tailWord_495267).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_495267).length < 2 ^ (prefixWord ++ tailWord_495267).sum := by decide
  have hdescent : baseEnd_495267 < baseStart_495267 := by decide
  rcases family_descends (prefixWord ++ tailWord_495267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_495287 : List Nat := [1, 1, 3, 1, 5, 2, 3, 1, 3]
def baseStart_495287 : Nat := 118140960795 + 495287 * 2 ^ 59
def prefixEnd_495287 : Nat := 4983230072969 + 3 ^ 40 * 495287 * 2
def baseEnd_495287 : Nat := 226062482598674596475309

theorem tailTrace_495287 : CollatzResearch.WordTrace tailWord_495287 prefixEnd_495287 226062482598674596475309 := by
  unfold tailWord_495287
  simp only [CollatzResearch.WordTrace]
  refine ⟨18064600956667262130292115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12043067304444841420194743 18064600956667262130292115)
  ·
    refine ⟨27096901435000893195438173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18064600956667262130292115 27096901435000893195438173)
    ·
      refine ⟨10161338038125334948289315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27096901435000893195438173 10161338038125334948289315)
      ·
        refine ⟨15242007057188002422433973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10161338038125334948289315 15242007057188002422433973)
        ·
          refine ⟨1428938161611375227103185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 15242007057188002422433973 1428938161611375227103185)
          ·
            refine ⟨1071703621208531420327389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1428938161611375227103185 1071703621208531420327389)
            ·
              refine ⟨401888857953199282622771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1071703621208531420327389 401888857953199282622771)
              ·
                refine ⟨602833286929798923934157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 401888857953199282622771 602833286929798923934157)
                ·
                  refine ⟨226062482598674596475309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 602833286929798923934157 226062482598674596475309)
                  ·
                    rfl

theorem cell20_495287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 2, 3, 1, 3].length) (baseStart_495287 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_495287 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_495287 prefixEnd_495287 := by exact prefixLift 495287
  have htrace : WordTrace (prefixWord ++ tailWord_495287) baseStart_495287 baseEnd_495287 := by
    simpa [prefixWord, tailWord_495287, baseEnd_495287] using wordTrace_append hprefix tailTrace_495287
  have hstable : (prefixWord ++ tailWord_495287).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_495287).length < 2 ^ (prefixWord ++ tailWord_495287).sum := by decide
  have hdescent : baseEnd_495287 < baseStart_495287 := by decide
  rcases family_descends (prefixWord ++ tailWord_495287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_495291 : List Nat := [1, 1, 1, 1, 1, 2, 3, 7, 3]
def baseStart_495291 : Nat := 118140960795 + 495291 * 2 ^ 59
def prefixEnd_495291 : Nat := 4983230072969 + 3 ^ 40 * 495291 * 2
def baseEnd_495291 : Nat := 226064308307668360341959

theorem tailTrace_495291 : CollatzResearch.WordTrace tailWord_495291 prefixEnd_495291 226064308307668360341959 := by
  unfold tailWord_495291
  simp only [CollatzResearch.WordTrace]
  refine ⟨18064746848652770813437727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12043164565768513875625151 18064746848652770813437727)
  ·
    refine ⟨27097120272979156220156591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18064746848652770813437727 27097120272979156220156591)
    ·
      refine ⟨40645680409468734330234887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27097120272979156220156591 40645680409468734330234887)
      ·
        refine ⟨60968520614203101495352331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40645680409468734330234887 60968520614203101495352331)
        ·
          refine ⟨91452780921304652243028497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60968520614203101495352331 91452780921304652243028497)
          ·
            refine ⟨68589585690978489182271373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 91452780921304652243028497 68589585690978489182271373)
            ·
              refine ⟨25721094634116933443351765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 68589585690978489182271373 25721094634116933443351765)
              ·
                refine ⟨602838155487115627578557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 25721094634116933443351765 602838155487115627578557)
                ·
                  refine ⟨226064308307668360341959, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 602838155487115627578557 226064308307668360341959)
                  ·
                    rfl

theorem cell20_495291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 7, 3].length) (baseStart_495291 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_495291 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_495291 prefixEnd_495291 := by exact prefixLift 495291
  have htrace : WordTrace (prefixWord ++ tailWord_495291) baseStart_495291 baseEnd_495291 := by
    simpa [prefixWord, tailWord_495291, baseEnd_495291] using wordTrace_append hprefix tailTrace_495291
  have hstable : (prefixWord ++ tailWord_495291).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_495291).length < 2 ^ (prefixWord ++ tailWord_495291).sum := by decide
  have hdescent : baseEnd_495291 < baseStart_495291 := by decide
  rcases family_descends (prefixWord ++ tailWord_495291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_495322 : List Nat := [3, 1, 1, 2, 2, 5, 6]
def baseStart_495322 : Nat := 118140960795 + 495322 * 2 ^ 59
def prefixEnd_495322 : Nat := 4983230072969 + 3 ^ 40 * 495322 * 2
def baseEnd_495322 : Nat := 25119828616930003367611

theorem tailTrace_495322 : CollatzResearch.WordTrace tailWord_495322 prefixEnd_495322 25119828616930003367611 := by
  unfold tailWord_495322
  simp only [CollatzResearch.WordTrace]
  refine ⟨4516469377885115776954055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12043918341026975405210813 4516469377885115776954055)
  ·
    refine ⟨6774704066827673665431083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4516469377885115776954055 6774704066827673665431083)
    ·
      refine ⟨10162056100241510498146625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6774704066827673665431083 10162056100241510498146625)
      ·
        refine ⟨7621542075181132873609969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10162056100241510498146625 7621542075181132873609969)
        ·
          refine ⟨5716156556385849655207477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7621542075181132873609969 5716156556385849655207477)
          ·
            refine ⟨535889677161173405175701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 5716156556385849655207477 535889677161173405175701)
            ·
              refine ⟨25119828616930003367611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 535889677161173405175701 25119828616930003367611)
              ·
                rfl

theorem cell20_495322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 5, 6].length) (baseStart_495322 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_495322 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_495322 prefixEnd_495322 := by exact prefixLift 495322
  have htrace : WordTrace (prefixWord ++ tailWord_495322) baseStart_495322 baseEnd_495322 := by
    simpa [prefixWord, tailWord_495322, baseEnd_495322] using wordTrace_append hprefix tailTrace_495322
  have hstable : (prefixWord ++ tailWord_495322).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_495322).length < 2 ^ (prefixWord ++ tailWord_495322).sum := by decide
  have hdescent : baseEnd_495322 < baseStart_495322 := by decide
  rcases family_descends (prefixWord ++ tailWord_495322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_495346 : List Nat := [3, 2, 1, 3, 1, 1, 3, 3, 3]
def baseStart_495346 : Nat := 118140960795 + 495346 * 2 ^ 59
def prefixEnd_495346 : Nat := 4983230072969 + 3 ^ 40 * 495346 * 2
def baseEnd_495346 : Nat := 226089411806332613508401

theorem tailTrace_495346 : CollatzResearch.WordTrace tailWord_495346 prefixEnd_495346 226089411806332613508401 := by
  unfold tailWord_495346
  simp only [CollatzResearch.WordTrace]
  refine ⟨4516688215863378801672473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12044501908969010137793261 4516688215863378801672473)
  ·
    refine ⟨3387516161897534101254355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4516688215863378801672473 3387516161897534101254355)
    ·
      refine ⟨5081274242846301151881533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3387516161897534101254355 5081274242846301151881533)
      ·
        refine ⟨1905477841067362931955575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5081274242846301151881533 1905477841067362931955575)
        ·
          refine ⟨2858216761601044397933363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1905477841067362931955575 2858216761601044397933363)
          ·
            refine ⟨4287325142401566596900045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2858216761601044397933363 4287325142401566596900045)
            ·
              refine ⟨1607746928400587473837517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4287325142401566596900045 1607746928400587473837517)
              ·
                refine ⟨602905098150220302689069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1607746928400587473837517 602905098150220302689069)
                ·
                  refine ⟨226089411806332613508401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 602905098150220302689069 226089411806332613508401)
                  ·
                    rfl

theorem cell20_495346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 3, 3, 3].length) (baseStart_495346 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_495346 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_495346 prefixEnd_495346 := by exact prefixLift 495346
  have htrace : WordTrace (prefixWord ++ tailWord_495346) baseStart_495346 baseEnd_495346 := by
    simpa [prefixWord, tailWord_495346, baseEnd_495346] using wordTrace_append hprefix tailTrace_495346
  have hstable : (prefixWord ++ tailWord_495346).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_495346).length < 2 ^ (prefixWord ++ tailWord_495346).sum := by decide
  have hdescent : baseEnd_495346 < baseStart_495346 := by decide
  rcases family_descends (prefixWord ++ tailWord_495346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_495373 : List Nat := [1, 7, 2, 1, 1, 8]
def baseStart_495373 : Nat := 118140960795 + 495373 * 2 ^ 59
def prefixEnd_495373 : Nat := 4983230072969 + 3 ^ 40 * 495373 * 2
def baseEnd_495373 : Nat := 8374138346001500726233

theorem tailTrace_495373 : CollatzResearch.WordTrace tailWord_495373 prefixEnd_495373 8374138346001500726233 := by
  unfold tailWord_495373
  simp only [CollatzResearch.WordTrace]
  refine ⟨18067737634355698817922773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12045158422903799211948515 18067737634355698817922773)
  ·
    refine ⟨423462600805211691045065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 18067737634355698817922773 423462600805211691045065)
    ·
      refine ⟨317596950603908768283799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 423462600805211691045065 317596950603908768283799)
      ·
        refine ⟨476395425905863152425699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 317596950603908768283799 476395425905863152425699)
        ·
          refine ⟨714593138858794728638549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 476395425905863152425699 714593138858794728638549)
          ·
            refine ⟨8374138346001500726233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 714593138858794728638549 8374138346001500726233)
            ·
              rfl

theorem cell20_495373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 8].length) (baseStart_495373 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_495373 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_495373 prefixEnd_495373 := by exact prefixLift 495373
  have htrace : WordTrace (prefixWord ++ tailWord_495373) baseStart_495373 baseEnd_495373 := by
    simpa [prefixWord, tailWord_495373, baseEnd_495373] using wordTrace_append hprefix tailTrace_495373
  have hstable : (prefixWord ++ tailWord_495373).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_495373).length < 2 ^ (prefixWord ++ tailWord_495373).sum := by decide
  have hdescent : baseEnd_495373 < baseStart_495373 := by decide
  rcases family_descends (prefixWord ++ tailWord_495373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_495381 : List Nat := [1, 3, 2, 1, 2, 11]
def baseStart_495381 : Nat := 118140960795 + 495381 * 2 ^ 59
def prefixEnd_495381 : Nat := 4983230072969 + 3 ^ 40 * 495381 * 2
def baseEnd_495381 : Nat := 8374273583704742494133

theorem tailTrace_495381 : CollatzResearch.WordTrace tailWord_495381 prefixEnd_495381 8374273583704742494133 := by
  unfold tailWord_495381
  simp only [CollatzResearch.WordTrace]
  refine ⟨18068029418326716184213997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12045352945551144122809331 18068029418326716184213997)
  ·
    refine ⟨6775511031872518569080249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18068029418326716184213997 6775511031872518569080249)
    ·
      refine ⟨5081633273904388926810187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6775511031872518569080249 5081633273904388926810187)
      ·
        refine ⟨7622449910856583390215281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5081633273904388926810187 7622449910856583390215281)
        ·
          refine ⟨5716837433142437542661461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7622449910856583390215281 5716837433142437542661461)
          ·
            refine ⟨8374273583704742494133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 5716837433142437542661461 8374273583704742494133)
            ·
              rfl

theorem cell20_495381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 11].length) (baseStart_495381 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_495381 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_495381 prefixEnd_495381 := by exact prefixLift 495381
  have htrace : WordTrace (prefixWord ++ tailWord_495381) baseStart_495381 baseEnd_495381 := by
    simpa [prefixWord, tailWord_495381, baseEnd_495381] using wordTrace_append hprefix tailTrace_495381
  have hstable : (prefixWord ++ tailWord_495381).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_495381).length < 2 ^ (prefixWord ++ tailWord_495381).sum := by decide
  have hdescent : baseEnd_495381 < baseStart_495381 := by decide
  rcases family_descends (prefixWord ++ tailWord_495381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_495390 : List Nat := [4, 3, 2, 2, 2, 1, 1, 5]
def baseStart_495390 : Nat := 118140960795 + 495390 * 2 ^ 59
def prefixEnd_495390 : Nat := 4983230072969 + 3 ^ 40 * 495390 * 2
def baseEnd_495390 : Nat := 75369831535088005347185

theorem tailTrace_495390 : CollatzResearch.WordTrace tailWord_495390 prefixEnd_495390 75369831535088005347185 := by
  unfold tailWord_495390
  simp only [CollatzResearch.WordTrace]
  refine ⟨2258544709411763840161453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12045571783529407147527749 2258544709411763840161453)
  ·
    refine ⟨846954266029411440060545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2258544709411763840161453 846954266029411440060545)
    ·
      refine ⟨635215699522058580045409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 846954266029411440060545 635215699522058580045409)
      ·
        refine ⟨476411774641543935034057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 635215699522058580045409 476411774641543935034057)
        ·
          refine ⟨357308830981157951275543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 476411774641543935034057 357308830981157951275543)
          ·
            refine ⟨535963246471736926913315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 357308830981157951275543 535963246471736926913315)
            ·
              refine ⟨803944869707605390369973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 535963246471736926913315 803944869707605390369973)
              ·
                refine ⟨75369831535088005347185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 803944869707605390369973 75369831535088005347185)
                ·
                  rfl

theorem cell20_495390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 2, 1, 1, 5].length) (baseStart_495390 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_495390 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_495390 prefixEnd_495390 := by exact prefixLift 495390
  have htrace : WordTrace (prefixWord ++ tailWord_495390) baseStart_495390 baseEnd_495390 := by
    simpa [prefixWord, tailWord_495390, baseEnd_495390] using wordTrace_append hprefix tailTrace_495390
  have hstable : (prefixWord ++ tailWord_495390).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_495390).length < 2 ^ (prefixWord ++ tailWord_495390).sum := by decide
  have hdescent : baseEnd_495390 < baseStart_495390 := by decide
  rcases family_descends (prefixWord ++ tailWord_495390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_495436 : List Nat := [2, 2, 1, 3, 4, 1, 7]
def baseStart_495436 : Nat := 118140960795 + 495436 * 2 ^ 59
def prefixEnd_495436 : Nat := 4983230072969 + 3 ^ 40 * 495436 * 2
def baseEnd_495436 : Nat := 25125610028743588945337

theorem tailTrace_495436 : CollatzResearch.WordTrace tailWord_495436 prefixEnd_495436 25125610028743588945337 := by
  unfold tailWord_495436
  simp only [CollatzResearch.WordTrace]
  refine ⟨9035017716563730288733081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12046690288751640384977441 9035017716563730288733081)
  ·
    refine ⟨6776263287422797716549811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9035017716563730288733081 6776263287422797716549811)
    ·
      refine ⟨10164394931134196574824717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6776263287422797716549811 10164394931134196574824717)
      ·
        refine ⟨3811648099175323715559269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10164394931134196574824717 3811648099175323715559269)
        ·
          refine ⟨714684018595373196667363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3811648099175323715559269 714684018595373196667363)
          ·
            refine ⟨1072026027893059795001045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 714684018595373196667363 1072026027893059795001045)
            ·
              refine ⟨25125610028743588945337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1072026027893059795001045 25125610028743588945337)
              ·
                rfl

theorem cell20_495436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 1, 7].length) (baseStart_495436 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_495436 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_495436 prefixEnd_495436 := by exact prefixLift 495436
  have htrace : WordTrace (prefixWord ++ tailWord_495436) baseStart_495436 baseEnd_495436 := by
    simpa [prefixWord, tailWord_495436, baseEnd_495436] using wordTrace_append hprefix tailTrace_495436
  have hstable : (prefixWord ++ tailWord_495436).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_495436).length < 2 ^ (prefixWord ++ tailWord_495436).sum := by decide
  have hdescent : baseEnd_495436 < baseStart_495436 := by decide
  rcases family_descends (prefixWord ++ tailWord_495436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_495457 : List Nat := [1, 2, 3, 1, 1, 1, 4, 7]
def baseStart_495457 : Nat := 118140960795 + 495457 * 2 ^ 59
def prefixEnd_495457 : Nat := 4983230072969 + 3 ^ 40 * 495457 * 2
def baseEnd_495457 : Nat := 75380025076969853602649

theorem tailTrace_495457 : CollatzResearch.WordTrace tailWord_495457 prefixEnd_495457 75380025076969853602649 := by
  unfold tailWord_495457
  simp only [CollatzResearch.WordTrace]
  refine ⟨18070801366051381163980625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12047200910700920775987083 18070801366051381163980625)
  ·
    refine ⟨13553101024538535872985469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18070801366051381163980625 13553101024538535872985469)
    ·
      refine ⟨5082412884201950952369551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13553101024538535872985469 5082412884201950952369551)
      ·
        refine ⟨7623619326302926428554327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5082412884201950952369551 7623619326302926428554327)
        ·
          refine ⟨11435428989454389642831491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7623619326302926428554327 11435428989454389642831491)
          ·
            refine ⟨17153143484181584464247237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11435428989454389642831491 17153143484181584464247237)
            ·
              refine ⟨3216214403284047087046357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17153143484181584464247237 3216214403284047087046357)
              ·
                refine ⟨75380025076969853602649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3216214403284047087046357 75380025076969853602649)
                ·
                  rfl

theorem cell20_495457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 4, 7].length) (baseStart_495457 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_495457 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_495457 prefixEnd_495457 := by exact prefixLift 495457
  have htrace : WordTrace (prefixWord ++ tailWord_495457) baseStart_495457 baseEnd_495457 := by
    simpa [prefixWord, tailWord_495457, baseEnd_495457] using wordTrace_append hprefix tailTrace_495457
  have hstable : (prefixWord ++ tailWord_495457).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_495457).length < 2 ^ (prefixWord ++ tailWord_495457).sum := by decide
  have hdescent : baseEnd_495457 < baseStart_495457 := by decide
  rcases family_descends (prefixWord ++ tailWord_495457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_495470 : List Nat := [4, 1, 2, 3, 1, 3, 2, 4]
def baseStart_495470 : Nat := 118140960795 + 495470 * 2 ^ 59
def prefixEnd_495470 : Nat := 4983230072969 + 3 ^ 40 * 495470 * 2
def baseEnd_495470 : Nat := 75382002928379764458187

theorem tailTrace_495470 : CollatzResearch.WordTrace tailWord_495470 prefixEnd_495470 75382002928379764458187 := by
  unfold tailWord_495470
  simp only [CollatzResearch.WordTrace]
  refine ⟨2258909439375535548025483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12047517010002856256135909 2258909439375535548025483)
  ·
    refine ⟨3388364159063303322038225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2258909439375535548025483 3388364159063303322038225)
    ·
      refine ⟨2541273119297477491528669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3388364159063303322038225 2541273119297477491528669)
      ·
        refine ⟨952977419736554059323251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2541273119297477491528669 952977419736554059323251)
        ·
          refine ⟨1429466129604831088984877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 952977419736554059323251 1429466129604831088984877)
          ·
            refine ⟨536049798601811658369329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1429466129604831088984877 536049798601811658369329)
            ·
              refine ⟨402037348951358743776997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 536049798601811658369329 402037348951358743776997)
              ·
                refine ⟨75382002928379764458187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 402037348951358743776997 75382002928379764458187)
                ·
                  rfl

theorem cell20_495470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 3, 2, 4].length) (baseStart_495470 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_495470 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_495470 prefixEnd_495470 := by exact prefixLift 495470
  have htrace : WordTrace (prefixWord ++ tailWord_495470) baseStart_495470 baseEnd_495470 := by
    simpa [prefixWord, tailWord_495470, baseEnd_495470] using wordTrace_append hprefix tailTrace_495470
  have hstable : (prefixWord ++ tailWord_495470).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_495470).length < 2 ^ (prefixWord ++ tailWord_495470).sum := by decide
  have hdescent : baseEnd_495470 < baseStart_495470 := by decide
  rcases family_descends (prefixWord ++ tailWord_495470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_495505 : List Nat := [1, 2, 2, 1, 1, 1, 4, 6, 2]
def baseStart_495505 : Nat := 118140960795 + 495505 * 2 ^ 59
def prefixEnd_495505 : Nat := 4983230072969 + 3 ^ 40 * 495505 * 2
def baseEnd_495505 : Nat := 226161983738834727207751

theorem tailTrace_495505 : CollatzResearch.WordTrace tailWord_495505 prefixEnd_495505 226161983738834727207751 := by
  unfold tailWord_495505
  simp only [CollatzResearch.WordTrace]
  refine ⟨18072552069877485361727969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12048368046584990241151979 18072552069877485361727969)
  ·
    refine ⟨13554414052408114021295977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18072552069877485361727969 13554414052408114021295977)
    ·
      refine ⟨10165810539306085515971983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13554414052408114021295977 10165810539306085515971983)
      ·
        refine ⟨15248715808959128273957975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10165810539306085515971983 15248715808959128273957975)
        ·
          refine ⟨22873073713438692410936963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15248715808959128273957975 22873073713438692410936963)
          ·
            refine ⟨34309610570158038616405445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22873073713438692410936963 34309610570158038616405445)
            ·
              refine ⟨6433051981904632240576021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34309610570158038616405445 6433051981904632240576021)
              ·
                refine ⟨301549311651779636277001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 6433051981904632240576021 301549311651779636277001)
                ·
                  refine ⟨226161983738834727207751, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 301549311651779636277001 226161983738834727207751)
                  ·
                    rfl

theorem cell20_495505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 4, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 4, 6, 2].length) (baseStart_495505 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_495505 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_495505 prefixEnd_495505 := by exact prefixLift 495505
  have htrace : WordTrace (prefixWord ++ tailWord_495505) baseStart_495505 baseEnd_495505 := by
    simpa [prefixWord, tailWord_495505, baseEnd_495505] using wordTrace_append hprefix tailTrace_495505
  have hstable : (prefixWord ++ tailWord_495505).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_495505).length < 2 ^ (prefixWord ++ tailWord_495505).sum := by decide
  have hdescent : baseEnd_495505 < baseStart_495505 := by decide
  rcases family_descends (prefixWord ++ tailWord_495505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_495543 : List Nat := [1, 1, 3, 1, 3, 1, 1, 7, 2]
def baseStart_495543 : Nat := 118140960795 + 495543 * 2 ^ 59
def prefixEnd_495543 : Nat := 4983230072969 + 3 ^ 40 * 495543 * 2
def baseEnd_495543 : Nat := 226179327974275483940929

theorem tailTrace_495543 : CollatzResearch.WordTrace tailWord_495543 prefixEnd_495543 226179327974275483940929 := by
  unfold tailWord_495543
  simp only [CollatzResearch.WordTrace]
  refine ⟨18073938043739817851611283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12049292029159878567740855 18073938043739817851611283)
  ·
    refine ⟨27110907065609726777416925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18073938043739817851611283 27110907065609726777416925)
    ·
      refine ⟨10166590149603647541531347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27110907065609726777416925 10166590149603647541531347)
      ·
        refine ⟨15249885224405471312297021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10166590149603647541531347 15249885224405471312297021)
        ·
          refine ⟨5718706959152051742111383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15249885224405471312297021 5718706959152051742111383)
          ·
            refine ⟨8578060438728077613167075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5718706959152051742111383 8578060438728077613167075)
            ·
              refine ⟨12867090658092116419750613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8578060438728077613167075 12867090658092116419750613)
              ·
                refine ⟨301572437299033978587905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 12867090658092116419750613 301572437299033978587905)
                ·
                  refine ⟨226179327974275483940929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 301572437299033978587905 226179327974275483940929)
                  ·
                    rfl

theorem cell20_495543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 7, 2].length) (baseStart_495543 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_495543 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_495543 prefixEnd_495543 := by exact prefixLift 495543
  have htrace : WordTrace (prefixWord ++ tailWord_495543) baseStart_495543 baseEnd_495543 := by
    simpa [prefixWord, tailWord_495543, baseEnd_495543] using wordTrace_append hprefix tailTrace_495543
  have hstable : (prefixWord ++ tailWord_495543).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_495543).length < 2 ^ (prefixWord ++ tailWord_495543).sum := by decide
  have hdescent : baseEnd_495543 < baseStart_495543 := by decide
  rcases family_descends (prefixWord ++ tailWord_495543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_495560 : List Nat := [2, 1, 3, 1, 4, 2, 1, 4, 2]
def baseStart_495560 : Nat := 118140960795 + 495560 * 2 ^ 59
def prefixEnd_495560 : Nat := 4983230072969 + 3 ^ 40 * 495560 * 2
def baseEnd_495560 : Nat := 226187087237498980374193

theorem tailTrace_495560 : CollatzResearch.WordTrace tailWord_495560 prefixEnd_495560 226187087237498980374193 := by
  unfold tailWord_495560
  simp only [CollatzResearch.WordTrace]
  refine ⟨9037279042339114877490067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12049705389785486503320089 9037279042339114877490067)
  ·
    refine ⟨13555918563508672316235101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9037279042339114877490067 13555918563508672316235101)
    ·
      refine ⟨5083469461315752118588163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13555918563508672316235101 5083469461315752118588163)
      ·
        refine ⟨7625204191973628177882245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5083469461315752118588163 7625204191973628177882245)
        ·
          refine ⟨1429725785995055283352921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7625204191973628177882245 1429725785995055283352921)
          ·
            refine ⟨1072294339496291462514691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1429725785995055283352921 1072294339496291462514691)
            ·
              refine ⟨1608441509244437193772037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1072294339496291462514691 1608441509244437193772037)
              ·
                refine ⟨301582782983331973832257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1608441509244437193772037 301582782983331973832257)
                ·
                  refine ⟨226187087237498980374193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 301582782983331973832257 226187087237498980374193)
                  ·
                    rfl

theorem cell20_495560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 2, 1, 4, 2].length) (baseStart_495560 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_495560 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_495560 prefixEnd_495560 := by exact prefixLift 495560
  have htrace : WordTrace (prefixWord ++ tailWord_495560) baseStart_495560 baseEnd_495560 := by
    simpa [prefixWord, tailWord_495560, baseEnd_495560] using wordTrace_append hprefix tailTrace_495560
  have hstable : (prefixWord ++ tailWord_495560).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_495560).length < 2 ^ (prefixWord ++ tailWord_495560).sum := by decide
  have hdescent : baseEnd_495560 < baseStart_495560 := by decide
  rcases family_descends (prefixWord ++ tailWord_495560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_495588 : List Nat := [2, 3, 1, 1, 1, 1, 7, 4]
def baseStart_495588 : Nat := 118140960795 + 495588 * 2 ^ 59
def prefixEnd_495588 : Nat := 4983230072969 + 3 ^ 40 * 495588 * 2
def baseEnd_495588 : Nat := 75399955733485109146915

theorem tailTrace_495588 : CollatzResearch.WordTrace tailWord_495588 prefixEnd_495588 75399955733485109146915 := by
  unfold tailWord_495588
  simp only [CollatzResearch.WordTrace]
  refine ⟨9037789664288395268499709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12050386219051193691332945 9037789664288395268499709)
  ·
    refine ⟨3389171124108148225687391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9037789664288395268499709 3389171124108148225687391)
    ·
      refine ⟨5083756686162222338531087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3389171124108148225687391 5083756686162222338531087)
      ·
        refine ⟨7625635029243333507796631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5083756686162222338531087 7625635029243333507796631)
        ·
          refine ⟨11438452543865000261694947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7625635029243333507796631 11438452543865000261694947)
          ·
            refine ⟨17157678815797500392542421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11438452543865000261694947 17157678815797500392542421)
            ·
              refine ⟨402133097245253915450213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 17157678815797500392542421 402133097245253915450213)
              ·
                refine ⟨75399955733485109146915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 402133097245253915450213 75399955733485109146915)
                ·
                  rfl

theorem cell20_495588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 7, 4].length) (baseStart_495588 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_495588 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_495588 prefixEnd_495588 := by exact prefixLift 495588
  have htrace : WordTrace (prefixWord ++ tailWord_495588) baseStart_495588 baseEnd_495588 := by
    simpa [prefixWord, tailWord_495588, baseEnd_495588] using wordTrace_append hprefix tailTrace_495588
  have hstable : (prefixWord ++ tailWord_495588).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_495588).length < 2 ^ (prefixWord ++ tailWord_495588).sum := by decide
  have hdescent : baseEnd_495588 < baseStart_495588 := by decide
  rcases family_descends (prefixWord ++ tailWord_495588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_495598 : List Nat := [4, 1, 2, 1, 3, 1, 1, 5, 2]
def baseStart_495598 : Nat := 118140960795 + 495598 * 2 ^ 59
def prefixEnd_495598 : Nat := 4983230072969 + 3 ^ 40 * 495598 * 2
def baseEnd_495598 : Nat := 226204431472939737107371

theorem tailTrace_495598 : CollatzResearch.WordTrace tailWord_495598 prefixEnd_495598 226204431472939737107371 := by
  unfold tailWord_495598
  simp only [CollatzResearch.WordTrace]
  refine ⟨2259493007317570280607931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12050629372360374829908965 2259493007317570280607931)
  ·
    refine ⟨3389239510976355420911897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2259493007317570280607931 3389239510976355420911897)
    ·
      refine ⟨2541929633232266565683923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3389239510976355420911897 2541929633232266565683923)
      ·
        refine ⟨3812894449848399848525885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2541929633232266565683923 3812894449848399848525885)
        ·
          refine ⟨1429835418693149943197207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3812894449848399848525885 1429835418693149943197207)
          ·
            refine ⟨2144753128039724914795811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1429835418693149943197207 2144753128039724914795811)
            ·
              refine ⟨3217129692059587372193717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2144753128039724914795811 3217129692059587372193717)
              ·
                refine ⟨301605908630586316143161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3217129692059587372193717 301605908630586316143161)
                ·
                  refine ⟨226204431472939737107371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 301605908630586316143161 226204431472939737107371)
                  ·
                    rfl

theorem cell20_495598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 1, 5, 2].length) (baseStart_495598 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_495598 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_495598 prefixEnd_495598 := by exact prefixLift 495598
  have htrace : WordTrace (prefixWord ++ tailWord_495598) baseStart_495598 baseEnd_495598 := by
    simpa [prefixWord, tailWord_495598, baseEnd_495598] using wordTrace_append hprefix tailTrace_495598
  have hstable : (prefixWord ++ tailWord_495598).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_495598).length < 2 ^ (prefixWord ++ tailWord_495598).sum := by decide
  have hdescent : baseEnd_495598 < baseStart_495598 := by decide
  rcases family_descends (prefixWord ++ tailWord_495598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_495609 : List Nat := [1, 2, 1, 3, 1, 5, 7]
def baseStart_495609 : Nat := 118140960795 + 495609 * 2 ^ 59
def prefixEnd_495609 : Nat := 4983230072969 + 3 ^ 40 * 495609 * 2
def baseEnd_495609 : Nat := 25134383574741398637851

theorem tailTrace_495609 : CollatzResearch.WordTrace tailWord_495609 prefixEnd_495609 25134383574741398637851 := by
  unfold tailWord_495609
  simp only [CollatzResearch.WordTrace]
  refine ⟨18076345261500711123513881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12050896841000474082342587 18076345261500711123513881)
  ·
    refine ⟨13557258946125533342635411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18076345261500711123513881 13557258946125533342635411)
    ·
      refine ⟨20335888419188300013953117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13557258946125533342635411 20335888419188300013953117)
      ·
        refine ⟨7625958157195612505232419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20335888419188300013953117 7625958157195612505232419)
        ·
          refine ⟨11438937235793418757848629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7625958157195612505232419 11438937235793418757848629)
          ·
            refine ⟨1072400365855633008548309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 11438937235793418757848629 1072400365855633008548309)
            ·
              refine ⟨25134383574741398637851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1072400365855633008548309 25134383574741398637851)
              ·
                rfl

theorem cell20_495609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 5, 7].length) (baseStart_495609 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_495609 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_495609 prefixEnd_495609 := by exact prefixLift 495609
  have htrace : WordTrace (prefixWord ++ tailWord_495609) baseStart_495609 baseEnd_495609 := by
    simpa [prefixWord, tailWord_495609, baseEnd_495609] using wordTrace_append hprefix tailTrace_495609
  have hstable : (prefixWord ++ tailWord_495609).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_495609).length < 2 ^ (prefixWord ++ tailWord_495609).sum := by decide
  have hdescent : baseEnd_495609 < baseStart_495609 := by decide
  rcases family_descends (prefixWord ++ tailWord_495609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_495640 : List Nat := [2, 1, 2, 3, 2, 1, 1, 4, 4]
def baseStart_495640 : Nat := 118140960795 + 495640 * 2 ^ 59
def prefixEnd_495640 : Nat := 4983230072969 + 3 ^ 40 * 495640 * 2
def baseEnd_495640 : Nat := 226223601417374257707199

theorem tailTrace_495640 : CollatzResearch.WordTrace tailWord_495640 prefixEnd_495640 226223601417374257707199 := by
  unfold tailWord_495640
  simp only [CollatzResearch.WordTrace]
  refine ⟨9038737962194201708946187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12051650616258935611928249 9038737962194201708946187)
  ·
    refine ⟨13558106943291302563419281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9038737962194201708946187 13558106943291302563419281)
    ·
      refine ⟨10168580207468476922564461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13558106943291302563419281 10168580207468476922564461)
      ·
        refine ⟨3813217577800678845961673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10168580207468476922564461 3813217577800678845961673)
        ·
          refine ⟨2859913183350509134471255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3813217577800678845961673 2859913183350509134471255)
          ·
            refine ⟨4289869775025763701706883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2859913183350509134471255 4289869775025763701706883)
            ·
              refine ⟨6434804662538645552560325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4289869775025763701706883 6434804662538645552560325)
              ·
                refine ⟨1206525874225996041105061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6434804662538645552560325 1206525874225996041105061)
                ·
                  refine ⟨226223601417374257707199, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1206525874225996041105061 226223601417374257707199)
                  ·
                    rfl

theorem cell20_495640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 1, 4, 4].length) (baseStart_495640 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_495640 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_495640 prefixEnd_495640 := by exact prefixLift 495640
  have htrace : WordTrace (prefixWord ++ tailWord_495640) baseStart_495640 baseEnd_495640 := by
    simpa [prefixWord, tailWord_495640, baseEnd_495640] using wordTrace_append hprefix tailTrace_495640
  have hstable : (prefixWord ++ tailWord_495640).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_495640).length < 2 ^ (prefixWord ++ tailWord_495640).sum := by decide
  have hdescent : baseEnd_495640 < baseStart_495640 := by decide
  rcases family_descends (prefixWord ++ tailWord_495640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_495647 : List Nat := [1, 1, 2, 4, 1, 2, 3, 6]
def baseStart_495647 : Nat := 118140960795 + 495647 * 2 ^ 59
def prefixEnd_495647 : Nat := 4983230072969 + 3 ^ 40 * 495647 * 2
def baseEnd_495647 : Nat := 75408932136037781491279

theorem tailTrace_495647 : CollatzResearch.WordTrace tailWord_495647 prefixEnd_495647 75408932136037781491279 := by
  unfold tailWord_495647
  simp only [CollatzResearch.WordTrace]
  refine ⟨18077731235363043613397195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12051820823575362408931463 18077731235363043613397195)
  ·
    refine ⟨27116596853044565420095793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18077731235363043613397195 27116596853044565420095793)
    ·
      refine ⟨20337447639783424065071845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27116596853044565420095793 20337447639783424065071845)
      ·
        refine ⟨3813271432459392012200971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20337447639783424065071845 3813271432459392012200971)
        ·
          refine ⟨5719907148689088018301457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3813271432459392012200971 5719907148689088018301457)
          ·
            refine ⟨4289930361516816013726093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5719907148689088018301457 4289930361516816013726093)
            ·
              refine ⟨1608723885568806005147285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4289930361516816013726093 1608723885568806005147285)
              ·
                refine ⟨75408932136037781491279, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1608723885568806005147285 75408932136037781491279)
                ·
                  rfl

theorem cell20_495647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 3, 6].length) (baseStart_495647 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_495647 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_495647 prefixEnd_495647 := by exact prefixLift 495647
  have htrace : WordTrace (prefixWord ++ tailWord_495647) baseStart_495647 baseEnd_495647 := by
    simpa [prefixWord, tailWord_495647, baseEnd_495647] using wordTrace_append hprefix tailTrace_495647
  have hstable : (prefixWord ++ tailWord_495647).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_495647).length < 2 ^ (prefixWord ++ tailWord_495647).sum := by decide
  have hdescent : baseEnd_495647 < baseStart_495647 := by decide
  rcases family_descends (prefixWord ++ tailWord_495647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_495726 : List Nat := [4, 1, 2, 2, 1, 1, 4, 2, 3]
def baseStart_495726 : Nat := 118140960795 + 495726 * 2 ^ 59
def prefixEnd_495726 : Nat := 4983230072969 + 3 ^ 40 * 495726 * 2
def baseEnd_495726 : Nat := 226262854160740180840181

theorem tailTrace_495726 : CollatzResearch.WordTrace tailWord_495726 prefixEnd_495726 226262854160740180840181 := by
  unfold tailWord_495726
  simp only [CollatzResearch.WordTrace]
  refine ⟨2260076575259605013190379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12053741734717893403682021 2260076575259605013190379)
  ·
    refine ⟨3390114862889407519785569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2260076575259605013190379 3390114862889407519785569)
    ·
      refine ⟨2542586147167055639839177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3390114862889407519785569 2542586147167055639839177)
      ·
        refine ⟨1906939610375291729879383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2542586147167055639839177 1906939610375291729879383)
        ·
          refine ⟨2860409415562937594819075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1906939610375291729879383 2860409415562937594819075)
          ·
            refine ⟨4290614123344406392228613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2860409415562937594819075 4290614123344406392228613)
            ·
              refine ⟨804490148127076198542865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4290614123344406392228613 804490148127076198542865)
              ·
                refine ⟨603367611095307148907149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 804490148127076198542865 603367611095307148907149)
                ·
                  refine ⟨226262854160740180840181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 603367611095307148907149 226262854160740180840181)
                  ·
                    rfl

theorem cell20_495726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 4, 2, 3].length) (baseStart_495726 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_495726 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_495726 prefixEnd_495726 := by exact prefixLift 495726
  have htrace : WordTrace (prefixWord ++ tailWord_495726) baseStart_495726 baseEnd_495726 := by
    simpa [prefixWord, tailWord_495726, baseEnd_495726] using wordTrace_append hprefix tailTrace_495726
  have hstable : (prefixWord ++ tailWord_495726).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_495726).length < 2 ^ (prefixWord ++ tailWord_495726).sum := by decide
  have hdescent : baseEnd_495726 < baseStart_495726 := by decide
  rcases family_descends (prefixWord ++ tailWord_495726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_495740 : List Nat := [2, 2, 2, 1, 1, 6, 1, 5]
def baseStart_495740 : Nat := 118140960795 + 495740 * 2 ^ 59
def prefixEnd_495740 : Nat := 4983230072969 + 3 ^ 40 * 495740 * 2
def baseEnd_495740 : Nat := 75423081380739451457819

theorem tailTrace_495740 : CollatzResearch.WordTrace tailWord_495740 prefixEnd_495740 75423081380739451457819 := by
  unfold tailWord_495740
  simp only [CollatzResearch.WordTrace]
  refine ⟨9040561612013060248266337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12054082149350746997688449 9040561612013060248266337)
  ·
    refine ⟨6780421209009795186199753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9040561612013060248266337 6780421209009795186199753)
    ·
      refine ⟨5085315906757346389649815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6780421209009795186199753 5085315906757346389649815)
      ·
        refine ⟨7627973860136019584474723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5085315906757346389649815 7627973860136019584474723)
        ·
          refine ⟨11441960790204029376712085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7627973860136019584474723 11441960790204029376712085)
          ·
            refine ⟨536341912040813877033379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 11441960790204029376712085 536341912040813877033379)
            ·
              refine ⟨804512868061220815550069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 536341912040813877033379 804512868061220815550069)
              ·
                refine ⟨75423081380739451457819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 804512868061220815550069 75423081380739451457819)
                ·
                  rfl

theorem cell20_495740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 6, 1, 5].length) (baseStart_495740 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_495740 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_495740 prefixEnd_495740 := by exact prefixLift 495740
  have htrace : WordTrace (prefixWord ++ tailWord_495740) baseStart_495740 baseEnd_495740 := by
    simpa [prefixWord, tailWord_495740, baseEnd_495740] using wordTrace_append hprefix tailTrace_495740
  have hstable : (prefixWord ++ tailWord_495740).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_495740).length < 2 ^ (prefixWord ++ tailWord_495740).sum := by decide
  have hdescent : baseEnd_495740 < baseStart_495740 := by decide
  rcases family_descends (prefixWord ++ tailWord_495740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_495747 : List Nat := [1, 1, 1, 3, 3, 3, 2, 3, 3]
def baseStart_495747 : Nat := 118140960795 + 495747 * 2 ^ 59
def prefixEnd_495747 : Nat := 4983230072969 + 3 ^ 40 * 495747 * 2
def baseEnd_495747 : Nat := 226272439132957441140095

theorem tailTrace_495747 : CollatzResearch.WordTrace tailWord_495747 prefixEnd_495747 226272439132957441140095 := by
  unfold tailWord_495747
  simp only [CollatzResearch.WordTrace]
  refine ⟨18081378535000760692037495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12054252356667173794691663 18081378535000760692037495)
  ·
    refine ⟨27122067802501141038056243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18081378535000760692037495 27122067802501141038056243)
    ·
      refine ⟨40683101703751711557084365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27122067802501141038056243 40683101703751711557084365)
      ·
        refine ⟨15256163138906891833906637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40683101703751711557084365 15256163138906891833906637)
        ·
          refine ⟨5721061177090084437714989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15256163138906891833906637 5721061177090084437714989)
          ·
            refine ⟨2145397941408781664143121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5721061177090084437714989 2145397941408781664143121)
            ·
              refine ⟨1609048456056586248107341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2145397941408781664143121 1609048456056586248107341)
              ·
                refine ⟨603393171021219843040253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1609048456056586248107341 603393171021219843040253)
                ·
                  refine ⟨226272439132957441140095, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 603393171021219843040253 226272439132957441140095)
                  ·
                    rfl

theorem cell20_495747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 2, 3, 3].length) (baseStart_495747 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_495747 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_495747 prefixEnd_495747 := by exact prefixLift 495747
  have htrace : WordTrace (prefixWord ++ tailWord_495747) baseStart_495747 baseEnd_495747 := by
    simpa [prefixWord, tailWord_495747, baseEnd_495747] using wordTrace_append hprefix tailTrace_495747
  have hstable : (prefixWord ++ tailWord_495747).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_495747).length < 2 ^ (prefixWord ++ tailWord_495747).sum := by decide
  have hdescent : baseEnd_495747 < baseStart_495747 := by decide
  rcases family_descends (prefixWord ++ tailWord_495747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_495754 : List Nat := [3, 1, 2, 3, 1, 2, 1, 1, 6]
def baseStart_495754 : Nat := 118140960795 + 495754 * 2 ^ 59
def prefixEnd_495754 : Nat := 4983230072969 + 3 ^ 40 * 495754 * 2
def baseEnd_495754 : Nat := 226275634123696527906733

theorem tailTrace_495754 : CollatzResearch.WordTrace tailWord_495754 prefixEnd_495754 226275634123696527906733 := by
  unfold tailWord_495754
  simp only [CollatzResearch.WordTrace]
  refine ⟨4520408461493850221885579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12054422563983600591694877 4520408461493850221885579)
  ·
    refine ⟨6780612692240775332828369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4520408461493850221885579 6780612692240775332828369)
    ·
      refine ⟨5085459519180581499621277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6780612692240775332828369 5085459519180581499621277)
      ·
        refine ⟨1907047319692718062357979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5085459519180581499621277 1907047319692718062357979)
        ·
          refine ⟨2860570979539077093536969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1907047319692718062357979 2860570979539077093536969)
          ·
            refine ⟨2145428234654307820152727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2860570979539077093536969 2145428234654307820152727)
            ·
              refine ⟨3218142351981461730229091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2145428234654307820152727 3218142351981461730229091)
              ·
                refine ⟨4827213527972192595343637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3218142351981461730229091 4827213527972192595343637)
                ·
                  refine ⟨226275634123696527906733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4827213527972192595343637 226275634123696527906733)
                  ·
                    rfl

theorem cell20_495754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 1, 1, 6].length) (baseStart_495754 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_495754 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_495754 prefixEnd_495754 := by exact prefixLift 495754
  have htrace : WordTrace (prefixWord ++ tailWord_495754) baseStart_495754 baseEnd_495754 := by
    simpa [prefixWord, tailWord_495754, baseEnd_495754] using wordTrace_append hprefix tailTrace_495754
  have hstable : (prefixWord ++ tailWord_495754).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_495754).length < 2 ^ (prefixWord ++ tailWord_495754).sum := by decide
  have hdescent : baseEnd_495754 < baseStart_495754 := by decide
  rcases family_descends (prefixWord ++ tailWord_495754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_495778 : List Nat := [3, 3, 1, 3, 1, 2, 7]
def baseStart_495778 : Nat := 118140960795 + 495778 * 2 ^ 59
def prefixEnd_495778 : Nat := 4983230072969 + 3 ^ 40 * 495778 * 2
def baseEnd_495778 : Nat := 25142954264184345678515

theorem tailTrace_495778 : CollatzResearch.WordTrace tailWord_495778 prefixEnd_495778 25142954264184345678515 := by
  unfold tailWord_495778
  simp only [CollatzResearch.WordTrace]
  refine ⟨4520627299472113246603997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12055006131925635324277325 4520627299472113246603997)
  ·
    refine ⟨1695235237302042467476499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4520627299472113246603997 1695235237302042467476499)
    ·
      refine ⟨2542852855953063701214749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1695235237302042467476499 2542852855953063701214749)
      ·
        refine ⟨953569820982398887955531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2542852855953063701214749 953569820982398887955531)
        ·
          refine ⟨1430354731473598331933297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 953569820982398887955531 1430354731473598331933297)
          ·
            refine ⟨1072766048605198748949973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1430354731473598331933297 1072766048605198748949973)
            ·
              refine ⟨25142954264184345678515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1072766048605198748949973 25142954264184345678515)
              ·
                rfl

theorem cell20_495778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 2, 7].length) (baseStart_495778 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_495778 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_495778 prefixEnd_495778 := by exact prefixLift 495778
  have htrace : WordTrace (prefixWord ++ tailWord_495778) baseStart_495778 baseEnd_495778 := by
    simpa [prefixWord, tailWord_495778, baseEnd_495778] using wordTrace_append hprefix tailTrace_495778
  have hstable : (prefixWord ++ tailWord_495778).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_495778).length < 2 ^ (prefixWord ++ tailWord_495778).sum := by decide
  have hdescent : baseEnd_495778 < baseStart_495778 := by decide
  rcases family_descends (prefixWord ++ tailWord_495778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_495826 : List Nat := [3, 2, 2, 2, 1, 2, 3, 3, 2]
def baseStart_495826 : Nat := 118140960795 + 495826 * 2 ^ 59
def prefixEnd_495826 : Nat := 4983230072969 + 3 ^ 40 * 495826 * 2
def baseEnd_495826 : Nat := 226308496885584277506439

theorem tailTrace_495826 : CollatzResearch.WordTrace tailWord_495826 prefixEnd_495826 226308496885584277506439 := by
  unfold tailWord_495826
  simp only [CollatzResearch.WordTrace]
  refine ⟨4521064975428639296040833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12056173267809704789442221 4521064975428639296040833)
  ·
    refine ⟨3390798731571479472030625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4521064975428639296040833 3390798731571479472030625)
    ·
      refine ⟨2543099048678609604022969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3390798731571479472030625 2543099048678609604022969)
      ·
        refine ⟨1907324286508957203017227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2543099048678609604022969 1907324286508957203017227)
        ·
          refine ⟨2860986429763435804525841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1907324286508957203017227 2860986429763435804525841)
          ·
            refine ⟨2145739822322576853394381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2860986429763435804525841 2145739822322576853394381)
            ·
              refine ⟨804652433370966320022893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2145739822322576853394381 804652433370966320022893)
              ·
                refine ⟨301744662514112370008585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 804652433370966320022893 301744662514112370008585)
                ·
                  refine ⟨226308496885584277506439, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 301744662514112370008585 226308496885584277506439)
                  ·
                    rfl

theorem cell20_495826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 3, 3, 2].length) (baseStart_495826 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_495826 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_495826 prefixEnd_495826 := by exact prefixLift 495826
  have htrace : WordTrace (prefixWord ++ tailWord_495826) baseStart_495826 baseEnd_495826 := by
    simpa [prefixWord, tailWord_495826, baseEnd_495826] using wordTrace_append hprefix tailTrace_495826
  have hstable : (prefixWord ++ tailWord_495826).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_495826).length < 2 ^ (prefixWord ++ tailWord_495826).sum := by decide
  have hdescent : baseEnd_495826 < baseStart_495826 := by decide
  rcases family_descends (prefixWord ++ tailWord_495826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_495843 : List Nat := [1, 1, 1, 8, 2, 1, 1, 1, 4]
def baseStart_495843 : Nat := 118140960795 + 495843 * 2 ^ 59
def prefixEnd_495843 : Nat := 4983230072969 + 3 ^ 40 * 495843 * 2
def baseEnd_495843 : Nat := 226316256148807773939703

theorem tailTrace_495843 : CollatzResearch.WordTrace tailWord_495843 prefixEnd_495843 226316256148807773939703 := by
  unfold tailWord_495843
  simp only [CollatzResearch.WordTrace]
  refine ⟨18084879942652969087532183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12056586628435312725021455 18084879942652969087532183)
  ·
    refine ⟨27127319913979453631298275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18084879942652969087532183 27127319913979453631298275)
    ·
      refine ⟨40690979870969180446947413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27127319913979453631298275 40690979870969180446947413)
      ·
        refine ⟨476847420362920083362665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 8 40690979870969180446947413 476847420362920083362665)
        ·
          refine ⟨357635565272190062521999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 476847420362920083362665 357635565272190062521999)
          ·
            refine ⟨536453347908285093782999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 357635565272190062521999 536453347908285093782999)
            ·
              refine ⟨804680021862427640674499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 536453347908285093782999 804680021862427640674499)
              ·
                refine ⟨1207020032793641461011749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 804680021862427640674499 1207020032793641461011749)
                ·
                  refine ⟨226316256148807773939703, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1207020032793641461011749 226316256148807773939703)
                  ·
                    rfl

theorem cell20_495843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 2, 1, 1, 1, 4].length) (baseStart_495843 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_495843 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_495843 prefixEnd_495843 := by exact prefixLift 495843
  have htrace : WordTrace (prefixWord ++ tailWord_495843) baseStart_495843 baseEnd_495843 := by
    simpa [prefixWord, tailWord_495843, baseEnd_495843] using wordTrace_append hprefix tailTrace_495843
  have hstable : (prefixWord ++ tailWord_495843).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_495843).length < 2 ^ (prefixWord ++ tailWord_495843).sum := by decide
  have hdescent : baseEnd_495843 < baseStart_495843 := by decide
  rcases family_descends (prefixWord ++ tailWord_495843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_495847 : List Nat := [1, 1, 5, 3, 1, 1, 3, 1, 4]
def baseStart_495847 : Nat := 118140960795 + 495847 * 2 ^ 59
def prefixEnd_495847 : Nat := 4983230072969 + 3 ^ 40 * 495847 * 2
def baseEnd_495847 : Nat := 226318081857801537806353

theorem tailTrace_495847 : CollatzResearch.WordTrace tailWord_495847 prefixEnd_495847 226318081857801537806353 := by
  unfold tailWord_495847
  simp only [CollatzResearch.WordTrace]
  refine ⟨18085025834638477770677795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12056683889758985180451863 18085025834638477770677795)
  ·
    refine ⟨27127538751957716656016693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18085025834638477770677795 27127538751957716656016693)
    ·
      refine ⟨2543206757996035936501565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 27127538751957716656016693 2543206757996035936501565)
      ·
        refine ⟨953702534248513476188087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2543206757996035936501565 953702534248513476188087)
        ·
          refine ⟨1430553801372770214282131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 953702534248513476188087 1430553801372770214282131)
          ·
            refine ⟨2145830702059155321423197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1430553801372770214282131 2145830702059155321423197)
            ·
              refine ⟨804686513272183245533699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2145830702059155321423197 804686513272183245533699)
              ·
                refine ⟨1207029769908274868300549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 804686513272183245533699 1207029769908274868300549)
                ·
                  refine ⟨226318081857801537806353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1207029769908274868300549 226318081857801537806353)
                  ·
                    rfl

theorem cell20_495847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 3, 1, 4].length) (baseStart_495847 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_495847 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_495847 prefixEnd_495847 := by exact prefixLift 495847
  have htrace : WordTrace (prefixWord ++ tailWord_495847) baseStart_495847 baseEnd_495847 := by
    simpa [prefixWord, tailWord_495847, baseEnd_495847] using wordTrace_append hprefix tailTrace_495847
  have hstable : (prefixWord ++ tailWord_495847).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_495847).length < 2 ^ (prefixWord ++ tailWord_495847).sum := by decide
  have hdescent : baseEnd_495847 < baseStart_495847 := by decide
  rcases family_descends (prefixWord ++ tailWord_495847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_495882 : List Nat := [3, 1, 2, 2, 1, 1, 2, 1, 7]
def baseStart_495882 : Nat := 118140960795 + 495882 * 2 ^ 59
def prefixEnd_495882 : Nat := 4983230072969 + 3 ^ 40 * 495882 * 2
def baseEnd_495882 : Nat := 226334056811496971639543

theorem tailTrace_495882 : CollatzResearch.WordTrace tailWord_495882 prefixEnd_495882 226334056811496971639543 := by
  unfold tailWord_495882
  simp only [CollatzResearch.WordTrace]
  refine ⟨4521575597377919687050475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12057534926341119165467933 4521575597377919687050475)
  ·
    refine ⟨6782363396066879530575713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4521575597377919687050475 6782363396066879530575713)
    ·
      refine ⟨5086772547050159647931785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6782363396066879530575713 5086772547050159647931785)
      ·
        refine ⟨3815079410287619735948839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5086772547050159647931785 3815079410287619735948839)
        ·
          refine ⟨5722619115431429603923259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3815079410287619735948839 5722619115431429603923259)
          ·
            refine ⟨8583928673147144405884889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5722619115431429603923259 8583928673147144405884889)
            ·
              refine ⟨6437946504860358304413667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8583928673147144405884889 6437946504860358304413667)
              ·
                refine ⟨9656919757290537456620501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6437946504860358304413667 9656919757290537456620501)
                ·
                  refine ⟨226334056811496971639543, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9656919757290537456620501 226334056811496971639543)
                  ·
                    rfl

theorem cell20_495882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 2, 1, 7].length) (baseStart_495882 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_495882 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_495882 prefixEnd_495882 := by exact prefixLift 495882
  have htrace : WordTrace (prefixWord ++ tailWord_495882) baseStart_495882 baseEnd_495882 := by
    simpa [prefixWord, tailWord_495882, baseEnd_495882] using wordTrace_append hprefix tailTrace_495882
  have hstable : (prefixWord ++ tailWord_495882).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_495882).length < 2 ^ (prefixWord ++ tailWord_495882).sum := by decide
  have hdescent : baseEnd_495882 < baseStart_495882 := by decide
  rcases family_descends (prefixWord ++ tailWord_495882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_495898 : List Nat := [3, 1, 1, 3, 5, 1, 2, 2, 2]
def baseStart_495898 : Nat := 118140960795 + 495898 * 2 ^ 59
def prefixEnd_495898 : Nat := 4983230072969 + 3 ^ 40 * 495898 * 2
def baseEnd_495898 : Nat := 226341359647472027106145

theorem tailTrace_495898 : CollatzResearch.WordTrace tailWord_495898 prefixEnd_495898 226341359647472027106145 := by
  unfold tailWord_495898
  simp only [CollatzResearch.WordTrace]
  refine ⟨4521721489363428370196087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12057923971635808987189565 4521721489363428370196087)
  ·
    refine ⟨6782582234045142555294131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4521721489363428370196087 6782582234045142555294131)
    ·
      refine ⟨10173873351067713832941197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6782582234045142555294131 10173873351067713832941197)
      ·
        refine ⟨3815202506650392687352949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10173873351067713832941197 3815202506650392687352949)
        ·
          refine ⟨357675234998474314439339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 3815202506650392687352949 357675234998474314439339)
          ·
            refine ⟨536512852497711471659009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 357675234998474314439339 536512852497711471659009)
            ·
              refine ⟨402384639373283603744257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 536512852497711471659009 402384639373283603744257)
              ·
                refine ⟨301788479529962702808193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 402384639373283603744257 301788479529962702808193)
                ·
                  refine ⟨226341359647472027106145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 301788479529962702808193 226341359647472027106145)
                  ·
                    rfl

theorem cell20_495898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 5, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 5, 1, 2, 2, 2].length) (baseStart_495898 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_495898 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_495898 prefixEnd_495898 := by exact prefixLift 495898
  have htrace : WordTrace (prefixWord ++ tailWord_495898) baseStart_495898 baseEnd_495898 := by
    simpa [prefixWord, tailWord_495898, baseEnd_495898] using wordTrace_append hprefix tailTrace_495898
  have hstable : (prefixWord ++ tailWord_495898).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_495898).length < 2 ^ (prefixWord ++ tailWord_495898).sum := by decide
  have hdescent : baseEnd_495898 < baseStart_495898 := by decide
  rcases family_descends (prefixWord ++ tailWord_495898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_495909 : List Nat := [1, 3, 1, 2, 6, 1, 1, 5]
def baseStart_495909 : Nat := 118140960795 + 495909 * 2 ^ 59
def prefixEnd_495909 : Nat := 4983230072969 + 3 ^ 40 * 495909 * 2
def baseEnd_495909 : Nat := 75448793449068292579811

theorem tailTrace_495909 : CollatzResearch.WordTrace tailWord_495909 prefixEnd_495909 75448793449068292579811 := by
  unfold tailWord_495909
  simp only [CollatzResearch.WordTrace]
  refine ⟨18087287160413862359434781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12058191440275908239623187 18087287160413862359434781)
  ·
    refine ⟨6782732685155198384788043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18087287160413862359434781 6782732685155198384788043)
    ·
      refine ⟨10174099027732797577182065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6782732685155198384788043 10174099027732797577182065)
      ·
        refine ⟨7630574270799598182886549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10174099027732797577182065 7630574270799598182886549)
        ·
          refine ⟨357683168943731164822807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 7630574270799598182886549 357683168943731164822807)
          ·
            refine ⟨536524753415596747234211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 357683168943731164822807 536524753415596747234211)
            ·
              refine ⟨804787130123395120851317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 536524753415596747234211 804787130123395120851317)
              ·
                refine ⟨75448793449068292579811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 804787130123395120851317 75448793449068292579811)
                ·
                  rfl

theorem cell20_495909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 6, 1, 1, 5].length) (baseStart_495909 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_495909 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_495909 prefixEnd_495909 := by exact prefixLift 495909
  have htrace : WordTrace (prefixWord ++ tailWord_495909) baseStart_495909 baseEnd_495909 := by
    simpa [prefixWord, tailWord_495909, baseEnd_495909] using wordTrace_append hprefix tailTrace_495909
  have hstable : (prefixWord ++ tailWord_495909).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_495909).length < 2 ^ (prefixWord ++ tailWord_495909).sum := by decide
  have hdescent : baseEnd_495909 < baseStart_495909 := by decide
  rcases family_descends (prefixWord ++ tailWord_495909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_495930 : List Nat := [3, 1, 1, 1, 4, 3, 3, 4]
def baseStart_495930 : Nat := 118140960795 + 495930 * 2 ^ 59
def prefixEnd_495930 : Nat := 4983230072969 + 3 ^ 40 * 495930 * 2
def baseEnd_495930 : Nat := 75451988439807379346449

theorem tailTrace_495930 : CollatzResearch.WordTrace tailWord_495930 prefixEnd_495930 75451988439807379346449 := by
  unfold tailWord_495930
  simp only [CollatzResearch.WordTrace]
  refine ⟨4522013273334445736487311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12058702062225188630632829 4522013273334445736487311)
  ·
    refine ⟨6783019910001668604730967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4522013273334445736487311 6783019910001668604730967)
    ·
      refine ⟨10174529865002502907096451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6783019910001668604730967 10174529865002502907096451)
      ·
        refine ⟨15261794797503754360644677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10174529865002502907096451 15261794797503754360644677)
        ·
          refine ⟨2861586524531953942620877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15261794797503754360644677 2861586524531953942620877)
          ·
            refine ⟨1073094946699482728482829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2861586524531953942620877 1073094946699482728482829)
            ·
              refine ⟨402410605012306023181061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1073094946699482728482829 402410605012306023181061)
              ·
                refine ⟨75451988439807379346449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 402410605012306023181061 75451988439807379346449)
                ·
                  rfl

theorem cell20_495930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 3, 3, 4].length) (baseStart_495930 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_495930 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_495930 prefixEnd_495930 := by exact prefixLift 495930
  have htrace : WordTrace (prefixWord ++ tailWord_495930) baseStart_495930 baseEnd_495930 := by
    simpa [prefixWord, tailWord_495930, baseEnd_495930] using wordTrace_append hprefix tailTrace_495930
  have hstable : (prefixWord ++ tailWord_495930).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_495930).length < 2 ^ (prefixWord ++ tailWord_495930).sum := by decide
  have hdescent : baseEnd_495930 < baseStart_495930 := by decide
  rcases family_descends (prefixWord ++ tailWord_495930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_496002 : List Nat := [3, 4, 2, 1, 3, 1, 6]
def baseStart_496002 : Nat := 118140960795 + 496002 * 2 ^ 59
def prefixEnd_496002 : Nat := 4983230072969 + 3 ^ 40 * 496002 * 2
def baseEnd_496002 : Nat := 25154314231256654182117

theorem tailTrace_496002 : CollatzResearch.WordTrace tailWord_496002 prefixEnd_496002 25154314231256654182117 := by
  unfold tailWord_496002
  simp only [CollatzResearch.WordTrace]
  refine ⟨4522669787269234810642565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12060452766051292828380173 4522669787269234810642565)
  ·
    refine ⟨848000585112981526995481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4522669787269234810642565 848000585112981526995481)
    ·
      refine ⟨636000438834736145246611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 848000585112981526995481 636000438834736145246611)
      ·
        refine ⟨954000658252104217869917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 636000438834736145246611 954000658252104217869917)
        ·
          refine ⟨357750246844539081701219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 954000658252104217869917 357750246844539081701219)
          ·
            refine ⟨536625370266808622551829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 357750246844539081701219 536625370266808622551829)
            ·
              refine ⟨25154314231256654182117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 536625370266808622551829 25154314231256654182117)
              ·
                rfl

theorem cell20_496002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 3, 1, 6].length) (baseStart_496002 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_496002 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_496002 prefixEnd_496002 := by exact prefixLift 496002
  have htrace : WordTrace (prefixWord ++ tailWord_496002) baseStart_496002 baseEnd_496002 := by
    simpa [prefixWord, tailWord_496002, baseEnd_496002] using wordTrace_append hprefix tailTrace_496002
  have hstable : (prefixWord ++ tailWord_496002).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_496002).length < 2 ^ (prefixWord ++ tailWord_496002).sum := by decide
  have hdescent : baseEnd_496002 < baseStart_496002 := by decide
  rcases family_descends (prefixWord ++ tailWord_496002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_496022 : List Nat := [5, 3, 1, 2, 1, 2, 2, 1, 3]
def baseStart_496022 : Nat := 118140960795 + 496022 * 2 ^ 59
def prefixEnd_496022 : Nat := 4983230072969 + 3 ^ 40 * 496022 * 2
def baseEnd_496022 : Nat := 226397956626278706972305

theorem tailTrace_496022 : CollatzResearch.WordTrace tailWord_496022 prefixEnd_496022 226397956626278706972305 := by
  unfold tailWord_496022
  simp only [CollatzResearch.WordTrace]
  refine ⟨1130713038062780166143645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 12060939072669655105532213 1130713038062780166143645)
  ·
    refine ⟨424017389273542562303867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1130713038062780166143645 424017389273542562303867)
    ·
      refine ⟨636026083910313843455801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 424017389273542562303867 636026083910313843455801)
      ·
        refine ⟨477019562932735382591851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 636026083910313843455801 477019562932735382591851)
        ·
          refine ⟨715529344399103073887777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 477019562932735382591851 715529344399103073887777)
          ·
            refine ⟨536647008299327305415833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 715529344399103073887777 536647008299327305415833)
            ·
              refine ⟨402485256224495479061875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 536647008299327305415833 402485256224495479061875)
              ·
                refine ⟨603727884336743218592813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 402485256224495479061875 603727884336743218592813)
                ·
                  refine ⟨226397956626278706972305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 603727884336743218592813 226397956626278706972305)
                  ·
                    rfl

theorem cell20_496022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 2, 2, 1, 3].length) (baseStart_496022 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_496022 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_496022 prefixEnd_496022 := by exact prefixLift 496022
  have htrace : WordTrace (prefixWord ++ tailWord_496022) baseStart_496022 baseEnd_496022 := by
    simpa [prefixWord, tailWord_496022, baseEnd_496022] using wordTrace_append hprefix tailTrace_496022
  have hstable : (prefixWord ++ tailWord_496022).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_496022).length < 2 ^ (prefixWord ++ tailWord_496022).sum := by decide
  have hdescent : baseEnd_496022 < baseStart_496022 := by decide
  rcases family_descends (prefixWord ++ tailWord_496022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_496041 : List Nat := [1, 2, 1, 1, 1, 1, 3, 6, 4]
def baseStart_496041 : Nat := 118140960795 + 496041 * 2 ^ 59
def prefixEnd_496041 : Nat := 4983230072969 + 3 ^ 40 * 496041 * 2
def baseEnd_496041 : Nat := 226406628743999085338893

theorem tailTrace_496041 : CollatzResearch.WordTrace tailWord_496041 prefixEnd_496041 226406628743999085338893 := by
  unfold tailWord_496041
  simp only [CollatzResearch.WordTrace]
  refine ⟨18092101595935648903239977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12061401063957099268826651 18092101595935648903239977)
  ·
    refine ⟨13569076196951736677429983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18092101595935648903239977 13569076196951736677429983)
    ·
      refine ⟨20353614295427605016144975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13569076196951736677429983 20353614295427605016144975)
      ·
        refine ⟨30530421443141407524217463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20353614295427605016144975 30530421443141407524217463)
        ·
          refine ⟨45795632164712111286326195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30530421443141407524217463 45795632164712111286326195)
          ·
            refine ⟨68693448247068166929489293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45795632164712111286326195 68693448247068166929489293)
            ·
              refine ⟨25760043092650562598558485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 68693448247068166929489293 25760043092650562598558485)
              ·
                refine ⟨1207502019967995121807429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 25760043092650562598558485 1207502019967995121807429)
                ·
                  refine ⟨226406628743999085338893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1207502019967995121807429 226406628743999085338893)
                  ·
                    rfl

theorem cell20_496041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 6, 4].length) (baseStart_496041 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_496041 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_496041 prefixEnd_496041 := by exact prefixLift 496041
  have htrace : WordTrace (prefixWord ++ tailWord_496041) baseStart_496041 baseEnd_496041 := by
    simpa [prefixWord, tailWord_496041, baseEnd_496041] using wordTrace_append hprefix tailTrace_496041
  have hstable : (prefixWord ++ tailWord_496041).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_496041).length < 2 ^ (prefixWord ++ tailWord_496041).sum := by decide
  have hdescent : baseEnd_496041 < baseStart_496041 := by decide
  rcases family_descends (prefixWord ++ tailWord_496041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_496079 : List Nat := [1, 1, 2, 1, 1, 4, 1, 5, 4]
def baseStart_496079 : Nat := 118140960795 + 496079 * 2 ^ 59
def prefixEnd_496079 : Nat := 4983230072969 + 3 ^ 40 * 496079 * 2
def baseEnd_496079 : Nat := 226423972979439842072071

theorem tailTrace_496079 : CollatzResearch.WordTrace tailWord_496079 prefixEnd_496079 226423972979439842072071 := by
  unfold tailWord_496079
  simp only [CollatzResearch.WordTrace]
  refine ⟨18093487569797981393123291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12062325046531987595415527 18093487569797981393123291)
  ·
    refine ⟨27140231354696972089684937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18093487569797981393123291 27140231354696972089684937)
    ·
      refine ⟨20355173516022729067263703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27140231354696972089684937 20355173516022729067263703)
      ·
        refine ⟨30532760274034093600895555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20355173516022729067263703 30532760274034093600895555)
        ·
          refine ⟨45799140411051140401343333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30532760274034093600895555 45799140411051140401343333)
          ·
            refine ⟨8587338827072088825251875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 45799140411051140401343333 8587338827072088825251875)
            ·
              refine ⟨12881008240608133237877813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8587338827072088825251875 12881008240608133237877813)
              ·
                refine ⟨1207594522557012491051045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12881008240608133237877813 1207594522557012491051045)
                ·
                  refine ⟨226423972979439842072071, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1207594522557012491051045 226423972979439842072071)
                  ·
                    rfl

theorem cell20_496079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 5, 4].length) (baseStart_496079 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_496079 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_496079 prefixEnd_496079 := by exact prefixLift 496079
  have htrace : WordTrace (prefixWord ++ tailWord_496079) baseStart_496079 baseEnd_496079 := by
    simpa [prefixWord, tailWord_496079, baseEnd_496079] using wordTrace_append hprefix tailTrace_496079
  have hstable : (prefixWord ++ tailWord_496079).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_496079).length < 2 ^ (prefixWord ++ tailWord_496079).sum := by decide
  have hdescent : baseEnd_496079 < baseStart_496079 := by decide
  rcases family_descends (prefixWord ++ tailWord_496079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_496113 : List Nat := [1, 2, 2, 2, 3, 1, 4, 3, 2]
def baseStart_496113 : Nat := 118140960795 + 496113 * 2 ^ 59
def prefixEnd_496113 : Nat := 4983230072969 + 3 ^ 40 * 496113 * 2
def baseEnd_496113 : Nat := 226439491505886834938599

theorem tailTrace_496113 : CollatzResearch.WordTrace tailWord_496113 prefixEnd_496113 226439491505886834938599 := by
  unfold tailWord_496113
  simp only [CollatzResearch.WordTrace]
  refine ⟨18094727651674805199860993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12063151767783203466573995 18094727651674805199860993)
  ·
    refine ⟨13571045738756103899895745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18094727651674805199860993 13571045738756103899895745)
    ·
      refine ⟨10178284304067077924921809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13571045738756103899895745 10178284304067077924921809)
      ·
        refine ⟨7633713228050308443691357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10178284304067077924921809 7633713228050308443691357)
        ·
          refine ⟨2862642460518865666384259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7633713228050308443691357 2862642460518865666384259)
          ·
            refine ⟨4293963690778298499576389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2862642460518865666384259 4293963690778298499576389)
            ·
              refine ⟨805118192020930968670573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4293963690778298499576389 805118192020930968670573)
              ·
                refine ⟨301919322007849113251465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 805118192020930968670573 301919322007849113251465)
                ·
                  refine ⟨226439491505886834938599, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 301919322007849113251465 226439491505886834938599)
                  ·
                    rfl

theorem cell20_496113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 4, 3, 2].length) (baseStart_496113 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_496113 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_496113 prefixEnd_496113 := by exact prefixLift 496113
  have htrace : WordTrace (prefixWord ++ tailWord_496113) baseStart_496113 baseEnd_496113 := by
    simpa [prefixWord, tailWord_496113, baseEnd_496113] using wordTrace_append hprefix tailTrace_496113
  have hstable : (prefixWord ++ tailWord_496113).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_496113).length < 2 ^ (prefixWord ++ tailWord_496113).sum := by decide
  have hdescent : baseEnd_496113 < baseStart_496113 := by decide
  rcases family_descends (prefixWord ++ tailWord_496113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_496130 : List Nat := [3, 4, 1, 2, 2, 1, 2, 1, 4]
def baseStart_496130 : Nat := 118140960795 + 496130 * 2 ^ 59
def prefixEnd_496130 : Nat := 4983230072969 + 3 ^ 40 * 496130 * 2
def baseEnd_496130 : Nat := 226447250769110331371863

theorem tailTrace_496130 : CollatzResearch.WordTrace tailWord_496130 prefixEnd_496130 226447250769110331371863 := by
  unfold tailWord_496130
  simp only [CollatzResearch.WordTrace]
  refine ⟨4523836923153304275807461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12063565128408811402153229 4523836923153304275807461)
  ·
    refine ⟨848219423091244551713899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4523836923153304275807461 848219423091244551713899)
    ·
      refine ⟨1272329134636866827570849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 848219423091244551713899 1272329134636866827570849)
      ·
        refine ⟨954246850977650120678137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1272329134636866827570849 954246850977650120678137)
        ·
          refine ⟨715685138233237590508603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 954246850977650120678137 715685138233237590508603)
          ·
            refine ⟨1073527707349856385762905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 715685138233237590508603 1073527707349856385762905)
            ·
              refine ⟨805145780512392289322179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1073527707349856385762905 805145780512392289322179)
              ·
                refine ⟨1207718670768588433983269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 805145780512392289322179 1207718670768588433983269)
                ·
                  refine ⟨226447250769110331371863, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1207718670768588433983269 226447250769110331371863)
                  ·
                    rfl

theorem cell20_496130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 1, 2, 1, 4].length) (baseStart_496130 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_496130 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_496130 prefixEnd_496130 := by exact prefixLift 496130
  have htrace : WordTrace (prefixWord ++ tailWord_496130) baseStart_496130 baseEnd_496130 := by
    simpa [prefixWord, tailWord_496130, baseEnd_496130] using wordTrace_append hprefix tailTrace_496130
  have hstable : (prefixWord ++ tailWord_496130).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_496130).length < 2 ^ (prefixWord ++ tailWord_496130).sum := by decide
  have hdescent : baseEnd_496130 < baseStart_496130 := by decide
  rcases family_descends (prefixWord ++ tailWord_496130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_496164 : List Nat := [2, 3, 1, 5, 2, 1, 1, 3, 2]
def baseStart_496164 : Nat := 118140960795 + 496164 * 2 ^ 59
def prefixEnd_496164 : Nat := 4983230072969 + 3 ^ 40 * 496164 * 2
def baseEnd_496164 : Nat := 226462769295557324238391

theorem tailTrace_496164 : CollatzResearch.WordTrace tailWord_496164 prefixEnd_496164 226462769295557324238391 := by
  unfold tailWord_496164
  simp only [CollatzResearch.WordTrace]
  refine ⟨9048293887245020454983773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12064391849660027273311697 9048293887245020454983773)
  ·
    refine ⟨3393110207716882670618915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9048293887245020454983773 3393110207716882670618915)
    ·
      refine ⟨5089665311575324005928373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3393110207716882670618915 5089665311575324005928373)
      ·
        refine ⟨477156122960186625555785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 5089665311575324005928373 477156122960186625555785)
        ·
          refine ⟨357867092220139969166839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 477156122960186625555785 357867092220139969166839)
          ·
            refine ⟨536800638330209953750259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 357867092220139969166839 536800638330209953750259)
            ·
              refine ⟨805200957495314930625389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 536800638330209953750259 805200957495314930625389)
              ·
                refine ⟨301950359060743098984521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 805200957495314930625389 301950359060743098984521)
                ·
                  refine ⟨226462769295557324238391, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 301950359060743098984521 226462769295557324238391)
                  ·
                    rfl

theorem cell20_496164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 2, 1, 1, 3, 2].length) (baseStart_496164 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_496164 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_496164 prefixEnd_496164 := by exact prefixLift 496164
  have htrace : WordTrace (prefixWord ++ tailWord_496164) baseStart_496164 baseEnd_496164 := by
    simpa [prefixWord, tailWord_496164, baseEnd_496164] using wordTrace_append hprefix tailTrace_496164
  have hstable : (prefixWord ++ tailWord_496164).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_496164).length < 2 ^ (prefixWord ++ tailWord_496164).sum := by decide
  have hdescent : baseEnd_496164 < baseStart_496164 := by decide
  rcases family_descends (prefixWord ++ tailWord_496164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_496168 : List Nat := [2, 1, 5, 2, 1, 1, 3, 3, 2]
def baseStart_496168 : Nat := 118140960795 + 496168 * 2 ^ 59
def prefixEnd_496168 : Nat := 4983230072969 + 3 ^ 40 * 496168 * 2
def baseEnd_496168 : Nat := 226464595004551088105041

theorem tailTrace_496168 : CollatzResearch.WordTrace tailWord_496168 prefixEnd_496168 226464595004551088105041 := by
  unfold tailWord_496168
  simp only [CollatzResearch.WordTrace]
  refine ⟨9048366833237774796556579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12064489110983699728742105 9048366833237774796556579)
  ·
    refine ⟨13572550249856662194834869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9048366833237774796556579 13572550249856662194834869)
    ·
      refine ⟨1272426585924062080765769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 13572550249856662194834869 1272426585924062080765769)
      ·
        refine ⟨954319939443046560574327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1272426585924062080765769 954319939443046560574327)
        ·
          refine ⟨1431479909164569840861491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 954319939443046560574327 1431479909164569840861491)
          ·
            refine ⟨2147219863746854761292237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1431479909164569840861491 2147219863746854761292237)
            ·
              refine ⟨805207448905070535484589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2147219863746854761292237 805207448905070535484589)
              ·
                refine ⟨301952793339401450806721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 805207448905070535484589 301952793339401450806721)
                ·
                  refine ⟨226464595004551088105041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 301952793339401450806721 226464595004551088105041)
                  ·
                    rfl

theorem cell20_496168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 3, 3, 2].length) (baseStart_496168 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_496168 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_496168 prefixEnd_496168 := by exact prefixLift 496168
  have htrace : WordTrace (prefixWord ++ tailWord_496168) baseStart_496168 baseEnd_496168 := by
    simpa [prefixWord, tailWord_496168, baseEnd_496168] using wordTrace_append hprefix tailTrace_496168
  have hstable : (prefixWord ++ tailWord_496168).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_496168).length < 2 ^ (prefixWord ++ tailWord_496168).sum := by decide
  have hdescent : baseEnd_496168 < baseStart_496168 := by decide
  rcases family_descends (prefixWord ++ tailWord_496168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_496186 : List Nat := [3, 1, 1, 1, 3, 3, 2, 1, 5]
def baseStart_496186 : Nat := 118140960795 + 496186 * 2 ^ 59
def prefixEnd_496186 : Nat := 4983230072969 + 3 ^ 40 * 496186 * 2
def baseEnd_496186 : Nat := 226472810695023025504967

theorem tailTrace_496186 : CollatzResearch.WordTrace tailWord_496186 prefixEnd_496186 226472810695023025504967 := by
  unfold tailWord_496186
  simp only [CollatzResearch.WordTrace]
  refine ⟨4524347545102584666817103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12064926786940225778178941 4524347545102584666817103)
  ·
    refine ⟨6786521317653877000225655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4524347545102584666817103 6786521317653877000225655)
    ·
      refine ⟨10179781976480815500338483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6786521317653877000225655 10179781976480815500338483)
      ·
        refine ⟨15269672964721223250507725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10179781976480815500338483 15269672964721223250507725)
        ·
          refine ⟨5726127361770458718940397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15269672964721223250507725 5726127361770458718940397)
          ·
            refine ⟨2147297760663922019602649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5726127361770458718940397 2147297760663922019602649)
            ·
              refine ⟨1610473320497941514701987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2147297760663922019602649 1610473320497941514701987)
              ·
                refine ⟨2415709980746912272052981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1610473320497941514701987 2415709980746912272052981)
                ·
                  refine ⟨226472810695023025504967, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2415709980746912272052981 226472810695023025504967)
                  ·
                    rfl

theorem cell20_496186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 2, 1, 5].length) (baseStart_496186 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_496186 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_496186 prefixEnd_496186 := by exact prefixLift 496186
  have htrace : WordTrace (prefixWord ++ tailWord_496186) baseStart_496186 baseEnd_496186 := by
    simpa [prefixWord, tailWord_496186, baseEnd_496186] using wordTrace_append hprefix tailTrace_496186
  have hstable : (prefixWord ++ tailWord_496186).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_496186).length < 2 ^ (prefixWord ++ tailWord_496186).sum := by decide
  have hdescent : baseEnd_496186 < baseStart_496186 := by decide
  rcases family_descends (prefixWord ++ tailWord_496186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_496189 : List Nat := [1, 4, 1, 3, 2, 3, 1, 1, 4]
def baseStart_496189 : Nat := 118140960795 + 496189 * 2 ^ 59
def prefixEnd_496189 : Nat := 4983230072969 + 3 ^ 40 * 496189 * 2
def baseEnd_496189 : Nat := 226474179976768348404955

theorem tailTrace_496189 : CollatzResearch.WordTrace tailWord_496189 prefixEnd_496189 226474179976768348404955 := by
  unfold tailWord_496189
  simp only [CollatzResearch.WordTrace]
  refine ⟨18097499599399470179627621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12064999732932980119751747 18097499599399470179627621)
  ·
    refine ⟨3393281174887400658680179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18097499599399470179627621 3393281174887400658680179)
    ·
      refine ⟨5089921762331100988020269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3393281174887400658680179 5089921762331100988020269)
      ·
        refine ⟨1908720660874162870507601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5089921762331100988020269 1908720660874162870507601)
        ·
          refine ⟨1431540495655622152880701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1908720660874162870507601 1431540495655622152880701)
          ·
            refine ⟨536827685870858307330263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1431540495655622152880701 536827685870858307330263)
            ·
              refine ⟨805241528806287460995395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 536827685870858307330263 805241528806287460995395)
              ·
                refine ⟨1207862293209431191493093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 805241528806287460995395 1207862293209431191493093)
                ·
                  refine ⟨226474179976768348404955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1207862293209431191493093 226474179976768348404955)
                  ·
                    rfl

theorem cell20_496189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 3, 1, 1, 4].length) (baseStart_496189 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_496189 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_496189 prefixEnd_496189 := by exact prefixLift 496189
  have htrace : WordTrace (prefixWord ++ tailWord_496189) baseStart_496189 baseEnd_496189 := by
    simpa [prefixWord, tailWord_496189, baseEnd_496189] using wordTrace_append hprefix tailTrace_496189
  have hstable : (prefixWord ++ tailWord_496189).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_496189).length < 2 ^ (prefixWord ++ tailWord_496189).sum := by decide
  have hdescent : baseEnd_496189 < baseStart_496189 := by decide
  rcases family_descends (prefixWord ++ tailWord_496189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_496203 : List Nat := [1, 1, 1, 1, 3, 1, 8, 1, 3]
def baseStart_496203 : Nat := 118140960795 + 496203 * 2 ^ 59
def prefixEnd_496203 : Nat := 4983230072969 + 3 ^ 40 * 496203 * 2
def baseEnd_496203 : Nat := 226480569958246521938231

theorem tailTrace_496203 : CollatzResearch.WordTrace tailWord_496203 prefixEnd_496203 226480569958246521938231 := by
  unfold tailWord_496203
  simp only [CollatzResearch.WordTrace]
  refine ⟨18098010221348750570637263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12065340147565833713758175 18098010221348750570637263)
  ·
    refine ⟨27147015332023125855955895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18098010221348750570637263 27147015332023125855955895)
    ·
      refine ⟨40720522998034688783933843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27147015332023125855955895 40720522998034688783933843)
      ·
        refine ⟨61080784497052033175900765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40720522998034688783933843 61080784497052033175900765)
        ·
          refine ⟨22905294186394512440962787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61080784497052033175900765 22905294186394512440962787)
          ·
            refine ⟨34357941279591768661444181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22905294186394512440962787 34357941279591768661444181)
            ·
              refine ⟨402632124370216039001299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 34357941279591768661444181 402632124370216039001299)
              ·
                refine ⟨603948186555324058501949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 402632124370216039001299 603948186555324058501949)
                ·
                  refine ⟨226480569958246521938231, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 603948186555324058501949 226480569958246521938231)
                  ·
                    rfl

theorem cell20_496203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 8, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 8, 1, 3].length) (baseStart_496203 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_496203 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_496203 prefixEnd_496203 := by exact prefixLift 496203
  have htrace : WordTrace (prefixWord ++ tailWord_496203) baseStart_496203 baseEnd_496203 := by
    simpa [prefixWord, tailWord_496203, baseEnd_496203] using wordTrace_append hprefix tailTrace_496203
  have hstable : (prefixWord ++ tailWord_496203).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_496203).length < 2 ^ (prefixWord ++ tailWord_496203).sum := by decide
  have hdescent : baseEnd_496203 < baseStart_496203 := by decide
  rcases family_descends (prefixWord ++ tailWord_496203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_496248 : List Nat := [2, 1, 2, 1, 1, 1, 2, 8, 2]
def baseStart_496248 : Nat := 118140960795 + 496248 * 2 ^ 59
def prefixEnd_496248 : Nat := 4983230072969 + 3 ^ 40 * 496248 * 2
def baseEnd_496248 : Nat := 226501109184426365438047

theorem tailTrace_496248 : CollatzResearch.WordTrace tailWord_496248 prefixEnd_496248 226501109184426365438047 := by
  unfold tailWord_496248
  simp only [CollatzResearch.WordTrace]
  refine ⟨9049825753092861628012699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12066434337457148837350265 9049825753092861628012699)
  ·
    refine ⟨13574738629639292442019049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9049825753092861628012699 13574738629639292442019049)
    ·
      refine ⟨10181053972229469331514287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13574738629639292442019049 10181053972229469331514287)
      ·
        refine ⟨15271580958344203997271431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10181053972229469331514287 15271580958344203997271431)
        ·
          refine ⟨22907371437516305995907147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15271580958344203997271431 22907371437516305995907147)
          ·
            refine ⟨34361057156274458993860721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22907371437516305995907147 34361057156274458993860721)
            ·
              refine ⟨25770792867205844245395541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34361057156274458993860721 25770792867205844245395541)
              ·
                refine ⟨302001478912568487250729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 25770792867205844245395541 302001478912568487250729)
                ·
                  refine ⟨226501109184426365438047, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 302001478912568487250729 226501109184426365438047)
                  ·
                    rfl

theorem cell20_496248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 8, 2].length) (baseStart_496248 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_496248 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_496248 prefixEnd_496248 := by exact prefixLift 496248
  have htrace : WordTrace (prefixWord ++ tailWord_496248) baseStart_496248 baseEnd_496248 := by
    simpa [prefixWord, tailWord_496248, baseEnd_496248] using wordTrace_append hprefix tailTrace_496248
  have hstable : (prefixWord ++ tailWord_496248).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_496248).length < 2 ^ (prefixWord ++ tailWord_496248).sum := by decide
  have hdescent : baseEnd_496248 < baseStart_496248 := by decide
  rcases family_descends (prefixWord ++ tailWord_496248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_496286 : List Nat := [4, 3, 1, 1, 1, 1, 1, 2, 6]
def baseStart_496286 : Nat := 118140960795 + 496286 * 2 ^ 59
def prefixEnd_496286 : Nat := 4983230072969 + 3 ^ 40 * 496286 * 2
def baseEnd_496286 : Nat := 226518453419867122171225

theorem tailTrace_496286 : CollatzResearch.WordTrace tailWord_496286 prefixEnd_496286 226518453419867122171225 := by
  unfold tailWord_496286
  simp only [CollatzResearch.WordTrace]
  refine ⟨2262629685006006968238589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12067358320032037163939141 2262629685006006968238589)
  ·
    refine ⟨848486131877252613089471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2262629685006006968238589 848486131877252613089471)
    ·
      refine ⟨1272729197815878919634207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 848486131877252613089471 1272729197815878919634207)
      ·
        refine ⟨1909093796723818379451311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1272729197815878919634207 1909093796723818379451311)
        ·
          refine ⟨2863640695085727569176967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1909093796723818379451311 2863640695085727569176967)
          ·
            refine ⟨4295461042628591353765451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2863640695085727569176967 4295461042628591353765451)
            ·
              refine ⟨6443191563942887030648177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4295461042628591353765451 6443191563942887030648177)
              ·
                refine ⟨4832393672957165272986133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6443191563942887030648177 4832393672957165272986133)
                ·
                  refine ⟨226518453419867122171225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4832393672957165272986133 226518453419867122171225)
                  ·
                    rfl

theorem cell20_496286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 1, 2, 6].length) (baseStart_496286 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_496286 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_496286 prefixEnd_496286 := by exact prefixLift 496286
  have htrace : WordTrace (prefixWord ++ tailWord_496286) baseStart_496286 baseEnd_496286 := by
    simpa [prefixWord, tailWord_496286, baseEnd_496286] using wordTrace_append hprefix tailTrace_496286
  have hstable : (prefixWord ++ tailWord_496286).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_496286).length < 2 ^ (prefixWord ++ tailWord_496286).sum := by decide
  have hdescent : baseEnd_496286 < baseStart_496286 := by decide
  rcases family_descends (prefixWord ++ tailWord_496286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_496307 : List Nat := [1, 1, 1, 2, 3, 4, 1, 3, 4]
def baseStart_496307 : Nat := 118140960795 + 496307 * 2 ^ 59
def prefixEnd_496307 : Nat := 4983230072969 + 3 ^ 40 * 496307 * 2
def baseEnd_496307 : Nat := 226528038392084382471139

theorem tailTrace_496307 : CollatzResearch.WordTrace tailWord_496307 prefixEnd_496307 226528038392084382471139 := by
  unfold tailWord_496307
  simp only [CollatzResearch.WordTrace]
  refine ⟨18101803412971976332423175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12067868941981317554948783 18101803412971976332423175)
  ·
    refine ⟨27152705119457964498634763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18101803412971976332423175 27152705119457964498634763)
    ·
      refine ⟨40729057679186946747952145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27152705119457964498634763 40729057679186946747952145)
      ·
        refine ⟨30546793259390210060964109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40729057679186946747952145 30546793259390210060964109)
        ·
          refine ⟨11455047472271328772861541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30546793259390210060964109 11455047472271328772861541)
          ·
            refine ⟨2147821401050874144911539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11455047472271328772861541 2147821401050874144911539)
            ·
              refine ⟨3221732101576311217367309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2147821401050874144911539 3221732101576311217367309)
              ·
                refine ⟨1208149538091116706512741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3221732101576311217367309 1208149538091116706512741)
                ·
                  refine ⟨226528038392084382471139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1208149538091116706512741 226528038392084382471139)
                  ·
                    rfl

theorem cell20_496307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 1, 3, 4].length) (baseStart_496307 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_496307 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_496307 prefixEnd_496307 := by exact prefixLift 496307
  have htrace : WordTrace (prefixWord ++ tailWord_496307) baseStart_496307 baseEnd_496307 := by
    simpa [prefixWord, tailWord_496307, baseEnd_496307] using wordTrace_append hprefix tailTrace_496307
  have hstable : (prefixWord ++ tailWord_496307).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_496307).length < 2 ^ (prefixWord ++ tailWord_496307).sum := by decide
  have hdescent : baseEnd_496307 < baseStart_496307 := by decide
  rcases family_descends (prefixWord ++ tailWord_496307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_496314 : List Nat := [3, 1, 1, 1, 2, 3, 2, 7]
def baseStart_496314 : Nat := 118140960795 + 496314 * 2 ^ 59
def prefixEnd_496314 : Nat := 4983230072969 + 3 ^ 40 * 496314 * 2
def baseEnd_496314 : Nat := 75510411127607823079259

theorem tailTrace_496314 : CollatzResearch.WordTrace tailWord_496314 prefixEnd_496314 75510411127607823079259 := by
  unfold tailWord_496314
  simp only [CollatzResearch.WordTrace]
  refine ⟨4525514680986654131981999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12068039149297744351951997 4525514680986654131981999)
  ·
    refine ⟨6788272021479981197972999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4525514680986654131981999 6788272021479981197972999)
    ·
      refine ⟨10182408032219971796959499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6788272021479981197972999 10182408032219971796959499)
      ·
        refine ⟨15273612048329957695439249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10182408032219971796959499 15273612048329957695439249)
        ·
          refine ⟨11455209036247468271579437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15273612048329957695439249 11455209036247468271579437)
          ·
            refine ⟨4295703388592800601842289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11455209036247468271579437 4295703388592800601842289)
            ·
              refine ⟨3221777541444600451381717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4295703388592800601842289 3221777541444600451381717)
              ·
                refine ⟨75510411127607823079259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3221777541444600451381717 75510411127607823079259)
                ·
                  rfl

theorem cell20_496314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 2, 7].length) (baseStart_496314 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_496314 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_496314 prefixEnd_496314 := by exact prefixLift 496314
  have htrace : WordTrace (prefixWord ++ tailWord_496314) baseStart_496314 baseEnd_496314 := by
    simpa [prefixWord, tailWord_496314, baseEnd_496314] using wordTrace_append hprefix tailTrace_496314
  have hstable : (prefixWord ++ tailWord_496314).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_496314).length < 2 ^ (prefixWord ++ tailWord_496314).sum := by decide
  have hdescent : baseEnd_496314 < baseStart_496314 := by decide
  rcases family_descends (prefixWord ++ tailWord_496314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_496324 : List Nat := [2, 3, 3, 1, 1, 2, 2, 2, 4]
def baseStart_496324 : Nat := 118140960795 + 496324 * 2 ^ 59
def prefixEnd_496324 : Nat := 4983230072969 + 3 ^ 40 * 496324 * 2
def baseEnd_496324 : Nat := 226535797655307878904403

theorem tailTrace_496324 : CollatzResearch.WordTrace tailWord_496324 prefixEnd_496324 226535797655307878904403 := by
  unfold tailWord_496324
  simp only [CollatzResearch.WordTrace]
  refine ⟨9051211726955194117896013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12068282302606925490528017 9051211726955194117896013)
  ·
    refine ⟨3394204397608197794211005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9051211726955194117896013 3394204397608197794211005)
    ·
      refine ⟨1272826649103074172829127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3394204397608197794211005 1272826649103074172829127)
      ·
        refine ⟨1909239973654611259243691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1272826649103074172829127 1909239973654611259243691)
        ·
          refine ⟨2863859960481916888865537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1909239973654611259243691 2863859960481916888865537)
          ·
            refine ⟨2147894970361437666649153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2863859960481916888865537 2147894970361437666649153)
            ·
              refine ⟨1610921227771078249986865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2147894970361437666649153 1610921227771078249986865)
              ·
                refine ⟨1208190920828308687490149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1610921227771078249986865 1208190920828308687490149)
                ·
                  refine ⟨226535797655307878904403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1208190920828308687490149 226535797655307878904403)
                  ·
                    rfl

theorem cell20_496324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 2, 2, 4].length) (baseStart_496324 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_496324 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_496324 prefixEnd_496324 := by exact prefixLift 496324
  have htrace : WordTrace (prefixWord ++ tailWord_496324) baseStart_496324 baseEnd_496324 := by
    simpa [prefixWord, tailWord_496324, baseEnd_496324] using wordTrace_append hprefix tailTrace_496324
  have hstable : (prefixWord ++ tailWord_496324).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_496324).length < 2 ^ (prefixWord ++ tailWord_496324).sum := by decide
  have hdescent : baseEnd_496324 < baseStart_496324 := by decide
  rcases family_descends (prefixWord ++ tailWord_496324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_496348 : List Nat := [2, 2, 5, 1, 1, 3, 6]
def baseStart_496348 : Nat := 118140960795 + 496348 * 2 ^ 59
def prefixEnd_496348 : Nat := 4983230072969 + 3 ^ 40 * 496348 * 2
def baseEnd_496348 : Nat := 25171861323252273567145

theorem tailTrace_496348 : CollatzResearch.WordTrace tailWord_496348 prefixEnd_496348 25171861323252273567145 := by
  unfold tailWord_496348
  simp only [CollatzResearch.WordTrace]
  refine ⟨9051649402911720167332849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12068865870548960223110465 9051649402911720167332849)
  ·
    refine ⟨6788737052183790125499637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9051649402911720167332849 6788737052183790125499637)
    ·
      refine ⟨636444098642230324265591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 6788737052183790125499637 636444098642230324265591)
      ·
        refine ⟨954666147963345486398387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 636444098642230324265591 954666147963345486398387)
        ·
          refine ⟨1431999221945018229597581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 954666147963345486398387 1431999221945018229597581)
          ·
            refine ⟨536999708229381836099093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1431999221945018229597581 536999708229381836099093)
            ·
              refine ⟨25171861323252273567145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 536999708229381836099093 25171861323252273567145)
              ·
                rfl

theorem cell20_496348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 3, 6].length) (baseStart_496348 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_496348 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_496348 prefixEnd_496348 := by exact prefixLift 496348
  have htrace : WordTrace (prefixWord ++ tailWord_496348) baseStart_496348 baseEnd_496348 := by
    simpa [prefixWord, tailWord_496348, baseEnd_496348] using wordTrace_append hprefix tailTrace_496348
  have hstable : (prefixWord ++ tailWord_496348).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_496348).length < 2 ^ (prefixWord ++ tailWord_496348).sum := by decide
  have hdescent : baseEnd_496348 < baseStart_496348 := by decide
  rcases family_descends (prefixWord ++ tailWord_496348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_496376 : List Nat := [2, 1, 2, 1, 1, 2, 5, 3, 3]
def baseStart_496376 : Nat := 118140960795 + 496376 * 2 ^ 59
def prefixEnd_496376 : Nat := 4983230072969 + 3 ^ 40 * 496376 * 2
def baseEnd_496376 : Nat := 226559531872226809170857

theorem tailTrace_496376 : CollatzResearch.WordTrace tailWord_496376 prefixEnd_496376 226559531872226809170857 := by
  unfold tailWord_496376
  simp only [CollatzResearch.WordTrace]
  refine ⟨9052160024861000558342491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12069546699814667411123321 9052160024861000558342491)
  ·
    refine ⟨13578240037291500837513737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9052160024861000558342491 13578240037291500837513737)
    ·
      refine ⟨10183680027968625628135303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13578240037291500837513737 10183680027968625628135303)
      ·
        refine ⟨15275520041952938442202955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10183680027968625628135303 15275520041952938442202955)
        ·
          refine ⟨22913280062929407663304433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15275520041952938442202955 22913280062929407663304433)
          ·
            refine ⟨17184960047197055747478325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22913280062929407663304433 17184960047197055747478325)
            ·
              refine ⟨1611090004424723976326093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 17184960047197055747478325 1611090004424723976326093)
              ·
                refine ⟨604158751659271491122285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1611090004424723976326093 604158751659271491122285)
                ·
                  refine ⟨226559531872226809170857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 604158751659271491122285 226559531872226809170857)
                  ·
                    rfl

theorem cell20_496376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 5, 3, 3].length) (baseStart_496376 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_496376 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_496376 prefixEnd_496376 := by exact prefixLift 496376
  have htrace : WordTrace (prefixWord ++ tailWord_496376) baseStart_496376 baseEnd_496376 := by
    simpa [prefixWord, tailWord_496376, baseEnd_496376] using wordTrace_append hprefix tailTrace_496376
  have hstable : (prefixWord ++ tailWord_496376).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_496376).length < 2 ^ (prefixWord ++ tailWord_496376).sum := by decide
  have hdescent : baseEnd_496376 < baseStart_496376 := by decide
  rcases family_descends (prefixWord ++ tailWord_496376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_496407 : List Nat := [1, 1, 3, 4, 4, 7]
def baseStart_496407 : Nat := 118140960795 + 496407 * 2 ^ 59
def prefixEnd_496407 : Nat := 4983230072969 + 3 ^ 40 * 496407 * 2
def baseEnd_496407 : Nat := 8391617819145499227311

theorem tailTrace_496407 : CollatzResearch.WordTrace tailWord_496407 prefixEnd_496407 8391617819145499227311 := by
  unfold tailWord_496407
  simp only [CollatzResearch.WordTrace]
  refine ⟨18105450712609693411063475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12070300475073128940708983 18105450712609693411063475)
  ·
    refine ⟨27158176068914540116595213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18105450712609693411063475 27158176068914540116595213)
    ·
      refine ⟨10184316025842952543723205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27158176068914540116595213 10184316025842952543723205)
      ·
        refine ⟨1909559254845553601948101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10184316025842952543723205 1909559254845553601948101)
        ·
          refine ⟨358042360283541300365269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1909559254845553601948101 358042360283541300365269)
          ·
            refine ⟨8391617819145499227311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 358042360283541300365269 8391617819145499227311)
            ·
              rfl

theorem cell20_496407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 4, 7].length) (baseStart_496407 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_496407 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_496407 prefixEnd_496407 := by exact prefixLift 496407
  have htrace : WordTrace (prefixWord ++ tailWord_496407) baseStart_496407 baseEnd_496407 := by
    simpa [prefixWord, tailWord_496407, baseEnd_496407] using wordTrace_append hprefix tailTrace_496407
  have hstable : (prefixWord ++ tailWord_496407).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_496407).length < 2 ^ (prefixWord ++ tailWord_496407).sum := by decide
  have hdescent : baseEnd_496407 < baseStart_496407 := by decide
  rcases family_descends (prefixWord ++ tailWord_496407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_496421 : List Nat := [1, 3, 1, 2, 3, 1, 2, 3, 4]
def baseStart_496421 : Nat := 118140960795 + 496421 * 2 ^ 59
def prefixEnd_496421 : Nat := 4983230072969 + 3 ^ 40 * 496421 * 2
def baseEnd_496421 : Nat := 226580071098406652670673

theorem tailTrace_496421 : CollatzResearch.WordTrace tailWord_496421 prefixEnd_496421 226580071098406652670673 := by
  unfold tailWord_496421
  simp only [CollatzResearch.WordTrace]
  refine ⟨18105961334558973802073117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12070640889705982534715411 18105961334558973802073117)
  ·
    refine ⟨6789735500459615175777419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18105961334558973802073117 6789735500459615175777419)
    ·
      refine ⟨10184603250689422763666129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6789735500459615175777419 10184603250689422763666129)
      ·
        refine ⟨7638452438017067072749597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10184603250689422763666129 7638452438017067072749597)
        ·
          refine ⟨2864419664256400152281099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7638452438017067072749597 2864419664256400152281099)
          ·
            refine ⟨4296629496384600228421649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2864419664256400152281099 4296629496384600228421649)
            ·
              refine ⟨3222472122288450171316237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4296629496384600228421649 3222472122288450171316237)
              ·
                refine ⟨1208427045858168814243589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3222472122288450171316237 1208427045858168814243589)
                ·
                  refine ⟨226580071098406652670673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1208427045858168814243589 226580071098406652670673)
                  ·
                    rfl

theorem cell20_496421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 2, 3, 4].length) (baseStart_496421 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_496421 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_496421 prefixEnd_496421 := by exact prefixLift 496421
  have htrace : WordTrace (prefixWord ++ tailWord_496421) baseStart_496421 baseEnd_496421 := by
    simpa [prefixWord, tailWord_496421, baseEnd_496421] using wordTrace_append hprefix tailTrace_496421
  have hstable : (prefixWord ++ tailWord_496421).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_496421).length < 2 ^ (prefixWord ++ tailWord_496421).sum := by decide
  have hdescent : baseEnd_496421 < baseStart_496421 := by decide
  rcases family_descends (prefixWord ++ tailWord_496421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_496466 : List Nat := [3, 2, 2, 1, 1, 2, 9]
def baseStart_496466 : Nat := 118140960795 + 496466 * 2 ^ 59
def prefixEnd_496466 : Nat := 4983230072969 + 3 ^ 40 * 496466 * 2
def baseEnd_496466 : Nat := 25177845591620721796721

theorem tailTrace_496466 : CollatzResearch.WordTrace tailWord_496466 prefixEnd_496466 25177845591620721796721 := by
  unfold tailWord_496466
  simp only [CollatzResearch.WordTrace]
  refine ⟨4526900654848986621865313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12071735079597297658307501 4526900654848986621865313)
  ·
    refine ⟨3395175491136739966398985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4526900654848986621865313 3395175491136739966398985)
    ·
      refine ⟨2546381618352554974799239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3395175491136739966398985 2546381618352554974799239)
      ·
        refine ⟨3819572427528832462198859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2546381618352554974799239 3819572427528832462198859)
        ·
          refine ⟨5729358641293248693298289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3819572427528832462198859 5729358641293248693298289)
          ·
            refine ⟨4297018980969936519973717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5729358641293248693298289 4297018980969936519973717)
            ·
              refine ⟨25177845591620721796721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 4297018980969936519973717 25177845591620721796721)
              ·
                rfl

theorem cell20_496466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 9].length) (baseStart_496466 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_496466 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_496466 prefixEnd_496466 := by exact prefixLift 496466
  have htrace : WordTrace (prefixWord ++ tailWord_496466) baseStart_496466 baseEnd_496466 := by
    simpa [prefixWord, tailWord_496466, baseEnd_496466] using wordTrace_append hprefix tailTrace_496466
  have hstable : (prefixWord ++ tailWord_496466).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_496466).length < 2 ^ (prefixWord ++ tailWord_496466).sum := by decide
  have hdescent : baseEnd_496466 < baseStart_496466 := by decide
  rcases family_descends (prefixWord ++ tailWord_496466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_496476 : List Nat := [2, 2, 4, 2, 1, 1, 1, 3, 4]
def baseStart_496476 : Nat := 118140960795 + 496476 * 2 ^ 59
def prefixEnd_496476 : Nat := 4983230072969 + 3 ^ 40 * 496476 * 2
def baseEnd_496476 : Nat := 226605174597070905837115

theorem tailTrace_496476 : CollatzResearch.WordTrace tailWord_496476 prefixEnd_496476 226605174597070905837115 := by
  unfold tailWord_496476
  simp only [CollatzResearch.WordTrace]
  refine ⟨9053983674679859097662641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12071978232906478796883521 9053983674679859097662641)
  ·
    refine ⟨6790487756009894323246981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9053983674679859097662641 6790487756009894323246981)
    ·
      refine ⟨1273216454251855185608809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6790487756009894323246981 1273216454251855185608809)
      ·
        refine ⟨954912340688891389206607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1273216454251855185608809 954912340688891389206607)
        ·
          refine ⟨1432368511033337083809911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 954912340688891389206607 1432368511033337083809911)
          ·
            refine ⟨2148552766550005625714867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1432368511033337083809911 2148552766550005625714867)
            ·
              refine ⟨3222829149825008438572301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2148552766550005625714867 3222829149825008438572301)
              ·
                refine ⟨1208560931184378164464613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3222829149825008438572301 1208560931184378164464613)
                ·
                  refine ⟨226605174597070905837115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1208560931184378164464613 226605174597070905837115)
                  ·
                    rfl

theorem cell20_496476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 1, 3, 4].length) (baseStart_496476 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_496476 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_496476 prefixEnd_496476 := by exact prefixLift 496476
  have htrace : WordTrace (prefixWord ++ tailWord_496476) baseStart_496476 baseEnd_496476 := by
    simpa [prefixWord, tailWord_496476, baseEnd_496476] using wordTrace_append hprefix tailTrace_496476
  have hstable : (prefixWord ++ tailWord_496476).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_496476).length < 2 ^ (prefixWord ++ tailWord_496476).sum := by decide
  have hdescent : baseEnd_496476 < baseStart_496476 := by decide
  rcases family_descends (prefixWord ++ tailWord_496476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_496497 : List Nat := [1, 2, 2, 2, 1, 4, 2, 2, 4]
def baseStart_496497 : Nat := 118140960795 + 496497 * 2 ^ 59
def prefixEnd_496497 : Nat := 4983230072969 + 3 ^ 40 * 496497 * 2
def baseEnd_496497 : Nat := 226614759569288166137029

theorem tailTrace_496497 : CollatzResearch.WordTrace tailWord_496497 prefixEnd_496497 226614759569288166137029 := by
  unfold tailWord_496497
  simp only [CollatzResearch.WordTrace]
  refine ⟨18108733282283638781839745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12072488854855759187893163 18108733282283638781839745)
  ·
    refine ⟨13581549961712729086379809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18108733282283638781839745 13581549961712729086379809)
    ·
      refine ⟨10186162471284546814784857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13581549961712729086379809 10186162471284546814784857)
      ·
        refine ⟨7639621853463410111088643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10186162471284546814784857 7639621853463410111088643)
        ·
          refine ⟨11459432780195115166632965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7639621853463410111088643 11459432780195115166632965)
          ·
            refine ⟨2148643646286584093743681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11459432780195115166632965 2148643646286584093743681)
            ·
              refine ⟨1611482734714938070307761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2148643646286584093743681 1611482734714938070307761)
              ·
                refine ⟨1208612051036203552730821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1611482734714938070307761 1208612051036203552730821)
                ·
                  refine ⟨226614759569288166137029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1208612051036203552730821 226614759569288166137029)
                  ·
                    rfl

theorem cell20_496497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 2, 2, 4].length) (baseStart_496497 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_496497 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_496497 prefixEnd_496497 := by exact prefixLift 496497
  have htrace : WordTrace (prefixWord ++ tailWord_496497) baseStart_496497 baseEnd_496497 := by
    simpa [prefixWord, tailWord_496497, baseEnd_496497] using wordTrace_append hprefix tailTrace_496497
  have hstable : (prefixWord ++ tailWord_496497).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_496497).length < 2 ^ (prefixWord ++ tailWord_496497).sum := by decide
  have hdescent : baseEnd_496497 < baseStart_496497 := by decide
  rcases family_descends (prefixWord ++ tailWord_496497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_496511 : List Nat := [1, 1, 2, 2, 1, 1, 5, 2, 5]
def baseStart_496511 : Nat := 118140960795 + 496511 * 2 ^ 59
def prefixEnd_496511 : Nat := 4983230072969 + 3 ^ 40 * 496511 * 2
def baseEnd_496511 : Nat := 226621149550766339670305

theorem tailTrace_496511 : CollatzResearch.WordTrace tailWord_496511 prefixEnd_496511 226621149550766339670305 := by
  unfold tailWord_496511
  simp only [CollatzResearch.WordTrace]
  refine ⟨18109243904232919172849387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12072829269488612781899591 18109243904232919172849387)
  ·
    refine ⟨27163865856349378759274081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18109243904232919172849387 27163865856349378759274081)
    ·
      refine ⟨20372899392262034069455561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27163865856349378759274081 20372899392262034069455561)
      ·
        refine ⟨15279674544196525552091671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20372899392262034069455561 15279674544196525552091671)
        ·
          refine ⟨22919511816294788328137507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15279674544196525552091671 22919511816294788328137507)
          ·
            refine ⟨34379267724442182492206261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22919511816294788328137507 34379267724442182492206261)
            ·
              refine ⟨3223056349166454608644337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 34379267724442182492206261 3223056349166454608644337)
              ·
                refine ⟨2417292261874840956483253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3223056349166454608644337 2417292261874840956483253)
                ·
                  refine ⟨226621149550766339670305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2417292261874840956483253 226621149550766339670305)
                  ·
                    rfl

theorem cell20_496511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 5, 2, 5].length) (baseStart_496511 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_496511 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_496511 prefixEnd_496511 := by exact prefixLift 496511
  have htrace : WordTrace (prefixWord ++ tailWord_496511) baseStart_496511 baseEnd_496511 := by
    simpa [prefixWord, tailWord_496511, baseEnd_496511] using wordTrace_append hprefix tailTrace_496511
  have hstable : (prefixWord ++ tailWord_496511).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_496511).length < 2 ^ (prefixWord ++ tailWord_496511).sum := by decide
  have hdescent : baseEnd_496511 < baseStart_496511 := by decide
  rcases family_descends (prefixWord ++ tailWord_496511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_496545 : List Nat := [1, 2, 3, 4, 1, 2, 1, 3, 3]
def baseStart_496545 : Nat := 118140960795 + 496545 * 2 ^ 59
def prefixEnd_496545 : Nat := 4983230072969 + 3 ^ 40 * 496545 * 2
def baseEnd_496545 : Nat := 226636668077213332536833

theorem tailTrace_496545 : CollatzResearch.WordTrace tailWord_496545 prefixEnd_496545 226636668077213332536833 := by
  unfold tailWord_496545
  simp only [CollatzResearch.WordTrace]
  refine ⟨18110483986109742979587089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12073655990739828653058059 18110483986109742979587089)
  ·
    refine ⟨13582862989582307234690317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18110483986109742979587089 13582862989582307234690317)
    ·
      refine ⟨5093573621093365213008869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13582862989582307234690317 5093573621093365213008869)
      ·
        refine ⟨955045053955005977439163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5093573621093365213008869 955045053955005977439163)
        ·
          refine ⟨1432567580932508966158745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 955045053955005977439163 1432567580932508966158745)
          ·
            refine ⟨1074425685699381724619059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1432567580932508966158745 1074425685699381724619059)
            ·
              refine ⟨1611638528549072586928589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1074425685699381724619059 1611638528549072586928589)
              ·
                refine ⟨604364448205902220098221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1611638528549072586928589 604364448205902220098221)
                ·
                  refine ⟨226636668077213332536833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 604364448205902220098221 226636668077213332536833)
                  ·
                    rfl

theorem cell20_496545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 2, 1, 3, 3].length) (baseStart_496545 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_496545 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_496545 prefixEnd_496545 := by exact prefixLift 496545
  have htrace : WordTrace (prefixWord ++ tailWord_496545) baseStart_496545 baseEnd_496545 := by
    simpa [prefixWord, tailWord_496545, baseEnd_496545] using wordTrace_append hprefix tailTrace_496545
  have hstable : (prefixWord ++ tailWord_496545).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_496545).length < 2 ^ (prefixWord ++ tailWord_496545).sum := by decide
  have hdescent : baseEnd_496545 < baseStart_496545 := by decide
  rcases family_descends (prefixWord ++ tailWord_496545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_496589 : List Nat := [1, 6, 3, 1, 2, 1, 1, 5]
def baseStart_496589 : Nat := 118140960795 + 496589 * 2 ^ 59
def prefixEnd_496589 : Nat := 4983230072969 + 3 ^ 40 * 496589 * 2
def baseEnd_496589 : Nat := 75552250292048245023329

theorem tailTrace_496589 : CollatzResearch.WordTrace tailWord_496589 prefixEnd_496589 75552250292048245023329 := by
  unfold tailWord_496589
  simp only [CollatzResearch.WordTrace]
  refine ⟨18112088797950338494188821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12074725865300225662792547 18112088797950338494188821)
  ·
    refine ⟨849004162403922116915101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 18112088797950338494188821 849004162403922116915101)
    ·
      refine ⟨318376560901470793843163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 849004162403922116915101 318376560901470793843163)
      ·
        refine ⟨477564841352206190764745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 318376560901470793843163 477564841352206190764745)
        ·
          refine ⟨358173631014154643073559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 477564841352206190764745 358173631014154643073559)
          ·
            refine ⟨537260446521231964610339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 358173631014154643073559 537260446521231964610339)
            ·
              refine ⟨805890669781847946915509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 537260446521231964610339 805890669781847946915509)
              ·
                refine ⟨75552250292048245023329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 805890669781847946915509 75552250292048245023329)
                ·
                  rfl

theorem cell20_496589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 2, 1, 1, 5].length) (baseStart_496589 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_496589 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_496589 prefixEnd_496589 := by exact prefixLift 496589
  have htrace : WordTrace (prefixWord ++ tailWord_496589) baseStart_496589 baseEnd_496589 := by
    simpa [prefixWord, tailWord_496589, baseEnd_496589] using wordTrace_append hprefix tailTrace_496589
  have hstable : (prefixWord ++ tailWord_496589).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_496589).length < 2 ^ (prefixWord ++ tailWord_496589).sum := by decide
  have hdescent : baseEnd_496589 < baseStart_496589 := by decide
  rcases family_descends (prefixWord ++ tailWord_496589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_496611 : List Nat := [1, 1, 1, 6, 1, 1, 3, 2, 4]
def baseStart_496611 : Nat := 118140960795 + 496611 * 2 ^ 59
def prefixEnd_496611 : Nat := 4983230072969 + 3 ^ 40 * 496611 * 2
def baseEnd_496611 : Nat := 226666792275610436336563

theorem tailTrace_496611 : CollatzResearch.WordTrace tailWord_496611 prefixEnd_496611 226666792275610436336563 := by
  unfold tailWord_496611
  simp only [CollatzResearch.WordTrace]
  refine ⟨18112891203870636251489687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12075260802580424167659791 18112891203870636251489687)
  ·
    refine ⟨27169336805805954377234531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18112891203870636251489687 27169336805805954377234531)
    ·
      refine ⟨40754005208708931565851797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27169336805805954377234531 40754005208708931565851797)
      ·
        refine ⟨1910343994158231167149303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 40754005208708931565851797 1910343994158231167149303)
        ·
          refine ⟨2865515991237346750723955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1910343994158231167149303 2865515991237346750723955)
          ·
            refine ⟨4298273986856020126085933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2865515991237346750723955 4298273986856020126085933)
            ·
              refine ⟨1611852745071007547282225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4298273986856020126085933 1611852745071007547282225)
              ·
                refine ⟨1208889558803255660461669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1611852745071007547282225 1208889558803255660461669)
                ·
                  refine ⟨226666792275610436336563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1208889558803255660461669 226666792275610436336563)
                  ·
                    rfl

theorem cell20_496611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 3, 2, 4].length) (baseStart_496611 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_496611 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_496611 prefixEnd_496611 := by exact prefixLift 496611
  have htrace : WordTrace (prefixWord ++ tailWord_496611) baseStart_496611 baseEnd_496611 := by
    simpa [prefixWord, tailWord_496611, baseEnd_496611] using wordTrace_append hprefix tailTrace_496611
  have hstable : (prefixWord ++ tailWord_496611).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_496611).length < 2 ^ (prefixWord ++ tailWord_496611).sum := by decide
  have hdescent : baseEnd_496611 < baseStart_496611 := by decide
  rcases family_descends (prefixWord ++ tailWord_496611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_496632 : List Nat := [2, 1, 2, 1, 1, 3, 1, 1, 8]
def baseStart_496632 : Nat := 118140960795 + 496632 * 2 ^ 59
def prefixEnd_496632 : Nat := 4983230072969 + 3 ^ 40 * 496632 * 2
def baseEnd_496632 : Nat := 226676377247827696636477

theorem tailTrace_496632 : CollatzResearch.WordTrace tailWord_496632 prefixEnd_496632 226676377247827696636477 := by
  unfold tailWord_496632
  simp only [CollatzResearch.WordTrace]
  refine ⟨9056828568397278419002075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12075771424529704558669433 9056828568397278419002075)
  ·
    refine ⟨13585242852595917628503113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9056828568397278419002075 13585242852595917628503113)
    ·
      refine ⟨10188932139446938221377335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13585242852595917628503113 10188932139446938221377335)
      ·
        refine ⟨15283398209170407332066003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10188932139446938221377335 15283398209170407332066003)
        ·
          refine ⟨22925097313755610998099005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15283398209170407332066003 22925097313755610998099005)
          ·
            refine ⟨8596911492658354124287127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22925097313755610998099005 8596911492658354124287127)
            ·
              refine ⟨12895367238987531186430691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8596911492658354124287127 12895367238987531186430691)
              ·
                refine ⟨19343050858481296779646037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12895367238987531186430691 19343050858481296779646037)
                ·
                  refine ⟨226676377247827696636477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 19343050858481296779646037 226676377247827696636477)
                  ·
                    rfl

theorem cell20_496632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 1, 8].length) (baseStart_496632 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_496632 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_496632 prefixEnd_496632 := by exact prefixLift 496632
  have htrace : WordTrace (prefixWord ++ tailWord_496632) baseStart_496632 baseEnd_496632 := by
    simpa [prefixWord, tailWord_496632, baseEnd_496632] using wordTrace_append hprefix tailTrace_496632
  have hstable : (prefixWord ++ tailWord_496632).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_496632).length < 2 ^ (prefixWord ++ tailWord_496632).sum := by decide
  have hdescent : baseEnd_496632 < baseStart_496632 := by decide
  rcases family_descends (prefixWord ++ tailWord_496632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_496669 : List Nat := [1, 4, 2, 2, 4, 1, 2, 4]
def baseStart_496669 : Nat := 118140960795 + 496669 * 2 ^ 59
def prefixEnd_496669 : Nat := 4983230072969 + 3 ^ 40 * 496669 * 2
def baseEnd_496669 : Nat := 75564421685340004134331

theorem tailTrace_496669 : CollatzResearch.WordTrace tailWord_496669 prefixEnd_496669 75564421685340004134331 := by
  unfold tailWord_496669
  simp only [CollatzResearch.WordTrace]
  refine ⟨18115006637660512157101061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12076671091773674771400707 18115006637660512157101061)
  ·
    refine ⟨3396563744561346029456449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18115006637660512157101061 3396563744561346029456449)
    ·
      refine ⟨2547422808421009522092337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3396563744561346029456449 2547422808421009522092337)
      ·
        refine ⟨1910567106315757141569253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2547422808421009522092337 1910567106315757141569253)
        ·
          refine ⟨358231332434204464044235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1910567106315757141569253 358231332434204464044235)
          ·
            refine ⟨537346998651306696066353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 358231332434204464044235 537346998651306696066353)
            ·
              refine ⟨403010248988480022049765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 537346998651306696066353 403010248988480022049765)
              ·
                refine ⟨75564421685340004134331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 403010248988480022049765 75564421685340004134331)
                ·
                  rfl

theorem cell20_496669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 4, 1, 2, 4].length) (baseStart_496669 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_496669 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_496669 prefixEnd_496669 := by exact prefixLift 496669
  have htrace : WordTrace (prefixWord ++ tailWord_496669) baseStart_496669 baseEnd_496669 := by
    simpa [prefixWord, tailWord_496669, baseEnd_496669] using wordTrace_append hprefix tailTrace_496669
  have hstable : (prefixWord ++ tailWord_496669).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_496669).length < 2 ^ (prefixWord ++ tailWord_496669).sum := by decide
  have hdescent : baseEnd_496669 < baseStart_496669 := by decide
  rcases family_descends (prefixWord ++ tailWord_496669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_496673 : List Nat := [1, 2, 3, 2, 3, 1, 4, 4]
def baseStart_496673 : Nat := 118140960795 + 496673 * 2 ^ 59
def prefixEnd_496673 : Nat := 4983230072969 + 3 ^ 40 * 496673 * 2
def baseEnd_496673 : Nat := 75565030255004592089881

theorem tailTrace_496673 : CollatzResearch.WordTrace tailWord_496673 prefixEnd_496673 75565030255004592089881 := by
  unfold tailWord_496673
  simp only [CollatzResearch.WordTrace]
  refine ⟨18115152529646020840246673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12076768353097347226831115 18115152529646020840246673)
  ·
    refine ⟨13586364397234515630185005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18115152529646020840246673 13586364397234515630185005)
    ·
      refine ⟨5094886648962943361319377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13586364397234515630185005 5094886648962943361319377)
      ·
        refine ⟨3821164986722207520989533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5094886648962943361319377 3821164986722207520989533)
        ·
          refine ⟨1432936870020827820371075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3821164986722207520989533 1432936870020827820371075)
          ·
            refine ⟨2149405305031241730556613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1432936870020827820371075 2149405305031241730556613)
            ·
              refine ⟨403013494693357824479365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2149405305031241730556613 403013494693357824479365)
              ·
                refine ⟨75565030255004592089881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 403013494693357824479365 75565030255004592089881)
                ·
                  rfl

theorem cell20_496673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 4, 4].length) (baseStart_496673 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_496673 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_496673 prefixEnd_496673 := by exact prefixLift 496673
  have htrace : WordTrace (prefixWord ++ tailWord_496673) baseStart_496673 baseEnd_496673 := by
    simpa [prefixWord, tailWord_496673, baseEnd_496673] using wordTrace_append hprefix tailTrace_496673
  have hstable : (prefixWord ++ tailWord_496673).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_496673).length < 2 ^ (prefixWord ++ tailWord_496673).sum := by decide
  have hdescent : baseEnd_496673 < baseStart_496673 := by decide
  rcases family_descends (prefixWord ++ tailWord_496673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_496718 : List Nat := [4, 1, 1, 1, 1, 3, 3, 3, 3]
def baseStart_496718 : Nat := 118140960795 + 496718 * 2 ^ 59
def prefixEnd_496718 : Nat := 4983230072969 + 3 ^ 40 * 496718 * 2
def baseEnd_496718 : Nat := 226715629991193619769459

theorem tailTrace_496718 : CollatzResearch.WordTrace tailWord_496718 prefixEnd_496718 226715629991193619769459 := by
  unfold tailWord_496718
  simp only [CollatzResearch.WordTrace]
  refine ⟨2264599226810374190704351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12077862542988662350423205 2264599226810374190704351)
  ·
    refine ⟨3396898840215561286056527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2264599226810374190704351 3396898840215561286056527)
    ·
      refine ⟨5095348260323341929084791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3396898840215561286056527 5095348260323341929084791)
      ·
        refine ⟨7643022390485012893627187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5095348260323341929084791 7643022390485012893627187)
        ·
          refine ⟨11464533585727519340440781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7643022390485012893627187 11464533585727519340440781)
          ·
            refine ⟨4299200094647819752665293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11464533585727519340440781 4299200094647819752665293)
            ·
              refine ⟨1612200035492932407249485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4299200094647819752665293 1612200035492932407249485)
              ·
                refine ⟨604575013309849652718557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1612200035492932407249485 604575013309849652718557)
                ·
                  refine ⟨226715629991193619769459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 604575013309849652718557 226715629991193619769459)
                  ·
                    rfl

theorem cell20_496718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 3, 3, 3].length) (baseStart_496718 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_496718 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_496718 prefixEnd_496718 := by exact prefixLift 496718
  have htrace : WordTrace (prefixWord ++ tailWord_496718) baseStart_496718 baseEnd_496718 := by
    simpa [prefixWord, tailWord_496718, baseEnd_496718] using wordTrace_append hprefix tailTrace_496718
  have hstable : (prefixWord ++ tailWord_496718).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_496718).length < 2 ^ (prefixWord ++ tailWord_496718).sum := by decide
  have hdescent : baseEnd_496718 < baseStart_496718 := by decide
  rcases family_descends (prefixWord ++ tailWord_496718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_496732 : List Nat := [2, 2, 4, 1, 1, 1, 1, 8]
def baseStart_496732 : Nat := 118140960795 + 496732 * 2 ^ 59
def prefixEnd_496732 : Nat := 4983230072969 + 3 ^ 40 * 496732 * 2
def baseEnd_496732 : Nat := 75574006657557264434245

theorem tailTrace_496732 : CollatzResearch.WordTrace tailWord_496732 prefixEnd_496732 75574006657557264434245 := by
  unfold tailWord_496732
  simp only [CollatzResearch.WordTrace]
  refine ⟨9058652218216136958322225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12078202957621515944429633 9058652218216136958322225)
  ·
    refine ⟨6793989163662102718741669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9058652218216136958322225 6793989163662102718741669)
    ·
      refine ⟨1273872968186644259764063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6793989163662102718741669 1273872968186644259764063)
      ·
        refine ⟨1910809452279966389646095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1273872968186644259764063 1910809452279966389646095)
        ·
          refine ⟨2866214178419949584469143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1910809452279966389646095 2866214178419949584469143)
          ·
            refine ⟨4299321267629924376703715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2866214178419949584469143 4299321267629924376703715)
            ·
              refine ⟨6448981901444886565055573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4299321267629924376703715 6448981901444886565055573)
              ·
                refine ⟨75574006657557264434245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6448981901444886565055573 75574006657557264434245)
                ·
                  rfl

theorem cell20_496732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 1, 8].length) (baseStart_496732 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_496732 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_496732 prefixEnd_496732 := by exact prefixLift 496732
  have htrace : WordTrace (prefixWord ++ tailWord_496732) baseStart_496732 baseEnd_496732 := by
    simpa [prefixWord, tailWord_496732, baseEnd_496732] using wordTrace_append hprefix tailTrace_496732
  have hstable : (prefixWord ++ tailWord_496732).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_496732).length < 2 ^ (prefixWord ++ tailWord_496732).sum := by decide
  have hdescent : baseEnd_496732 < baseStart_496732 := by decide
  rcases family_descends (prefixWord ++ tailWord_496732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_496818 : List Nat := [3, 2, 1, 1, 1, 4, 2, 4, 2]
def baseStart_496818 : Nat := 118140960795 + 496818 * 2 ^ 59
def prefixEnd_496818 : Nat := 4983230072969 + 3 ^ 40 * 496818 * 2
def baseEnd_496818 : Nat := 226761272716037716435717

theorem tailTrace_496818 : CollatzResearch.WordTrace tailWord_496818 prefixEnd_496818 226761272716037716435717 := by
  unfold tailWord_496818
  simp only [CollatzResearch.WordTrace]
  refine ⟨4530110278530177651068777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12080294076080473736183405 4530110278530177651068777)
  ·
    refine ⟨3397582708897633238301583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4530110278530177651068777 3397582708897633238301583)
    ·
      refine ⟨5096374063346449857452375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3397582708897633238301583 5096374063346449857452375)
      ·
        refine ⟨7644561095019674786178563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5096374063346449857452375 7644561095019674786178563)
        ·
          refine ⟨11466841642529512179267845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7644561095019674786178563 11466841642529512179267845)
          ·
            refine ⟨2150032807974283533612721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11466841642529512179267845 2150032807974283533612721)
            ·
              refine ⟨1612524605980712650209541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2150032807974283533612721 1612524605980712650209541)
              ·
                refine ⟨302348363621383621914289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1612524605980712650209541 302348363621383621914289)
                ·
                  refine ⟨226761272716037716435717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 302348363621383621914289 226761272716037716435717)
                  ·
                    rfl

theorem cell20_496818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 2, 4, 2].length) (baseStart_496818 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_496818 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_496818 prefixEnd_496818 := by exact prefixLift 496818
  have htrace : WordTrace (prefixWord ++ tailWord_496818) baseStart_496818 baseEnd_496818 := by
    simpa [prefixWord, tailWord_496818, baseEnd_496818] using wordTrace_append hprefix tailTrace_496818
  have hstable : (prefixWord ++ tailWord_496818).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_496818).length < 2 ^ (prefixWord ++ tailWord_496818).sum := by decide
  have hdescent : baseEnd_496818 < baseStart_496818 := by decide
  rcases family_descends (prefixWord ++ tailWord_496818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_496905 : List Nat := [1, 2, 1, 1, 3, 3, 1, 8]
def baseStart_496905 : Nat := 118140960795 + 496905 * 2 ^ 59
def prefixEnd_496905 : Nat := 4983230072969 + 3 ^ 40 * 496905 * 2
def baseEnd_496905 : Nat := 75600327295550693511787

theorem tailTrace_496905 : CollatzResearch.WordTrace tailWord_496905 prefixEnd_496905 75600327295550693511787 := by
  unfold tailWord_496905
  simp only [CollatzResearch.WordTrace]
  refine ⟨18123614264805524462692169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12082409509870349641794779 18123614264805524462692169)
  ·
    refine ⟨13592710698604143347019127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18123614264805524462692169 13592710698604143347019127)
    ·
      refine ⟨20389066047906215020528691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13592710698604143347019127 20389066047906215020528691)
      ·
        refine ⟨30583599071859322530793037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20389066047906215020528691 30583599071859322530793037)
        ·
          refine ⟨11468849651947245949047389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30583599071859322530793037 11468849651947245949047389)
          ·
            refine ⟨4300818619480217230892771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11468849651947245949047389 4300818619480217230892771)
            ·
              refine ⟨6451227929220325846339157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4300818619480217230892771 6451227929220325846339157)
              ·
                refine ⟨75600327295550693511787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6451227929220325846339157 75600327295550693511787)
                ·
                  rfl

theorem cell20_496905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 1, 8].length) (baseStart_496905 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_496905 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_496905 prefixEnd_496905 := by exact prefixLift 496905
  have htrace : WordTrace (prefixWord ++ tailWord_496905) baseStart_496905 baseEnd_496905 := by
    simpa [prefixWord, tailWord_496905, baseEnd_496905] using wordTrace_append hprefix tailTrace_496905
  have hstable : (prefixWord ++ tailWord_496905).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_496905).length < 2 ^ (prefixWord ++ tailWord_496905).sum := by decide
  have hdescent : baseEnd_496905 < baseStart_496905 := by decide
  rcases family_descends (prefixWord ++ tailWord_496905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_496925 : List Nat := [1, 4, 2, 3, 1, 2, 2, 2, 3]
def baseStart_496925 : Nat := 118140960795 + 496925 * 2 ^ 59
def prefixEnd_496925 : Nat := 4983230072969 + 3 ^ 40 * 496925 * 2
def baseEnd_496925 : Nat := 226810110431620899868613

theorem tailTrace_496925 : CollatzResearch.WordTrace tailWord_496925 prefixEnd_496925 226810110431620899868613 := by
  unfold tailWord_496925
  simp only [CollatzResearch.WordTrace]
  refine ⟨18124343724733067878420229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12082895816488711918946819 18124343724733067878420229)
  ·
    refine ⟨3398314448387450227203793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18124343724733067878420229 3398314448387450227203793)
    ·
      refine ⟨2548735836290587670402845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3398314448387450227203793 2548735836290587670402845)
      ·
        refine ⟨955775938608970376401067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2548735836290587670402845 955775938608970376401067)
        ·
          refine ⟨1433663907913455564601601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 955775938608970376401067 1433663907913455564601601)
          ·
            refine ⟨1075247930935091673451201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1433663907913455564601601 1075247930935091673451201)
            ·
              refine ⟨806435948201318755088401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1075247930935091673451201 806435948201318755088401)
              ·
                refine ⟨604826961150989066316301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 806435948201318755088401 604826961150989066316301)
                ·
                  refine ⟨226810110431620899868613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 604826961150989066316301 226810110431620899868613)
                  ·
                    rfl

theorem cell20_496925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 2, 2, 2, 3].length) (baseStart_496925 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_496925 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_496925 prefixEnd_496925 := by exact prefixLift 496925
  have htrace : WordTrace (prefixWord ++ tailWord_496925) baseStart_496925 baseEnd_496925 := by
    simpa [prefixWord, tailWord_496925, baseEnd_496925] using wordTrace_append hprefix tailTrace_496925
  have hstable : (prefixWord ++ tailWord_496925).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_496925).length < 2 ^ (prefixWord ++ tailWord_496925).sum := by decide
  have hdescent : baseEnd_496925 < baseStart_496925 := by decide
  rcases family_descends (prefixWord ++ tailWord_496925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_496928 : List Nat := [2, 1, 1, 5, 3, 2, 2, 2, 2]
def baseStart_496928 : Nat := 118140960795 + 496928 * 2 ^ 59
def prefixEnd_496928 : Nat := 4983230072969 + 3 ^ 40 * 496928 * 2
def baseEnd_496928 : Nat := 226811479713366222768601

theorem tailTrace_496928 : CollatzResearch.WordTrace tailWord_496928 prefixEnd_496928 226811479713366222768601 := by
  unfold tailWord_496928
  simp only [CollatzResearch.WordTrace]
  refine ⟨9062226571861099695389719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12082968762481466260519625 9062226571861099695389719)
  ·
    refine ⟨13593339857791649543084579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9062226571861099695389719 13593339857791649543084579)
    ·
      refine ⟨20390009786687474314626869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13593339857791649543084579 20390009786687474314626869)
      ·
        refine ⟨1911563417501950716996269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 20390009786687474314626869 1911563417501950716996269)
        ·
          refine ⟨716836281563231518873601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1911563417501950716996269 716836281563231518873601)
          ·
            refine ⟨537627211172423639155201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 716836281563231518873601 537627211172423639155201)
            ·
              refine ⟨403220408379317729366401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 537627211172423639155201 403220408379317729366401)
              ·
                refine ⟨302415306284488297024801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 403220408379317729366401 302415306284488297024801)
                ·
                  refine ⟨226811479713366222768601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 302415306284488297024801 226811479713366222768601)
                  ·
                    rfl

theorem cell20_496928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 2, 2, 2, 2].length) (baseStart_496928 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_496928 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_496928 prefixEnd_496928 := by exact prefixLift 496928
  have htrace : WordTrace (prefixWord ++ tailWord_496928) baseStart_496928 baseEnd_496928 := by
    simpa [prefixWord, tailWord_496928, baseEnd_496928] using wordTrace_append hprefix tailTrace_496928
  have hstable : (prefixWord ++ tailWord_496928).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_496928).length < 2 ^ (prefixWord ++ tailWord_496928).sum := by decide
  have hdescent : baseEnd_496928 < baseStart_496928 := by decide
  rcases family_descends (prefixWord ++ tailWord_496928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_496932 : List Nat := [2, 3, 1, 3, 1, 1, 3, 4, 2]
def baseStart_496932 : Nat := 118140960795 + 496932 * 2 ^ 59
def prefixEnd_496932 : Nat := 4983230072969 + 3 ^ 40 * 496932 * 2
def baseEnd_496932 : Nat := 226813305422359986635251

theorem tailTrace_496932 : CollatzResearch.WordTrace tailWord_496932 prefixEnd_496932 226813305422359986635251 := by
  unfold tailWord_496932
  simp only [CollatzResearch.WordTrace]
  refine ⟨9062299517853854036962525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12083066023805138715950033 9062299517853854036962525)
  ·
    refine ⟨3398362319195195263860947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9062299517853854036962525 3398362319195195263860947)
    ·
      refine ⟨5097543478792792895791421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3398362319195195263860947 5097543478792792895791421)
      ·
        refine ⟨1911578804547297335921783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5097543478792792895791421 1911578804547297335921783)
        ·
          refine ⟨2867368206820946003882675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1911578804547297335921783 2867368206820946003882675)
          ·
            refine ⟨4301052310231419005824013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2867368206820946003882675 4301052310231419005824013)
            ·
              refine ⟨1612894616336782127184005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4301052310231419005824013 1612894616336782127184005)
              ·
                refine ⟨302417740563146648847001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1612894616336782127184005 302417740563146648847001)
                ·
                  refine ⟨226813305422359986635251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 302417740563146648847001 226813305422359986635251)
                  ·
                    rfl

theorem cell20_496932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 3, 4, 2].length) (baseStart_496932 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_496932 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_496932 prefixEnd_496932 := by exact prefixLift 496932
  have htrace : WordTrace (prefixWord ++ tailWord_496932) baseStart_496932 baseEnd_496932 := by
    simpa [prefixWord, tailWord_496932, baseEnd_496932] using wordTrace_append hprefix tailTrace_496932
  have hstable : (prefixWord ++ tailWord_496932).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_496932).length < 2 ^ (prefixWord ++ tailWord_496932).sum := by decide
  have hdescent : baseEnd_496932 < baseStart_496932 := by decide
  rcases family_descends (prefixWord ++ tailWord_496932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_496946 : List Nat := [3, 2, 1, 1, 4, 1, 2, 3, 3]
def baseStart_496946 : Nat := 118140960795 + 496946 * 2 ^ 59
def prefixEnd_496946 : Nat := 4983230072969 + 3 ^ 40 * 496946 * 2
def baseEnd_496946 : Nat := 226819695403838160168527

theorem tailTrace_496946 : CollatzResearch.WordTrace tailWord_496946 prefixEnd_496946 226819695403838160168527 := by
  unfold tailWord_496946
  simp only [CollatzResearch.WordTrace]
  refine ⟨4531277414414247116233673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12083406438437992309956461 4531277414414247116233673)
  ·
    refine ⟨3398458060810685337175255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4531277414414247116233673 3398458060810685337175255)
    ·
      refine ⟨5097687091216028005762883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3398458060810685337175255 5097687091216028005762883)
      ·
        refine ⟨7646530636824042008644325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5097687091216028005762883 7646530636824042008644325)
        ·
          refine ⟨1433724494404507876620811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7646530636824042008644325 1433724494404507876620811)
          ·
            refine ⟨2150586741606761814931217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1433724494404507876620811 2150586741606761814931217)
            ·
              refine ⟨1612940056205071361198413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2150586741606761814931217 1612940056205071361198413)
              ·
                refine ⟨604852521076901760449405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1612940056205071361198413 604852521076901760449405)
                ·
                  refine ⟨226819695403838160168527, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 604852521076901760449405 226819695403838160168527)
                  ·
                    rfl

theorem cell20_496946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 2, 3, 3].length) (baseStart_496946 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_496946 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_496946 prefixEnd_496946 := by exact prefixLift 496946
  have htrace : WordTrace (prefixWord ++ tailWord_496946) baseStart_496946 baseEnd_496946 := by
    simpa [prefixWord, tailWord_496946, baseEnd_496946] using wordTrace_append hprefix tailTrace_496946
  have hstable : (prefixWord ++ tailWord_496946).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_496946).length < 2 ^ (prefixWord ++ tailWord_496946).sum := by decide
  have hdescent : baseEnd_496946 < baseStart_496946 := by decide
  rcases family_descends (prefixWord ++ tailWord_496946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_496960 : List Nat := [2, 1, 1, 2, 2, 1, 7, 4]
def baseStart_496960 : Nat := 118140960795 + 496960 * 2 ^ 59
def prefixEnd_496960 : Nat := 4983230072969 + 3 ^ 40 * 496960 * 2
def baseEnd_496960 : Nat := 75608695128438777900601

theorem tailTrace_496960 : CollatzResearch.WordTrace tailWord_496960 prefixEnd_496960 75608695128438777900601 := by
  unfold tailWord_496960
  simp only [CollatzResearch.WordTrace]
  refine ⟨9062810139803134427972167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12083746853070845903962889 9062810139803134427972167)
  ·
    refine ⟨13594215209704701641958251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9062810139803134427972167 13594215209704701641958251)
    ·
      refine ⟨20391322814557052462937377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13594215209704701641958251 20391322814557052462937377)
      ·
        refine ⟨15293492110917789347203033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20391322814557052462937377 15293492110917789347203033)
        ·
          refine ⟨11470119083188342010402275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15293492110917789347203033 11470119083188342010402275)
          ·
            refine ⟨17205178624782513015603413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11470119083188342010402275 17205178624782513015603413)
            ·
              refine ⟨403246374018340148803205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 17205178624782513015603413 403246374018340148803205)
              ·
                refine ⟨75608695128438777900601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 403246374018340148803205 75608695128438777900601)
                ·
                  rfl

theorem cell20_496960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 7, 4].length) (baseStart_496960 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_496960 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_496960 prefixEnd_496960 := by exact prefixLift 496960
  have htrace : WordTrace (prefixWord ++ tailWord_496960) baseStart_496960 baseEnd_496960 := by
    simpa [prefixWord, tailWord_496960, baseEnd_496960] using wordTrace_append hprefix tailTrace_496960
  have hstable : (prefixWord ++ tailWord_496960).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_496960).length < 2 ^ (prefixWord ++ tailWord_496960).sum := by decide
  have hdescent : baseEnd_496960 < baseStart_496960 := by decide
  rcases family_descends (prefixWord ++ tailWord_496960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_496974 : List Nat := [4, 1, 1, 1, 1, 1, 3, 2, 6]
def baseStart_496974 : Nat := 118140960795 + 496974 * 2 ^ 59
def prefixEnd_496974 : Nat := 4983230072969 + 3 ^ 40 * 496974 * 2
def baseEnd_496974 : Nat := 226832475366794507235079

theorem tailTrace_496974 : CollatzResearch.WordTrace tailWord_496974 prefixEnd_496974 226832475366794507235079 := by
  unfold tailWord_496974
  simp only [CollatzResearch.WordTrace]
  refine ⟨2265766362694443655869247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12084087267703699497969317 2265766362694443655869247)
  ·
    refine ⟨3398649544041665483803871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2265766362694443655869247 3398649544041665483803871)
    ·
      refine ⟨5097974316062498225705807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3398649544041665483803871 5097974316062498225705807)
      ·
        refine ⟨7646961474093747338558711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5097974316062498225705807 7646961474093747338558711)
        ·
          refine ⟨11470442211140621007838067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7646961474093747338558711 11470442211140621007838067)
          ·
            refine ⟨17205663316710931511757101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11470442211140621007838067 17205663316710931511757101)
            ·
              refine ⟨6452123743766599316908913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17205663316710931511757101 6452123743766599316908913)
              ·
                refine ⟨4839092807824949487681685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6452123743766599316908913 4839092807824949487681685)
                ·
                  refine ⟨226832475366794507235079, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4839092807824949487681685 226832475366794507235079)
                  ·
                    rfl

theorem cell20_496974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 3, 2, 6].length) (baseStart_496974 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_496974 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_496974 prefixEnd_496974 := by exact prefixLift 496974
  have htrace : WordTrace (prefixWord ++ tailWord_496974) baseStart_496974 baseEnd_496974 := by
    simpa [prefixWord, tailWord_496974, baseEnd_496974] using wordTrace_append hprefix tailTrace_496974
  have hstable : (prefixWord ++ tailWord_496974).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_496974).length < 2 ^ (prefixWord ++ tailWord_496974).sum := by decide
  have hdescent : baseEnd_496974 < baseStart_496974 := by decide
  rcases family_descends (prefixWord ++ tailWord_496974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_497019 : List Nat := [1, 1, 1, 1, 1, 6, 3, 6]
def baseStart_497019 : Nat := 118140960795 + 497019 * 2 ^ 59
def prefixEnd_497019 : Nat := 4983230072969 + 3 ^ 40 * 497019 * 2
def baseEnd_497019 : Nat := 75617671530991450244965

theorem tailTrace_497019 : CollatzResearch.WordTrace tailWord_497019 prefixEnd_497019 75617671530991450244965 := by
  unfold tailWord_497019
  simp only [CollatzResearch.WordTrace]
  refine ⟨18127772186392521932342111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12085181457595014621561407 18127772186392521932342111)
  ·
    refine ⟨27191658279588782898513167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18127772186392521932342111 27191658279588782898513167)
    ·
      refine ⟨40787487419383174347769751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27191658279588782898513167 40787487419383174347769751)
      ·
        refine ⟨61181231129074761521654627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40787487419383174347769751 61181231129074761521654627)
        ·
          refine ⟨91771846693612142282481941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61181231129074761521654627 91771846693612142282481941)
          ·
            refine ⟨4301805313763069169491341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 91771846693612142282481941 4301805313763069169491341)
            ·
              refine ⟨1613176992661150938559253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4301805313763069169491341 1613176992661150938559253)
              ·
                refine ⟨75617671530991450244965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1613176992661150938559253 75617671530991450244965)
                ·
                  rfl

theorem cell20_497019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 3, 6].length) (baseStart_497019 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_497019 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_497019 prefixEnd_497019 := by exact prefixLift 497019
  have htrace : WordTrace (prefixWord ++ tailWord_497019) baseStart_497019 baseEnd_497019 := by
    simpa [prefixWord, tailWord_497019, baseEnd_497019] using wordTrace_append hprefix tailTrace_497019
  have hstable : (prefixWord ++ tailWord_497019).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_497019).length < 2 ^ (prefixWord ++ tailWord_497019).sum := by decide
  have hdescent : baseEnd_497019 < baseStart_497019 := by decide
  rcases family_descends (prefixWord ++ tailWord_497019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_497042 : List Nat := [3, 2, 3, 3, 2, 1, 1, 1, 4]
def baseStart_497042 : Nat := 118140960795 + 497042 * 2 ^ 59
def prefixEnd_497042 : Nat := 4983230072969 + 3 ^ 40 * 497042 * 2
def baseEnd_497042 : Nat := 226863512419688492968135

theorem tailTrace_497042 : CollatzResearch.WordTrace tailWord_497042 prefixEnd_497042 226863512419688492968135 := by
  unfold tailWord_497042
  simp only [CollatzResearch.WordTrace]
  refine ⟨4532152766327299215107345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12085740710206131240286253 4532152766327299215107345)
  ·
    refine ⟨3399114574745474411330509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4532152766327299215107345 3399114574745474411330509)
    ·
      refine ⟨1274667965529552904248941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3399114574745474411330509 1274667965529552904248941)
      ·
        refine ⟨478000487073582339093353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1274667965529552904248941 478000487073582339093353)
        ·
          refine ⟨358500365305186754320015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 478000487073582339093353 358500365305186754320015)
          ·
            refine ⟨537750547957780131480023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 358500365305186754320015 537750547957780131480023)
            ·
              refine ⟨806625821936670197220035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 537750547957780131480023 806625821936670197220035)
              ·
                refine ⟨1209938732905005295830053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 806625821936670197220035 1209938732905005295830053)
                ·
                  refine ⟨226863512419688492968135, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1209938732905005295830053 226863512419688492968135)
                  ·
                    rfl

theorem cell20_497042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 2, 1, 1, 1, 4].length) (baseStart_497042 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_497042 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_497042 prefixEnd_497042 := by exact prefixLift 497042
  have htrace : WordTrace (prefixWord ++ tailWord_497042) baseStart_497042 baseEnd_497042 := by
    simpa [prefixWord, tailWord_497042, baseEnd_497042] using wordTrace_append hprefix tailTrace_497042
  have hstable : (prefixWord ++ tailWord_497042).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_497042).length < 2 ^ (prefixWord ++ tailWord_497042).sum := by decide
  have hdescent : baseEnd_497042 < baseStart_497042 := by decide
  rcases family_descends (prefixWord ++ tailWord_497042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_497090 : List Nat := [3, 5, 2, 1, 1, 1, 2, 2, 3]
def baseStart_497090 : Nat := 118140960795 + 497090 * 2 ^ 59
def prefixEnd_497090 : Nat := 4983230072969 + 3 ^ 40 * 497090 * 2
def baseEnd_497090 : Nat := 226885420927613659367939

theorem tailTrace_497090 : CollatzResearch.WordTrace tailWord_497090 prefixEnd_497090 226885420927613659367939 := by
  unfold tailWord_497090
  simp only [CollatzResearch.WordTrace]
  refine ⟨4532590442283825264544181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12086907846090200705451149 4532590442283825264544181)
  ·
    refine ⟨424930353964108618551017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 4532590442283825264544181 424930353964108618551017)
    ·
      refine ⟨318697765473081463913263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 424930353964108618551017 318697765473081463913263)
      ·
        refine ⟨478046648209622195869895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 318697765473081463913263 478046648209622195869895)
        ·
          refine ⟨717069972314433293804843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 478046648209622195869895 717069972314433293804843)
          ·
            refine ⟨1075604958471649940707265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 717069972314433293804843 1075604958471649940707265)
            ·
              refine ⟨806703718853737455530449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1075604958471649940707265 806703718853737455530449)
              ·
                refine ⟨605027789140303091647837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 806703718853737455530449 605027789140303091647837)
                ·
                  refine ⟨226885420927613659367939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 605027789140303091647837 226885420927613659367939)
                  ·
                    rfl

theorem cell20_497090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 1, 2, 2, 3].length) (baseStart_497090 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_497090 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_497090 prefixEnd_497090 := by exact prefixLift 497090
  have htrace : WordTrace (prefixWord ++ tailWord_497090) baseStart_497090 baseEnd_497090 := by
    simpa [prefixWord, tailWord_497090, baseEnd_497090] using wordTrace_append hprefix tailTrace_497090
  have hstable : (prefixWord ++ tailWord_497090).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_497090).length < 2 ^ (prefixWord ++ tailWord_497090).sum := by decide
  have hdescent : baseEnd_497090 < baseStart_497090 := by decide
  rcases family_descends (prefixWord ++ tailWord_497090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_497098 : List Nat := [3, 1, 2, 1, 2, 4, 2, 2, 3]
def baseStart_497098 : Nat := 118140960795 + 497098 * 2 ^ 59
def prefixEnd_497098 : Nat := 4983230072969 + 3 ^ 40 * 497098 * 2
def baseEnd_497098 : Nat := 226889072345601187101239

theorem tailTrace_497098 : CollatzResearch.WordTrace tailWord_497098 prefixEnd_497098 226889072345601187101239 := by
  unfold tailWord_497098
  simp only [CollatzResearch.WordTrace]
  refine ⟨4532663388276579606116987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12087102368737545616311965 4532663388276579606116987)
  ·
    refine ⟨6798995082414869409175481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4532663388276579606116987 6798995082414869409175481)
    ·
      refine ⟨5099246311811152056881611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6798995082414869409175481 5099246311811152056881611)
      ·
        refine ⟨7648869467716728085322417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5099246311811152056881611 7648869467716728085322417)
        ·
          refine ⟨5736652100787546063991813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7648869467716728085322417 5736652100787546063991813)
          ·
            refine ⟨1075622268897664886998465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5736652100787546063991813 1075622268897664886998465)
            ·
              refine ⟨806716701673248665248849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1075622268897664886998465 806716701673248665248849)
              ·
                refine ⟨605037526254936498936637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 806716701673248665248849 605037526254936498936637)
                ·
                  refine ⟨226889072345601187101239, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 605037526254936498936637 226889072345601187101239)
                  ·
                    rfl

theorem cell20_497098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 4, 2, 2, 3].length) (baseStart_497098 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_497098 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_497098 prefixEnd_497098 := by exact prefixLift 497098
  have htrace : WordTrace (prefixWord ++ tailWord_497098) baseStart_497098 baseEnd_497098 := by
    simpa [prefixWord, tailWord_497098, baseEnd_497098] using wordTrace_append hprefix tailTrace_497098
  have hstable : (prefixWord ++ tailWord_497098).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_497098).length < 2 ^ (prefixWord ++ tailWord_497098).sum := by decide
  have hdescent : baseEnd_497098 < baseStart_497098 := by decide
  rcases family_descends (prefixWord ++ tailWord_497098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_497108 : List Nat := [2, 4, 1, 2, 4, 1, 1, 5]
def baseStart_497108 : Nat := 118140960795 + 497108 * 2 ^ 59
def prefixEnd_497108 : Nat := 4983230072969 + 3 ^ 40 * 497108 * 2
def baseEnd_497108 : Nat := 75631212206028532255955

theorem tailTrace_497108 : CollatzResearch.WordTrace tailWord_497108 prefixEnd_497108 75631212206028532255955 := by
  unfold tailWord_497108
  simp only [CollatzResearch.WordTrace]
  refine ⟨9065509141535045066165989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12087345522046726754887985 9065509141535045066165989)
  ·
    refine ⟨1699782964037820949906123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9065509141535045066165989 1699782964037820949906123)
    ·
      refine ⟨2549674446056731424859185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1699782964037820949906123 2549674446056731424859185)
      ·
        refine ⟨1912255834542548568644389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2549674446056731424859185 1912255834542548568644389)
        ·
          refine ⟨358547968976727856620823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1912255834542548568644389 358547968976727856620823)
          ·
            refine ⟨537821953465091784931235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 358547968976727856620823 537821953465091784931235)
            ·
              refine ⟨806732930197637677396853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 537821953465091784931235 806732930197637677396853)
              ·
                refine ⟨75631212206028532255955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 806732930197637677396853 75631212206028532255955)
                ·
                  rfl

theorem cell20_497108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 4, 1, 1, 5].length) (baseStart_497108 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_497108 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_497108 prefixEnd_497108 := by exact prefixLift 497108
  have htrace : WordTrace (prefixWord ++ tailWord_497108) baseStart_497108 baseEnd_497108 := by
    simpa [prefixWord, tailWord_497108, baseEnd_497108] using wordTrace_append hprefix tailTrace_497108
  have hstable : (prefixWord ++ tailWord_497108).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_497108).length < 2 ^ (prefixWord ++ tailWord_497108).sum := by decide
  have hdescent : baseEnd_497108 < baseStart_497108 := by decide
  rcases family_descends (prefixWord ++ tailWord_497108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_497119 : List Nat := [1, 1, 2, 3, 3, 1, 1, 5, 3]
def baseStart_497119 : Nat := 118140960795 + 497119 * 2 ^ 59
def prefixEnd_497119 : Nat := 4983230072969 + 3 ^ 40 * 497119 * 2
def baseEnd_497119 : Nat := 226898657317818447401153

theorem tailTrace_497119 : CollatzResearch.WordTrace tailWord_497119 prefixEnd_497119 226898657317818447401153 := by
  unfold tailWord_497119
  simp only [CollatzResearch.WordTrace]
  refine ⟨18131419486030239010982411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12087612990686826007321607 18131419486030239010982411)
  ·
    refine ⟨27197129229045358516473617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18131419486030239010982411 27197129229045358516473617)
    ·
      refine ⟨20397846921784018887355213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27197129229045358516473617 20397846921784018887355213)
      ·
        refine ⟨7649192595669007082758205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20397846921784018887355213 7649192595669007082758205)
        ·
          refine ⟨2868447223375877656034327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7649192595669007082758205 2868447223375877656034327)
          ·
            refine ⟨4302670835063816484051491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2868447223375877656034327 4302670835063816484051491)
            ·
              refine ⟨6454006252595724726077237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4302670835063816484051491 6454006252595724726077237)
              ·
                refine ⟨605063086180849193069741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6454006252595724726077237 605063086180849193069741)
                ·
                  refine ⟨226898657317818447401153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 605063086180849193069741 226898657317818447401153)
                  ·
                    rfl

theorem cell20_497119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 1, 5, 3].length) (baseStart_497119 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_497119 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_497119 prefixEnd_497119 := by exact prefixLift 497119
  have htrace : WordTrace (prefixWord ++ tailWord_497119) baseStart_497119 baseEnd_497119 := by
    simpa [prefixWord, tailWord_497119, baseEnd_497119] using wordTrace_append hprefix tailTrace_497119
  have hstable : (prefixWord ++ tailWord_497119).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_497119).length < 2 ^ (prefixWord ++ tailWord_497119).sum := by decide
  have hdescent : baseEnd_497119 < baseStart_497119 := by decide
  rcases family_descends (prefixWord ++ tailWord_497119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_497153 : List Nat := [1, 2, 4, 1, 4, 2, 1, 2, 3]
def baseStart_497153 : Nat := 118140960795 + 497153 * 2 ^ 59
def prefixEnd_497153 : Nat := 4983230072969 + 3 ^ 40 * 497153 * 2
def baseEnd_497153 : Nat := 226914175844265440267681

theorem tailTrace_497153 : CollatzResearch.WordTrace tailWord_497153 prefixEnd_497153 226914175844265440267681 := by
  unfold tailWord_497153
  simp only [CollatzResearch.WordTrace]
  refine ⟨18132659567907062817720113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12088439711938041878480075 18132659567907062817720113)
  ·
    refine ⟨13599494675930297113290085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18132659567907062817720113 13599494675930297113290085)
    ·
      refine ⟨2549905251736930708741891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13599494675930297113290085 2549905251736930708741891)
      ·
        refine ⟨3824857877605396063112837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2549905251736930708741891 3824857877605396063112837)
        ·
          refine ⟨717160852051011761833657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3824857877605396063112837 717160852051011761833657)
          ·
            refine ⟨537870639038258821375243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 717160852051011761833657 537870639038258821375243)
            ·
              refine ⟨806805958557388232062865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 537870639038258821375243 806805958557388232062865)
              ·
                refine ⟨605104468918041174047149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 806805958557388232062865 605104468918041174047149)
                ·
                  refine ⟨226914175844265440267681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 605104468918041174047149 226914175844265440267681)
                  ·
                    rfl

theorem cell20_497153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 2, 1, 2, 3].length) (baseStart_497153 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_497153 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_497153 prefixEnd_497153 := by exact prefixLift 497153
  have htrace : WordTrace (prefixWord ++ tailWord_497153) baseStart_497153 baseEnd_497153 := by
    simpa [prefixWord, tailWord_497153, baseEnd_497153] using wordTrace_append hprefix tailTrace_497153
  have hstable : (prefixWord ++ tailWord_497153).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_497153).length < 2 ^ (prefixWord ++ tailWord_497153).sum := by decide
  have hdescent : baseEnd_497153 < baseStart_497153 := by decide
  rcases family_descends (prefixWord ++ tailWord_497153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_497209 : List Nat := [1, 2, 1, 5, 1, 2, 8]
def baseStart_497209 : Nat := 118140960795 + 497209 * 2 ^ 59
def prefixEnd_497209 : Nat := 4983230072969 + 3 ^ 40 * 497209 * 2
def baseEnd_497209 : Nat := 25215526196686459377865

theorem tailTrace_497209 : CollatzResearch.WordTrace tailWord_497209 prefixEnd_497209 25215526196686459377865 := by
  unfold tailWord_497209
  simp only [CollatzResearch.WordTrace]
  refine ⟨18134702055704184381758681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12089801370469456254505787 18134702055704184381758681)
  ·
    refine ⟨13601026541778138286319011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18134702055704184381758681 13601026541778138286319011)
    ·
      refine ⟨20401539812667207429478517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13601026541778138286319011 20401539812667207429478517)
      ·
        refine ⟨1912644357437550696513611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 20401539812667207429478517 1912644357437550696513611)
        ·
          refine ⟨2868966536156326044770417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1912644357437550696513611 2868966536156326044770417)
          ·
            refine ⟨2151724902117244533577813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2868966536156326044770417 2151724902117244533577813)
            ·
              refine ⟨25215526196686459377865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2151724902117244533577813 25215526196686459377865)
              ·
                rfl

theorem cell20_497209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 8].length) (baseStart_497209 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_497209 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_497209 prefixEnd_497209 := by exact prefixLift 497209
  have htrace : WordTrace (prefixWord ++ tailWord_497209) baseStart_497209 baseEnd_497209 := by
    simpa [prefixWord, tailWord_497209, baseEnd_497209] using wordTrace_append hprefix tailTrace_497209
  have hstable : (prefixWord ++ tailWord_497209).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_497209).length < 2 ^ (prefixWord ++ tailWord_497209).sum := by decide
  have hdescent : baseEnd_497209 < baseStart_497209 := by decide
  rcases family_descends (prefixWord ++ tailWord_497209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_497222 : List Nat := [6, 1, 1, 1, 3, 1, 2, 5]
def baseStart_497222 : Nat := 118140960795 + 497222 * 2 ^ 59
def prefixEnd_497222 : Nat := 4983230072969 + 3 ^ 40 * 497222 * 2
def baseEnd_497222 : Nat := 75648556441469288989133

theorem tailTrace_497222 : CollatzResearch.WordTrace tailWord_497222 prefixEnd_497222 75648556441469288989133 := by
  unfold tailWord_497222
  simp only [CollatzResearch.WordTrace]
  refine ⟨566724256395533987561935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 12090117469771391734654613 566724256395533987561935)
  ·
    refine ⟨850086384593300981342903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 566724256395533987561935 850086384593300981342903)
    ·
      refine ⟨1275129576889951472014355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 850086384593300981342903 1275129576889951472014355)
      ·
        refine ⟨1912694365334927208021533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1275129576889951472014355 1912694365334927208021533)
        ·
          refine ⟨717260387000597703008075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1912694365334927208021533 717260387000597703008075)
          ·
            refine ⟨1075890580500896554512113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 717260387000597703008075 1075890580500896554512113)
            ·
              refine ⟨806917935375672415884085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1075890580500896554512113 806917935375672415884085)
              ·
                refine ⟨75648556441469288989133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 806917935375672415884085 75648556441469288989133)
                ·
                  rfl

theorem cell20_497222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 1, 2, 5].length) (baseStart_497222 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_497222 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_497222 prefixEnd_497222 := by exact prefixLift 497222
  have htrace : WordTrace (prefixWord ++ tailWord_497222) baseStart_497222 baseEnd_497222 := by
    simpa [prefixWord, tailWord_497222, baseEnd_497222] using wordTrace_append hprefix tailTrace_497222
  have hstable : (prefixWord ++ tailWord_497222).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_497222).length < 2 ^ (prefixWord ++ tailWord_497222).sum := by decide
  have hdescent : baseEnd_497222 < baseStart_497222 := by decide
  rcases family_descends (prefixWord ++ tailWord_497222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_497229 : List Nat := [1, 6, 1, 1, 3, 1, 1, 3, 3]
def baseStart_497229 : Nat := 118140960795 + 497229 * 2 ^ 59
def prefixEnd_497229 : Nat := 4983230072969 + 3 ^ 40 * 497229 * 2
def baseEnd_497229 : Nat := 226948864315146953734037

theorem tailTrace_497229 : CollatzResearch.WordTrace tailWord_497229 prefixEnd_497229 226948864315146953734037 := by
  unfold tailWord_497229
  simp only [CollatzResearch.WordTrace]
  refine ⟨18135431515631727797486741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12090287677087818531657827 18135431515631727797486741)
  ·
    refine ⟨850098352295237240507191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 18135431515631727797486741 850098352295237240507191)
    ·
      refine ⟨1275147528442855860760787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 850098352295237240507191 1275147528442855860760787)
      ·
        refine ⟨1912721292664283791141181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1275147528442855860760787 1912721292664283791141181)
        ·
          refine ⟨717270484749106421677943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1912721292664283791141181 717270484749106421677943)
          ·
            refine ⟨1075905727123659632516915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 717270484749106421677943 1075905727123659632516915)
            ·
              refine ⟨1613858590685489448775373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1075905727123659632516915 1613858590685489448775373)
              ·
                refine ⟨605196971507058543290765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1613858590685489448775373 605196971507058543290765)
                ·
                  refine ⟨226948864315146953734037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 605196971507058543290765 226948864315146953734037)
                  ·
                    rfl

theorem cell20_497229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 1, 1, 3, 3].length) (baseStart_497229 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_497229 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_497229 prefixEnd_497229 := by exact prefixLift 497229
  have htrace : WordTrace (prefixWord ++ tailWord_497229) baseStart_497229 baseEnd_497229 := by
    simpa [prefixWord, tailWord_497229, baseEnd_497229] using wordTrace_append hprefix tailTrace_497229
  have hstable : (prefixWord ++ tailWord_497229).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_497229).length < 2 ^ (prefixWord ++ tailWord_497229).sum := by decide
  have hdescent : baseEnd_497229 < baseStart_497229 := by decide
  rcases family_descends (prefixWord ++ tailWord_497229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_497233 : List Nat := [1, 2, 2, 1, 3, 2, 3, 3, 3]
def baseStart_497233 : Nat := 118140960795 + 497233 * 2 ^ 59
def prefixEnd_497233 : Nat := 4983230072969 + 3 ^ 40 * 497233 * 2
def baseEnd_497233 : Nat := 226950690024140717600687

theorem tailTrace_497233 : CollatzResearch.WordTrace tailWord_497233 prefixEnd_497233 226950690024140717600687 := by
  unfold tailWord_497233
  simp only [CollatzResearch.WordTrace]
  refine ⟨18135577407617236480632353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12090384938411490987088235 18135577407617236480632353)
  ·
    refine ⟨13601683055712927360474265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18135577407617236480632353 13601683055712927360474265)
    ·
      refine ⟨10201262291784695520355699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13601683055712927360474265 10201262291784695520355699)
      ·
        refine ⟨15301893437677043280533549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10201262291784695520355699 15301893437677043280533549)
        ·
          refine ⟨5738210039128891230200081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15301893437677043280533549 5738210039128891230200081)
          ·
            refine ⟨4303657529346668422650061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5738210039128891230200081 4303657529346668422650061)
            ·
              refine ⟨1613871573505000658493773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4303657529346668422650061 1613871573505000658493773)
              ·
                refine ⟨605201840064375246935165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1613871573505000658493773 605201840064375246935165)
                ·
                  refine ⟨226950690024140717600687, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 605201840064375246935165 226950690024140717600687)
                  ·
                    rfl

theorem cell20_497233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 3, 3, 3].length) (baseStart_497233 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_497233 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_497233 prefixEnd_497233 := by exact prefixLift 497233
  have htrace : WordTrace (prefixWord ++ tailWord_497233) baseStart_497233 baseEnd_497233 := by
    simpa [prefixWord, tailWord_497233, baseEnd_497233] using wordTrace_append hprefix tailTrace_497233
  have hstable : (prefixWord ++ tailWord_497233).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_497233).length < 2 ^ (prefixWord ++ tailWord_497233).sum := by decide
  have hdescent : baseEnd_497233 < baseStart_497233 := by decide
  rcases family_descends (prefixWord ++ tailWord_497233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_497270 : List Nat := [5, 1, 1, 2, 2, 3, 2, 2, 2]
def baseStart_497270 : Nat := 118140960795 + 497270 * 2 ^ 59
def prefixEnd_497270 : Nat := 4983230072969 + 3 ^ 40 * 497270 * 2
def baseEnd_497270 : Nat := 226967577832333033367203

theorem tailTrace_497270 : CollatzResearch.WordTrace tailWord_497270 prefixEnd_497270 226967577832333033367203 := by
  unfold tailWord_497270
  simp only [CollatzResearch.WordTrace]
  refine ⟨1133557931780199487483079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 12091284605655461199819509 1133557931780199487483079)
  ·
    refine ⟨1700336897670299231224619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1133557931780199487483079 1700336897670299231224619)
    ·
      refine ⟨2550505346505448846836929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1700336897670299231224619 2550505346505448846836929)
      ·
        refine ⟨1912879009879086635127697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2550505346505448846836929 1912879009879086635127697)
        ·
          refine ⟨1434659257409314976345773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1912879009879086635127697 1434659257409314976345773)
          ·
            refine ⟨537997221528493116129665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1434659257409314976345773 537997221528493116129665)
            ·
              refine ⟨403497916146369837097249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 537997221528493116129665 403497916146369837097249)
              ·
                refine ⟨302623437109777377822937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 403497916146369837097249 302623437109777377822937)
                ·
                  refine ⟨226967577832333033367203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 302623437109777377822937 226967577832333033367203)
                  ·
                    rfl

theorem cell20_497270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 3, 2, 2, 2].length) (baseStart_497270 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_497270 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_497270 prefixEnd_497270 := by exact prefixLift 497270
  have htrace : WordTrace (prefixWord ++ tailWord_497270) baseStart_497270 baseEnd_497270 := by
    simpa [prefixWord, tailWord_497270, baseEnd_497270] using wordTrace_append hprefix tailTrace_497270
  have hstable : (prefixWord ++ tailWord_497270).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_497270).length < 2 ^ (prefixWord ++ tailWord_497270).sum := by decide
  have hdescent : baseEnd_497270 < baseStart_497270 := by decide
  rcases family_descends (prefixWord ++ tailWord_497270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_497312 : List Nat := [2, 1, 1, 4, 3, 2, 2, 3, 2]
def baseStart_497312 : Nat := 118140960795 + 497312 * 2 ^ 59
def prefixEnd_497312 : Nat := 4983230072969 + 3 ^ 40 * 497312 * 2
def baseEnd_497312 : Nat := 226986747776767553967031

theorem tailTrace_497312 : CollatzResearch.WordTrace tailWord_497312 prefixEnd_497312 226986747776767553967031 := by
  unfold tailWord_497312
  simp only [CollatzResearch.WordTrace]
  refine ⟨9069229387165516486379095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12092305849554021981838793 9069229387165516486379095)
  ·
    refine ⟨13603844080748274729568643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9069229387165516486379095 13603844080748274729568643)
    ·
      refine ⟨20405766121122412094352965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13603844080748274729568643 20405766121122412094352965)
      ·
        refine ⟨3826081147710452267691181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20405766121122412094352965 3826081147710452267691181)
        ·
          refine ⟨1434780430391419600384193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3826081147710452267691181 1434780430391419600384193)
          ·
            refine ⟨1076085322793564700288145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1434780430391419600384193 1076085322793564700288145)
            ·
              refine ⟨807063992095173525216109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1076085322793564700288145 807063992095173525216109)
              ·
                refine ⟨302648997035690071956041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 807063992095173525216109 302648997035690071956041)
                ·
                  refine ⟨226986747776767553967031, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 302648997035690071956041 226986747776767553967031)
                  ·
                    rfl

theorem cell20_497312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 2, 2, 3, 2].length) (baseStart_497312 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_497312 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_497312 prefixEnd_497312 := by exact prefixLift 497312
  have htrace : WordTrace (prefixWord ++ tailWord_497312) baseStart_497312 baseEnd_497312 := by
    simpa [prefixWord, tailWord_497312, baseEnd_497312] using wordTrace_append hprefix tailTrace_497312
  have hstable : (prefixWord ++ tailWord_497312).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_497312).length < 2 ^ (prefixWord ++ tailWord_497312).sum := by decide
  have hdescent : baseEnd_497312 < baseStart_497312 := by decide
  rcases family_descends (prefixWord ++ tailWord_497312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_497357 : List Nat := [1, 6, 2, 1, 1, 2, 1, 6]
def baseStart_497357 : Nat := 118140960795 + 497357 * 2 ^ 59
def prefixEnd_497357 : Nat := 4983230072969 + 3 ^ 40 * 497357 * 2
def baseEnd_497357 : Nat := 75669095667649132488949

theorem tailTrace_497357 : CollatzResearch.WordTrace tailWord_497357 prefixEnd_497357 75669095667649132488949 := by
  unfold tailWord_497357
  simp only [CollatzResearch.WordTrace]
  refine ⟨18140100059168005658146325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12093400039445337105430883 18140100059168005658146325)
  ·
    refine ⟨850317190273500265225609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 18140100059168005658146325 850317190273500265225609)
    ·
      refine ⟨637737892705125198919207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 850317190273500265225609 637737892705125198919207)
      ·
        refine ⟨956606839057687798378811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 637737892705125198919207 956606839057687798378811)
        ·
          refine ⟨1434910258586531697568217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 956606839057687798378811 1434910258586531697568217)
          ·
            refine ⟨1076182693939898773176163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1434910258586531697568217 1076182693939898773176163)
            ·
              refine ⟨1614274040909848159764245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1076182693939898773176163 1614274040909848159764245)
              ·
                refine ⟨75669095667649132488949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1614274040909848159764245 75669095667649132488949)
                ·
                  rfl

theorem cell20_497357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 2, 1, 6].length) (baseStart_497357 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_497357 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_497357 prefixEnd_497357 := by exact prefixLift 497357
  have htrace : WordTrace (prefixWord ++ tailWord_497357) baseStart_497357 baseEnd_497357 := by
    simpa [prefixWord, tailWord_497357, baseEnd_497357] using wordTrace_append hprefix tailTrace_497357
  have hstable : (prefixWord ++ tailWord_497357).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_497357).length < 2 ^ (prefixWord ++ tailWord_497357).sum := by decide
  have hdescent : baseEnd_497357 < baseStart_497357 := by decide
  rcases family_descends (prefixWord ++ tailWord_497357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_497361 : List Nat := [1, 2, 2, 1, 2, 5, 1, 6]
def baseStart_497361 : Nat := 118140960795 + 497361 * 2 ^ 59
def prefixEnd_497361 : Nat := 4983230072969 + 3 ^ 40 * 497361 * 2
def baseEnd_497361 : Nat := 75669704237313720444499

theorem tailTrace_497361 : CollatzResearch.WordTrace tailWord_497361 prefixEnd_497361 75669704237313720444499 := by
  unfold tailWord_497361
  simp only [CollatzResearch.WordTrace]
  refine ⟨18140245951153514341291937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12093497300769009560861291 18140245951153514341291937)
  ·
    refine ⟨13605184463365135755968953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18140245951153514341291937 13605184463365135755968953)
    ·
      refine ⟨10203888347523851816976715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13605184463365135755968953 10203888347523851816976715)
      ·
        refine ⟨15305832521285777725465073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10203888347523851816976715 15305832521285777725465073)
        ·
          refine ⟨11479374390964333294098805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15305832521285777725465073 11479374390964333294098805)
          ·
            refine ⟨1076191349152906246321763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 11479374390964333294098805 1076191349152906246321763)
            ·
              refine ⟨1614287023729359369482645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1076191349152906246321763 1614287023729359369482645)
              ·
                refine ⟨75669704237313720444499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1614287023729359369482645 75669704237313720444499)
                ·
                  rfl

theorem cell20_497361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 5, 1, 6].length) (baseStart_497361 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_497361 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_497361 prefixEnd_497361 := by exact prefixLift 497361
  have htrace : WordTrace (prefixWord ++ tailWord_497361) baseStart_497361 baseEnd_497361 := by
    simpa [prefixWord, tailWord_497361, baseEnd_497361] using wordTrace_append hprefix tailTrace_497361
  have hstable : (prefixWord ++ tailWord_497361).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_497361).length < 2 ^ (prefixWord ++ tailWord_497361).sum := by decide
  have hdescent : baseEnd_497361 < baseStart_497361 := by decide
  rcases family_descends (prefixWord ++ tailWord_497361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_497368 : List Nat := [2, 1, 2, 2, 3, 1, 1, 1, 7]
def baseStart_497368 : Nat := 118140960795 + 497368 * 2 ^ 59
def prefixEnd_497368 : Nat := 4983230072969 + 3 ^ 40 * 497368 * 2
def baseEnd_497368 : Nat := 227012307702680248100135

theorem tailTrace_497368 : CollatzResearch.WordTrace tailWord_497368 prefixEnd_497368 227012307702680248100135 := by
  unfold tailWord_497368
  simp only [CollatzResearch.WordTrace]
  refine ⟨9070250631064077268398379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12093667508085436357864505 9070250631064077268398379)
  ·
    refine ⟨13605375946596115902597569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9070250631064077268398379 13605375946596115902597569)
    ·
      refine ⟨10204031959947086926948177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13605375946596115902597569 10204031959947086926948177)
      ·
        refine ⟨7653023969960315195211133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10204031959947086926948177 7653023969960315195211133)
        ·
          refine ⟨2869883988735118198204175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7653023969960315195211133 2869883988735118198204175)
          ·
            refine ⟨4304825983102677297306263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2869883988735118198204175 4304825983102677297306263)
            ·
              refine ⟨6457238974654015945959395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4304825983102677297306263 6457238974654015945959395)
              ·
                refine ⟨9685858461981023918939093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6457238974654015945959395 9685858461981023918939093)
                ·
                  refine ⟨227012307702680248100135, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9685858461981023918939093 227012307702680248100135)
                  ·
                    rfl

theorem cell20_497368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 1, 1, 7].length) (baseStart_497368 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_497368 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_497368 prefixEnd_497368 := by exact prefixLift 497368
  have htrace : WordTrace (prefixWord ++ tailWord_497368) baseStart_497368 baseEnd_497368 := by
    simpa [prefixWord, tailWord_497368, baseEnd_497368] using wordTrace_append hprefix tailTrace_497368
  have hstable : (prefixWord ++ tailWord_497368).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_497368).length < 2 ^ (prefixWord ++ tailWord_497368).sum := by decide
  have hdescent : baseEnd_497368 < baseStart_497368 := by decide
  rcases family_descends (prefixWord ++ tailWord_497368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_497482 : List Nat := [3, 1, 2, 1, 1, 1, 4, 2, 5]
def baseStart_497482 : Nat := 118140960795 + 497482 * 2 ^ 59
def prefixEnd_497482 : Nat := 4983230072969 + 3 ^ 40 * 497482 * 2
def baseEnd_497482 : Nat := 227064340409002518299669

theorem tailTrace_497482 : CollatzResearch.WordTrace tailWord_497482 prefixEnd_497482 227064340409002518299669 := by
  unfold tailWord_497482
  simp only [CollatzResearch.WordTrace]
  refine ⟨4536164795928788001611675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12096439455810101337631133 4536164795928788001611675)
  ·
    refine ⟨6804247193893182002417513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4536164795928788001611675 6804247193893182002417513)
    ·
      refine ⟨5103185395419886501813135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6804247193893182002417513 5103185395419886501813135)
      ·
        refine ⟨7654778093129829752719703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5103185395419886501813135 7654778093129829752719703)
        ·
          refine ⟨11482167139694744629079555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7654778093129829752719703 11482167139694744629079555)
          ·
            refine ⟨17223250709542116943619333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11482167139694744629079555 17223250709542116943619333)
            ·
              refine ⟨3229359508039146926928625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17223250709542116943619333 3229359508039146926928625)
              ·
                refine ⟨2422019631029360195196469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3229359508039146926928625 2422019631029360195196469)
                ·
                  refine ⟨227064340409002518299669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2422019631029360195196469 227064340409002518299669)
                  ·
                    rfl

theorem cell20_497482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 4, 2, 5].length) (baseStart_497482 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_497482 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_497482 prefixEnd_497482 := by exact prefixLift 497482
  have htrace : WordTrace (prefixWord ++ tailWord_497482) baseStart_497482 baseEnd_497482 := by
    simpa [prefixWord, tailWord_497482, baseEnd_497482] using wordTrace_append hprefix tailTrace_497482
  have hstable : (prefixWord ++ tailWord_497482).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_497482).length < 2 ^ (prefixWord ++ tailWord_497482).sum := by decide
  have hdescent : baseEnd_497482 < baseStart_497482 := by decide
  rcases family_descends (prefixWord ++ tailWord_497482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_497495 : List Nat := [1, 1, 3, 2, 6, 1, 1, 2, 3]
def baseStart_497495 : Nat := 118140960795 + 497495 * 2 ^ 59
def prefixEnd_497495 : Nat := 4983230072969 + 3 ^ 40 * 497495 * 2
def baseEnd_497495 : Nat := 227070273963232250866283

theorem tailTrace_497495 : CollatzResearch.WordTrace tailWord_497495 prefixEnd_497495 227070273963232250866283 := by
  unfold tailWord_497495
  simp only [CollatzResearch.WordTrace]
  refine ⟨18145133332668055226669939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12096755555112036817779959 18145133332668055226669939)
  ·
    refine ⟨27217699999002082840004909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18145133332668055226669939 27217699999002082840004909)
    ·
      refine ⟨10206637499625781065001841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27217699999002082840004909 10206637499625781065001841)
      ·
        refine ⟨7654978124719335798751381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10206637499625781065001841 7654978124719335798751381)
        ·
          refine ⟨358827099596218865566471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 7654978124719335798751381 358827099596218865566471)
          ·
            refine ⟨538240649394328298349707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 358827099596218865566471 538240649394328298349707)
            ·
              refine ⟨807360974091492447524561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 538240649394328298349707 807360974091492447524561)
              ·
                refine ⟨605520730568619335643421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 807360974091492447524561 605520730568619335643421)
                ·
                  refine ⟨227070273963232250866283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 605520730568619335643421 227070273963232250866283)
                  ·
                    rfl

theorem cell20_497495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 6, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 6, 1, 1, 2, 3].length) (baseStart_497495 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_497495 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_497495 prefixEnd_497495 := by exact prefixLift 497495
  have htrace : WordTrace (prefixWord ++ tailWord_497495) baseStart_497495 baseEnd_497495 := by
    simpa [prefixWord, tailWord_497495, baseEnd_497495] using wordTrace_append hprefix tailTrace_497495
  have hstable : (prefixWord ++ tailWord_497495).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_497495).length < 2 ^ (prefixWord ++ tailWord_497495).sum := by decide
  have hdescent : baseEnd_497495 < baseStart_497495 := by decide
  rcases family_descends (prefixWord ++ tailWord_497495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_497516 : List Nat := [2, 2, 1, 1, 4, 3, 3, 1, 3]
def baseStart_497516 : Nat := 118140960795 + 497516 * 2 ^ 59
def prefixEnd_497516 : Nat := 4983230072969 + 3 ^ 40 * 497516 * 2
def baseEnd_497516 : Nat := 227079858935449511166197

theorem tailTrace_497516 : CollatzResearch.WordTrace tailWord_497516 prefixEnd_497516 227079858935449511166197 := by
  unfold tailWord_497516
  simp only [CollatzResearch.WordTrace]
  refine ⟨9072949632795987906592201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12097266177061317208789601 9072949632795987906592201)
  ·
    refine ⟨6804712224596990929944151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9072949632795987906592201 6804712224596990929944151)
    ·
      refine ⟨10207068336895486394916227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6804712224596990929944151 10207068336895486394916227)
      ·
        refine ⟨15310602505343229592374341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10207068336895486394916227 15310602505343229592374341)
        ·
          refine ⟨2870737969751855548570189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15310602505343229592374341 2870737969751855548570189)
          ·
            refine ⟨1076526738656945830713821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2870737969751855548570189 1076526738656945830713821)
            ·
              refine ⟨403697526996354686517683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1076526738656945830713821 403697526996354686517683)
              ·
                refine ⟨605546290494532029776525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 403697526996354686517683 605546290494532029776525)
                ·
                  refine ⟨227079858935449511166197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 605546290494532029776525 227079858935449511166197)
                  ·
                    rfl

theorem cell20_497516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 3].length) (baseStart_497516 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_497516 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_497516 prefixEnd_497516 := by exact prefixLift 497516
  have htrace : WordTrace (prefixWord ++ tailWord_497516) baseStart_497516 baseEnd_497516 := by
    simpa [prefixWord, tailWord_497516, baseEnd_497516] using wordTrace_append hprefix tailTrace_497516
  have hstable : (prefixWord ++ tailWord_497516).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_497516).length < 2 ^ (prefixWord ++ tailWord_497516).sum := by decide
  have hdescent : baseEnd_497516 < baseStart_497516 := by decide
  rcases family_descends (prefixWord ++ tailWord_497516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_497526 : List Nat := [5, 1, 1, 3, 2, 2, 2, 4]
def baseStart_497526 : Nat := 118140960795 + 497526 * 2 ^ 59
def prefixEnd_497526 : Nat := 4983230072969 + 3 ^ 40 * 497526 * 2
def baseEnd_497526 : Nat := 75694807735977973610941

theorem tailTrace_497526 : CollatzResearch.WordTrace tailWord_497526 prefixEnd_497526 75694807735977973610941 := by
  unfold tailWord_497526
  simp only [CollatzResearch.WordTrace]
  refine ⟨1134141499722234220065527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 12097509330370498347365621 1134141499722234220065527)
  ·
    refine ⟨1701212249583351330098291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1134141499722234220065527 1701212249583351330098291)
    ·
      refine ⟨2551818374375026995147437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1701212249583351330098291 2551818374375026995147437)
      ·
        refine ⟨956931890390635123180289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2551818374375026995147437 956931890390635123180289)
        ·
          refine ⟨717698917792976342385217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 956931890390635123180289 717698917792976342385217)
          ·
            refine ⟨538274188344732256788913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 717698917792976342385217 538274188344732256788913)
            ·
              refine ⟨403705641258549192591685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 538274188344732256788913 403705641258549192591685)
              ·
                refine ⟨75694807735977973610941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 403705641258549192591685 75694807735977973610941)
                ·
                  rfl

theorem cell20_497526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 2, 2, 4].length) (baseStart_497526 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_497526 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_497526 prefixEnd_497526 := by exact prefixLift 497526
  have htrace : WordTrace (prefixWord ++ tailWord_497526) baseStart_497526 baseEnd_497526 := by
    simpa [prefixWord, tailWord_497526, baseEnd_497526] using wordTrace_append hprefix tailTrace_497526
  have hstable : (prefixWord ++ tailWord_497526).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_497526).length < 2 ^ (prefixWord ++ tailWord_497526).sum := by decide
  have hdescent : baseEnd_497526 < baseStart_497526 := by decide
  rcases family_descends (prefixWord ++ tailWord_497526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_497589 : List Nat := [1, 3, 3, 2, 1, 2, 2, 6]
def baseStart_497589 : Nat := 118140960795 + 497589 * 2 ^ 59
def prefixEnd_497589 : Nat := 4983230072969 + 3 ^ 40 * 497589 * 2
def baseEnd_497589 : Nat := 75704392708195233910855

theorem tailTrace_497589 : CollatzResearch.WordTrace tailWord_497589 prefixEnd_497589 75704392708195233910855 := by
  unfold tailWord_497589
  simp only [CollatzResearch.WordTrace]
  refine ⟨18148561794327509280591821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12099041196218339520394547 18148561794327509280591821)
  ·
    refine ⟨6805710672872815980221933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18148561794327509280591821 6805710672872815980221933)
    ·
      refine ⟨2552141502327305992583225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6805710672872815980221933 2552141502327305992583225)
      ·
        refine ⟨1914106126745479494437419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2552141502327305992583225 1914106126745479494437419)
        ·
          refine ⟨2871159190118219241656129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1914106126745479494437419 2871159190118219241656129)
          ·
            refine ⟨2153369392588664431242097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2871159190118219241656129 2153369392588664431242097)
            ·
              refine ⟨1615027044441498323431573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2153369392588664431242097 1615027044441498323431573)
              ·
                refine ⟨75704392708195233910855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1615027044441498323431573 75704392708195233910855)
                ·
                  rfl

theorem cell20_497589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 2, 6].length) (baseStart_497589 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_497589 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_497589 prefixEnd_497589 := by exact prefixLift 497589
  have htrace : WordTrace (prefixWord ++ tailWord_497589) baseStart_497589 baseEnd_497589 := by
    simpa [prefixWord, tailWord_497589, baseEnd_497589] using wordTrace_append hprefix tailTrace_497589
  have hstable : (prefixWord ++ tailWord_497589).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_497589).length < 2 ^ (prefixWord ++ tailWord_497589).sum := by decide
  have hdescent : baseEnd_497589 < baseStart_497589 := by decide
  rcases family_descends (prefixWord ++ tailWord_497589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_497620 : List Nat := [2, 4, 1, 2, 1, 1, 2, 3, 4]
def baseStart_497620 : Nat := 118140960795 + 497620 * 2 ^ 59
def prefixEnd_497620 : Nat := 4983230072969 + 3 ^ 40 * 497620 * 2
def baseEnd_497620 : Nat := 227127327369287371699105

theorem tailTrace_497620 : CollatzResearch.WordTrace tailWord_497620 prefixEnd_497620 227127327369287371699105 := by
  unfold tailWord_497620
  simp only [CollatzResearch.WordTrace]
  refine ⟨9074846228607600787485157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12099794971476801049980209 9074846228607600787485157)
  ·
    refine ⟨1701533667863925147653467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9074846228607600787485157 1701533667863925147653467)
    ·
      refine ⟨2552300501795887721480201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1701533667863925147653467 2552300501795887721480201)
      ·
        refine ⟨1914225376346915791110151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2552300501795887721480201 1914225376346915791110151)
        ·
          refine ⟨2871338064520373686665227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1914225376346915791110151 2871338064520373686665227)
          ·
            refine ⟨4307007096780560529997841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2871338064520373686665227 4307007096780560529997841)
            ·
              refine ⟨3230255322585420397498381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4307007096780560529997841 3230255322585420397498381)
              ·
                refine ⟨1211345745969532649061893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3230255322585420397498381 1211345745969532649061893)
                ·
                  refine ⟨227127327369287371699105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1211345745969532649061893 227127327369287371699105)
                  ·
                    rfl

theorem cell20_497620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 2, 3, 4].length) (baseStart_497620 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_497620 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_497620 prefixEnd_497620 := by exact prefixLift 497620
  have htrace : WordTrace (prefixWord ++ tailWord_497620) baseStart_497620 baseEnd_497620 := by
    simpa [prefixWord, tailWord_497620, baseEnd_497620] using wordTrace_append hprefix tailTrace_497620
  have hstable : (prefixWord ++ tailWord_497620).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_497620).length < 2 ^ (prefixWord ++ tailWord_497620).sum := by decide
  have hdescent : baseEnd_497620 < baseStart_497620 := by decide
  rcases family_descends (prefixWord ++ tailWord_497620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_497648 : List Nat := [2, 1, 1, 1, 3, 2, 2, 8]
def baseStart_497648 : Nat := 118140960795 + 497648 * 2 ^ 59
def prefixEnd_497648 : Nat := 4983230072969 + 3 ^ 40 * 497648 * 2
def baseEnd_497648 : Nat := 75713369110747906255219

theorem tailTrace_497648 : CollatzResearch.WordTrace tailWord_497648 prefixEnd_497648 75713369110747906255219 := by
  unfold tailWord_497648
  simp only [CollatzResearch.WordTrace]
  refine ⟨9075356850556881178494799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12100475800742508237993065 9075356850556881178494799)
  ·
    refine ⟨13613035275835321767742199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9075356850556881178494799 13613035275835321767742199)
    ·
      refine ⟨20419552913752982651613299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13613035275835321767742199 20419552913752982651613299)
      ·
        refine ⟨30629329370629473977419949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20419552913752982651613299 30629329370629473977419949)
        ·
          refine ⟨11485998513986052741532481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30629329370629473977419949 11485998513986052741532481)
          ·
            refine ⟨8614498885489539556149361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11485998513986052741532481 8614498885489539556149361)
            ·
              refine ⟨6460874164117154667112021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8614498885489539556149361 6460874164117154667112021)
              ·
                refine ⟨75713369110747906255219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6460874164117154667112021 75713369110747906255219)
                ·
                  rfl

theorem cell20_497648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 2, 8].length) (baseStart_497648 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_497648 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_497648 prefixEnd_497648 := by exact prefixLift 497648
  have htrace : WordTrace (prefixWord ++ tailWord_497648) baseStart_497648 baseEnd_497648 := by
    simpa [prefixWord, tailWord_497648, baseEnd_497648] using wordTrace_append hprefix tailTrace_497648
  have hstable : (prefixWord ++ tailWord_497648).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_497648).length < 2 ^ (prefixWord ++ tailWord_497648).sum := by decide
  have hdescent : baseEnd_497648 < baseStart_497648 := by decide
  rcases family_descends (prefixWord ++ tailWord_497648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_497668 : List Nat := [2, 3, 2, 4, 1, 1, 1, 1, 5]
def baseStart_497668 : Nat := 118140960795 + 497668 * 2 ^ 59
def prefixEnd_497668 : Nat := 4983230072969 + 3 ^ 40 * 497668 * 2
def baseEnd_497668 : Nat := 227149235877212538098909

theorem tailTrace_497668 : CollatzResearch.WordTrace tailWord_497668 prefixEnd_497668 227149235877212538098909 := by
  unfold tailWord_497668
  simp only [CollatzResearch.WordTrace]
  refine ⟨9075721580520652886358829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12100962107360870515145105 9075721580520652886358829)
  ·
    refine ⟨3403395592695244832384561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9075721580520652886358829 3403395592695244832384561)
    ·
      refine ⟨2552546694521433624288421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3403395592695244832384561 2552546694521433624288421)
      ·
        refine ⟨478602505222768804554079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2552546694521433624288421 478602505222768804554079)
        ·
          refine ⟨717903757834153206831119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 478602505222768804554079 717903757834153206831119)
          ·
            refine ⟨1076855636751229810246679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 717903757834153206831119 1076855636751229810246679)
            ·
              refine ⟨1615283455126844715370019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1076855636751229810246679 1615283455126844715370019)
              ·
                refine ⟨2422925182690267073055029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1615283455126844715370019 2422925182690267073055029)
                ·
                  refine ⟨227149235877212538098909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2422925182690267073055029 227149235877212538098909)
                  ·
                    rfl

theorem cell20_497668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 1, 1, 1, 5].length) (baseStart_497668 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_497668 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_497668 prefixEnd_497668 := by exact prefixLift 497668
  have htrace : WordTrace (prefixWord ++ tailWord_497668) baseStart_497668 baseEnd_497668 := by
    simpa [prefixWord, tailWord_497668, baseEnd_497668] using wordTrace_append hprefix tailTrace_497668
  have hstable : (prefixWord ++ tailWord_497668).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_497668).length < 2 ^ (prefixWord ++ tailWord_497668).sum := by decide
  have hdescent : baseEnd_497668 < baseStart_497668 := by decide
  rcases family_descends (prefixWord ++ tailWord_497668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_497672 : List Nat := [2, 1, 3, 2, 1, 2, 3, 1, 5]
def baseStart_497672 : Nat := 118140960795 + 497672 * 2 ^ 59
def prefixEnd_497672 : Nat := 4983230072969 + 3 ^ 40 * 497672 * 2
def baseEnd_497672 : Nat := 227151061586206301965559

theorem tailTrace_497672 : CollatzResearch.WordTrace tailWord_497672 prefixEnd_497672 227151061586206301965559 := by
  unfold tailWord_497672
  simp only [CollatzResearch.WordTrace]
  refine ⟨9075794526513407227931635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12101059368684542970575513 9075794526513407227931635)
  ·
    refine ⟨13613691789770110841897453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9075794526513407227931635 13613691789770110841897453)
    ·
      refine ⟨5105134421163791565711545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13613691789770110841897453 5105134421163791565711545)
      ·
        refine ⟨3828850815872843674283659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5105134421163791565711545 3828850815872843674283659)
        ·
          refine ⟨5743276223809265511425489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3828850815872843674283659 5743276223809265511425489)
          ·
            refine ⟨4307457167856949133569117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5743276223809265511425489 4307457167856949133569117)
            ·
              refine ⟨1615296437946355925088419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4307457167856949133569117 1615296437946355925088419)
              ·
                refine ⟨2422944656919533887632629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1615296437946355925088419 2422944656919533887632629)
                ·
                  refine ⟨227151061586206301965559, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2422944656919533887632629 227151061586206301965559)
                  ·
                    rfl

theorem cell20_497672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 3, 1, 5].length) (baseStart_497672 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_497672 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_497672 prefixEnd_497672 := by exact prefixLift 497672
  have htrace : WordTrace (prefixWord ++ tailWord_497672) baseStart_497672 baseEnd_497672 := by
    simpa [prefixWord, tailWord_497672, baseEnd_497672] using wordTrace_append hprefix tailTrace_497672
  have hstable : (prefixWord ++ tailWord_497672).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_497672).length < 2 ^ (prefixWord ++ tailWord_497672).sum := by decide
  have hdescent : baseEnd_497672 < baseStart_497672 := by decide
  rcases family_descends (prefixWord ++ tailWord_497672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_497713 : List Nat := [1, 2, 2, 3, 1, 3, 3, 3, 2]
def baseStart_497713 : Nat := 118140960795 + 497713 * 2 ^ 59
def prefixEnd_497713 : Nat := 4983230072969 + 3 ^ 40 * 497713 * 2
def baseEnd_497713 : Nat := 227169775103392381598725

theorem tailTrace_497713 : CollatzResearch.WordTrace tailWord_497713 prefixEnd_497713 227169775103392381598725 := by
  unfold tailWord_497713
  simp only [CollatzResearch.WordTrace]
  refine ⟨18153084445878278458105793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12102056297252185638737195 18153084445878278458105793)
  ·
    refine ⟨13614813334408708843579345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18153084445878278458105793 13614813334408708843579345)
    ·
      refine ⟨10211110000806531632684509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13614813334408708843579345 10211110000806531632684509)
      ·
        refine ⟨3829166250302449362256691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10211110000806531632684509 3829166250302449362256691)
        ·
          refine ⟨5743749375453674043385037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3829166250302449362256691 5743749375453674043385037)
          ·
            refine ⟨2153906015795127766269389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5743749375453674043385037 2153906015795127766269389)
            ·
              refine ⟨807714755923172912351021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2153906015795127766269389 807714755923172912351021)
              ·
                refine ⟨302893033471189842131633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 807714755923172912351021 302893033471189842131633)
                ·
                  refine ⟨227169775103392381598725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 302893033471189842131633 227169775103392381598725)
                  ·
                    rfl

theorem cell20_497713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 3, 3, 2].length) (baseStart_497713 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_497713 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_497713 prefixEnd_497713 := by exact prefixLift 497713
  have htrace : WordTrace (prefixWord ++ tailWord_497713) baseStart_497713 baseEnd_497713 := by
    simpa [prefixWord, tailWord_497713, baseEnd_497713] using wordTrace_append hprefix tailTrace_497713
  have hstable : (prefixWord ++ tailWord_497713).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_497713).length < 2 ^ (prefixWord ++ tailWord_497713).sum := by decide
  have hdescent : baseEnd_497713 < baseStart_497713 := by decide
  rcases family_descends (prefixWord ++ tailWord_497713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_497717 : List Nat := [1, 3, 3, 1, 1, 1, 2, 2, 6]
def baseStart_497717 : Nat := 118140960795 + 497717 * 2 ^ 59
def prefixEnd_497717 : Nat := 4983230072969 + 3 ^ 40 * 497717 * 2
def baseEnd_497717 : Nat := 227171600812386145465375

theorem tailTrace_497717 : CollatzResearch.WordTrace tailWord_497717 prefixEnd_497717 227171600812386145465375 := by
  unfold tailWord_497717
  simp only [CollatzResearch.WordTrace]
  refine ⟨18153230337863787141251405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12102153558575858094167603 18153230337863787141251405)
  ·
    refine ⟨6807461376698920177969277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18153230337863787141251405 6807461376698920177969277)
    ·
      refine ⟨2552798016262095066738479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6807461376698920177969277 2552798016262095066738479)
      ·
        refine ⟨3829197024393142600107719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2552798016262095066738479 3829197024393142600107719)
        ·
          refine ⟨5743795536589713900161579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3829197024393142600107719 5743795536589713900161579)
          ·
            refine ⟨8615693304884570850242369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5743795536589713900161579 8615693304884570850242369)
            ·
              refine ⟨6461769978663428137681777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8615693304884570850242369 6461769978663428137681777)
              ·
                refine ⟨4846327483997571103261333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6461769978663428137681777 4846327483997571103261333)
                ·
                  refine ⟨227171600812386145465375, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4846327483997571103261333 227171600812386145465375)
                  ·
                    rfl

theorem cell20_497717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 2, 2, 6].length) (baseStart_497717 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_497717 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_497717 prefixEnd_497717 := by exact prefixLift 497717
  have htrace : WordTrace (prefixWord ++ tailWord_497717) baseStart_497717 baseEnd_497717 := by
    simpa [prefixWord, tailWord_497717, baseEnd_497717] using wordTrace_append hprefix tailTrace_497717
  have hstable : (prefixWord ++ tailWord_497717).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_497717).length < 2 ^ (prefixWord ++ tailWord_497717).sum := by decide
  have hdescent : baseEnd_497717 < baseStart_497717 := by decide
  rcases family_descends (prefixWord ++ tailWord_497717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_497720 : List Nat := [2, 1, 2, 1, 7, 1, 6]
def baseStart_497720 : Nat := 118140960795 + 497720 * 2 ^ 59
def prefixEnd_497720 : Nat := 4983230072969 + 3 ^ 40 * 497720 * 2
def baseEnd_497720 : Nat := 25241441121570163151707

theorem tailTrace_497720 : CollatzResearch.WordTrace tailWord_497720 prefixEnd_497720 25241441121570163151707 := by
  unfold tailWord_497720
  simp only [CollatzResearch.WordTrace]
  refine ⟨9076669878426459326805307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12102226504568612435740409 9076669878426459326805307)
  ·
    refine ⟨13615004817639688990207961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9076669878426459326805307 13615004817639688990207961)
    ·
      refine ⟨10211253613229766742655971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13615004817639688990207961 10211253613229766742655971)
      ·
        refine ⟨15316880419844650113983957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10211253613229766742655971 15316880419844650113983957)
        ·
          refine ⟨358989384840108987046499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 15316880419844650113983957 358989384840108987046499)
          ·
            refine ⟨538484077260163480569749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 358989384840108987046499 538484077260163480569749)
            ·
              refine ⟨25241441121570163151707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 538484077260163480569749 25241441121570163151707)
              ·
                rfl

theorem cell20_497720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 7, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 7, 1, 6].length) (baseStart_497720 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_497720 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_497720 prefixEnd_497720 := by exact prefixLift 497720
  have htrace : WordTrace (prefixWord ++ tailWord_497720) baseStart_497720 baseEnd_497720 := by
    simpa [prefixWord, tailWord_497720, baseEnd_497720] using wordTrace_append hprefix tailTrace_497720
  have hstable : (prefixWord ++ tailWord_497720).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_497720).length < 2 ^ (prefixWord ++ tailWord_497720).sum := by decide
  have hdescent : baseEnd_497720 < baseStart_497720 := by decide
  rcases family_descends (prefixWord ++ tailWord_497720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_497782 : List Nat := [5, 1, 1, 2, 1, 3, 2, 2, 3]
def baseStart_497782 : Nat := 118140960795 + 497782 * 2 ^ 59
def prefixEnd_497782 : Nat := 4983230072969 + 3 ^ 40 * 497782 * 2
def baseEnd_497782 : Nat := 227201268583534808298443

theorem tailTrace_497782 : CollatzResearch.WordTrace tailWord_497782 prefixEnd_497782 227201268583534808298443 := by
  unfold tailWord_497782
  simp only [CollatzResearch.WordTrace]
  refine ⟨1134725067664268952647975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 12103734055085535494911733 1134725067664268952647975)
  ·
    refine ⟨1702087601496403428971963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1134725067664268952647975 1702087601496403428971963)
    ·
      refine ⟨2553131402244605143457945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1702087601496403428971963 2553131402244605143457945)
      ·
        refine ⟨1914848551683453857593459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2553131402244605143457945 1914848551683453857593459)
        ·
          refine ⟨2872272827525180786390189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1914848551683453857593459 2872272827525180786390189)
          ·
            refine ⟨1077102310321942794896321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2872272827525180786390189 1077102310321942794896321)
            ·
              refine ⟨807826732741457096172241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1077102310321942794896321 807826732741457096172241)
              ·
                refine ⟨605870049556092822129181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 807826732741457096172241 605870049556092822129181)
                ·
                  refine ⟨227201268583534808298443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 605870049556092822129181 227201268583534808298443)
                  ·
                    rfl

theorem cell20_497782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 3, 2, 2, 3].length) (baseStart_497782 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_497782 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_497782 prefixEnd_497782 := by exact prefixLift 497782
  have htrace : WordTrace (prefixWord ++ tailWord_497782) baseStart_497782 baseEnd_497782 := by
    simpa [prefixWord, tailWord_497782, baseEnd_497782] using wordTrace_append hprefix tailTrace_497782
  have hstable : (prefixWord ++ tailWord_497782).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_497782).length < 2 ^ (prefixWord ++ tailWord_497782).sum := by decide
  have hdescent : baseEnd_497782 < baseStart_497782 := by decide
  rcases family_descends (prefixWord ++ tailWord_497782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_497789 : List Nat := [1, 4, 1, 1, 3, 3, 1, 4, 2]
def baseStart_497789 : Nat := 118140960795 + 497789 * 2 ^ 59
def prefixEnd_497789 : Nat := 4983230072969 + 3 ^ 40 * 497789 * 2
def baseEnd_497789 : Nat := 227204463574273895065081

theorem tailTrace_497789 : CollatzResearch.WordTrace tailWord_497789 prefixEnd_497789 227204463574273895065081 := by
  unfold tailWord_497789
  simp only [CollatzResearch.WordTrace]
  refine ⟨18155856393602943437872421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12103904262401962291914947 18155856393602943437872421)
  ·
    refine ⟨3404223073800551894601079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18155856393602943437872421 3404223073800551894601079)
    ·
      refine ⟨5106334610700827841901619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3404223073800551894601079 5106334610700827841901619)
      ·
        refine ⟨7659501916051241762852429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5106334610700827841901619 7659501916051241762852429)
        ·
          refine ⟨2872313218519215661069661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7659501916051241762852429 2872313218519215661069661)
          ·
            refine ⟨1077117456944705872901123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2872313218519215661069661 1077117456944705872901123)
            ·
              refine ⟨1615676185417058809351685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1077117456944705872901123 1615676185417058809351685)
              ·
                refine ⟨302939284765698526753441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1615676185417058809351685 302939284765698526753441)
                ·
                  refine ⟨227204463574273895065081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 302939284765698526753441 227204463574273895065081)
                  ·
                    rfl

theorem cell20_497789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 3, 1, 4, 2].length) (baseStart_497789 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_497789 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_497789 prefixEnd_497789 := by exact prefixLift 497789
  have htrace : WordTrace (prefixWord ++ tailWord_497789) baseStart_497789 baseEnd_497789 := by
    simpa [prefixWord, tailWord_497789, baseEnd_497789] using wordTrace_append hprefix tailTrace_497789
  have hstable : (prefixWord ++ tailWord_497789).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_497789).length < 2 ^ (prefixWord ++ tailWord_497789).sum := by decide
  have hdescent : baseEnd_497789 < baseStart_497789 := by decide
  rcases family_descends (prefixWord ++ tailWord_497789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_497810 : List Nat := [3, 2, 3, 1, 1, 1, 3, 2, 4]
def baseStart_497810 : Nat := 118140960795 + 497810 * 2 ^ 59
def prefixEnd_497810 : Nat := 4983230072969 + 3 ^ 40 * 497810 * 2
def baseEnd_497810 : Nat := 227214048546491155364995

theorem tailTrace_497810 : CollatzResearch.WordTrace tailWord_497810 prefixEnd_497810 227214048546491155364995 := by
  unfold tailWord_497810
  simp only [CollatzResearch.WordTrace]
  refine ⟨4539155581631716006096721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12104414884351242682924589 4539155581631716006096721)
  ·
    refine ⟨3404366686223787004572541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4539155581631716006096721 3404366686223787004572541)
    ·
      refine ⟨1276637507333920126714703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3404366686223787004572541 1276637507333920126714703)
      ·
        refine ⟨1914956261000880190072055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1276637507333920126714703 1914956261000880190072055)
        ·
          refine ⟨2872434391501320285108083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1914956261000880190072055 2872434391501320285108083)
          ·
            refine ⟨4308651587251980427662125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2872434391501320285108083 4308651587251980427662125)
            ·
              refine ⟨1615744345219492660373297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4308651587251980427662125 1615744345219492660373297)
              ·
                refine ⟨1211808258914619495279973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1615744345219492660373297 1211808258914619495279973)
                ·
                  refine ⟨227214048546491155364995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1211808258914619495279973 227214048546491155364995)
                  ·
                    rfl

theorem cell20_497810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 3, 2, 4].length) (baseStart_497810 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_497810 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_497810 prefixEnd_497810 := by exact prefixLift 497810
  have htrace : WordTrace (prefixWord ++ tailWord_497810) baseStart_497810 baseEnd_497810 := by
    simpa [prefixWord, tailWord_497810, baseEnd_497810] using wordTrace_append hprefix tailTrace_497810
  have hstable : (prefixWord ++ tailWord_497810).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_497810).length < 2 ^ (prefixWord ++ tailWord_497810).sum := by decide
  have hdescent : baseEnd_497810 < baseStart_497810 := by decide
  rcases family_descends (prefixWord ++ tailWord_497810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_497834 : List Nat := [3, 1, 5, 1, 2, 1, 7]
def baseStart_497834 : Nat := 118140960795 + 497834 * 2 ^ 59
def prefixEnd_497834 : Nat := 4983230072969 + 3 ^ 40 * 497834 * 2
def baseEnd_497834 : Nat := 25247222533383748729433

theorem tailTrace_497834 : CollatzResearch.WordTrace tailWord_497834 prefixEnd_497834 25247222533383748729433 := by
  unfold tailWord_497834
  simp only [CollatzResearch.WordTrace]
  refine ⟨4539374419609979030815139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12104998452293277415507037 4539374419609979030815139)
  ·
    refine ⟨6809061629414968546222709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4539374419609979030815139 6809061629414968546222709)
    ·
      refine ⟨638349527757653301208379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 6809061629414968546222709 638349527757653301208379)
      ·
        refine ⟨957524291636479951812569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 638349527757653301208379 957524291636479951812569)
        ·
          refine ⟨718143218727359963859427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 957524291636479951812569 718143218727359963859427)
          ·
            refine ⟨1077214828091039945789141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 718143218727359963859427 1077214828091039945789141)
            ·
              refine ⟨25247222533383748729433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1077214828091039945789141 25247222533383748729433)
              ·
                rfl

theorem cell20_497834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 1, 7].length) (baseStart_497834 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_497834 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_497834 prefixEnd_497834 := by exact prefixLift 497834
  have htrace : WordTrace (prefixWord ++ tailWord_497834) baseStart_497834 baseEnd_497834 := by
    simpa [prefixWord, tailWord_497834, baseEnd_497834] using wordTrace_append hprefix tailTrace_497834
  have hstable : (prefixWord ++ tailWord_497834).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_497834).length < 2 ^ (prefixWord ++ tailWord_497834).sum := by decide
  have hdescent : baseEnd_497834 < baseStart_497834 := by decide
  rcases family_descends (prefixWord ++ tailWord_497834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_497841 : List Nat := [1, 2, 2, 5, 2, 1, 1, 1, 5]
def baseStart_497841 : Nat := 118140960795 + 497841 * 2 ^ 59
def prefixEnd_497841 : Nat := 4983230072969 + 3 ^ 40 * 497841 * 2
def baseEnd_497841 : Nat := 227228197791192825331535

theorem tailTrace_497841 : CollatzResearch.WordTrace tailWord_497841 prefixEnd_497841 227228197791192825331535 := by
  unfold tailWord_497841
  simp only [CollatzResearch.WordTrace]
  refine ⟨18157752989414556318765377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12105168659609704212510251 18157752989414556318765377)
  ·
    refine ⟨13618314742060917239074033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18157752989414556318765377 13618314742060917239074033)
    ·
      refine ⟨10213736056545687929305525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13618314742060917239074033 10213736056545687929305525)
      ·
        refine ⟨957537755301158243372393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 10213736056545687929305525 957537755301158243372393)
        ·
          refine ⟨718153316475868682529295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 957537755301158243372393 718153316475868682529295)
          ·
            refine ⟨1077229974713803023793943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 718153316475868682529295 1077229974713803023793943)
            ·
              refine ⟨1615844962070704535690915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1077229974713803023793943 1615844962070704535690915)
              ·
                refine ⟨2423767443106056803536373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1615844962070704535690915 2423767443106056803536373)
                ·
                  refine ⟨227228197791192825331535, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2423767443106056803536373 227228197791192825331535)
                  ·
                    rfl

theorem cell20_497841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 1, 1, 1, 5].length) (baseStart_497841 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_497841 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_497841 prefixEnd_497841 := by exact prefixLift 497841
  have htrace : WordTrace (prefixWord ++ tailWord_497841) baseStart_497841 baseEnd_497841 := by
    simpa [prefixWord, tailWord_497841, baseEnd_497841] using wordTrace_append hprefix tailTrace_497841
  have hstable : (prefixWord ++ tailWord_497841).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_497841).length < 2 ^ (prefixWord ++ tailWord_497841).sum := by decide
  have hdescent : baseEnd_497841 < baseStart_497841 := by decide
  rcases family_descends (prefixWord ++ tailWord_497841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_497848 : List Nat := [2, 1, 2, 1, 2, 1, 3, 6, 2]
def baseStart_497848 : Nat := 118140960795 + 497848 * 2 ^ 59
def prefixEnd_497848 : Nat := 4983230072969 + 3 ^ 40 * 497848 * 2
def baseEnd_497848 : Nat := 227231392781931912098173

theorem tailTrace_497848 : CollatzResearch.WordTrace tailWord_497848 prefixEnd_497848 227231392781931912098173 := by
  unfold tailWord_497848
  simp only [CollatzResearch.WordTrace]
  refine ⟨9079004150194598257135099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12105338866926131009513465 9079004150194598257135099)
  ·
    refine ⟨13618506225291897385702649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9079004150194598257135099 13618506225291897385702649)
    ·
      refine ⟨10213879668968923039276987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13618506225291897385702649 10213879668968923039276987)
      ·
        refine ⟨15320819503453384558915481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10213879668968923039276987 15320819503453384558915481)
        ·
          refine ⟨11490614627590038419186611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15320819503453384558915481 11490614627590038419186611)
          ·
            refine ⟨17235921941385057628779917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11490614627590038419186611 17235921941385057628779917)
            ·
              refine ⟨6463470728019396610792469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17235921941385057628779917 6463470728019396610792469)
              ·
                refine ⟨302975190375909216130897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 6463470728019396610792469 302975190375909216130897)
                ·
                  refine ⟨227231392781931912098173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 302975190375909216130897 227231392781931912098173)
                  ·
                    rfl

theorem cell20_497848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 3, 6, 2].length) (baseStart_497848 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_497848 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_497848 prefixEnd_497848 := by exact prefixLift 497848
  have htrace : WordTrace (prefixWord ++ tailWord_497848) baseStart_497848 baseEnd_497848 := by
    simpa [prefixWord, tailWord_497848, baseEnd_497848] using wordTrace_append hprefix tailTrace_497848
  have hstable : (prefixWord ++ tailWord_497848).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_497848).length < 2 ^ (prefixWord ++ tailWord_497848).sum := by decide
  have hdescent : baseEnd_497848 < baseStart_497848 := by decide
  rcases family_descends (prefixWord ++ tailWord_497848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_497868 : List Nat := [2, 2, 1, 6, 2, 1, 2, 4]
def baseStart_497868 : Nat := 118140960795 + 497868 * 2 ^ 59
def prefixEnd_497868 : Nat := 4983230072969 + 3 ^ 40 * 497868 * 2
def baseEnd_497868 : Nat := 75746840442300243810475

theorem tailTrace_497868 : CollatzResearch.WordTrace tailWord_497868 prefixEnd_497868 75746840442300243810475 := by
  unfold tailWord_497868
  simp only [CollatzResearch.WordTrace]
  refine ⟨9079368880158369964999129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12105825173544493286665505 9079368880158369964999129)
  ·
    refine ⟨6809526660118777473749347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9079368880158369964999129 6809526660118777473749347)
    ·
      refine ⟨10214289990178166210624021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6809526660118777473749347 10214289990178166210624021)
      ·
        refine ⟨478794843289601541123001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 10214289990178166210624021 478794843289601541123001)
        ·
          refine ⟨359096132467201155842251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 478794843289601541123001 359096132467201155842251)
          ·
            refine ⟨538644198700801733763377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 359096132467201155842251 538644198700801733763377)
            ·
              refine ⟨403983149025601300322533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 538644198700801733763377 403983149025601300322533)
              ·
                refine ⟨75746840442300243810475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 403983149025601300322533 75746840442300243810475)
                ·
                  rfl

theorem cell20_497868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 2, 1, 2, 4].length) (baseStart_497868 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_497868 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_497868 prefixEnd_497868 := by exact prefixLift 497868
  have htrace : WordTrace (prefixWord ++ tailWord_497868) baseStart_497868 baseEnd_497868 := by
    simpa [prefixWord, tailWord_497868, baseEnd_497868] using wordTrace_append hprefix tailTrace_497868
  have hstable : (prefixWord ++ tailWord_497868).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_497868).length < 2 ^ (prefixWord ++ tailWord_497868).sum := by decide
  have hdescent : baseEnd_497868 < baseStart_497868 := by decide
  rcases family_descends (prefixWord ++ tailWord_497868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_497883 : List Nat := [1, 1, 1, 1, 1, 1, 1, 8, 5]
def baseStart_497883 : Nat := 118140960795 + 497883 * 2 ^ 59
def prefixEnd_497883 : Nat := 4983230072969 + 3 ^ 40 * 497883 * 2
def baseEnd_497883 : Nat := 227247367735627345931363

theorem tailTrace_497883 : CollatzResearch.WordTrace tailWord_497883 prefixEnd_497883 227247367735627345931363 := by
  unfold tailWord_497883
  simp only [CollatzResearch.WordTrace]
  refine ⟨18159284855262397491794303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12106189903508264994529535 18159284855262397491794303)
  ·
    refine ⟨27238927282893596237691455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18159284855262397491794303 27238927282893596237691455)
    ·
      refine ⟨40858390924340394356537183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27238927282893596237691455 40858390924340394356537183)
      ·
        refine ⟨61287586386510591534805775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40858390924340394356537183 61287586386510591534805775)
        ·
          refine ⟨91931379579765887302208663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61287586386510591534805775 91931379579765887302208663)
          ·
            refine ⟨137897069369648830953312995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 91931379579765887302208663 137897069369648830953312995)
            ·
              refine ⟨206845604054473246429969493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 137897069369648830953312995 206845604054473246429969493)
              ·
                refine ⟨2423971922513358356601205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 206845604054473246429969493 2423971922513358356601205)
                ·
                  refine ⟨227247367735627345931363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2423971922513358356601205 227247367735627345931363)
                  ·
                    rfl

theorem cell20_497883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 8, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 8, 5].length) (baseStart_497883 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_497883 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_497883 prefixEnd_497883 := by exact prefixLift 497883
  have htrace : WordTrace (prefixWord ++ tailWord_497883) baseStart_497883 baseEnd_497883 := by
    simpa [prefixWord, tailWord_497883, baseEnd_497883] using wordTrace_append hprefix tailTrace_497883
  have hstable : (prefixWord ++ tailWord_497883).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_497883).length < 2 ^ (prefixWord ++ tailWord_497883).sum := by decide
  have hdescent : baseEnd_497883 < baseStart_497883 := by decide
  rcases family_descends (prefixWord ++ tailWord_497883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_497893 : List Nat := [1, 3, 1, 4, 2, 3, 6]
def baseStart_497893 : Nat := 118140960795 + 497893 * 2 ^ 59
def prefixEnd_497893 : Nat := 4983230072969 + 3 ^ 40 * 497893 * 2
def baseEnd_497893 : Nat := 25250214667567972844221

theorem tailTrace_497893 : CollatzResearch.WordTrace tailWord_497893 prefixEnd_497893 25250214667567972844221 := by
  unfold tailWord_497893
  simp only [CollatzResearch.WordTrace]
  refine ⟨18159649585226169199658333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12106433056817446133105555 18159649585226169199658333)
  ·
    refine ⟨6809868594459813449871875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18159649585226169199658333 6809868594459813449871875)
    ·
      refine ⟨10214802891689720174807813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6809868594459813449871875 10214802891689720174807813)
      ·
        refine ⟨1915275542191822532776465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10214802891689720174807813 1915275542191822532776465)
        ·
          refine ⟨1436456656643866899582349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1915275542191822532776465 1436456656643866899582349)
          ·
            refine ⟨538671246241450087343381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1436456656643866899582349 538671246241450087343381)
            ·
              refine ⟨25250214667567972844221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 538671246241450087343381 25250214667567972844221)
              ·
                rfl

theorem cell20_497893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 3, 6].length) (baseStart_497893 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_497893 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_497893 prefixEnd_497893 := by exact prefixLift 497893
  have htrace : WordTrace (prefixWord ++ tailWord_497893) baseStart_497893 baseEnd_497893 := by
    simpa [prefixWord, tailWord_497893, baseEnd_497893] using wordTrace_append hprefix tailTrace_497893
  have hstable : (prefixWord ++ tailWord_497893).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_497893).length < 2 ^ (prefixWord ++ tailWord_497893).sum := by decide
  have hdescent : baseEnd_497893 < baseStart_497893 := by decide
  rcases family_descends (prefixWord ++ tailWord_497893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_497900 : List Nat := [2, 2, 1, 1, 2, 3, 2, 4, 3]
def baseStart_497900 : Nat := 118140960795 + 497900 * 2 ^ 59
def prefixEnd_497900 : Nat := 4983230072969 + 3 ^ 40 * 497900 * 2
def baseEnd_497900 : Nat := 227255126998850842364627

theorem tailTrace_497900 : CollatzResearch.WordTrace tailWord_497900 prefixEnd_497900 227255126998850842364627 := by
  unfold tailWord_497900
  simp only [CollatzResearch.WordTrace]
  refine ⟨9079952448100404697581577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12106603264133872930108769 9079952448100404697581577)
  ·
    refine ⟨6809964336075303523186183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9079952448100404697581577 6809964336075303523186183)
    ·
      refine ⟨10214946504112955284779275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6809964336075303523186183 10214946504112955284779275)
      ·
        refine ⟨15322419756169432927168913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10214946504112955284779275 15322419756169432927168913)
        ·
          refine ⟨11491814817127074695376685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15322419756169432927168913 11491814817127074695376685)
          ·
            refine ⟨4309430556422653010766257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11491814817127074695376685 4309430556422653010766257)
            ·
              refine ⟨3232072917316989758074693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4309430556422653010766257 3232072917316989758074693)
              ·
                refine ⟨606013671996935579639005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3232072917316989758074693 606013671996935579639005)
                ·
                  refine ⟨227255126998850842364627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 606013671996935579639005 227255126998850842364627)
                  ·
                    rfl

theorem cell20_497900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 3].length) (baseStart_497900 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_497900 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_497900 prefixEnd_497900 := by exact prefixLift 497900
  have htrace : WordTrace (prefixWord ++ tailWord_497900) baseStart_497900 baseEnd_497900 := by
    simpa [prefixWord, tailWord_497900, baseEnd_497900] using wordTrace_append hprefix tailTrace_497900
  have hstable : (prefixWord ++ tailWord_497900).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_497900).length < 2 ^ (prefixWord ++ tailWord_497900).sum := by decide
  have hdescent : baseEnd_497900 < baseStart_497900 := by decide
  rcases family_descends (prefixWord ++ tailWord_497900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_497914 : List Nat := [3, 1, 1, 1, 1, 5, 1, 7]
def baseStart_497914 : Nat := 118140960795 + 497914 * 2 ^ 59
def prefixEnd_497914 : Nat := 4983230072969 + 3 ^ 40 * 497914 * 2
def baseEnd_497914 : Nat := 75753838993443005299301

theorem tailTrace_497914 : CollatzResearch.WordTrace tailWord_497914 prefixEnd_497914 75753838993443005299301 := by
  unfold tailWord_497914
  simp only [CollatzResearch.WordTrace]
  refine ⟨4540103879537522446543199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12106943678766726524115197 4540103879537522446543199)
  ·
    refine ⟨6810155819306283669814799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4540103879537522446543199 6810155819306283669814799)
    ·
      refine ⟨10215233728959425504722199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6810155819306283669814799 10215233728959425504722199)
      ·
        refine ⟨15322850593439138257083299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10215233728959425504722199 15322850593439138257083299)
        ·
          refine ⟨22984275890158707385624949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15322850593439138257083299 22984275890158707385624949)
          ·
            refine ⟨2154775864702378817402339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 22984275890158707385624949 2154775864702378817402339)
            ·
              refine ⟨3232163797053568226103509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2154775864702378817402339 3232163797053568226103509)
              ·
                refine ⟨75753838993443005299301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3232163797053568226103509 75753838993443005299301)
                ·
                  rfl

theorem cell20_497914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 1, 7].length) (baseStart_497914 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_497914 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_497914 prefixEnd_497914 := by exact prefixLift 497914
  have htrace : WordTrace (prefixWord ++ tailWord_497914) baseStart_497914 baseEnd_497914 := by
    simpa [prefixWord, tailWord_497914, baseEnd_497914] using wordTrace_append hprefix tailTrace_497914
  have hstable : (prefixWord ++ tailWord_497914).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_497914).length < 2 ^ (prefixWord ++ tailWord_497914).sum := by decide
  have hdescent : baseEnd_497914 < baseStart_497914 := by decide
  rcases family_descends (prefixWord ++ tailWord_497914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_497952 : List Nat := [2, 1, 1, 5, 2, 9]
def baseStart_497952 : Nat := 118140960795 + 497952 * 2 ^ 59
def prefixEnd_497952 : Nat := 4983230072969 + 3 ^ 40 * 497952 * 2
def baseEnd_497952 : Nat := 8417735600584065653003

theorem tailTrace_497952 : CollatzResearch.WordTrace tailWord_497952 prefixEnd_497952 8417735600584065653003 := by
  unfold tailWord_497952
  simp only [CollatzResearch.WordTrace]
  refine ⟨9080900746006211138028055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12107867661341614850704073 9080900746006211138028055)
  ·
    refine ⟨13621351119009316707042083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9080900746006211138028055 13621351119009316707042083)
    ·
      refine ⟨20432026678513975060563125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13621351119009316707042083 20432026678513975060563125)
      ·
        refine ⟨1915502501110685161927793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 20432026678513975060563125 1915502501110685161927793)
        ·
          refine ⟨1436626875833013871445845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1915502501110685161927793 1436626875833013871445845)
          ·
            refine ⟨8417735600584065653003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 1436626875833013871445845 8417735600584065653003)
            ·
              rfl

theorem cell20_497952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 9].length) (baseStart_497952 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_497952 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_497952 prefixEnd_497952 := by exact prefixLift 497952
  have htrace : WordTrace (prefixWord ++ tailWord_497952) baseStart_497952 baseEnd_497952 := by
    simpa [prefixWord, tailWord_497952, baseEnd_497952] using wordTrace_append hprefix tailTrace_497952
  have hstable : (prefixWord ++ tailWord_497952).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_497952).length < 2 ^ (prefixWord ++ tailWord_497952).sum := by decide
  have hdescent : baseEnd_497952 < baseStart_497952 := by decide
  rcases family_descends (prefixWord ++ tailWord_497952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_497965 : List Nat := [1, 5, 3, 1, 2, 2, 1, 5]
def baseStart_497965 : Nat := 118140960795 + 497965 * 2 ^ 59
def prefixEnd_497965 : Nat := 4983230072969 + 3 ^ 40 * 497965 * 2
def baseEnd_497965 : Nat := 75761598256666501732565

theorem tailTrace_497965 : CollatzResearch.WordTrace tailWord_497965 prefixEnd_497965 75761598256666501732565 := by
  unfold tailWord_497965
  simp only [CollatzResearch.WordTrace]
  refine ⟨18162275640965325496279349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12108183760643550330852899 18162275640965325496279349)
  ·
    refine ⟨1702713341340499265276189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 18162275640965325496279349 1702713341340499265276189)
    ·
      refine ⟨638517503002687224478571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1702713341340499265276189 638517503002687224478571)
      ·
        refine ⟨957776254504030836717857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 638517503002687224478571 957776254504030836717857)
        ·
          refine ⟨718332190878023127538393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 957776254504030836717857 718332190878023127538393)
          ·
            refine ⟨538749143158517345653795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 718332190878023127538393 538749143158517345653795)
            ·
              refine ⟨808123714737776018480693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 538749143158517345653795 808123714737776018480693)
              ·
                refine ⟨75761598256666501732565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 808123714737776018480693 75761598256666501732565)
                ·
                  rfl

theorem cell20_497965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 2, 1, 5].length) (baseStart_497965 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_497965 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_497965 prefixEnd_497965 := by exact prefixLift 497965
  have htrace : WordTrace (prefixWord ++ tailWord_497965) baseStart_497965 baseEnd_497965 := by
    simpa [prefixWord, tailWord_497965, baseEnd_497965] using wordTrace_append hprefix tailTrace_497965
  have hstable : (prefixWord ++ tailWord_497965).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_497965).length < 2 ^ (prefixWord ++ tailWord_497965).sum := by decide
  have hdescent : baseEnd_497965 < baseStart_497965 := by decide
  rcases family_descends (prefixWord ++ tailWord_497965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_497976 : List Nat := [2, 1, 2, 1, 3, 1, 4, 3, 3]
def baseStart_497976 : Nat := 118140960795 + 497976 * 2 ^ 59
def prefixEnd_497976 : Nat := 4983230072969 + 3 ^ 40 * 497976 * 2
def baseEnd_497976 : Nat := 227289815469732355830983

theorem tailTrace_497976 : CollatzResearch.WordTrace tailWord_497976 prefixEnd_497976 227289815469732355830983 := by
  unfold tailWord_497976
  simp only [CollatzResearch.WordTrace]
  refine ⟨9081338421962737187464891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12108451229283649583286521 9081338421962737187464891)
  ·
    refine ⟨13622007632944105781197337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9081338421962737187464891 13622007632944105781197337)
    ·
      refine ⟨10216505724708079335898003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13622007632944105781197337 10216505724708079335898003)
      ·
        refine ⟨15324758587062119003847005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10216505724708079335898003 15324758587062119003847005)
        ·
          refine ⟨5746784470148294626442627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15324758587062119003847005 5746784470148294626442627)
          ·
            refine ⟨8620176705222441939663941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5746784470148294626442627 8620176705222441939663941)
            ·
              refine ⟨1616283132229207863686989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8620176705222441939663941 1616283132229207863686989)
              ·
                refine ⟨606106174585952948882621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1616283132229207863686989 606106174585952948882621)
                ·
                  refine ⟨227289815469732355830983, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 606106174585952948882621 227289815469732355830983)
                  ·
                    rfl

theorem cell20_497976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 4, 3, 3].length) (baseStart_497976 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_497976 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_497976 prefixEnd_497976 := by exact prefixLift 497976
  have htrace : WordTrace (prefixWord ++ tailWord_497976) baseStart_497976 baseEnd_497976 := by
    simpa [prefixWord, tailWord_497976, baseEnd_497976] using wordTrace_append hprefix tailTrace_497976
  have hstable : (prefixWord ++ tailWord_497976).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_497976).length < 2 ^ (prefixWord ++ tailWord_497976).sum := by decide
  have hdescent : baseEnd_497976 < baseStart_497976 := by decide
  rcases family_descends (prefixWord ++ tailWord_497976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_497983 : List Nat := [1, 1, 2, 2, 4, 1, 3, 2, 4]
def baseStart_497983 : Nat := 118140960795 + 497983 * 2 ^ 59
def prefixEnd_497983 : Nat := 4983230072969 + 3 ^ 40 * 497983 * 2
def baseEnd_497983 : Nat := 227293010460471442597621

theorem tailTrace_497983 : CollatzResearch.WordTrace tailWord_497983 prefixEnd_497983 227293010460471442597621 := by
  unfold tailWord_497983
  simp only [CollatzResearch.WordTrace]
  refine ⟨18162932154900114570434603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12108621436600076380289735 18162932154900114570434603)
  ·
    refine ⟨27244398232350171855651905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18162932154900114570434603 27244398232350171855651905)
    ·
      refine ⟨20433298674262628891738929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27244398232350171855651905 20433298674262628891738929)
      ·
        refine ⟨15324974005696971668804197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20433298674262628891738929 15324974005696971668804197)
        ·
          refine ⟨2873432626068182187900787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15324974005696971668804197 2873432626068182187900787)
          ·
            refine ⟨4310148939102273281851181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2873432626068182187900787 4310148939102273281851181)
            ·
              refine ⟨1616305852163352480694193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4310148939102273281851181 1616305852163352480694193)
              ·
                refine ⟨1212229389122514360520645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1616305852163352480694193 1212229389122514360520645)
                ·
                  refine ⟨227293010460471442597621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1212229389122514360520645 227293010460471442597621)
                  ·
                    rfl

theorem cell20_497983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 3, 2, 4].length) (baseStart_497983 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_497983 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_497983 prefixEnd_497983 := by exact prefixLift 497983
  have htrace : WordTrace (prefixWord ++ tailWord_497983) baseStart_497983 baseEnd_497983 := by
    simpa [prefixWord, tailWord_497983, baseEnd_497983] using wordTrace_append hprefix tailTrace_497983
  have hstable : (prefixWord ++ tailWord_497983).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_497983).length < 2 ^ (prefixWord ++ tailWord_497983).sum := by decide
  have hdescent : baseEnd_497983 < baseStart_497983 := by decide
  rcases family_descends (prefixWord ++ tailWord_497983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_498000 : List Nat := [2, 1, 1, 1, 1, 6, 1, 5, 2]
def baseStart_498000 : Nat := 118140960795 + 498000 * 2 ^ 59
def prefixEnd_498000 : Nat := 4983230072969 + 3 ^ 40 * 498000 * 2
def baseEnd_498000 : Nat := 227300769723694939030885

theorem tailTrace_498000 : CollatzResearch.WordTrace tailWord_498000 prefixEnd_498000 227300769723694939030885 := by
  unfold tailWord_498000
  simp only [CollatzResearch.WordTrace]
  refine ⟨9081776097919263236901727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12109034797225684315868969 9081776097919263236901727)
  ·
    refine ⟨13622664146878894855352591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9081776097919263236901727 13622664146878894855352591)
    ·
      refine ⟨20433996220318342283028887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13622664146878894855352591 20433996220318342283028887)
      ·
        refine ⟨30650994330477513424543331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20433996220318342283028887 30650994330477513424543331)
        ·
          refine ⟨45976491495716270136814997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30650994330477513424543331 45976491495716270136814997)
          ·
            refine ⟨2155148038861700162663203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 45976491495716270136814997 2155148038861700162663203)
            ·
              refine ⟨3232722058292550243994805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2155148038861700162663203 3232722058292550243994805)
              ·
                refine ⟨303067692964926585374513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3232722058292550243994805 303067692964926585374513)
                ·
                  refine ⟨227300769723694939030885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 303067692964926585374513 227300769723694939030885)
                  ·
                    rfl

theorem cell20_498000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 1, 5, 2].length) (baseStart_498000 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_498000 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_498000 prefixEnd_498000 := by exact prefixLift 498000
  have htrace : WordTrace (prefixWord ++ tailWord_498000) baseStart_498000 baseEnd_498000 := by
    simpa [prefixWord, tailWord_498000, baseEnd_498000] using wordTrace_append hprefix tailTrace_498000
  have hstable : (prefixWord ++ tailWord_498000).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_498000).length < 2 ^ (prefixWord ++ tailWord_498000).sum := by decide
  have hdescent : baseEnd_498000 < baseStart_498000 := by decide
  rcases family_descends (prefixWord ++ tailWord_498000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_498021 : List Nat := [1, 3, 1, 3, 1, 3, 1, 3, 4]
def baseStart_498021 : Nat := 118140960795 + 498021 * 2 ^ 59
def prefixEnd_498021 : Nat := 4983230072969 + 3 ^ 40 * 498021 * 2
def baseEnd_498021 : Nat := 227310354695912199330799

theorem tailTrace_498021 : CollatzResearch.WordTrace tailWord_498021 prefixEnd_498021 227310354695912199330799 := by
  unfold tailWord_498021
  simp only [CollatzResearch.WordTrace]
  refine ⟨18164318128762447060317917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12109545419174964706878611 18164318128762447060317917)
  ·
    refine ⟨6811619298285917647619219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18164318128762447060317917 6811619298285917647619219)
    ·
      refine ⟨10217428947428876471428829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6811619298285917647619219 10217428947428876471428829)
      ·
        refine ⟨3831535855285828676785811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10217428947428876471428829 3831535855285828676785811)
        ·
          refine ⟨5747303782928743015178717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3831535855285828676785811 5747303782928743015178717)
          ·
            refine ⟨2155238918598278630692019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5747303782928743015178717 2155238918598278630692019)
            ·
              refine ⟨3232858377897417946038029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2155238918598278630692019 3232858377897417946038029)
              ·
                refine ⟨1212321891711531729764261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3232858377897417946038029 1212321891711531729764261)
                ·
                  refine ⟨227310354695912199330799, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1212321891711531729764261 227310354695912199330799)
                  ·
                    rfl

theorem cell20_498021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 1, 3, 4].length) (baseStart_498021 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_498021 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_498021 prefixEnd_498021 := by exact prefixLift 498021
  have htrace : WordTrace (prefixWord ++ tailWord_498021) baseStart_498021 baseEnd_498021 := by
    simpa [prefixWord, tailWord_498021, baseEnd_498021] using wordTrace_append hprefix tailTrace_498021
  have hstable : (prefixWord ++ tailWord_498021).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_498021).length < 2 ^ (prefixWord ++ tailWord_498021).sum := by decide
  have hdescent : baseEnd_498021 < baseStart_498021 := by decide
  rcases family_descends (prefixWord ++ tailWord_498021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_498045 : List Nat := [1, 4, 1, 1, 2, 3, 4, 4]
def baseStart_498045 : Nat := 118140960795 + 498045 * 2 ^ 59
def prefixEnd_498045 : Nat := 4983230072969 + 3 ^ 40 * 498045 * 2
def baseEnd_498045 : Nat := 75773769649958260843567

theorem tailTrace_498045 : CollatzResearch.WordTrace tailWord_498045 prefixEnd_498045 75773769649958260843567 := by
  unfold tailWord_498045
  simp only [CollatzResearch.WordTrace]
  refine ⟨18165193480675499159191589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12110128987116999439461059 18165193480675499159191589)
  ·
    refine ⟨3405973777626656092348423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18165193480675499159191589 3405973777626656092348423)
    ·
      refine ⟨5108960666439984138522635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3405973777626656092348423 5108960666439984138522635)
      ·
        refine ⟨7663440999659976207783953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5108960666439984138522635 7663440999659976207783953)
        ·
          refine ⟨5747580749744982155837965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7663440999659976207783953 5747580749744982155837965)
          ·
            refine ⟨2155342781154368308439237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5747580749744982155837965 2155342781154368308439237)
            ·
              refine ⟨404126771466444057832357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2155342781154368308439237 404126771466444057832357)
              ·
                refine ⟨75773769649958260843567, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 404126771466444057832357 75773769649958260843567)
                ·
                  rfl

theorem cell20_498045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 4, 4].length) (baseStart_498045 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_498045 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_498045 prefixEnd_498045 := by exact prefixLift 498045
  have htrace : WordTrace (prefixWord ++ tailWord_498045) baseStart_498045 baseEnd_498045 := by
    simpa [prefixWord, tailWord_498045, baseEnd_498045] using wordTrace_append hprefix tailTrace_498045
  have hstable : (prefixWord ++ tailWord_498045).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_498045).length < 2 ^ (prefixWord ++ tailWord_498045).sum := by decide
  have hdescent : baseEnd_498045 < baseStart_498045 := by decide
  rcases family_descends (prefixWord ++ tailWord_498045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_498072 : List Nat := [2, 1, 2, 5, 1, 2, 3, 2, 2]
def baseStart_498072 : Nat := 118140960795 + 498072 * 2 ^ 59
def prefixEnd_498072 : Nat := 4983230072969 + 3 ^ 40 * 498072 * 2
def baseEnd_498072 : Nat := 227333632485582688630591

theorem tailTrace_498072 : CollatzResearch.WordTrace tailWord_498072 prefixEnd_498072 227333632485582688630591 := by
  unfold tailWord_498072
  simp only [CollatzResearch.WordTrace]
  refine ⟨9083089125788841385212235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12110785501051788513616313 9083089125788841385212235)
  ·
    refine ⟨13624633688683262077818353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9083089125788841385212235 13624633688683262077818353)
    ·
      refine ⟨10218475266512446558363765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13624633688683262077818353 10218475266512446558363765)
      ·
        refine ⟨957982056235541864846603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 10218475266512446558363765 957982056235541864846603)
        ·
          refine ⟨1436973084353312797269905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 957982056235541864846603 1436973084353312797269905)
          ·
            refine ⟨1077729813264984597952429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1436973084353312797269905 1077729813264984597952429)
            ·
              refine ⟨404148679974369224232161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1077729813264984597952429 404148679974369224232161)
              ·
                refine ⟨303111509980776918174121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 404148679974369224232161 303111509980776918174121)
                ·
                  refine ⟨227333632485582688630591, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 303111509980776918174121 227333632485582688630591)
                  ·
                    rfl

theorem cell20_498072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 2, 3, 2, 2].length) (baseStart_498072 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_498072 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_498072 prefixEnd_498072 := by exact prefixLift 498072
  have htrace : WordTrace (prefixWord ++ tailWord_498072) baseStart_498072 baseEnd_498072 := by
    simpa [prefixWord, tailWord_498072, baseEnd_498072] using wordTrace_append hprefix tailTrace_498072
  have hstable : (prefixWord ++ tailWord_498072).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_498072).length < 2 ^ (prefixWord ++ tailWord_498072).sum := by decide
  have hdescent : baseEnd_498072 < baseStart_498072 := by decide
  rcases family_descends (prefixWord ++ tailWord_498072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_498073 : List Nat := [1, 2, 1, 2, 1, 4, 1, 3, 5]
def baseStart_498073 : Nat := 118140960795 + 498073 * 2 ^ 59
def prefixEnd_498073 : Nat := 4983230072969 + 3 ^ 40 * 498073 * 2
def baseEnd_498073 : Nat := 227334088912831129597253

theorem tailTrace_498073 : CollatzResearch.WordTrace tailWord_498073 prefixEnd_498073 227334088912831129597253 := by
  unfold tailWord_498073
  simp only [CollatzResearch.WordTrace]
  refine ⟨18166214724574059941210873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12110809816382706627473915 18166214724574059941210873)
  ·
    refine ⟨13624661043430544955908155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18166214724574059941210873 13624661043430544955908155)
    ·
      refine ⟨20436991565145817433862233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13624661043430544955908155 20436991565145817433862233)
      ·
        refine ⟨15327743673859363075396675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20436991565145817433862233 15327743673859363075396675)
        ·
          refine ⟨22991615510789044613095013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15327743673859363075396675 22991615510789044613095013)
          ·
            refine ⟨4310927908272945864955315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22991615510789044613095013 4310927908272945864955315)
            ·
              refine ⟨6466391862409418797432973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4310927908272945864955315 6466391862409418797432973)
              ·
                refine ⟨2424896948403532049037365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6466391862409418797432973 2424896948403532049037365)
                ·
                  refine ⟨227334088912831129597253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2424896948403532049037365 227334088912831129597253)
                  ·
                    rfl

theorem cell20_498073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 1, 3, 5].length) (baseStart_498073 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_498073 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_498073 prefixEnd_498073 := by exact prefixLift 498073
  have htrace : WordTrace (prefixWord ++ tailWord_498073) baseStart_498073 baseEnd_498073 := by
    simpa [prefixWord, tailWord_498073, baseEnd_498073] using wordTrace_append hprefix tailTrace_498073
  have hstable : (prefixWord ++ tailWord_498073).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_498073).length < 2 ^ (prefixWord ++ tailWord_498073).sum := by decide
  have hdescent : baseEnd_498073 < baseStart_498073 := by decide
  rcases family_descends (prefixWord ++ tailWord_498073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_498166 : List Nat := [5, 1, 1, 1, 2, 1, 2, 2, 5]
def baseStart_498166 : Nat := 118140960795 + 498166 * 2 ^ 59
def prefixEnd_498166 : Nat := 4983230072969 + 3 ^ 40 * 498166 * 2
def baseEnd_498166 : Nat := 227376536646936139496873

theorem tailTrace_498166 : CollatzResearch.WordTrace tailWord_498166 prefixEnd_498166 227376536646936139496873 := by
  unfold tailWord_498166
  simp only [CollatzResearch.WordTrace]
  refine ⟨1135600419577321051521647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 12113071142158091216230901 1135600419577321051521647)
  ·
    refine ⟨1703400629365981577282471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1135600419577321051521647 1703400629365981577282471)
    ·
      refine ⟨2555100944048972365923707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1703400629365981577282471 2555100944048972365923707)
      ·
        refine ⟨3832651416073458548885561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2555100944048972365923707 3832651416073458548885561)
        ·
          refine ⟨2874488562055093911664171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3832651416073458548885561 2874488562055093911664171)
          ·
            refine ⟨4311732843082640867496257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2874488562055093911664171 4311732843082640867496257)
            ·
              refine ⟨3233799632311980650622193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4311732843082640867496257 3233799632311980650622193)
              ·
                refine ⟨2425349724233985487966645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3233799632311980650622193 2425349724233985487966645)
                ·
                  refine ⟨227376536646936139496873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2425349724233985487966645 227376536646936139496873)
                  ·
                    rfl

theorem cell20_498166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 2, 2, 5].length) (baseStart_498166 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_498166 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_498166 prefixEnd_498166 := by exact prefixLift 498166
  have htrace : WordTrace (prefixWord ++ tailWord_498166) baseStart_498166 baseEnd_498166 := by
    simpa [prefixWord, tailWord_498166, baseEnd_498166] using wordTrace_append hprefix tailTrace_498166
  have hstable : (prefixWord ++ tailWord_498166).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_498166).length < 2 ^ (prefixWord ++ tailWord_498166).sum := by decide
  have hdescent : baseEnd_498166 < baseStart_498166 := by decide
  rcases family_descends (prefixWord ++ tailWord_498166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_498190 : List Nat := [4, 1, 1, 2, 3, 2, 2, 1, 4]
def baseStart_498190 : Nat := 118140960795 + 498190 * 2 ^ 59
def prefixEnd_498190 : Nat := 4983230072969 + 3 ^ 40 * 498190 * 2
def baseEnd_498190 : Nat := 227387490900898722696775

theorem tailTrace_498190 : CollatzResearch.WordTrace tailWord_498190 prefixEnd_498190 227387490900898722696775 := by
  unfold tailWord_498190
  simp only [CollatzResearch.WordTrace]
  refine ⟨2271310258143773615402503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12113654710100125948813349 2271310258143773615402503)
  ·
    refine ⟨3406965387215660423103755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2271310258143773615402503 3406965387215660423103755)
    ·
      refine ⟨5110448080823490634655633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3406965387215660423103755 5110448080823490634655633)
      ·
        refine ⟨3832836060617617975991725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5110448080823490634655633 3832836060617617975991725)
        ·
          refine ⟨1437313522731606740996897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3832836060617617975991725 1437313522731606740996897)
          ·
            refine ⟨1077985142048705055747673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1437313522731606740996897 1077985142048705055747673)
            ·
              refine ⟨808488856536528791810755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1077985142048705055747673 808488856536528791810755)
              ·
                refine ⟨1212733284804793187716133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 808488856536528791810755 1212733284804793187716133)
                ·
                  refine ⟨227387490900898722696775, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1212733284804793187716133 227387490900898722696775)
                  ·
                    rfl

theorem cell20_498190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 2, 2, 1, 4].length) (baseStart_498190 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_498190 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_498190 prefixEnd_498190 := by exact prefixLift 498190
  have htrace : WordTrace (prefixWord ++ tailWord_498190) baseStart_498190 baseEnd_498190 := by
    simpa [prefixWord, tailWord_498190, baseEnd_498190] using wordTrace_append hprefix tailTrace_498190
  have hstable : (prefixWord ++ tailWord_498190).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_498190).length < 2 ^ (prefixWord ++ tailWord_498190).sum := by decide
  have hdescent : baseEnd_498190 < baseStart_498190 := by decide
  rcases family_descends (prefixWord ++ tailWord_498190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_498211 : List Nat := [1, 1, 1, 4, 4, 1, 2, 2, 4]
def baseStart_498211 : Nat := 118140960795 + 498211 * 2 ^ 59
def prefixEnd_498211 : Nat := 4983230072969 + 3 ^ 40 * 498211 * 2
def baseEnd_498211 : Nat := 227397075873115982996689

theorem tailTrace_498211 : CollatzResearch.WordTrace tailWord_498211 prefixEnd_498211 227397075873115982996689 := by
  unfold tailWord_498211
  simp only [CollatzResearch.WordTrace]
  refine ⟨18171247998074109509734487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12114165332049406339822991 18171247998074109509734487)
  ·
    refine ⟨27256871997111164264601731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18171247998074109509734487 27256871997111164264601731)
    ·
      refine ⟨40885307995666746396902597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27256871997111164264601731 40885307995666746396902597)
      ·
        refine ⟨7665995249187514949419237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 40885307995666746396902597 7665995249187514949419237)
        ·
          refine ⟨1437374109222659053016107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7665995249187514949419237 1437374109222659053016107)
          ·
            refine ⟨2156061163833988579524161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1437374109222659053016107 2156061163833988579524161)
            ·
              refine ⟨1617045872875491434643121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2156061163833988579524161 1617045872875491434643121)
              ·
                refine ⟨1212784404656618575982341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1617045872875491434643121 1212784404656618575982341)
                ·
                  refine ⟨227397075873115982996689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1212784404656618575982341 227397075873115982996689)
                  ·
                    rfl

theorem cell20_498211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 2, 2, 4].length) (baseStart_498211 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_498211 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_498211 prefixEnd_498211 := by exact prefixLift 498211
  have htrace : WordTrace (prefixWord ++ tailWord_498211) baseStart_498211 baseEnd_498211 := by
    simpa [prefixWord, tailWord_498211, baseEnd_498211] using wordTrace_append hprefix tailTrace_498211
  have hstable : (prefixWord ++ tailWord_498211).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_498211).length < 2 ^ (prefixWord ++ tailWord_498211).sum := by decide
  have hdescent : baseEnd_498211 < baseStart_498211 := by decide
  rcases family_descends (prefixWord ++ tailWord_498211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_498225 : List Nat := [1, 2, 2, 3, 1, 1, 3, 2, 5]
def baseStart_498225 : Nat := 118140960795 + 498225 * 2 ^ 59
def prefixEnd_498225 : Nat := 4983230072969 + 3 ^ 40 * 498225 * 2
def baseEnd_498225 : Nat := 227403465854594156529965

theorem tailTrace_498225 : CollatzResearch.WordTrace tailWord_498225 prefixEnd_498225 227403465854594156529965 := by
  unfold tailWord_498225
  simp only [CollatzResearch.WordTrace]
  refine ⟨18171758620023389900744129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12114505746682259933829419 18171758620023389900744129)
  ·
    refine ⟨13628818965017542425558097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18171758620023389900744129 13628818965017542425558097)
    ·
      refine ⟨10221614223763156819168573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13628818965017542425558097 10221614223763156819168573)
      ·
        refine ⟨3833105333911183807188215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10221614223763156819168573 3833105333911183807188215)
        ·
          refine ⟨5749658000866775710782323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3833105333911183807188215 5749658000866775710782323)
          ·
            refine ⟨8624487001300163566173485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5749658000866775710782323 8624487001300163566173485)
            ·
              refine ⟨3234182625487561337315057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8624487001300163566173485 3234182625487561337315057)
              ·
                refine ⟨2425636969115671002986293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3234182625487561337315057 2425636969115671002986293)
                ·
                  refine ⟨227403465854594156529965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2425636969115671002986293 227403465854594156529965)
                  ·
                    rfl

theorem cell20_498225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 3, 2, 5].length) (baseStart_498225 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_498225 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_498225 prefixEnd_498225 := by exact prefixLift 498225
  have htrace : WordTrace (prefixWord ++ tailWord_498225) baseStart_498225 baseEnd_498225 := by
    simpa [prefixWord, tailWord_498225, baseEnd_498225] using wordTrace_append hprefix tailTrace_498225
  have hstable : (prefixWord ++ tailWord_498225).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_498225).length < 2 ^ (prefixWord ++ tailWord_498225).sum := by decide
  have hdescent : baseEnd_498225 < baseStart_498225 := by decide
  rcases family_descends (prefixWord ++ tailWord_498225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_498245 : List Nat := [1, 3, 1, 1, 1, 6, 3, 2, 2]
def baseStart_498245 : Nat := 118140960795 + 498245 * 2 ^ 59
def prefixEnd_498245 : Nat := 4983230072969 + 3 ^ 40 * 498245 * 2
def baseEnd_498245 : Nat := 227412594399562975863217

theorem tailTrace_498245 : CollatzResearch.WordTrace tailWord_498245 prefixEnd_498245 227412594399562975863217 := by
  unfold tailWord_498245
  simp only [CollatzResearch.WordTrace]
  refine ⟨18172488079950933316472189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12114992053300622210981459 18172488079950933316472189)
  ·
    refine ⟨6814683029981599993677071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18172488079950933316472189 6814683029981599993677071)
    ·
      refine ⟨10222024544972399990515607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6814683029981599993677071 10222024544972399990515607)
      ·
        refine ⟨15333036817458599985773411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10222024544972399990515607 15333036817458599985773411)
        ·
          refine ⟨22999555226187899978660117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15333036817458599985773411 22999555226187899978660117)
          ·
            refine ⟨1078104151227557811499693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 22999555226187899978660117 1078104151227557811499693)
            ·
              refine ⟨404289056710334179312385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1078104151227557811499693 404289056710334179312385)
              ·
                refine ⟨303216792532750634484289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 404289056710334179312385 303216792532750634484289)
                ·
                  refine ⟨227412594399562975863217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 303216792532750634484289 227412594399562975863217)
                  ·
                    rfl

theorem cell20_498245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 6, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 6, 3, 2, 2].length) (baseStart_498245 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_498245 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_498245 prefixEnd_498245 := by exact prefixLift 498245
  have htrace : WordTrace (prefixWord ++ tailWord_498245) baseStart_498245 baseEnd_498245 := by
    simpa [prefixWord, tailWord_498245, baseEnd_498245] using wordTrace_append hprefix tailTrace_498245
  have hstable : (prefixWord ++ tailWord_498245).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_498245).length < 2 ^ (prefixWord ++ tailWord_498245).sum := by decide
  have hdescent : baseEnd_498245 < baseStart_498245 := by decide
  rcases family_descends (prefixWord ++ tailWord_498245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_498294 : List Nat := [5, 1, 1, 2, 11]
def baseStart_498294 : Nat := 118140960795 + 498294 * 2 ^ 59
def prefixEnd_498294 : Nat := 4983230072969 + 3 ^ 40 * 498294 * 2
def baseEnd_498294 : Nat := 2807839004132550410243

theorem tailTrace_498294 : CollatzResearch.WordTrace tailWord_498294 prefixEnd_498294 2807839004132550410243 := by
  unfold tailWord_498294
  simp only [CollatzResearch.WordTrace]
  refine ⟨1135892203548338417812871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 12116183504515609790003957 1135892203548338417812871)
  ·
    refine ⟨1703838305322507626719307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1135892203548338417812871 1703838305322507626719307)
    ·
      refine ⟨2555757457983761440078961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1703838305322507626719307 2555757457983761440078961)
      ·
        refine ⟨1916818093487821080059221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2555757457983761440078961 1916818093487821080059221)
        ·
          refine ⟨2807839004132550410243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 11 1916818093487821080059221 2807839004132550410243)
          ·
            rfl

theorem cell20_498294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 11].length) (baseStart_498294 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_498294 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_498294 prefixEnd_498294 := by exact prefixLift 498294
  have htrace : WordTrace (prefixWord ++ tailWord_498294) baseStart_498294 baseEnd_498294 := by
    simpa [prefixWord, tailWord_498294, baseEnd_498294] using wordTrace_append hprefix tailTrace_498294
  have hstable : (prefixWord ++ tailWord_498294).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_498294).length < 2 ^ (prefixWord ++ tailWord_498294).sum := by decide
  have hdescent : baseEnd_498294 < baseStart_498294 := by decide
  rcases family_descends (prefixWord ++ tailWord_498294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_498304 : List Nat := [2, 1, 1, 2, 1, 6, 1, 4, 2]
def baseStart_498304 : Nat := 118140960795 + 498304 * 2 ^ 59
def prefixEnd_498304 : Nat := 4983230072969 + 3 ^ 40 * 498304 * 2
def baseEnd_498304 : Nat := 227439523607220992896309

theorem tailTrace_498304 : CollatzResearch.WordTrace tailWord_498304 prefixEnd_498304 227439523607220992896309 := by
  unfold tailWord_498304
  simp only [CollatzResearch.WordTrace]
  refine ⟨9087319993368593196434983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12116426657824790928579977 9087319993368593196434983)
  ·
    refine ⟨13630979990052889794652475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9087319993368593196434983 13630979990052889794652475)
    ·
      refine ⟨20446469985079334691978713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13630979990052889794652475 20446469985079334691978713)
      ·
        refine ⟨15334852488809501018984035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20446469985079334691978713 15334852488809501018984035)
        ·
          refine ⟨23002278733214251528476053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15334852488809501018984035 23002278733214251528476053)
          ·
            refine ⟨1078231815619418040397315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 23002278733214251528476053 1078231815619418040397315)
            ·
              refine ⟨1617347723429127060595973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1078231815619418040397315 1617347723429127060595973)
              ·
                refine ⟨303252698142961323861745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1617347723429127060595973 303252698142961323861745)
                ·
                  refine ⟨227439523607220992896309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 303252698142961323861745 227439523607220992896309)
                  ·
                    rfl

theorem cell20_498304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 6, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 6, 1, 4, 2].length) (baseStart_498304 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_498304 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_498304 prefixEnd_498304 := by exact prefixLift 498304
  have htrace : WordTrace (prefixWord ++ tailWord_498304) baseStart_498304 baseEnd_498304 := by
    simpa [prefixWord, tailWord_498304, baseEnd_498304] using wordTrace_append hprefix tailTrace_498304
  have hstable : (prefixWord ++ tailWord_498304).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_498304).length < 2 ^ (prefixWord ++ tailWord_498304).sum := by decide
  have hdescent : baseEnd_498304 < baseStart_498304 := by decide
  rcases family_descends (prefixWord ++ tailWord_498304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_498315 : List Nat := [1, 1, 1, 1, 4, 1, 2, 9]
def baseStart_498315 : Nat := 118140960795 + 498315 * 2 ^ 59
def prefixEnd_498315 : Nat := 4983230072969 + 3 ^ 40 * 498315 * 2
def baseEnd_498315 : Nat := 75814848102317947843199

theorem tailTrace_498315 : CollatzResearch.WordTrace tailWord_498315 prefixEnd_498315 75814848102317947843199 := by
  unfold tailWord_498315
  simp only [CollatzResearch.WordTrace]
  refine ⟨18175041189697335271520399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12116694126464890181013599 18175041189697335271520399)
  ·
    refine ⟨27262561784546002907280599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18175041189697335271520399 27262561784546002907280599)
    ·
      refine ⟨40893842676819004360920899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27262561784546002907280599 40893842676819004360920899)
      ·
        refine ⟨61340764015228506541381349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40893842676819004360920899 61340764015228506541381349)
        ·
          refine ⟨11501393252855344976509003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 61340764015228506541381349 11501393252855344976509003)
          ·
            refine ⟨17252089879283017464763505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11501393252855344976509003 17252089879283017464763505)
            ·
              refine ⟨12939067409462263098572629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17252089879283017464763505 12939067409462263098572629)
              ·
                refine ⟨75814848102317947843199, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 12939067409462263098572629 75814848102317947843199)
                ·
                  rfl

theorem cell20_498315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 9].length) (baseStart_498315 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_498315 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_498315 prefixEnd_498315 := by exact prefixLift 498315
  have htrace : WordTrace (prefixWord ++ tailWord_498315) baseStart_498315 baseEnd_498315 := by
    simpa [prefixWord, tailWord_498315, baseEnd_498315] using wordTrace_append hprefix tailTrace_498315
  have hstable : (prefixWord ++ tailWord_498315).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_498315).length < 2 ^ (prefixWord ++ tailWord_498315).sum := by decide
  have hdescent : baseEnd_498315 < baseStart_498315 := by decide
  rcases family_descends (prefixWord ++ tailWord_498315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_498318 : List Nat := [4, 1, 1, 3, 1, 1, 1, 5, 3]
def baseStart_498318 : Nat := 118140960795 + 498318 * 2 ^ 59
def prefixEnd_498318 : Nat := 4983230072969 + 3 ^ 40 * 498318 * 2
def baseEnd_498318 : Nat := 227445913588699166429585

theorem tailTrace_498318 : CollatzResearch.WordTrace tailWord_498318 prefixEnd_498318 227445913588699166429585 := by
  unfold tailWord_498318
  simp only [CollatzResearch.WordTrace]
  refine ⟨2271893826085808347984951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12116767072457644522586405 2271893826085808347984951)
  ·
    refine ⟨3407840739128712521977427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2271893826085808347984951 3407840739128712521977427)
    ·
      refine ⟨5111761108693068782966141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3407840739128712521977427 5111761108693068782966141)
      ·
        refine ⟨1916910415759900793612303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5111761108693068782966141 1916910415759900793612303)
        ·
          refine ⟨2875365623639851190418455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1916910415759900793612303 2875365623639851190418455)
          ·
            refine ⟨4313048435459776785627683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2875365623639851190418455 4313048435459776785627683)
            ·
              refine ⟨6469572653189665178441525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4313048435459776785627683 6469572653189665178441525)
              ·
                refine ⟨606522436236531110478893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6469572653189665178441525 606522436236531110478893)
                ·
                  refine ⟨227445913588699166429585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 606522436236531110478893 227445913588699166429585)
                  ·
                    rfl

theorem cell20_498318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 1, 5, 3].length) (baseStart_498318 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_498318 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_498318 prefixEnd_498318 := by exact prefixLift 498318
  have htrace : WordTrace (prefixWord ++ tailWord_498318) baseStart_498318 baseEnd_498318 := by
    simpa [prefixWord, tailWord_498318, baseEnd_498318] using wordTrace_append hprefix tailTrace_498318
  have hstable : (prefixWord ++ tailWord_498318).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_498318).length < 2 ^ (prefixWord ++ tailWord_498318).sum := by decide
  have hdescent : baseEnd_498318 < baseStart_498318 := by decide
  rcases family_descends (prefixWord ++ tailWord_498318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_498369 : List Nat := [1, 2, 6, 2, 1, 1, 3, 1, 3]
def baseStart_498369 : Nat := 118140960795 + 498369 * 2 ^ 59
def prefixEnd_498369 : Nat := 4983230072969 + 3 ^ 40 * 498369 * 2
def baseEnd_498369 : Nat := 227469191378369655729377

theorem tailTrace_498369 : CollatzResearch.WordTrace tailWord_498369 prefixEnd_498369 227469191378369655729377 := by
  unfold tailWord_498369
  simp only [CollatzResearch.WordTrace]
  refine ⟨18177010731501702493986161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12118007154334468329324107 18177010731501702493986161)
  ·
    refine ⟨13632758048626276870489621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18177010731501702493986161 13632758048626276870489621)
    ·
      refine ⟨639035533529356728304201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 13632758048626276870489621 639035533529356728304201)
      ·
        refine ⟨479276650147017546228151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 639035533529356728304201 479276650147017546228151)
        ·
          refine ⟨718914975220526319342227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 479276650147017546228151 718914975220526319342227)
          ·
            refine ⟨1078372462830789479013341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 718914975220526319342227 1078372462830789479013341)
            ·
              refine ⟨404389673561546054630003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1078372462830789479013341 404389673561546054630003)
              ·
                refine ⟨606584510342319081945005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 404389673561546054630003 606584510342319081945005)
                ·
                  refine ⟨227469191378369655729377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 606584510342319081945005 227469191378369655729377)
                  ·
                    rfl

theorem cell20_498369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 1, 3, 1, 3].length) (baseStart_498369 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_498369 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_498369 prefixEnd_498369 := by exact prefixLift 498369
  have htrace : WordTrace (prefixWord ++ tailWord_498369) baseStart_498369 baseEnd_498369 := by
    simpa [prefixWord, tailWord_498369, baseEnd_498369] using wordTrace_append hprefix tailTrace_498369
  have hstable : (prefixWord ++ tailWord_498369).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_498369).length < 2 ^ (prefixWord ++ tailWord_498369).sum := by decide
  have hdescent : baseEnd_498369 < baseStart_498369 := by decide
  rcases family_descends (prefixWord ++ tailWord_498369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_498415 : List Nat := [1, 1, 2, 1, 5, 2, 2, 1, 5]
def baseStart_498415 : Nat := 118140960795 + 498415 * 2 ^ 59
def prefixEnd_498415 : Nat := 4983230072969 + 3 ^ 40 * 498415 * 2
def baseEnd_498415 : Nat := 227490187031797940195855

theorem tailTrace_498415 : CollatzResearch.WordTrace tailWord_498415 prefixEnd_498415 227490187031797940195855 := by
  unfold tailWord_498415
  simp only [CollatzResearch.WordTrace]
  refine ⟨18178688489335052350160699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12119125659556701566773799 18178688489335052350160699)
  ·
    refine ⟨27268032734002578525241049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18178688489335052350160699 27268032734002578525241049)
    ·
      refine ⟨20451024550501933893930787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27268032734002578525241049 20451024550501933893930787)
      ·
        refine ⟨30676536825752900840896181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20451024550501933893930787 30676536825752900840896181)
        ·
          refine ⟨2875925327414334453834017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 30676536825752900840896181 2875925327414334453834017)
          ·
            refine ⟨2156943995560750840375513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2875925327414334453834017 2156943995560750840375513)
            ·
              refine ⟨1617707996670563130281635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2156943995560750840375513 1617707996670563130281635)
              ·
                refine ⟨2426561995005844695422453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1617707996670563130281635 2426561995005844695422453)
                ·
                  refine ⟨227490187031797940195855, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2426561995005844695422453 227490187031797940195855)
                  ·
                    rfl

theorem cell20_498415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 2, 1, 5].length) (baseStart_498415 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_498415 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_498415 prefixEnd_498415 := by exact prefixLift 498415
  have htrace : WordTrace (prefixWord ++ tailWord_498415) baseStart_498415 baseEnd_498415 := by
    simpa [prefixWord, tailWord_498415, baseEnd_498415] using wordTrace_append hprefix tailTrace_498415
  have hstable : (prefixWord ++ tailWord_498415).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_498415).length < 2 ^ (prefixWord ++ tailWord_498415).sum := by decide
  have hdescent : baseEnd_498415 < baseStart_498415 := by decide
  rcases family_descends (prefixWord ++ tailWord_498415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_498418 : List Nat := [3, 2, 1, 3, 1, 4, 1, 1, 4]
def baseStart_498418 : Nat := 118140960795 + 498418 * 2 ^ 59
def prefixEnd_498418 : Nat := 4983230072969 + 3 ^ 40 * 498418 * 2
def baseEnd_498418 : Nat := 227491556313543263095843

theorem tailTrace_498418 : CollatzResearch.WordTrace tailWord_498418 prefixEnd_498418 227491556313543263095843 := by
  unfold tailWord_498418
  simp only [CollatzResearch.WordTrace]
  refine ⟨4544699477081045965629977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12119198605549455908346605 4544699477081045965629977)
  ·
    refine ⟨3408524607810784474222483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4544699477081045965629977 3408524607810784474222483)
    ·
      refine ⟨5112786911716176711333725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3408524607810784474222483 5112786911716176711333725)
      ·
        refine ⟨1917295091893566266750147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5112786911716176711333725 1917295091893566266750147)
        ·
          refine ⟨2875942637840349400125221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1917295091893566266750147 2875942637840349400125221)
          ·
            refine ⟨539239244595065512523479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2875942637840349400125221 539239244595065512523479)
            ·
              refine ⟨808858866892598268785219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 539239244595065512523479 808858866892598268785219)
              ·
                refine ⟨1213288300338897403177829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 808858866892598268785219 1213288300338897403177829)
                ·
                  refine ⟨227491556313543263095843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1213288300338897403177829 227491556313543263095843)
                  ·
                    rfl

theorem cell20_498418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 4, 1, 1, 4].length) (baseStart_498418 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_498418 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_498418 prefixEnd_498418 := by exact prefixLift 498418
  have htrace : WordTrace (prefixWord ++ tailWord_498418) baseStart_498418 baseEnd_498418 := by
    simpa [prefixWord, tailWord_498418, baseEnd_498418] using wordTrace_append hprefix tailTrace_498418
  have hstable : (prefixWord ++ tailWord_498418).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_498418).length < 2 ^ (prefixWord ++ tailWord_498418).sum := by decide
  have hdescent : baseEnd_498418 < baseStart_498418 := by decide
  rcases family_descends (prefixWord ++ tailWord_498418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_498421 : List Nat := [1, 3, 6, 1, 1, 1, 2, 5]
def baseStart_498421 : Nat := 118140960795 + 498421 * 2 ^ 59
def prefixEnd_498421 : Nat := 4983230072969 + 3 ^ 40 * 498421 * 2
def baseEnd_498421 : Nat := 75830975198429528665277

theorem tailTrace_498421 : CollatzResearch.WordTrace tailWord_498421 prefixEnd_498421 75830975198429528665277 := by
  unfold tailWord_498421
  simp only [CollatzResearch.WordTrace]
  refine ⟨18178907327313315374879117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12119271551542210249919411 18178907327313315374879117)
  ·
    refine ⟨6817090247742493265579669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18178907327313315374879117 6817090247742493265579669)
    ·
      refine ⟨319551105362929371824047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 6817090247742493265579669 319551105362929371824047)
      ·
        refine ⟨479326658044394057736071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 319551105362929371824047 479326658044394057736071)
        ·
          refine ⟨718989987066591086604107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 479326658044394057736071 718989987066591086604107)
          ·
            refine ⟨1078484980599886629906161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 718989987066591086604107 1078484980599886629906161)
            ·
              refine ⟨808863735449914972429621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1078484980599886629906161 808863735449914972429621)
              ·
                refine ⟨75830975198429528665277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 808863735449914972429621 75830975198429528665277)
                ·
                  rfl

theorem cell20_498421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 1, 2, 5].length) (baseStart_498421 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_498421 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_498421 prefixEnd_498421 := by exact prefixLift 498421
  have htrace : WordTrace (prefixWord ++ tailWord_498421) baseStart_498421 baseEnd_498421 := by
    simpa [prefixWord, tailWord_498421, baseEnd_498421] using wordTrace_append hprefix tailTrace_498421
  have hstable : (prefixWord ++ tailWord_498421).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_498421).length < 2 ^ (prefixWord ++ tailWord_498421).sum := by decide
  have hdescent : baseEnd_498421 < baseStart_498421 := by decide
  rcases family_descends (prefixWord ++ tailWord_498421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_498494 : List Nat := [4, 2, 1, 2, 3, 1, 1, 2, 4]
def baseStart_498494 : Nat := 118140960795 + 498494 * 2 ^ 59
def prefixEnd_498494 : Nat := 4983230072969 + 3 ^ 40 * 498494 * 2
def baseEnd_498494 : Nat := 227526244784424776562199

theorem tailTrace_498494 : CollatzResearch.WordTrace tailWord_498494 prefixEnd_498494 227526244784424776562199 := by
  unfold tailWord_498494
  simp only [CollatzResearch.WordTrace]
  refine ⟨2272696232006106105285817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12121046570699232561524357 2272696232006106105285817)
  ·
    refine ⟨1704522174004579578964363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2272696232006106105285817 1704522174004579578964363)
    ·
      refine ⟨2556783261006869368446545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1704522174004579578964363 2556783261006869368446545)
      ·
        refine ⟨1917587445755152026334909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2556783261006869368446545 1917587445755152026334909)
        ·
          refine ⟨719095292158182009875591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1917587445755152026334909 719095292158182009875591)
          ·
            refine ⟨1078642938237273014813387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 719095292158182009875591 1078642938237273014813387)
            ·
              refine ⟨1617964407355909522220081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1078642938237273014813387 1617964407355909522220081)
              ·
                refine ⟨1213473305516932141665061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1617964407355909522220081 1213473305516932141665061)
                ·
                  refine ⟨227526244784424776562199, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1213473305516932141665061 227526244784424776562199)
                  ·
                    rfl

theorem cell20_498494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 1, 1, 2, 4].length) (baseStart_498494 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_498494 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_498494 prefixEnd_498494 := by exact prefixLift 498494
  have htrace : WordTrace (prefixWord ++ tailWord_498494) baseStart_498494 baseEnd_498494 := by
    simpa [prefixWord, tailWord_498494, baseEnd_498494] using wordTrace_append hprefix tailTrace_498494
  have hstable : (prefixWord ++ tailWord_498494).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_498494).length < 2 ^ (prefixWord ++ tailWord_498494).sum := by decide
  have hdescent : baseEnd_498494 < baseStart_498494 := by decide
  rcases family_descends (prefixWord ++ tailWord_498494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_498529 : List Nat := [1, 2, 3, 1, 1, 1, 2, 6, 3]
def baseStart_498529 : Nat := 118140960795 + 498529 * 2 ^ 59
def prefixEnd_498529 : Nat := 4983230072969 + 3 ^ 40 * 498529 * 2
def baseEnd_498529 : Nat := 227542219738120210395389

theorem tailTrace_498529 : CollatzResearch.WordTrace tailWord_498529 prefixEnd_498529 227542219738120210395389 := by
  unfold tailWord_498529
  simp only [CollatzResearch.WordTrace]
  refine ⟨18182846410922049819810641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12121897607281366546540427 18182846410922049819810641)
  ·
    refine ⟨13637134808191537364857981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18182846410922049819810641 13637134808191537364857981)
    ·
      refine ⟨5113925553071826511821743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13637134808191537364857981 5113925553071826511821743)
      ·
        refine ⟨7670888329607739767732615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5113925553071826511821743 7670888329607739767732615)
        ·
          refine ⟨11506332494411609651598923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7670888329607739767732615 11506332494411609651598923)
          ·
            refine ⟨17259498741617414477398385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11506332494411609651598923 17259498741617414477398385)
            ·
              refine ⟨12944624056213060858048789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17259498741617414477398385 12944624056213060858048789)
              ·
                refine ⟨606779252634987227721037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 12944624056213060858048789 606779252634987227721037)
                ·
                  refine ⟨227542219738120210395389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 606779252634987227721037 227542219738120210395389)
                  ·
                    rfl

theorem cell20_498529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 6, 3].length) (baseStart_498529 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_498529 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_498529 prefixEnd_498529 := by exact prefixLift 498529
  have htrace : WordTrace (prefixWord ++ tailWord_498529) baseStart_498529 baseEnd_498529 := by
    simpa [prefixWord, tailWord_498529, baseEnd_498529] using wordTrace_append hprefix tailTrace_498529
  have hstable : (prefixWord ++ tailWord_498529).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_498529).length < 2 ^ (prefixWord ++ tailWord_498529).sum := by decide
  have hdescent : baseEnd_498529 < baseStart_498529 := by decide
  rcases family_descends (prefixWord ++ tailWord_498529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_498532 : List Nat := [2, 3, 1, 1, 4, 1, 2, 4, 2]
def baseStart_498532 : Nat := 118140960795 + 498532 * 2 ^ 59
def prefixEnd_498532 : Nat := 4983230072969 + 3 ^ 40 * 498532 * 2
def baseEnd_498532 : Nat := 227543589019865533295377

theorem tailTrace_498532 : CollatzResearch.WordTrace tailWord_498532 prefixEnd_498532 227543589019865533295377 := by
  unfold tailWord_498532
  simp only [CollatzResearch.WordTrace]
  refine ⟨9091477914955590666084925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12121970553274120888113233 9091477914955590666084925)
  ·
    refine ⟨3409304218108346499781847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9091477914955590666084925 3409304218108346499781847)
    ·
      refine ⟨5113956327162519749672771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3409304218108346499781847 5113956327162519749672771)
      ·
        refine ⟨7670934490743779624509157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5113956327162519749672771 7670934490743779624509157)
        ·
          refine ⟨1438300217014458679595467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7670934490743779624509157 1438300217014458679595467)
          ·
            refine ⟨2157450325521688019393201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1438300217014458679595467 2157450325521688019393201)
            ·
              refine ⟨1618087744141266014544901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2157450325521688019393201 1618087744141266014544901)
              ·
                refine ⟨303391452026487377727169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1618087744141266014544901 303391452026487377727169)
                ·
                  refine ⟨227543589019865533295377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 303391452026487377727169 227543589019865533295377)
                  ·
                    rfl

theorem cell20_498532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 2, 4, 2].length) (baseStart_498532 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_498532 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_498532 prefixEnd_498532 := by exact prefixLift 498532
  have htrace : WordTrace (prefixWord ++ tailWord_498532) baseStart_498532 baseEnd_498532 := by
    simpa [prefixWord, tailWord_498532, baseEnd_498532] using wordTrace_append hprefix tailTrace_498532
  have hstable : (prefixWord ++ tailWord_498532).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_498532).length < 2 ^ (prefixWord ++ tailWord_498532).sum := by decide
  have hdescent : baseEnd_498532 < baseStart_498532 := by decide
  rcases family_descends (prefixWord ++ tailWord_498532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_498542 : List Nat := [4, 1, 2, 3, 2, 1, 3, 1, 3]
def baseStart_498542 : Nat := 118140960795 + 498542 * 2 ^ 59
def prefixEnd_498542 : Nat := 4983230072969 + 3 ^ 40 * 498542 * 2
def baseEnd_498542 : Nat := 227548153292349942962003

theorem tailTrace_498542 : CollatzResearch.WordTrace tailWord_498542 prefixEnd_498542 227548153292349942962003 := by
  unfold tailWord_498542
  simp only [CollatzResearch.WordTrace]
  refine ⟨2272915069984369130004235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12122213706583302026689253 2272915069984369130004235)
  ·
    refine ⟨3409372604976553695006353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2272915069984369130004235 3409372604976553695006353)
    ·
      refine ⟨2557029453732415271254765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3409372604976553695006353 2557029453732415271254765)
      ·
        refine ⟨958886045149655726720537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2557029453732415271254765 958886045149655726720537)
        ·
          refine ⟨719164533862241795040403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 958886045149655726720537 719164533862241795040403)
          ·
            refine ⟨1078746800793362692560605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 719164533862241795040403 1078746800793362692560605)
            ·
              refine ⟨404530050297511009710227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1078746800793362692560605 404530050297511009710227)
              ·
                refine ⟨606795075446266514565341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 404530050297511009710227 606795075446266514565341)
                ·
                  refine ⟨227548153292349942962003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 606795075446266514565341 227548153292349942962003)
                  ·
                    rfl

theorem cell20_498542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 1, 3, 1, 3].length) (baseStart_498542 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_498542 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_498542 prefixEnd_498542 := by exact prefixLift 498542
  have htrace : WordTrace (prefixWord ++ tailWord_498542) baseStart_498542 baseEnd_498542 := by
    simpa [prefixWord, tailWord_498542, baseEnd_498542] using wordTrace_append hprefix tailTrace_498542
  have hstable : (prefixWord ++ tailWord_498542).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_498542).length < 2 ^ (prefixWord ++ tailWord_498542).sum := by decide
  have hdescent : baseEnd_498542 < baseStart_498542 := by decide
  rcases family_descends (prefixWord ++ tailWord_498542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_498562 : List Nat := [3, 4, 2, 2, 2, 1, 1, 3, 2]
def baseStart_498562 : Nat := 118140960795 + 498562 * 2 ^ 59
def prefixEnd_498562 : Nat := 4983230072969 + 3 ^ 40 * 498562 * 2
def baseEnd_498562 : Nat := 227557281837318762295255

theorem tailTrace_498562 : CollatzResearch.WordTrace tailWord_498562 prefixEnd_498562 227557281837318762295255 := by
  unfold tailWord_498562
  simp only [CollatzResearch.WordTrace]
  refine ⟨4546012504950624113940485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12122700013201664303841293 4546012504950624113940485)
  ·
    refine ⟨852377344678242021363841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4546012504950624113940485 852377344678242021363841)
    ·
      refine ⟨639283008508681516022881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 852377344678242021363841 639283008508681516022881)
      ·
        refine ⟨479462256381511137017161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 639283008508681516022881 479462256381511137017161)
        ·
          refine ⟨359596692286133352762871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 479462256381511137017161 359596692286133352762871)
          ·
            refine ⟨539395038429200029144307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 359596692286133352762871 539395038429200029144307)
            ·
              refine ⟨809092557643800043716461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 539395038429200029144307 809092557643800043716461)
              ·
                refine ⟨303409709116425016393673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 809092557643800043716461 303409709116425016393673)
                ·
                  refine ⟨227557281837318762295255, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 303409709116425016393673 227557281837318762295255)
                  ·
                    rfl

theorem cell20_498562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 2, 1, 1, 3, 2].length) (baseStart_498562 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_498562 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_498562 prefixEnd_498562 := by exact prefixLift 498562
  have htrace : WordTrace (prefixWord ++ tailWord_498562) baseStart_498562 baseEnd_498562 := by
    simpa [prefixWord, tailWord_498562, baseEnd_498562] using wordTrace_append hprefix tailTrace_498562
  have hstable : (prefixWord ++ tailWord_498562).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_498562).length < 2 ^ (prefixWord ++ tailWord_498562).sum := by decide
  have hdescent : baseEnd_498562 < baseStart_498562 := by decide
  rcases family_descends (prefixWord ++ tailWord_498562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_498567 : List Nat := [1, 1, 4, 2, 3, 1, 1, 2, 5]
def baseStart_498567 : Nat := 118140960795 + 498567 * 2 ^ 59
def prefixEnd_498567 : Nat := 4983230072969 + 3 ^ 40 * 498567 * 2
def baseEnd_498567 : Nat := 227559563973560967128567

theorem tailTrace_498567 : CollatzResearch.WordTrace tailWord_498567 prefixEnd_498567 227559563973560967128567 := by
  unfold tailWord_498567
  simp only [CollatzResearch.WordTrace]
  refine ⟨18184232384784382309693955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12122821589856254873129303 18184232384784382309693955)
  ·
    refine ⟨27276348577176573464540933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18184232384784382309693955 27276348577176573464540933)
    ·
      refine ⟨5114315358220607524601425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27276348577176573464540933 5114315358220607524601425)
      ·
        refine ⟨3835736518665455643451069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5114315358220607524601425 3835736518665455643451069)
        ·
          refine ⟨1438401194499545866294151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3835736518665455643451069 1438401194499545866294151)
          ·
            refine ⟨2157601791749318799441227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1438401194499545866294151 2157601791749318799441227)
            ·
              refine ⟨3236402687623978199161841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2157601791749318799441227 3236402687623978199161841)
              ·
                refine ⟨2427302015717983649371381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3236402687623978199161841 2427302015717983649371381)
                ·
                  refine ⟨227559563973560967128567, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2427302015717983649371381 227559563973560967128567)
                  ·
                    rfl

theorem cell20_498567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 1, 2, 5].length) (baseStart_498567 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_498567 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_498567 prefixEnd_498567 := by exact prefixLift 498567
  have htrace : WordTrace (prefixWord ++ tailWord_498567) baseStart_498567 baseEnd_498567 := by
    simpa [prefixWord, tailWord_498567, baseEnd_498567] using wordTrace_append hprefix tailTrace_498567
  have hstable : (prefixWord ++ tailWord_498567).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_498567).length < 2 ^ (prefixWord ++ tailWord_498567).sum := by decide
  have hdescent : baseEnd_498567 < baseStart_498567 := by decide
  rcases family_descends (prefixWord ++ tailWord_498567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_498581 : List Nat := [1, 3, 2, 1, 1, 4, 8]
def baseStart_498581 : Nat := 118140960795 + 498581 * 2 ^ 59
def prefixEnd_498581 : Nat := 4983230072969 + 3 ^ 40 * 498581 * 2
def baseEnd_498581 : Nat := 25285105995004348962427

theorem tailTrace_498581 : CollatzResearch.WordTrace tailWord_498581 prefixEnd_498581 25285105995004348962427 := by
  unfold tailWord_498581
  simp only [CollatzResearch.WordTrace]
  refine ⟨18184743006733662700703597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12123162004489108467135731 18184743006733662700703597)
  ·
    refine ⟨6819278627525123512763849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18184743006733662700703597 6819278627525123512763849)
    ·
      refine ⟨5114458970643842634572887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6819278627525123512763849 5114458970643842634572887)
      ·
        refine ⟨7671688455965763951859331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5114458970643842634572887 7671688455965763951859331)
        ·
          refine ⟨11507532683948645927788997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7671688455965763951859331 11507532683948645927788997)
          ·
            refine ⟨2157662378240371111460437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11507532683948645927788997 2157662378240371111460437)
            ·
              refine ⟨25285105995004348962427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2157662378240371111460437 25285105995004348962427)
              ·
                rfl

theorem cell20_498581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 8].length) (baseStart_498581 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_498581 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_498581 prefixEnd_498581 := by exact prefixLift 498581
  have htrace : WordTrace (prefixWord ++ tailWord_498581) baseStart_498581 baseEnd_498581 := by
    simpa [prefixWord, tailWord_498581, baseEnd_498581] using wordTrace_append hprefix tailTrace_498581
  have hstable : (prefixWord ++ tailWord_498581).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_498581).length < 2 ^ (prefixWord ++ tailWord_498581).sum := by decide
  have hdescent : baseEnd_498581 < baseStart_498581 := by decide
  rcases family_descends (prefixWord ++ tailWord_498581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_498591 : List Nat := [1, 1, 2, 5, 2, 1, 3, 1, 4]
def baseStart_498591 : Nat := 118140960795 + 498591 * 2 ^ 59
def prefixEnd_498591 : Nat := 4983230072969 + 3 ^ 40 * 498591 * 2
def baseEnd_498591 : Nat := 227570518227523550328469

theorem tailTrace_498591 : CollatzResearch.WordTrace tailWord_498591 prefixEnd_498591 227570518227523550328469 := by
  unfold tailWord_498591
  simp only [CollatzResearch.WordTrace]
  refine ⟨18185107736697434408567627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12123405157798289605711751 18185107736697434408567627)
  ·
    refine ⟨27277661605046151612851441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18185107736697434408567627 27277661605046151612851441)
    ·
      refine ⟨20458246203784613709638581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27277661605046151612851441 20458246203784613709638581)
      ·
        refine ⟨1917960581604807535278617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 20458246203784613709638581 1917960581604807535278617)
        ·
          refine ⟨1438470436203605651458963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1917960581604807535278617 1438470436203605651458963)
          ·
            refine ⟨2157705654305408477188445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1438470436203605651458963 2157705654305408477188445)
            ·
              refine ⟨809139620364528178945667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2157705654305408477188445 809139620364528178945667)
              ·
                refine ⟨1213709430546792268418501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 809139620364528178945667 1213709430546792268418501)
                ·
                  refine ⟨227570518227523550328469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1213709430546792268418501 227570518227523550328469)
                  ·
                    rfl

theorem cell20_498591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 3, 1, 4].length) (baseStart_498591 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_498591 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_498591 prefixEnd_498591 := by exact prefixLift 498591
  have htrace : WordTrace (prefixWord ++ tailWord_498591) baseStart_498591 baseEnd_498591 := by
    simpa [prefixWord, tailWord_498591, baseEnd_498591] using wordTrace_append hprefix tailTrace_498591
  have hstable : (prefixWord ++ tailWord_498591).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_498591).length < 2 ^ (prefixWord ++ tailWord_498591).sum := by decide
  have hdescent : baseEnd_498591 < baseStart_498591 := by decide
  rcases family_descends (prefixWord ++ tailWord_498591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_498642 : List Nat := [3, 2, 2, 3, 1, 3, 2, 2, 2]
def baseStart_498642 : Nat := 118140960795 + 498642 * 2 ^ 59
def prefixEnd_498642 : Nat := 4983230072969 + 3 ^ 40 * 498642 * 2
def baseEnd_498642 : Nat := 227593796017194039628261

theorem tailTrace_498642 : CollatzResearch.WordTrace tailWord_498642 prefixEnd_498642 227593796017194039628261 := by
  unfold tailWord_498642
  simp only [CollatzResearch.WordTrace]
  refine ⟨4546741964878167529668545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12124645239675113412449453 4546741964878167529668545)
  ·
    refine ⟨3410056473658625647251409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4546741964878167529668545 3410056473658625647251409)
    ·
      refine ⟨2557542355243969235438557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3410056473658625647251409 2557542355243969235438557)
      ·
        refine ⟨959078383216488463289459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2557542355243969235438557 959078383216488463289459)
        ·
          refine ⟨1438617574824732694934189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 959078383216488463289459 1438617574824732694934189)
          ·
            refine ⟨539481590559274760600321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1438617574824732694934189 539481590559274760600321)
            ·
              refine ⟨404611192919456070450241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 539481590559274760600321 404611192919456070450241)
              ·
                refine ⟨303458394689592052837681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 404611192919456070450241 303458394689592052837681)
                ·
                  refine ⟨227593796017194039628261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 303458394689592052837681 227593796017194039628261)
                  ·
                    rfl

theorem cell20_498642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 3, 2, 2, 2].length) (baseStart_498642 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_498642 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_498642 prefixEnd_498642 := by exact prefixLift 498642
  have htrace : WordTrace (prefixWord ++ tailWord_498642) baseStart_498642 baseEnd_498642 := by
    simpa [prefixWord, tailWord_498642, baseEnd_498642] using wordTrace_append hprefix tailTrace_498642
  have hstable : (prefixWord ++ tailWord_498642).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_498642).length < 2 ^ (prefixWord ++ tailWord_498642).sum := by decide
  have hdescent : baseEnd_498642 < baseStart_498642 := by decide
  rcases family_descends (prefixWord ++ tailWord_498642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_498653 : List Nat := [1, 4, 3, 1, 2, 3, 1, 5]
def baseStart_498653 : Nat := 118140960795 + 498653 * 2 ^ 59
def prefixEnd_498653 : Nat := 4983230072969 + 3 ^ 40 * 498653 * 2
def baseEnd_498653 : Nat := 75866272238975630087183

theorem tailTrace_498653 : CollatzResearch.WordTrace tailWord_498653 prefixEnd_498653 75866272238975630087183 := by
  unfold tailWord_498653
  simp only [CollatzResearch.WordTrace]
  refine ⟨18187369062472818997324613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12124912708315212664883075 18187369062472818997324613)
  ·
    refine ⟨3410131699213653561998365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 18187369062472818997324613 3410131699213653561998365)
    ·
      refine ⟨1278799387205120085749387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3410131699213653561998365 1278799387205120085749387)
      ·
        refine ⟨1918199080807680128624081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1278799387205120085749387 1918199080807680128624081)
        ·
          refine ⟨1438649310605760096468061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1918199080807680128624081 1438649310605760096468061)
          ·
            refine ⟨539493491477160036175523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1438649310605760096468061 539493491477160036175523)
            ·
              refine ⟨809240237215740054263285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 539493491477160036175523 809240237215740054263285)
              ·
                refine ⟨75866272238975630087183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 809240237215740054263285 75866272238975630087183)
                ·
                  rfl

theorem cell20_498653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 3, 1, 5].length) (baseStart_498653 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_498653 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_498653 prefixEnd_498653 := by exact prefixLift 498653
  have htrace : WordTrace (prefixWord ++ tailWord_498653) baseStart_498653 baseEnd_498653 := by
    simpa [prefixWord, tailWord_498653, baseEnd_498653] using wordTrace_append hprefix tailTrace_498653
  have hstable : (prefixWord ++ tailWord_498653).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_498653).length < 2 ^ (prefixWord ++ tailWord_498653).sum := by decide
  have hdescent : baseEnd_498653 < baseStart_498653 := by decide
  rcases family_descends (prefixWord ++ tailWord_498653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_498676 : List Nat := [2, 6, 2, 1, 1, 1, 2, 3, 2]
def baseStart_498676 : Nat := 118140960795 + 498676 * 2 ^ 59
def prefixEnd_498676 : Nat := 4983230072969 + 3 ^ 40 * 498676 * 2
def baseEnd_498676 : Nat := 227609314543641032494789

theorem tailTrace_498676 : CollatzResearch.WordTrace tailWord_498676 prefixEnd_498676 227609314543641032494789 := by
  unfold tailWord_498676
  simp only [CollatzResearch.WordTrace]
  refine ⟨9094103970694746962705941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12125471960926329283607921 9094103970694746962705941)
  ·
    refine ⟨426286123626316263876841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 9094103970694746962705941 426286123626316263876841)
    ·
      refine ⟨319714592719737197907631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 426286123626316263876841 319714592719737197907631)
      ·
        refine ⟨479571889079605796861447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 319714592719737197907631 479571889079605796861447)
        ·
          refine ⟨719357833619408695292171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 479571889079605796861447 719357833619408695292171)
          ·
            refine ⟨1079036750429113042938257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 719357833619408695292171 1079036750429113042938257)
            ·
              refine ⟨809277562821834782203693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1079036750429113042938257 809277562821834782203693)
              ·
                refine ⟨303479086058188043326385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 809277562821834782203693 303479086058188043326385)
                ·
                  refine ⟨227609314543641032494789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 303479086058188043326385 227609314543641032494789)
                  ·
                    rfl

theorem cell20_498676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 1, 2, 3, 2].length) (baseStart_498676 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_498676 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_498676 prefixEnd_498676 := by exact prefixLift 498676
  have htrace : WordTrace (prefixWord ++ tailWord_498676) baseStart_498676 baseEnd_498676 := by
    simpa [prefixWord, tailWord_498676, baseEnd_498676] using wordTrace_append hprefix tailTrace_498676
  have hstable : (prefixWord ++ tailWord_498676).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_498676).length < 2 ^ (prefixWord ++ tailWord_498676).sum := by decide
  have hdescent : baseEnd_498676 < baseStart_498676 := by decide
  rcases family_descends (prefixWord ++ tailWord_498676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_498684 : List Nat := [2, 2, 2, 1, 2, 4, 2, 3, 2]
def baseStart_498684 : Nat := 118140960795 + 498684 * 2 ^ 59
def prefixEnd_498684 : Nat := 4983230072969 + 3 ^ 40 * 498684 * 2
def baseEnd_498684 : Nat := 227612965961628560228089

theorem tailTrace_498684 : CollatzResearch.WordTrace tailWord_498684 prefixEnd_498684 227612965961628560228089 := by
  unfold tailWord_498684
  simp only [CollatzResearch.WordTrace]
  refine ⟨9094249862680255645851553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12125666483573674194468737 9094249862680255645851553)
  ·
    refine ⟨6820687397010191734388665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9094249862680255645851553 6820687397010191734388665)
    ·
      refine ⟨5115515547757643800791499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6820687397010191734388665 5115515547757643800791499)
      ·
        refine ⟨7673273321636465701187249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5115515547757643800791499 7673273321636465701187249)
        ·
          refine ⟨5754954991227349275890437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7673273321636465701187249 5754954991227349275890437)
          ·
            refine ⟨1079054060855127989229457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5754954991227349275890437 1079054060855127989229457)
            ·
              refine ⟨809290545641345991922093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1079054060855127989229457 809290545641345991922093)
              ·
                refine ⟨303483954615504746970785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 809290545641345991922093 303483954615504746970785)
                ·
                  refine ⟨227612965961628560228089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 303483954615504746970785 227612965961628560228089)
                  ·
                    rfl

theorem cell20_498684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 4, 2, 3, 2].length) (baseStart_498684 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_498684 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_498684 prefixEnd_498684 := by exact prefixLift 498684
  have htrace : WordTrace (prefixWord ++ tailWord_498684) baseStart_498684 baseEnd_498684 := by
    simpa [prefixWord, tailWord_498684, baseEnd_498684] using wordTrace_append hprefix tailTrace_498684
  have hstable : (prefixWord ++ tailWord_498684).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_498684).length < 2 ^ (prefixWord ++ tailWord_498684).sum := by decide
  have hdescent : baseEnd_498684 < baseStart_498684 := by decide
  rcases family_descends (prefixWord ++ tailWord_498684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_498695 : List Nat := [1, 1, 4, 3, 1, 1, 9]
def baseStart_498695 : Nat := 118140960795 + 498695 * 2 ^ 59
def prefixEnd_498695 : Nat := 4983230072969 + 3 ^ 40 * 498695 * 2
def baseEnd_498695 : Nat := 25290887406817934540153

theorem tailTrace_498695 : CollatzResearch.WordTrace tailWord_498695 prefixEnd_498695 25290887406817934540153 := by
  unfold tailWord_498695
  simp only [CollatzResearch.WordTrace]
  refine ⟨18188900928320660170353539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12125933952213773446902359 18188900928320660170353539)
  ·
    refine ⟨27283351392480990255530309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18188900928320660170353539 27283351392480990255530309)
    ·
      refine ⟨5115628386090185672911933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 27283351392480990255530309 5115628386090185672911933)
      ·
        refine ⟨1918360644783819627341975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5115628386090185672911933 1918360644783819627341975)
        ·
          refine ⟨2877540967175729441012963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1918360644783819627341975 2877540967175729441012963)
          ·
            refine ⟨4316311450763594161519445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2877540967175729441012963 4316311450763594161519445)
            ·
              refine ⟨25290887406817934540153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 4316311450763594161519445 25290887406817934540153)
              ·
                rfl

theorem cell20_498695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 9].length) (baseStart_498695 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_498695 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_498695 prefixEnd_498695 := by exact prefixLift 498695
  have htrace : WordTrace (prefixWord ++ tailWord_498695) baseStart_498695 baseEnd_498695 := by
    simpa [prefixWord, tailWord_498695, baseEnd_498695] using wordTrace_append hprefix tailTrace_498695
  have hstable : (prefixWord ++ tailWord_498695).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_498695).length < 2 ^ (prefixWord ++ tailWord_498695).sum := by decide
  have hdescent : baseEnd_498695 < baseStart_498695 := by decide
  rcases family_descends (prefixWord ++ tailWord_498695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_498698 : List Nat := [3, 1, 2, 2, 3, 1, 3, 2, 3]
def baseStart_498698 : Nat := 118140960795 + 498698 * 2 ^ 59
def prefixEnd_498698 : Nat := 4983230072969 + 3 ^ 40 * 498698 * 2
def baseEnd_498698 : Nat := 227619355943106733761365

theorem tailTrace_498698 : CollatzResearch.WordTrace tailWord_498698 prefixEnd_498698 227619355943106733761365 := by
  unfold tailWord_498698
  simp only [CollatzResearch.WordTrace]
  refine ⟨4547252586827447920678187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12126006898206527788475165 4547252586827447920678187)
  ·
    refine ⟨6820878880241171881017281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4547252586827447920678187 6820878880241171881017281)
    ·
      refine ⟨5115659160180878910762961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6820878880241171881017281 5115659160180878910762961)
      ·
        refine ⟨3836744370135659183072221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5115659160180878910762961 3836744370135659183072221)
        ·
          refine ⟨1438779138800872193652083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3836744370135659183072221 1438779138800872193652083)
          ·
            refine ⟨2158168708201308290478125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1438779138800872193652083 2158168708201308290478125)
            ·
              refine ⟨809313265575490608929297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2158168708201308290478125 809313265575490608929297)
              ·
                refine ⟨606984949181617956696973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 809313265575490608929297 606984949181617956696973)
                ·
                  refine ⟨227619355943106733761365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 606984949181617956696973 227619355943106733761365)
                  ·
                    rfl

theorem cell20_498698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 3, 2, 3].length) (baseStart_498698 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_498698 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_498698 prefixEnd_498698 := by exact prefixLift 498698
  have htrace : WordTrace (prefixWord ++ tailWord_498698) baseStart_498698 baseEnd_498698 := by
    simpa [prefixWord, tailWord_498698, baseEnd_498698] using wordTrace_append hprefix tailTrace_498698
  have hstable : (prefixWord ++ tailWord_498698).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_498698).length < 2 ^ (prefixWord ++ tailWord_498698).sum := by decide
  have hdescent : baseEnd_498698 < baseStart_498698 := by decide
  rcases family_descends (prefixWord ++ tailWord_498698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_498750 : List Nat := [4, 2, 1, 3, 1, 1, 8]
def baseStart_498750 : Nat := 118140960795 + 498750 * 2 ^ 59
def prefixEnd_498750 : Nat := 4983230072969 + 3 ^ 40 * 498750 * 2
def baseEnd_498750 : Nat := 25293676684447296003091

theorem tailTrace_498750 : CollatzResearch.WordTrace tailWord_498750 prefixEnd_498750 25293676684447296003091 := by
  unfold tailWord_498750
  simp only [CollatzResearch.WordTrace]
  refine ⟨2273863367890175570450713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 12127271295414269709070469 2273863367890175570450713)
  ·
    refine ⟨1705397525917631677838035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2273863367890175570450713 1705397525917631677838035)
    ·
      refine ⟨2558096288876447516757053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1705397525917631677838035 2558096288876447516757053)
      ·
        refine ⟨959286108328667818783895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2558096288876447516757053 959286108328667818783895)
        ·
          refine ⟨1438929162493001728175843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 959286108328667818783895 1438929162493001728175843)
          ·
            refine ⟨2158393743739502592263765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1438929162493001728175843 2158393743739502592263765)
            ·
              refine ⟨25293676684447296003091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2158393743739502592263765 25293676684447296003091)
              ·
                rfl

theorem cell20_498750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 8].length) (baseStart_498750 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_498750 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_498750 prefixEnd_498750 := by exact prefixLift 498750
  have htrace : WordTrace (prefixWord ++ tailWord_498750) baseStart_498750 baseEnd_498750 := by
    simpa [prefixWord, tailWord_498750, baseEnd_498750] using wordTrace_append hprefix tailTrace_498750
  have hstable : (prefixWord ++ tailWord_498750).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_498750).length < 2 ^ (prefixWord ++ tailWord_498750).sum := by decide
  have hdescent : baseEnd_498750 < baseStart_498750 := by decide
  rcases family_descends (prefixWord ++ tailWord_498750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_498760 : List Nat := [2, 1, 3, 1, 1, 1, 7, 2, 2]
def baseStart_498760 : Nat := 118140960795 + 498760 * 2 ^ 59
def prefixEnd_498760 : Nat := 4983230072969 + 3 ^ 40 * 498760 * 2
def baseEnd_498760 : Nat := 227647654432510073694445

theorem tailTrace_498760 : CollatzResearch.WordTrace tailWord_498760 prefixEnd_498760 227647654432510073694445 := by
  unfold tailWord_498760
  simp only [CollatzResearch.WordTrace]
  refine ⟨9095635836542588135734867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12127514448723450847646489 9095635836542588135734867)
  ·
    refine ⟨13643453754813882203602301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9095635836542588135734867 13643453754813882203602301)
    ·
      refine ⟨5116295158055205826350863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13643453754813882203602301 5116295158055205826350863)
      ·
        refine ⟨7674442737082808739526295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5116295158055205826350863 7674442737082808739526295)
        ·
          refine ⟨11511664105624213109289443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7674442737082808739526295 11511664105624213109289443)
          ·
            refine ⟨17267496158436319663934165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11511664105624213109289443 17267496158436319663934165)
            ·
              refine ⟨404706941213351242123457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 17267496158436319663934165 404706941213351242123457)
              ·
                refine ⟨303530205910013431592593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 404706941213351242123457 303530205910013431592593)
                ·
                  refine ⟨227647654432510073694445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 303530205910013431592593 227647654432510073694445)
                  ·
                    rfl

theorem cell20_498760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 7, 2, 2].length) (baseStart_498760 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_498760 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_498760 prefixEnd_498760 := by exact prefixLift 498760
  have htrace : WordTrace (prefixWord ++ tailWord_498760) baseStart_498760 baseEnd_498760 := by
    simpa [prefixWord, tailWord_498760, baseEnd_498760] using wordTrace_append hprefix tailTrace_498760
  have hstable : (prefixWord ++ tailWord_498760).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_498760).length < 2 ^ (prefixWord ++ tailWord_498760).sum := by decide
  have hdescent : baseEnd_498760 < baseStart_498760 := by decide
  rcases family_descends (prefixWord ++ tailWord_498760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_498778 : List Nat := [3, 1, 1, 2, 1, 1, 2, 2, 7]
def baseStart_498778 : Nat := 118140960795 + 498778 * 2 ^ 59
def prefixEnd_498778 : Nat := 4983230072969 + 3 ^ 40 * 498778 * 2
def baseEnd_498778 : Nat := 227655870122982011094371

theorem tailTrace_498778 : CollatzResearch.WordTrace tailWord_498778 prefixEnd_498778 227655870122982011094371 := by
  unfold tailWord_498778
  simp only [CollatzResearch.WordTrace]
  refine ⟨4547982046754991336406247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 12127952124679976897083325 4547982046754991336406247)
  ·
    refine ⟨6821973070132487004609371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4547982046754991336406247 6821973070132487004609371)
    ·
      refine ⟨10232959605198730506914057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6821973070132487004609371 10232959605198730506914057)
      ·
        refine ⟨7674719703899047880185543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10232959605198730506914057 7674719703899047880185543)
        ·
          refine ⟨11512079555848571820278315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7674719703899047880185543 11512079555848571820278315)
          ·
            refine ⟨17268119333772857730417473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11512079555848571820278315 17268119333772857730417473)
            ·
              refine ⟨12951089500329643297813105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17268119333772857730417473 12951089500329643297813105)
              ·
                refine ⟨9713317125247232473359829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12951089500329643297813105 9713317125247232473359829)
                ·
                  refine ⟨227655870122982011094371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9713317125247232473359829 227655870122982011094371)
                  ·
                    rfl

theorem cell20_498778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 2, 7].length) (baseStart_498778 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_498778 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_498778 prefixEnd_498778 := by exact prefixLift 498778
  have htrace : WordTrace (prefixWord ++ tailWord_498778) baseStart_498778 baseEnd_498778 := by
    simpa [prefixWord, tailWord_498778, baseEnd_498778] using wordTrace_append hprefix tailTrace_498778
  have hstable : (prefixWord ++ tailWord_498778).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_498778).length < 2 ^ (prefixWord ++ tailWord_498778).sum := by decide
  have hdescent : baseEnd_498778 < baseStart_498778 := by decide
  rcases family_descends (prefixWord ++ tailWord_498778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_498805 : List Nat := [1, 3, 4, 3, 2, 7]
def baseStart_498805 : Nat := 118140960795 + 498805 * 2 ^ 59
def prefixEnd_498805 : Nat := 4983230072969 + 3 ^ 40 * 498805 * 2
def baseEnd_498805 : Nat := 8432155320692219155343

theorem tailTrace_498805 : CollatzResearch.WordTrace tailWord_498805 prefixEnd_498805 8432155320692219155343 := by
  unfold tailWord_498805
  simp only [CollatzResearch.WordTrace]
  refine ⟨18192912957922148956857869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12128608638614765971238579 18192912957922148956857869)
  ·
    refine ⟨6822342359220805858821701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18192912957922148956857869 6822342359220805858821701)
    ·
      refine ⟨1279189192353901098529069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6822342359220805858821701 1279189192353901098529069)
      ·
        refine ⟨479695947132712911948401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1279189192353901098529069 479695947132712911948401)
        ·
          refine ⟨359771960349534683961301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 479695947132712911948401 359771960349534683961301)
          ·
            refine ⟨8432155320692219155343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 359771960349534683961301 8432155320692219155343)
            ·
              rfl

theorem cell20_498805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 2, 7].length) (baseStart_498805 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_498805 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_498805 prefixEnd_498805 := by exact prefixLift 498805
  have htrace : WordTrace (prefixWord ++ tailWord_498805) baseStart_498805 baseEnd_498805 := by
    simpa [prefixWord, tailWord_498805, baseEnd_498805] using wordTrace_append hprefix tailTrace_498805
  have hstable : (prefixWord ++ tailWord_498805).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_498805).length < 2 ^ (prefixWord ++ tailWord_498805).sum := by decide
  have hdescent : baseEnd_498805 < baseStart_498805 := by decide
  rcases family_descends (prefixWord ++ tailWord_498805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_498809 : List Nat := [1, 2, 1, 3, 5, 8]
def baseStart_498809 : Nat := 118140960795 + 498809 * 2 ^ 59
def prefixEnd_498809 : Nat := 4983230072969 + 3 ^ 40 * 498809 * 2
def baseEnd_498809 : Nat := 8432222939543840039293

theorem tailTrace_498809 : CollatzResearch.WordTrace tailWord_498809 prefixEnd_498809 8432222939543840039293 := by
  unfold tailWord_498809
  simp only [CollatzResearch.WordTrace]
  refine ⟨18193058849907657640003481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12128705899938438426668987 18193058849907657640003481)
  ·
    refine ⟨13644794137430743230002611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18193058849907657640003481 13644794137430743230002611)
    ·
      refine ⟨20467191206146114845003917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13644794137430743230002611 20467191206146114845003917)
      ·
        refine ⟨7675196702304793066876469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20467191206146114845003917 7675196702304793066876469)
        ·
          refine ⟨719549690841074350019669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 7675196702304793066876469 719549690841074350019669)
          ·
            refine ⟨8432222939543840039293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 719549690841074350019669 8432222939543840039293)
            ·
              rfl

theorem cell20_498809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 8].length) (baseStart_498809 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_498809 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_498809 prefixEnd_498809 := by exact prefixLift 498809
  have htrace : WordTrace (prefixWord ++ tailWord_498809) baseStart_498809 baseEnd_498809 := by
    simpa [prefixWord, tailWord_498809, baseEnd_498809] using wordTrace_append hprefix tailTrace_498809
  have hstable : (prefixWord ++ tailWord_498809).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_498809).length < 2 ^ (prefixWord ++ tailWord_498809).sum := by decide
  have hdescent : baseEnd_498809 < baseStart_498809 := by decide
  rcases family_descends (prefixWord ++ tailWord_498809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_498816 : List Nat := [2, 1, 1, 2, 1, 3, 2, 3, 5]
def baseStart_498816 : Nat := 118140960795 + 498816 * 2 ^ 59
def prefixEnd_498816 : Nat := 4983230072969 + 3 ^ 40 * 498816 * 2
def baseEnd_498816 : Nat := 227673214358422767827549

theorem tailTrace_498816 : CollatzResearch.WordTrace tailWord_498816 prefixEnd_498816 227673214358422767827549 := by
  unfold tailWord_498816
  simp only [CollatzResearch.WordTrace]
  refine ⟨9096657080441148917754151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12128876107254865223672201 9096657080441148917754151)
  ·
    refine ⟨13644985620661723376631227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9096657080441148917754151 13644985620661723376631227)
    ·
      refine ⟨20467478430992585064946841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13644985620661723376631227 20467478430992585064946841)
      ·
        refine ⟨15350608823244438798710131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20467478430992585064946841 15350608823244438798710131)
        ·
          refine ⟨23025913234866658198065197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15350608823244438798710131 23025913234866658198065197)
          ·
            refine ⟨8634717463074996824274449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23025913234866658198065197 8634717463074996824274449)
            ·
              refine ⟨6476038097306247618205837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8634717463074996824274449 6476038097306247618205837)
              ·
                refine ⟨2428514286489842856827189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6476038097306247618205837 2428514286489842856827189)
                ·
                  refine ⟨227673214358422767827549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2428514286489842856827189 227673214358422767827549)
                  ·
                    rfl

theorem cell20_498816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 2, 3, 5].length) (baseStart_498816 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_498816 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_498816 prefixEnd_498816 := by exact prefixLift 498816
  have htrace : WordTrace (prefixWord ++ tailWord_498816) baseStart_498816 baseEnd_498816 := by
    simpa [prefixWord, tailWord_498816, baseEnd_498816] using wordTrace_append hprefix tailTrace_498816
  have hstable : (prefixWord ++ tailWord_498816).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_498816).length < 2 ^ (prefixWord ++ tailWord_498816).sum := by decide
  have hdescent : baseEnd_498816 < baseStart_498816 := by decide
  rcases family_descends (prefixWord ++ tailWord_498816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_498819 : List Nat := [1, 1, 1, 3, 3, 2, 3, 4, 2]
def baseStart_498819 : Nat := 118140960795 + 498819 * 2 ^ 59
def prefixEnd_498819 : Nat := 4983230072969 + 3 ^ 40 * 498819 * 2
def baseEnd_498819 : Nat := 227674583640168090727537

theorem tailTrace_498819 : CollatzResearch.WordTrace tailWord_498819 prefixEnd_498819 227674583640168090727537 := by
  unfold tailWord_498819
  simp only [CollatzResearch.WordTrace]
  refine ⟨18193423579871429347867511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 12128949053247619565245007 18193423579871429347867511)
  ·
    refine ⟨27290135369807144021801267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18193423579871429347867511 27290135369807144021801267)
    ·
      refine ⟨40935203054710716032701901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27290135369807144021801267 40935203054710716032701901)
      ·
        refine ⟨15350701145516518512263213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40935203054710716032701901 15350701145516518512263213)
        ·
          refine ⟨5756512929568694442098705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15350701145516518512263213 5756512929568694442098705)
          ·
            refine ⟨4317384697176520831574029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5756512929568694442098705 4317384697176520831574029)
            ·
              refine ⟨1619019261441195311840261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4317384697176520831574029 1619019261441195311840261)
              ·
                refine ⟨303566111520224120970049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1619019261441195311840261 303566111520224120970049)
                ·
                  refine ⟨227674583640168090727537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 303566111520224120970049 227674583640168090727537)
                  ·
                    rfl

theorem cell20_498819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 3, 4, 2].length) (baseStart_498819 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_498819 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_498819 prefixEnd_498819 := by exact prefixLift 498819
  have htrace : WordTrace (prefixWord ++ tailWord_498819) baseStart_498819 baseEnd_498819 := by
    simpa [prefixWord, tailWord_498819, baseEnd_498819] using wordTrace_append hprefix tailTrace_498819
  have hstable : (prefixWord ++ tailWord_498819).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_498819).length < 2 ^ (prefixWord ++ tailWord_498819).sum := by decide
  have hdescent : baseEnd_498819 < baseStart_498819 := by decide
  rcases family_descends (prefixWord ++ tailWord_498819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_498840 : List Nat := [2, 1, 2, 4, 2, 1, 1, 1, 6]
def baseStart_498840 : Nat := 118140960795 + 498840 * 2 ^ 59
def prefixEnd_498840 : Nat := 4983230072969 + 3 ^ 40 * 498840 * 2
def baseEnd_498840 : Nat := 227684168612385351027451

theorem tailTrace_498840 : CollatzResearch.WordTrace tailWord_498840 prefixEnd_498840 227684168612385351027451 := by
  unfold tailWord_498840
  simp only [CollatzResearch.WordTrace]
  refine ⟨9097094756397674967190987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12129459675196899956254649 9097094756397674967190987)
  ·
    refine ⟨13645642134596512450786481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9097094756397674967190987 13645642134596512450786481)
    ·
      refine ⟨10234231600947384338089861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13645642134596512450786481 10234231600947384338089861)
      ·
        refine ⟨1918918425177634563391849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10234231600947384338089861 1918918425177634563391849)
        ·
          refine ⟨1439188818883225922543887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1918918425177634563391849 1439188818883225922543887)
          ·
            refine ⟨2158783228324838883815831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1439188818883225922543887 2158783228324838883815831)
            ·
              refine ⟨3238174842487258325723747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2158783228324838883815831 3238174842487258325723747)
              ·
                refine ⟨4857262263730887488585621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3238174842487258325723747 4857262263730887488585621)
                ·
                  refine ⟨227684168612385351027451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4857262263730887488585621 227684168612385351027451)
                  ·
                    rfl

theorem cell20_498840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 1, 1, 6].length) (baseStart_498840 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_498840 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_498840 prefixEnd_498840 := by exact prefixLift 498840
  have htrace : WordTrace (prefixWord ++ tailWord_498840) baseStart_498840 baseEnd_498840 := by
    simpa [prefixWord, tailWord_498840, baseEnd_498840] using wordTrace_append hprefix tailTrace_498840
  have hstable : (prefixWord ++ tailWord_498840).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_498840).length < 2 ^ (prefixWord ++ tailWord_498840).sum := by decide
  have hdescent : baseEnd_498840 < baseStart_498840 := by decide
  rcases family_descends (prefixWord ++ tailWord_498840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_498912 : List Nat := [2, 1, 1, 3, 1, 6, 1, 3, 2]
def baseStart_498912 : Nat := 118140960795 + 498912 * 2 ^ 59
def prefixEnd_498912 : Nat := 4983230072969 + 3 ^ 40 * 498912 * 2
def baseEnd_498912 : Nat := 227717031374273100627157

theorem tailTrace_498912 : CollatzResearch.WordTrace tailWord_498912 prefixEnd_498912 227717031374273100627157 := by
  unfold tailWord_498912
  simp only [CollatzResearch.WordTrace]
  refine ⟨9098407784267253115501495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 12131210379023004154001993 9098407784267253115501495)
  ·
    refine ⟨13647611676400879673252243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9098407784267253115501495 13647611676400879673252243)
    ·
      refine ⟨20471417514601319509878365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13647611676400879673252243 20471417514601319509878365)
      ·
        refine ⟨7676781567975494816204387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20471417514601319509878365 7676781567975494816204387)
        ·
          refine ⟨11515172351963242224306581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7676781567975494816204387 11515172351963242224306581)
          ·
            refine ⟨539773703998276979264371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 11515172351963242224306581 539773703998276979264371)
            ·
              refine ⟨809660555997415468896557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 539773703998276979264371 809660555997415468896557)
              ·
                refine ⟨303622708499030800836209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 809660555997415468896557 303622708499030800836209)
                ·
                  refine ⟨227717031374273100627157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 303622708499030800836209 227717031374273100627157)
                  ·
                    rfl

theorem cell20_498912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 6, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 6, 1, 3, 2].length) (baseStart_498912 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_498912 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_498912 prefixEnd_498912 := by exact prefixLift 498912
  have htrace : WordTrace (prefixWord ++ tailWord_498912) baseStart_498912 baseEnd_498912 := by
    simpa [prefixWord, tailWord_498912, baseEnd_498912] using wordTrace_append hprefix tailTrace_498912
  have hstable : (prefixWord ++ tailWord_498912).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_498912).length < 2 ^ (prefixWord ++ tailWord_498912).sum := by decide
  have hdescent : baseEnd_498912 < baseStart_498912 := by decide
  rcases family_descends (prefixWord ++ tailWord_498912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan20Incremental
