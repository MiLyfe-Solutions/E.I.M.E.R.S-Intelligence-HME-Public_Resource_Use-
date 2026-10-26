import V185TrunkScan23Chunk0826

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_4891837 : List Nat := [1, 4, 1, 2, 1, 1, 3, 2, 3, 1, 4]
def baseStart_4891837 : Nat := 118140960795 + 4891837 * 2 ^ 59
def prefixEnd_4891837 : Nat := 4983230072969 + 3 ^ 40 * 4891837 * 2
def baseEnd_4891837 : Nat := 2511863664448282398940357

theorem tailTrace_4891837 : CollatzResearch.WordTrace tailWord_4891837 prefixEnd_4891837 2511863664448282398940357 := by
  unfold tailWord_4891837
  simp only [CollatzResearch.WordTrace]
  refine ⟨178419953178717483090401765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118946635452478322060267843 178419953178717483090401765)
  ·
    refine ⟨33453741221009528079450331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 178419953178717483090401765 33453741221009528079450331)
    ·
      refine ⟨50180611831514292119175497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33453741221009528079450331 50180611831514292119175497)
      ·
        refine ⟨37635458873635719089381623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50180611831514292119175497 37635458873635719089381623)
        ·
          refine ⟨56453188310453578634072435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37635458873635719089381623 56453188310453578634072435)
          ·
            refine ⟨84679782465680367951108653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56453188310453578634072435 84679782465680367951108653)
            ·
              refine ⟨31754918424630137981665745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 84679782465680367951108653 31754918424630137981665745)
              ·
                refine ⟨23816188818472603486249309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31754918424630137981665745 23816188818472603486249309)
                ·
                  refine ⟨8931070806927226307343491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23816188818472603486249309 8931070806927226307343491)
                  ·
                    refine ⟨13396606210390839461015237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8931070806927226307343491 13396606210390839461015237)
                    ·
                      refine ⟨2511863664448282398940357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13396606210390839461015237 2511863664448282398940357)
                      ·
                        rfl

theorem cell23_4891837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 3, 2, 3, 1, 4].length) (baseStart_4891837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4891837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4891837 prefixEnd_4891837 := by exact prefixLift 4891837
  have htrace : WordTrace (prefixWord ++ tailWord_4891837) baseStart_4891837 baseEnd_4891837 := by
    simpa [prefixWord, tailWord_4891837, baseEnd_4891837] using wordTrace_append hprefix tailTrace_4891837
  have hstable : (prefixWord ++ tailWord_4891837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4891837).length < 2 ^ (prefixWord ++ tailWord_4891837).sum := by decide
  have hdescent : baseEnd_4891837 < baseStart_4891837 := by decide
  rcases family_descends (prefixWord ++ tailWord_4891837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4891877 : List Nat := [1, 3, 1, 4, 3, 1, 10]
def baseStart_4891877 : Nat := 118140960795 + 4891877 * 2 ^ 59
def prefixEnd_4891877 : Nat := 4983230072969 + 3 ^ 40 * 4891877 * 2
def baseEnd_4891877 : Nat := 31010916094746447437533

theorem tailTrace_4891877 : CollatzResearch.WordTrace tailWord_4891877 prefixEnd_4891877 31010916094746447437533 := by
  unfold tailWord_4891877
  simp only [CollatzResearch.WordTrace]
  refine ⟨178421412098572569921857885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118947608065715046614571923 178421412098572569921857885)
  ·
    refine ⟨66908029536964713720696707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 178421412098572569921857885 66908029536964713720696707)
    ·
      refine ⟨100362044305447070581045061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66908029536964713720696707 100362044305447070581045061)
      ·
        refine ⟨18817883307271325733945949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 100362044305447070581045061 18817883307271325733945949)
        ·
          refine ⟨7056706240226747150229731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18817883307271325733945949 7056706240226747150229731)
          ·
            refine ⟨10585059360340120725344597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7056706240226747150229731 10585059360340120725344597)
            ·
              refine ⟨31010916094746447437533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 10585059360340120725344597 31010916094746447437533)
              ·
                rfl

theorem cell23_4891877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 1, 10].length) (baseStart_4891877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4891877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4891877 prefixEnd_4891877 := by exact prefixLift 4891877
  have htrace : WordTrace (prefixWord ++ tailWord_4891877) baseStart_4891877 baseEnd_4891877 := by
    simpa [prefixWord, tailWord_4891877, baseEnd_4891877] using wordTrace_append hprefix tailTrace_4891877
  have hstable : (prefixWord ++ tailWord_4891877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4891877).length < 2 ^ (prefixWord ++ tailWord_4891877).sum := by decide
  have hdescent : baseEnd_4891877 < baseStart_4891877 := by decide
  rcases family_descends (prefixWord ++ tailWord_4891877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4891984 : List Nat := [2, 1, 1, 1, 1, 5, 2, 5, 5]
def baseStart_4891984 : Nat := 118140960795 + 4891984 * 2 ^ 59
def prefixEnd_4891984 : Nat := 4983230072969 + 3 ^ 40 * 4891984 * 2
def baseEnd_4891984 : Nat := 279104349567165924866909

theorem tailTrace_4891984 : CollatzResearch.WordTrace tailWord_4891984 prefixEnd_4891984 279104349567165924866909 := by
  unfold tailWord_4891984
  simp only [CollatzResearch.WordTrace]
  refine ⟨89212657354592463598001503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118950209806123284797335337 89212657354592463598001503)
  ·
    refine ⟨133818986031888695397002255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89212657354592463598001503 133818986031888695397002255)
    ·
      refine ⟨200728479047833043095503383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 133818986031888695397002255 200728479047833043095503383)
      ·
        refine ⟨301092718571749564643255075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 200728479047833043095503383 301092718571749564643255075)
        ·
          refine ⟨451639077857624346964882613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 301092718571749564643255075 451639077857624346964882613)
          ·
            refine ⟨42341163549152282527957745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 451639077857624346964882613 42341163549152282527957745)
            ·
              refine ⟨31755872661864211895968309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42341163549152282527957745 31755872661864211895968309)
              ·
                refine ⟨2977113062049769865247029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 31755872661864211895968309 2977113062049769865247029)
                ·
                  refine ⟨279104349567165924866909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2977113062049769865247029 279104349567165924866909)
                  ·
                    rfl

theorem cell23_4891984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 2, 5, 5].length) (baseStart_4891984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4891984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4891984 prefixEnd_4891984 := by exact prefixLift 4891984
  have htrace : WordTrace (prefixWord ++ tailWord_4891984) baseStart_4891984 baseEnd_4891984 := by
    simpa [prefixWord, tailWord_4891984, baseEnd_4891984] using wordTrace_append hprefix tailTrace_4891984
  have hstable : (prefixWord ++ tailWord_4891984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4891984).length < 2 ^ (prefixWord ++ tailWord_4891984).sum := by decide
  have hdescent : baseEnd_4891984 < baseStart_4891984 := by decide
  rcases family_descends (prefixWord ++ tailWord_4891984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4891990 : List Nat := [5, 2, 3, 1, 2, 1, 2, 2, 1, 2, 2]
def baseStart_4891990 : Nat := 118140960795 + 4891990 * 2 ^ 59
def prefixEnd_4891990 : Nat := 4983230072969 + 3 ^ 40 * 4891990 * 2
def baseEnd_4891990 : Nat := 2511942226988420300327155

theorem tailTrace_4891990 : CollatzResearch.WordTrace tailWord_4891990 prefixEnd_4891990 2511942226988420300327155 := by
  unfold tailWord_4891990
  simp only [CollatzResearch.WordTrace]
  refine ⟨11151595846697699388795089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 118950355698108793480480949 11151595846697699388795089)
  ·
    refine ⟨8363696885023274541596317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11151595846697699388795089 8363696885023274541596317)
    ·
      refine ⟨3136386331883727953098619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8363696885023274541596317 3136386331883727953098619)
      ·
        refine ⟨4704579497825591929647929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3136386331883727953098619 4704579497825591929647929)
        ·
          refine ⟨3528434623369193947235947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4704579497825591929647929 3528434623369193947235947)
          ·
            refine ⟨5292651935053790920853921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3528434623369193947235947 5292651935053790920853921)
            ·
              refine ⟨3969488951290343190640441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5292651935053790920853921 3969488951290343190640441)
              ·
                refine ⟨2977116713467757392980331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3969488951290343190640441 2977116713467757392980331)
                ·
                  refine ⟨4465675070201636089470497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2977116713467757392980331 4465675070201636089470497)
                  ·
                    refine ⟨3349256302651227067102873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4465675070201636089470497 3349256302651227067102873)
                    ·
                      refine ⟨2511942226988420300327155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3349256302651227067102873 2511942226988420300327155)
                      ·
                        rfl

theorem cell23_4891990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 2, 1, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 2, 1, 2, 2, 1, 2, 2].length) (baseStart_4891990 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4891990 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4891990 prefixEnd_4891990 := by exact prefixLift 4891990
  have htrace : WordTrace (prefixWord ++ tailWord_4891990) baseStart_4891990 baseEnd_4891990 := by
    simpa [prefixWord, tailWord_4891990, baseEnd_4891990] using wordTrace_append hprefix tailTrace_4891990
  have hstable : (prefixWord ++ tailWord_4891990).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4891990).length < 2 ^ (prefixWord ++ tailWord_4891990).sum := by decide
  have hdescent : baseEnd_4891990 < baseStart_4891990 := by decide
  rcases family_descends (prefixWord ++ tailWord_4891990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4892044 : List Nat := [2, 2, 1, 2, 1, 3, 1, 2, 5, 4]
def baseStart_4892044 : Nat := 118140960795 + 4892044 * 2 ^ 59
def prefixEnd_4892044 : Nat := 4983230072969 + 3 ^ 40 * 4892044 * 2
def baseEnd_4892044 : Nat := 837323318314587696350635

theorem tailTrace_4892044 : CollatzResearch.WordTrace tailWord_4892044 prefixEnd_4892044 837323318314587696350635 := by
  unfold tailWord_4892044
  simp only [CollatzResearch.WordTrace]
  refine ⟨89213751544483778721593593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118951668725978371628791457 89213751544483778721593593)
  ·
    refine ⟨66910313658362834041195195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89213751544483778721593593 66910313658362834041195195)
    ·
      refine ⟨100365470487544251061792793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66910313658362834041195195 100365470487544251061792793)
      ·
        refine ⟨75274102865658188296344595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 100365470487544251061792793 75274102865658188296344595)
        ·
          refine ⟨112911154298487282444516893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75274102865658188296344595 112911154298487282444516893)
          ·
            refine ⟨42341682861932730916693835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 112911154298487282444516893 42341682861932730916693835)
            ·
              refine ⟨63512524292899096375040753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42341682861932730916693835 63512524292899096375040753)
              ·
                refine ⟨47634393219674322281280565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 63512524292899096375040753 47634393219674322281280565)
                ·
                  refine ⟨4465724364344467713870053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 47634393219674322281280565 4465724364344467713870053)
                  ·
                    refine ⟨837323318314587696350635, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4465724364344467713870053 837323318314587696350635)
                    ·
                      rfl

theorem cell23_4892044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 1, 2, 5, 4].length) (baseStart_4892044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4892044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4892044 prefixEnd_4892044 := by exact prefixLift 4892044
  have htrace : WordTrace (prefixWord ++ tailWord_4892044) baseStart_4892044 baseEnd_4892044 := by
    simpa [prefixWord, tailWord_4892044, baseEnd_4892044] using wordTrace_append hprefix tailTrace_4892044
  have hstable : (prefixWord ++ tailWord_4892044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4892044).length < 2 ^ (prefixWord ++ tailWord_4892044).sum := by decide
  have hdescent : baseEnd_4892044 < baseStart_4892044 := by decide
  rcases family_descends (prefixWord ++ tailWord_4892044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4892061 : List Nat := [1, 4, 2, 1, 3, 1, 1, 3, 3, 4]
def baseStart_4892061 : Nat := 118140960795 + 4892061 * 2 ^ 59
def prefixEnd_4892061 : Nat := 4983230072969 + 3 ^ 40 * 4892061 * 2
def baseEnd_4892061 : Nat := 837326228038296507513109

theorem tailTrace_4892061 : CollatzResearch.WordTrace tailWord_4892061 prefixEnd_4892061 837326228038296507513109 := by
  unfold tailWord_4892061
  simp only [CollatzResearch.WordTrace]
  refine ⟨178428123129905969346556037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118952082086603979564370691 178428123129905969346556037)
  ·
    refine ⟨33455273086857369252479257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 178428123129905969346556037 33455273086857369252479257)
    ·
      refine ⟨25091454815143026939359443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33455273086857369252479257 25091454815143026939359443)
      ·
        refine ⟨37637182222714540409039165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25091454815143026939359443 37637182222714540409039165)
        ·
          refine ⟨14113943333517952653389687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37637182222714540409039165 14113943333517952653389687)
          ·
            refine ⟨21170915000276928980084531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14113943333517952653389687 21170915000276928980084531)
            ·
              refine ⟨31756372500415393470126797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21170915000276928980084531 31756372500415393470126797)
              ·
                refine ⟨11908639687655772551297549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31756372500415393470126797 11908639687655772551297549)
                ·
                  refine ⟨4465739882870914706736581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11908639687655772551297549 4465739882870914706736581)
                  ·
                    refine ⟨837326228038296507513109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4465739882870914706736581 837326228038296507513109)
                    ·
                      rfl

theorem cell23_4892061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 1, 3, 3, 4].length) (baseStart_4892061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4892061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4892061 prefixEnd_4892061 := by exact prefixLift 4892061
  have htrace : WordTrace (prefixWord ++ tailWord_4892061) baseStart_4892061 baseEnd_4892061 := by
    simpa [prefixWord, tailWord_4892061, baseEnd_4892061] using wordTrace_append hprefix tailTrace_4892061
  have hstable : (prefixWord ++ tailWord_4892061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4892061).length < 2 ^ (prefixWord ++ tailWord_4892061).sum := by decide
  have hdescent : baseEnd_4892061 < baseStart_4892061 := by decide
  rcases family_descends (prefixWord ++ tailWord_4892061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4892111 : List Nat := [1, 1, 2, 1, 1, 4, 3, 1, 4, 3, 2]
def baseStart_4892111 : Nat := 118140960795 + 4892111 * 2 ^ 59
def prefixEnd_4892111 : Nat := 4983230072969 + 3 ^ 40 * 4892111 * 2
def baseEnd_4892111 : Nat := 2512004358147614326914097

theorem tailTrace_4892111 : CollatzResearch.WordTrace tailWord_4892111 prefixEnd_4892111 2512004358147614326914097 := by
  unfold tailWord_4892111
  simp only [CollatzResearch.WordTrace]
  refine ⟨178429946779724827885876187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118953297853149885257250791 178429946779724827885876187)
  ·
    refine ⟨267644920169587241828814281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 178429946779724827885876187 267644920169587241828814281)
    ·
      refine ⟨200733690127190431371610711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 267644920169587241828814281 200733690127190431371610711)
      ·
        refine ⟨301100535190785647057416067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 200733690127190431371610711 301100535190785647057416067)
        ·
          refine ⟨451650802786178470586124101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 301100535190785647057416067 451650802786178470586124101)
          ·
            refine ⟨84684525522408463234898269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 451650802786178470586124101 84684525522408463234898269)
            ·
              refine ⟨31756697070903173713086851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 84684525522408463234898269 31756697070903173713086851)
              ·
                refine ⟨47635045606354760569630277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31756697070903173713086851 47635045606354760569630277)
                ·
                  refine ⟨8931571051191517606805677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 47635045606354760569630277 8931571051191517606805677)
                  ·
                    refine ⟨3349339144196819102552129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8931571051191517606805677 3349339144196819102552129)
                    ·
                      refine ⟨2512004358147614326914097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3349339144196819102552129 2512004358147614326914097)
                      ·
                        rfl

theorem cell23_4892111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 3, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 3, 1, 4, 3, 2].length) (baseStart_4892111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4892111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4892111 prefixEnd_4892111 := by exact prefixLift 4892111
  have htrace : WordTrace (prefixWord ++ tailWord_4892111) baseStart_4892111 baseEnd_4892111 := by
    simpa [prefixWord, tailWord_4892111, baseEnd_4892111] using wordTrace_append hprefix tailTrace_4892111
  have hstable : (prefixWord ++ tailWord_4892111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4892111).length < 2 ^ (prefixWord ++ tailWord_4892111).sum := by decide
  have hdescent : baseEnd_4892111 < baseStart_4892111 := by decide
  rcases family_descends (prefixWord ++ tailWord_4892111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4892164 : List Nat := [2, 3, 2, 3, 13]
def baseStart_4892164 : Nat := 118140960795 + 4892164 * 2 ^ 59
def prefixEnd_4892164 : Nat := 4983230072969 + 3 ^ 40 * 4892164 * 2
def baseEnd_4892164 : Nat := 3445859496052541316257

theorem tailTrace_4892164 : CollatzResearch.WordTrace tailWord_4892164 prefixEnd_4892164 3445859496052541316257 := by
  unfold tailWord_4892164
  simp only [CollatzResearch.WordTrace]
  refine ⟨89215939924266408968777773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118954586565688545291703697 89215939924266408968777773)
  ·
    refine ⟨33455977471599903363291665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 89215939924266408968777773 33455977471599903363291665)
    ·
      refine ⟨25091983103699927522468749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33455977471599903363291665 25091983103699927522468749)
      ·
        refine ⟨9409493663887472820925781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25091983103699927522468749 9409493663887472820925781)
        ·
          refine ⟨3445859496052541316257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 13 9409493663887472820925781 3445859496052541316257)
          ·
            rfl

theorem cell23_4892164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 13].length) (baseStart_4892164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4892164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4892164 prefixEnd_4892164 := by exact prefixLift 4892164
  have htrace : WordTrace (prefixWord ++ tailWord_4892164) baseStart_4892164 baseEnd_4892164 := by
    simpa [prefixWord, tailWord_4892164, baseEnd_4892164] using wordTrace_append hprefix tailTrace_4892164
  have hstable : (prefixWord ++ tailWord_4892164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4892164).length < 2 ^ (prefixWord ++ tailWord_4892164).sum := by decide
  have hdescent : baseEnd_4892164 < baseStart_4892164 := by decide
  rcases family_descends (prefixWord ++ tailWord_4892164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4892181 : List Nat := [1, 3, 2, 1, 3, 4, 1, 8]
def baseStart_4892181 : Nat := 118140960795 + 4892181 * 2 ^ 59
def prefixEnd_4892181 : Nat := 4983230072969 + 3 ^ 40 * 4892181 * 2
def baseEnd_4892181 : Nat := 93038529696052927890325

theorem tailTrace_4892181 : CollatzResearch.WordTrace tailWord_4892181 prefixEnd_4892181 93038529696052927890325 := by
  unfold tailWord_4892181
  simp only [CollatzResearch.WordTrace]
  refine ⟨178432499889471229840924397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118954999926314153227282931 178432499889471229840924397)
  ·
    refine ⟨66912187458551711190346649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 178432499889471229840924397 66912187458551711190346649)
    ·
      refine ⟨50184140593913783392759987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66912187458551711190346649 50184140593913783392759987)
      ·
        refine ⟨75276210890870675089139981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50184140593913783392759987 75276210890870675089139981)
        ·
          refine ⟨28228579084076503158427493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 75276210890870675089139981 28228579084076503158427493)
          ·
            refine ⟨5292858578264344342205155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 28228579084076503158427493 5292858578264344342205155)
            ·
              refine ⟨7939287867396516513307733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5292858578264344342205155 7939287867396516513307733)
              ·
                refine ⟨93038529696052927890325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7939287867396516513307733 93038529696052927890325)
                ·
                  rfl

theorem cell23_4892181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 4, 1, 8].length) (baseStart_4892181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4892181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4892181 prefixEnd_4892181 := by exact prefixLift 4892181
  have htrace : WordTrace (prefixWord ++ tailWord_4892181) baseStart_4892181 baseEnd_4892181 := by
    simpa [prefixWord, tailWord_4892181, baseEnd_4892181] using wordTrace_append hprefix tailTrace_4892181
  have hstable : (prefixWord ++ tailWord_4892181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4892181).length < 2 ^ (prefixWord ++ tailWord_4892181).sum := by decide
  have hdescent : baseEnd_4892181 < baseStart_4892181 := by decide
  rcases family_descends (prefixWord ++ tailWord_4892181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4892191 : List Nat := [1, 1, 2, 4, 1, 1, 3, 3, 1, 3, 3]
def baseStart_4892191 : Nat := 118140960795 + 4892191 * 2 ^ 59
def prefixEnd_4892191 : Nat := 4983230072969 + 3 ^ 40 * 4892191 * 2
def baseEnd_4892191 : Nat := 2512045436599974013913729

theorem tailTrace_4892191 : CollatzResearch.WordTrace tailWord_4892191 prefixEnd_4892191 2512045436599974013913729 := by
  unfold tailWord_4892191
  simp only [CollatzResearch.WordTrace]
  refine ⟨178432864619435001548788427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118955243079623334365858951 178432864619435001548788427)
  ·
    refine ⟨267649296929152502323182641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 178432864619435001548788427 267649296929152502323182641)
    ·
      refine ⟨200736972696864376742386981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 267649296929152502323182641 200736972696864376742386981)
      ·
        refine ⟨37638182380662070639197559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 200736972696864376742386981 37638182380662070639197559)
        ·
          refine ⟨56457273570993105958796339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37638182380662070639197559 56457273570993105958796339)
          ·
            refine ⟨84685910356489658938194509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56457273570993105958796339 84685910356489658938194509)
            ·
              refine ⟨31757216383683622101822941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 84685910356489658938194509 31757216383683622101822941)
              ·
                refine ⟨11908956143881358288183603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31757216383683622101822941 11908956143881358288183603)
                ·
                  refine ⟨17863434215822037432275405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11908956143881358288183603 17863434215822037432275405)
                  ·
                    refine ⟨6698787830933264037103277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17863434215822037432275405 6698787830933264037103277)
                    ·
                      refine ⟨2512045436599974013913729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6698787830933264037103277 2512045436599974013913729)
                      ·
                        rfl

theorem cell23_4892191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 3, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 3, 3, 1, 3, 3].length) (baseStart_4892191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4892191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4892191 prefixEnd_4892191 := by exact prefixLift 4892191
  have htrace : WordTrace (prefixWord ++ tailWord_4892191) baseStart_4892191 baseEnd_4892191 := by
    simpa [prefixWord, tailWord_4892191, baseEnd_4892191] using wordTrace_append hprefix tailTrace_4892191
  have hstable : (prefixWord ++ tailWord_4892191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4892191).length < 2 ^ (prefixWord ++ tailWord_4892191).sum := by decide
  have hdescent : baseEnd_4892191 < baseStart_4892191 := by decide
  rcases family_descends (prefixWord ++ tailWord_4892191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4892242 : List Nat := [3, 2, 2, 1, 2, 3, 3, 1, 2, 1, 3]
def baseStart_4892242 : Nat := 118140960795 + 4892242 * 2 ^ 59
def prefixEnd_4892242 : Nat := 4983230072969 + 3 ^ 40 * 4892242 * 2
def baseEnd_4892242 : Nat := 2512071624113353314375995

theorem tailTrace_4892242 : CollatzResearch.WordTrace tailWord_4892242 prefixEnd_4892242 2512071624113353314375995 := by
  unfold tailWord_4892242
  simp only [CollatzResearch.WordTrace]
  refine ⟨44608681185562559314723745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 118956483161500158172596653 44608681185562559314723745)
  ·
    refine ⟨33456510889171919486042809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44608681185562559314723745 33456510889171919486042809)
    ·
      refine ⟨25092383166878939614532107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33456510889171919486042809 25092383166878939614532107)
      ·
        refine ⟨37638574750318409421798161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25092383166878939614532107 37638574750318409421798161)
        ·
          refine ⟨28228931062738807066348621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37638574750318409421798161 28228931062738807066348621)
          ·
            refine ⟨10585849148527052649880733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28228931062738807066348621 10585849148527052649880733)
            ·
              refine ⟨3969693430697644743705275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10585849148527052649880733 3969693430697644743705275)
              ·
                refine ⟨5954540146046467115557913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3969693430697644743705275 5954540146046467115557913)
                ·
                  refine ⟨4465905109534850336668435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5954540146046467115557913 4465905109534850336668435)
                  ·
                    refine ⟨6698857664302275505002653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4465905109534850336668435 6698857664302275505002653)
                    ·
                      refine ⟨2512071624113353314375995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6698857664302275505002653 2512071624113353314375995)
                      ·
                        rfl

theorem cell23_4892242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 3, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 3, 3, 1, 2, 1, 3].length) (baseStart_4892242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4892242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4892242 prefixEnd_4892242 := by exact prefixLift 4892242
  have htrace : WordTrace (prefixWord ++ tailWord_4892242) baseStart_4892242 baseEnd_4892242 := by
    simpa [prefixWord, tailWord_4892242, baseEnd_4892242] using wordTrace_append hprefix tailTrace_4892242
  have hstable : (prefixWord ++ tailWord_4892242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4892242).length < 2 ^ (prefixWord ++ tailWord_4892242).sum := by decide
  have hdescent : baseEnd_4892242 < baseStart_4892242 := by decide
  rcases family_descends (prefixWord ++ tailWord_4892242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4892252 : List Nat := [2, 2, 4, 1, 2, 2, 2, 2, 1, 3, 2]
def baseStart_4892252 : Nat := 118140960795 + 4892252 * 2 ^ 59
def prefixEnd_4892252 : Nat := 4983230072969 + 3 ^ 40 * 4892252 * 2
def baseEnd_4892252 : Nat := 2512076758919898275250949

theorem tailTrace_4892252 : CollatzResearch.WordTrace tailWord_4892252 prefixEnd_4892252 2512076758919898275250949 := by
  unfold tailWord_4892252
  simp only [CollatzResearch.WordTrace]
  refine ⟨89217544736107004483379505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118956726314809339311172673 89217544736107004483379505)
  ·
    refine ⟨66913158552080253362534629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89217544736107004483379505 66913158552080253362534629)
    ·
      refine ⟨12546217228515047505475243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 66913158552080253362534629 12546217228515047505475243)
      ·
        refine ⟨18819325842772571258212865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12546217228515047505475243 18819325842772571258212865)
        ·
          refine ⟨14114494382079428443659649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18819325842772571258212865 14114494382079428443659649)
          ·
            refine ⟨10585870786559571332744737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14114494382079428443659649 10585870786559571332744737)
            ·
              refine ⟨7939403089919678499558553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10585870786559571332744737 7939403089919678499558553)
              ·
                refine ⟨5954552317439758874668915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7939403089919678499558553 5954552317439758874668915)
                ·
                  refine ⟨8931828476159638312003373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5954552317439758874668915 8931828476159638312003373)
                  ·
                    refine ⟨3349435678559864367001265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8931828476159638312003373 3349435678559864367001265)
                    ·
                      refine ⟨2512076758919898275250949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3349435678559864367001265 2512076758919898275250949)
                      ·
                        rfl

theorem cell23_4892252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 2, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 2, 2, 2, 1, 3, 2].length) (baseStart_4892252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4892252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4892252 prefixEnd_4892252 := by exact prefixLift 4892252
  have htrace : WordTrace (prefixWord ++ tailWord_4892252) baseStart_4892252 baseEnd_4892252 := by
    simpa [prefixWord, tailWord_4892252, baseEnd_4892252] using wordTrace_append hprefix tailTrace_4892252
  have hstable : (prefixWord ++ tailWord_4892252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4892252).length < 2 ^ (prefixWord ++ tailWord_4892252).sum := by decide
  have hdescent : baseEnd_4892252 < baseStart_4892252 := by decide
  rcases family_descends (prefixWord ++ tailWord_4892252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4892338 : List Nat := [3, 2, 1, 1, 1, 2, 4, 2, 2, 1, 4]
def baseStart_4892338 : Nat := 118140960795 + 4892338 * 2 ^ 59
def prefixEnd_4892338 : Nat := 4983230072969 + 3 ^ 40 * 4892338 * 2
def baseEnd_4892338 : Nat := 2512120918256184938775553

theorem tailTrace_4892338 : CollatzResearch.WordTrace tailWord_4892338 prefixEnd_4892338 2512120918256184938775553 := by
  unfold tailWord_4892338
  simp only [CollatzResearch.WordTrace]
  refine ⟨44609556537475611413597417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 118958817433268297102926445 44609556537475611413597417)
  ·
    refine ⟨33457167403106708560198063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44609556537475611413597417 33457167403106708560198063)
    ·
      refine ⟨50185751104660062840297095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33457167403106708560198063 50185751104660062840297095)
      ·
        refine ⟨75278626656990094260445643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50185751104660062840297095 75278626656990094260445643)
        ·
          refine ⟨112917939985485141390668465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75278626656990094260445643 112917939985485141390668465)
          ·
            refine ⟨84688454989113856043001349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 112917939985485141390668465 84688454989113856043001349)
            ·
              refine ⟨15879085310458848008062753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 84688454989113856043001349 15879085310458848008062753)
              ·
                refine ⟨11909313982844136006047065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15879085310458848008062753 11909313982844136006047065)
                ·
                  refine ⟨8931985487133102004535299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11909313982844136006047065 8931985487133102004535299)
                  ·
                    refine ⟨13397978230699653006802949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8931985487133102004535299 13397978230699653006802949)
                    ·
                      refine ⟨2512120918256184938775553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13397978230699653006802949 2512120918256184938775553)
                      ·
                        rfl

theorem cell23_4892338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 4, 2, 2, 1, 4].length) (baseStart_4892338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4892338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4892338 prefixEnd_4892338 := by exact prefixLift 4892338
  have htrace : WordTrace (prefixWord ++ tailWord_4892338) baseStart_4892338 baseEnd_4892338 := by
    simpa [prefixWord, tailWord_4892338, baseEnd_4892338] using wordTrace_append hprefix tailTrace_4892338
  have hstable : (prefixWord ++ tailWord_4892338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4892338).length < 2 ^ (prefixWord ++ tailWord_4892338).sum := by decide
  have hdescent : baseEnd_4892338 < baseStart_4892338 := by decide
  rcases family_descends (prefixWord ++ tailWord_4892338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4892342 : List Nat := [5, 1, 3, 1, 1, 1, 1, 1, 2, 5, 2]
def baseStart_4892342 : Nat := 118140960795 + 4892342 * 2 ^ 59
def prefixEnd_4892342 : Nat := 4983230072969 + 3 ^ 40 * 4892342 * 2
def baseEnd_4892342 : Nat := 2512122972178802923125535

theorem tailTrace_4892342 : CollatzResearch.WordTrace tailWord_4892342 prefixEnd_4892342 2512122972178802923125535 := by
  unfold tailWord_4892342
  simp only [CollatzResearch.WordTrace]
  refine ⟨11152398252617997146095955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 118958914694591969558356853 11152398252617997146095955)
  ·
    refine ⟨16728597378926995719143933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11152398252617997146095955 16728597378926995719143933)
    ·
      refine ⟨6273224017097623394678975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16728597378926995719143933 6273224017097623394678975)
      ·
        refine ⟨9409836025646435092018463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6273224017097623394678975 9409836025646435092018463)
        ·
          refine ⟨14114754038469652638027695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9409836025646435092018463 14114754038469652638027695)
          ·
            refine ⟨21172131057704478957041543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14114754038469652638027695 21172131057704478957041543)
            ·
              refine ⟨31758196586556718435562315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21172131057704478957041543 31758196586556718435562315)
              ·
                refine ⟨47637294879835077653343473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31758196586556718435562315 47637294879835077653343473)
                ·
                  refine ⟨35727971159876308240007605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 47637294879835077653343473 35727971159876308240007605)
                  ·
                    refine ⟨3349497296238403897500713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 35727971159876308240007605 3349497296238403897500713)
                    ·
                      refine ⟨2512122972178802923125535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3349497296238403897500713 2512122972178802923125535)
                      ·
                        rfl

theorem cell23_4892342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 1, 1, 2, 5, 2].length) (baseStart_4892342 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4892342 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4892342 prefixEnd_4892342 := by exact prefixLift 4892342
  have htrace : WordTrace (prefixWord ++ tailWord_4892342) baseStart_4892342 baseEnd_4892342 := by
    simpa [prefixWord, tailWord_4892342, baseEnd_4892342] using wordTrace_append hprefix tailTrace_4892342
  have hstable : (prefixWord ++ tailWord_4892342).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4892342).length < 2 ^ (prefixWord ++ tailWord_4892342).sum := by decide
  have hdescent : baseEnd_4892342 < baseStart_4892342 := by decide
  rcases family_descends (prefixWord ++ tailWord_4892342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4892372 : List Nat := [2, 4, 1, 3, 1, 3, 1, 1, 2, 1, 4]
def baseStart_4892372 : Nat := 118140960795 + 4892372 * 2 ^ 59
def prefixEnd_4892372 : Nat := 4983230072969 + 3 ^ 40 * 4892372 * 2
def baseEnd_4892372 : Nat := 2512138376598437805750397

theorem tailTrace_4892372 : CollatzResearch.WordTrace tailWord_4892372 prefixEnd_4892372 2512138376598437805750397 := by
  unfold tailWord_4892372
  simp only [CollatzResearch.WordTrace]
  refine ⟨89219733115889634730563685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118959644154519512974084913 89219733115889634730563685)
  ·
    refine ⟨16728699959229306511980691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 89219733115889634730563685 16728699959229306511980691)
    ·
      refine ⟨25093049938843959767971037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16728699959229306511980691 25093049938843959767971037)
      ·
        refine ⟨9409893727066484912989139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25093049938843959767971037 9409893727066484912989139)
        ·
          refine ⟨14114840590599727369483709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9409893727066484912989139 14114840590599727369483709)
          ·
            refine ⟨5293065221474897763556391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14114840590599727369483709 5293065221474897763556391)
            ·
              refine ⟨7939597832212346645334587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5293065221474897763556391 7939597832212346645334587)
              ·
                refine ⟨11909396748318519968001881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7939597832212346645334587 11909396748318519968001881)
                ·
                  refine ⟨8932047561238889976001411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11909396748318519968001881 8932047561238889976001411)
                  ·
                    refine ⟨13398071341858334964002117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8932047561238889976001411 13398071341858334964002117)
                    ·
                      refine ⟨2512138376598437805750397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13398071341858334964002117 2512138376598437805750397)
                      ·
                        rfl

theorem cell23_4892372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 3, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 3, 1, 1, 2, 1, 4].length) (baseStart_4892372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4892372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4892372 prefixEnd_4892372 := by exact prefixLift 4892372
  have htrace : WordTrace (prefixWord ++ tailWord_4892372) baseStart_4892372 baseEnd_4892372 := by
    simpa [prefixWord, tailWord_4892372, baseEnd_4892372] using wordTrace_append hprefix tailTrace_4892372
  have hstable : (prefixWord ++ tailWord_4892372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4892372).length < 2 ^ (prefixWord ++ tailWord_4892372).sum := by decide
  have hdescent : baseEnd_4892372 < baseStart_4892372 := by decide
  rcases family_descends (prefixWord ++ tailWord_4892372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4892411 : List Nat := [1, 1, 1, 1, 1, 3, 1, 3, 2, 5, 4]
def baseStart_4892411 : Nat := 118140960795 + 4892411 * 2 ^ 59
def prefixEnd_4892411 : Nat := 4983230072969 + 3 ^ 40 * 4892411 * 2
def baseEnd_4892411 : Nat := 2512158402343963153162717

theorem tailTrace_4892411 : CollatzResearch.WordTrace tailWord_4892411 prefixEnd_4892411 2512158402343963153162717 := by
  unfold tailWord_4892411
  simp only [CollatzResearch.WordTrace]
  refine ⟨178440888678637979121797087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118960592452425319414531391 178440888678637979121797087)
  ·
    refine ⟨267661333017956968682695631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 178440888678637979121797087 267661333017956968682695631)
    ·
      refine ⟨401491999526935453024043447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 267661333017956968682695631 401491999526935453024043447)
      ·
        refine ⟨602237999290403179536065171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 401491999526935453024043447 602237999290403179536065171)
        ·
          refine ⟨903356998935604769304097757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 602237999290403179536065171 903356998935604769304097757)
          ·
            refine ⟨338758874600851788489036659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 903356998935604769304097757 338758874600851788489036659)
            ·
              refine ⟨508138311901277682733554989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 338758874600851788489036659 508138311901277682733554989)
              ·
                refine ⟨190551866962979131025083121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 508138311901277682733554989 190551866962979131025083121)
                ·
                  refine ⟨142913900222234348268812341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 190551866962979131025083121 142913900222234348268812341)
                  ·
                    refine ⟨13398178145834470150201157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 142913900222234348268812341 13398178145834470150201157)
                    ·
                      refine ⟨2512158402343963153162717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13398178145834470150201157 2512158402343963153162717)
                      ·
                        rfl

theorem cell23_4892411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 5, 4].length) (baseStart_4892411 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4892411 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4892411 prefixEnd_4892411 := by exact prefixLift 4892411
  have htrace : WordTrace (prefixWord ++ tailWord_4892411) baseStart_4892411 baseEnd_4892411 := by
    simpa [prefixWord, tailWord_4892411, baseEnd_4892411] using wordTrace_append hprefix tailTrace_4892411
  have hstable : (prefixWord ++ tailWord_4892411).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4892411).length < 2 ^ (prefixWord ++ tailWord_4892411).sum := by decide
  have hdescent : baseEnd_4892411 < baseStart_4892411 := by decide
  rcases family_descends (prefixWord ++ tailWord_4892411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4892428 : List Nat := [2, 2, 1, 2, 2, 1, 2, 3, 3, 1, 4]
def baseStart_4892428 : Nat := 118140960795 + 4892428 * 2 ^ 59
def prefixEnd_4892428 : Nat := 4983230072969 + 3 ^ 40 * 4892428 * 2
def baseEnd_4892428 : Nat := 2512167131515089586650139

theorem tailTrace_4892428 : CollatzResearch.WordTrace tailWord_4892428 prefixEnd_4892428 2512167131515089586650139 := by
  unfold tailWord_4892428
  simp only [CollatzResearch.WordTrace]
  refine ⟨89220754359788195512582969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118961005813050927350110625 89220754359788195512582969)
  ·
    refine ⟨66915565769841146634437227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89220754359788195512582969 66915565769841146634437227)
    ·
      refine ⟨100373348654761719951655841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66915565769841146634437227 100373348654761719951655841)
      ·
        refine ⟨75280011491071289963741881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 100373348654761719951655841 75280011491071289963741881)
        ·
          refine ⟨56460008618303467472806411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 75280011491071289963741881 56460008618303467472806411)
          ·
            refine ⟨84690012927455201209209617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56460008618303467472806411 84690012927455201209209617)
            ·
              refine ⟨63517509695591400906907213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 84690012927455201209209617 63517509695591400906907213)
              ·
                refine ⟨23819066135846775340090205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 63517509695591400906907213 23819066135846775340090205)
                ·
                  refine ⟨8932149800942540752533827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23819066135846775340090205 8932149800942540752533827)
                  ·
                    refine ⟨13398224701413811128800741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8932149800942540752533827 13398224701413811128800741)
                    ·
                      refine ⟨2512167131515089586650139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13398224701413811128800741 2512167131515089586650139)
                      ·
                        rfl

theorem cell23_4892428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 2, 3, 3, 1, 4].length) (baseStart_4892428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4892428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4892428 prefixEnd_4892428 := by exact prefixLift 4892428
  have htrace : WordTrace (prefixWord ++ tailWord_4892428) baseStart_4892428 baseEnd_4892428 := by
    simpa [prefixWord, tailWord_4892428, baseEnd_4892428] using wordTrace_append hprefix tailTrace_4892428
  have hstable : (prefixWord ++ tailWord_4892428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4892428).length < 2 ^ (prefixWord ++ tailWord_4892428).sum := by decide
  have hdescent : baseEnd_4892428 < baseStart_4892428 := by decide
  rcases family_descends (prefixWord ++ tailWord_4892428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4892439 : List Nat := [1, 1, 3, 4, 2, 1, 3, 3, 1, 1, 3]
def baseStart_4892439 : Nat := 118140960795 + 4892439 * 2 ^ 59
def prefixEnd_4892439 : Nat := 4983230072969 + 3 ^ 40 * 4892439 * 2
def baseEnd_4892439 : Nat := 2512172779802289043612589

theorem tailTrace_4892439 : CollatzResearch.WordTrace tailWord_4892439 prefixEnd_4892439 2512172779802289043612589 := by
  unfold tailWord_4892439
  simp only [CollatzResearch.WordTrace]
  refine ⟨178441909922536539903816371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118961273281691026602544247 178441909922536539903816371)
  ·
    refine ⟨267662864883804809855724557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 178441909922536539903816371 267662864883804809855724557)
    ·
      refine ⟨100373574331426803695896709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 267662864883804809855724557 100373574331426803695896709)
      ·
        refine ⟨18820045187142525692980633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 100373574331426803695896709 18820045187142525692980633)
        ·
          refine ⟨14115033890356894269735475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18820045187142525692980633 14115033890356894269735475)
          ·
            refine ⟨21172550835535341404603213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14115033890356894269735475 21172550835535341404603213)
            ·
              refine ⟨7939706563325753026726205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21172550835535341404603213 7939706563325753026726205)
              ·
                refine ⟨2977389961247157385022327, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7939706563325753026726205 2977389961247157385022327)
                ·
                  refine ⟨4466084941870736077533491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2977389961247157385022327 4466084941870736077533491)
                  ·
                    refine ⟨6699127412806104116300237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4466084941870736077533491 6699127412806104116300237)
                    ·
                      refine ⟨2512172779802289043612589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6699127412806104116300237 2512172779802289043612589)
                      ·
                        rfl

theorem cell23_4892439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 3, 3, 1, 1, 3].length) (baseStart_4892439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4892439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4892439 prefixEnd_4892439 := by exact prefixLift 4892439
  have htrace : WordTrace (prefixWord ++ tailWord_4892439) baseStart_4892439 baseEnd_4892439 := by
    simpa [prefixWord, tailWord_4892439, baseEnd_4892439] using wordTrace_append hprefix tailTrace_4892439
  have hstable : (prefixWord ++ tailWord_4892439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4892439).length < 2 ^ (prefixWord ++ tailWord_4892439).sum := by decide
  have hdescent : baseEnd_4892439 < baseStart_4892439 := by decide
  rcases family_descends (prefixWord ++ tailWord_4892439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4892451 : List Nat := [1, 1, 1, 4, 2, 1, 13]
def baseStart_4892451 : Nat := 118140960795 + 4892451 * 2 ^ 59
def prefixEnd_4892451 : Nat := 4983230072969 + 3 ^ 40 * 4892451 * 2
def baseEnd_4892451 : Nat := 31014554834199296255093

theorem tailTrace_4892451 : CollatzResearch.WordTrace tailWord_4892451 prefixEnd_4892451 31014554834199296255093 := by
  unfold tailWord_4892451
  simp only [CollatzResearch.WordTrace]
  refine ⟨178442347598493065953253207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118961565065662043968835471 178442347598493065953253207)
  ·
    refine ⟨267663521397739598929879811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 178442347598493065953253207 267663521397739598929879811)
    ·
      refine ⟨401495282096609398394819717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 267663521397739598929879811 401495282096609398394819717)
      ·
        refine ⟨75280365393114262199028697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 401495282096609398394819717 75280365393114262199028697)
        ·
          refine ⟨56460274044835696649271523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 75280365393114262199028697 56460274044835696649271523)
          ·
            refine ⟨84690411067253544973907285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56460274044835696649271523 84690411067253544973907285)
            ·
              refine ⟨31014554834199296255093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 13 84690411067253544973907285 31014554834199296255093)
              ·
                rfl

theorem cell23_4892451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 13].length) (baseStart_4892451 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4892451 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4892451 prefixEnd_4892451 := by exact prefixLift 4892451
  have htrace : WordTrace (prefixWord ++ tailWord_4892451) baseStart_4892451 baseEnd_4892451 := by
    simpa [prefixWord, tailWord_4892451, baseEnd_4892451] using wordTrace_append hprefix tailTrace_4892451
  have hstable : (prefixWord ++ tailWord_4892451).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4892451).length < 2 ^ (prefixWord ++ tailWord_4892451).sum := by decide
  have hdescent : baseEnd_4892451 < baseStart_4892451 := by decide
  rcases family_descends (prefixWord ++ tailWord_4892451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4892456 : List Nat := [2, 1, 5, 1, 1, 3, 3, 2, 1, 1, 3]
def baseStart_4892456 : Nat := 118140960795 + 4892456 * 2 ^ 59
def prefixEnd_4892456 : Nat := 4983230072969 + 3 ^ 40 * 4892456 * 2
def baseEnd_4892456 : Nat := 2512181508973415477100011

theorem tailTrace_4892456 : CollatzResearch.WordTrace tailWord_4892456 prefixEnd_4892456 2512181508973415477100011 := by
  unfold tailWord_4892456
  simp only [CollatzResearch.WordTrace]
  refine ⟨89221264981737475903592611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118961686642316634538123481 89221264981737475903592611)
  ·
    refine ⟨133831897472606213855388917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89221264981737475903592611 133831897472606213855388917)
    ·
      refine ⟨12546740388056832548942711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 133831897472606213855388917 12546740388056832548942711)
      ·
        refine ⟨18820110582085248823414067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12546740388056832548942711 18820110582085248823414067)
        ·
          refine ⟨28230165873127873235121101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18820110582085248823414067 28230165873127873235121101)
          ·
            refine ⟨10586312202422952463170413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28230165873127873235121101 10586312202422952463170413)
            ·
              refine ⟨3969867075908607173688905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10586312202422952463170413 3969867075908607173688905)
              ·
                refine ⟨2977400306931455380266679, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3969867075908607173688905 2977400306931455380266679)
                ·
                  refine ⟨4466100460397183070400019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2977400306931455380266679 4466100460397183070400019)
                  ·
                    refine ⟨6699150690595774605600029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4466100460397183070400019 6699150690595774605600029)
                    ·
                      refine ⟨2512181508973415477100011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6699150690595774605600029 2512181508973415477100011)
                      ·
                        rfl

theorem cell23_4892456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 3, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 3, 3, 2, 1, 1, 3].length) (baseStart_4892456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4892456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4892456 prefixEnd_4892456 := by exact prefixLift 4892456
  have htrace : WordTrace (prefixWord ++ tailWord_4892456) baseStart_4892456 baseEnd_4892456 := by
    simpa [prefixWord, tailWord_4892456, baseEnd_4892456] using wordTrace_append hprefix tailTrace_4892456
  have hstable : (prefixWord ++ tailWord_4892456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4892456).length < 2 ^ (prefixWord ++ tailWord_4892456).sum := by decide
  have hdescent : baseEnd_4892456 < baseStart_4892456 := by decide
  rcases family_descends (prefixWord ++ tailWord_4892456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4892472 : List Nat := [2, 1, 2, 1, 3, 3, 4, 1, 2, 4]
def baseStart_4892472 : Nat := 118140960795 + 4892472 * 2 ^ 59
def prefixEnd_4892472 : Nat := 4983230072969 + 3 ^ 40 * 4892472 * 2
def baseEnd_4892472 : Nat := 837396574887962471499979

theorem tailTrace_4892472 : CollatzResearch.WordTrace tailWord_4892472 prefixEnd_4892472 837396574887962471499979 := by
  unfold tailWord_4892472
  simp only [CollatzResearch.WordTrace]
  refine ⟨89221556765708493269883835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118962075687611324359845113 89221556765708493269883835)
  ·
    refine ⟨133832335148562739904825753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89221556765708493269883835 133832335148562739904825753)
    ·
      refine ⟨100374251361422054928619315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 133832335148562739904825753 100374251361422054928619315)
      ·
        refine ⟨150561377042133082392928973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100374251361422054928619315 150561377042133082392928973)
        ·
          refine ⟨56460516390799905897348365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 150561377042133082392928973 56460516390799905897348365)
          ·
            refine ⟨21172693646549964711505637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 56460516390799905897348365 21172693646549964711505637)
            ·
              refine ⟨3969880058728118383407307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21172693646549964711505637 3969880058728118383407307)
              ·
                refine ⟨5954820088092177575110961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3969880058728118383407307 5954820088092177575110961)
                ·
                  refine ⟨4466115066069133181333221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5954820088092177575110961 4466115066069133181333221)
                  ·
                    refine ⟨837396574887962471499979, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4466115066069133181333221 837396574887962471499979)
                    ·
                      rfl

theorem cell23_4892472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 4, 1, 2, 4].length) (baseStart_4892472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4892472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4892472 prefixEnd_4892472 := by exact prefixLift 4892472
  have htrace : WordTrace (prefixWord ++ tailWord_4892472) baseStart_4892472 baseEnd_4892472 := by
    simpa [prefixWord, tailWord_4892472, baseEnd_4892472] using wordTrace_append hprefix tailTrace_4892472
  have hstable : (prefixWord ++ tailWord_4892472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4892472).length < 2 ^ (prefixWord ++ tailWord_4892472).sum := by decide
  have hdescent : baseEnd_4892472 < baseStart_4892472 := by decide
  rcases family_descends (prefixWord ++ tailWord_4892472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4892479 : List Nat := [1, 1, 2, 2, 7, 1, 1, 2, 1, 1, 4]
def baseStart_4892479 : Nat := 118140960795 + 4892479 * 2 ^ 59
def prefixEnd_4892479 : Nat := 4983230072969 + 3 ^ 40 * 4892479 * 2
def baseEnd_4892479 : Nat := 2512193319028468887112405

theorem tailTrace_4892479 : CollatzResearch.WordTrace tailWord_4892479 prefixEnd_4892479 2512193319028468887112405 := by
  unfold tailWord_4892479
  simp only [CollatzResearch.WordTrace]
  refine ⟨178443368842391626735272491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118962245894927751156848327 178443368842391626735272491)
  ·
    refine ⟨267665053263587440102908737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 178443368842391626735272491 267665053263587440102908737)
    ·
      refine ⟨200748789947690580077181553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 267665053263587440102908737 200748789947690580077181553)
      ·
        refine ⟨150561592460767935057886165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 200748789947690580077181553 150561592460767935057886165)
        ·
          refine ⟨3528787323299248477919207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 150561592460767935057886165 3528787323299248477919207)
          ·
            refine ⟨5293180984948872716878811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3528787323299248477919207 5293180984948872716878811)
            ·
              refine ⟨7939771477423309075318217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5293180984948872716878811 7939771477423309075318217)
              ·
                refine ⟨5954828608067481806488663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7939771477423309075318217 5954828608067481806488663)
                ·
                  refine ⟨8932242912101222709732995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5954828608067481806488663 8932242912101222709732995)
                  ·
                    refine ⟨13398364368151834064599493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8932242912101222709732995 13398364368151834064599493)
                    ·
                      refine ⟨2512193319028468887112405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13398364368151834064599493 2512193319028468887112405)
                      ·
                        rfl

theorem cell23_4892479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 7, 1, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 7, 1, 1, 2, 1, 1, 4].length) (baseStart_4892479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4892479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4892479 prefixEnd_4892479 := by exact prefixLift 4892479
  have htrace : WordTrace (prefixWord ++ tailWord_4892479) baseStart_4892479 baseEnd_4892479 := by
    simpa [prefixWord, tailWord_4892479, baseEnd_4892479] using wordTrace_append hprefix tailTrace_4892479
  have hstable : (prefixWord ++ tailWord_4892479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4892479).length < 2 ^ (prefixWord ++ tailWord_4892479).sum := by decide
  have hdescent : baseEnd_4892479 < baseStart_4892479 := by decide
  rcases family_descends (prefixWord ++ tailWord_4892479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4892512 : List Nat := [2, 1, 1, 3, 3, 2, 1, 4, 2, 1, 3]
def baseStart_4892512 : Nat := 118140960795 + 4892512 * 2 ^ 59
def prefixEnd_4892512 : Nat := 4983230072969 + 3 ^ 40 * 4892512 * 2
def baseEnd_4892512 : Nat := 2512210263890067257999753

theorem tailTrace_4892512 : CollatzResearch.WordTrace tailWord_4892512 prefixEnd_4892512 2512210263890067257999753 := by
  unfold tailWord_4892512
  simp only [CollatzResearch.WordTrace]
  refine ⟨89222286225636036685611895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118963048300848048914149193 89222286225636036685611895)
  ·
    refine ⟨133833429338454055028417843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89222286225636036685611895 133833429338454055028417843)
    ·
      refine ⟨200750144007681082542626765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 133833429338454055028417843 200750144007681082542626765)
      ·
        refine ⟨75281304002880405953485037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 200750144007681082542626765 75281304002880405953485037)
        ·
          refine ⟨28230489001080152232556889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 75281304002880405953485037 28230489001080152232556889)
          ·
            refine ⟨21172866750810114174417667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28230489001080152232556889 21172866750810114174417667)
            ·
              refine ⟨31759300126215171261626501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21172866750810114174417667 31759300126215171261626501)
              ·
                refine ⟨5954868773665344611554969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 31759300126215171261626501 5954868773665344611554969)
                ·
                  refine ⟨4466151580249008458666227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5954868773665344611554969 4466151580249008458666227)
                  ·
                    refine ⟨6699227370373512687999341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4466151580249008458666227 6699227370373512687999341)
                    ·
                      refine ⟨2512210263890067257999753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6699227370373512687999341 2512210263890067257999753)
                      ·
                        rfl

theorem cell23_4892512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 1, 4, 2, 1, 3].length) (baseStart_4892512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4892512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4892512 prefixEnd_4892512 := by exact prefixLift 4892512
  have htrace : WordTrace (prefixWord ++ tailWord_4892512) baseStart_4892512 baseEnd_4892512 := by
    simpa [prefixWord, tailWord_4892512, baseEnd_4892512] using wordTrace_append hprefix tailTrace_4892512
  have hstable : (prefixWord ++ tailWord_4892512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4892512).length < 2 ^ (prefixWord ++ tailWord_4892512).sum := by decide
  have hdescent : baseEnd_4892512 < baseStart_4892512 := by decide
  rcases family_descends (prefixWord ++ tailWord_4892512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4892538 : List Nat := [3, 1, 1, 1, 1, 1, 4, 1, 4, 1, 5]
def baseStart_4892538 : Nat := 118140960795 + 4892538 * 2 ^ 59
def prefixEnd_4892538 : Nat := 4983230072969 + 3 ^ 40 * 4892538 * 2
def baseEnd_4892538 : Nat := 2512223614387084156274633

theorem tailTrace_4892538 : CollatzResearch.WordTrace tailWord_4892538 prefixEnd_4892538 2512223614387084156274633 := by
  unfold tailWord_4892538
  simp only [CollatzResearch.WordTrace]
  refine ⟨44611380187294469952917567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 118963680499451919874446845 44611380187294469952917567)
  ·
    refine ⟨66917070280941704929376351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44611380187294469952917567 66917070280941704929376351)
    ·
      refine ⟨100375605421412557394064527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66917070280941704929376351 100375605421412557394064527)
      ·
        refine ⟨150563408132118836091096791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100375605421412557394064527 150563408132118836091096791)
        ·
          refine ⟨225845112198178254136645187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 150563408132118836091096791 225845112198178254136645187)
          ·
            refine ⟨338767668297267381204967781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 225845112198178254136645187 338767668297267381204967781)
            ·
              refine ⟨63518937805737633975931459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 338767668297267381204967781 63518937805737633975931459)
              ·
                refine ⟨95278406708606450963897189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 63518937805737633975931459 95278406708606450963897189)
                ·
                  refine ⟨17864701257863709555730723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 95278406708606450963897189 17864701257863709555730723)
                  ·
                    refine ⟨26797051886795564333596085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17864701257863709555730723 26797051886795564333596085)
                    ·
                      refine ⟨2512223614387084156274633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26797051886795564333596085 2512223614387084156274633)
                      ·
                        rfl

theorem cell23_4892538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 4, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 4, 1, 4, 1, 5].length) (baseStart_4892538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4892538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4892538 prefixEnd_4892538 := by exact prefixLift 4892538
  have htrace : WordTrace (prefixWord ++ tailWord_4892538) baseStart_4892538 baseEnd_4892538 := by
    simpa [prefixWord, tailWord_4892538, baseEnd_4892538] using wordTrace_append hprefix tailTrace_4892538
  have hstable : (prefixWord ++ tailWord_4892538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4892538).length < 2 ^ (prefixWord ++ tailWord_4892538).sum := by decide
  have hdescent : baseEnd_4892538 < baseStart_4892538 := by decide
  rcases family_descends (prefixWord ++ tailWord_4892538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4892569 : List Nat := [1, 2, 1, 2, 1, 3, 5, 2, 2, 2, 2]
def baseStart_4892569 : Nat := 118140960795 + 4892569 * 2 ^ 59
def prefixEnd_4892569 : Nat := 4983230072969 + 3 ^ 40 * 4892569 * 2
def baseEnd_4892569 : Nat := 2512239532287373534986991

theorem tailTrace_4892569 : CollatzResearch.WordTrace tailWord_4892569 prefixEnd_4892569 2512239532287373534986991 := by
  unfold tailWord_4892569
  simp only [CollatzResearch.WordTrace]
  refine ⟨178446651412065572106048761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118964434274710381404032507 178446651412065572106048761)
  ·
    refine ⟨133834988559049179079536571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 178446651412065572106048761 133834988559049179079536571)
    ·
      refine ⟨200752482838573768619304857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 133834988559049179079536571 200752482838573768619304857)
      ·
        refine ⟨150564362128930326464478643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 200752482838573768619304857 150564362128930326464478643)
        ·
          refine ⟨225846543193395489696717965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 150564362128930326464478643 225846543193395489696717965)
          ·
            refine ⟨84692453697523308636269237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 225846543193395489696717965 84692453697523308636269237)
            ·
              refine ⟨7939917534142810184650241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 84692453697523308636269237 7939917534142810184650241)
              ·
                refine ⟨5954938150607107638487681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7939917534142810184650241 5954938150607107638487681)
                ·
                  refine ⟨4466203612955330728865761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5954938150607107638487681 4466203612955330728865761)
                  ·
                    refine ⟨3349652709716498046649321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4466203612955330728865761 3349652709716498046649321)
                    ·
                      refine ⟨2512239532287373534986991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3349652709716498046649321 2512239532287373534986991)
                      ·
                        rfl

theorem cell23_4892569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 5, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 5, 2, 2, 2, 2].length) (baseStart_4892569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4892569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4892569 prefixEnd_4892569 := by exact prefixLift 4892569
  have htrace : WordTrace (prefixWord ++ tailWord_4892569) baseStart_4892569 baseEnd_4892569 := by
    simpa [prefixWord, tailWord_4892569, baseEnd_4892569] using wordTrace_append hprefix tailTrace_4892569
  have hstable : (prefixWord ++ tailWord_4892569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4892569).length < 2 ^ (prefixWord ++ tailWord_4892569).sum := by decide
  have hdescent : baseEnd_4892569 < baseStart_4892569 := by decide
  rcases family_descends (prefixWord ++ tailWord_4892569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4892590 : List Nat := [4, 1, 5, 1, 1, 1, 2, 2, 1, 3, 2]
def baseStart_4892590 : Nat := 118140960795 + 4892590 * 2 ^ 59
def prefixEnd_4892590 : Nat := 4983230072969 + 3 ^ 40 * 4892590 * 2
def baseEnd_4892590 : Nat := 2512250315381117952824395

theorem tailTrace_4892590 : CollatzResearch.WordTrace tailWord_4892590 prefixEnd_4892590 2512250315381117952824395 := by
  unfold tailWord_4892590
  simp only [CollatzResearch.WordTrace]
  refine ⟨22305927168123686586570403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 118964944896659661795042149 22305927168123686586570403)
  ·
    refine ⟨33458890752185529879855605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22305927168123686586570403 33458890752185529879855605)
    ·
      refine ⟨3136771008017393426236463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 33458890752185529879855605 3136771008017393426236463)
      ·
        refine ⟨4705156512026090139354695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3136771008017393426236463 4705156512026090139354695)
        ·
          refine ⟨7057734768039135209032043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4705156512026090139354695 7057734768039135209032043)
          ·
            refine ⟨10586602152058702813548065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7057734768039135209032043 10586602152058702813548065)
            ·
              refine ⟨7939951614044027110161049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10586602152058702813548065 7939951614044027110161049)
              ·
                refine ⟨5954963710533020332620787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7939951614044027110161049 5954963710533020332620787)
                ·
                  refine ⟨8932445565799530498931181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5954963710533020332620787 8932445565799530498931181)
                  ·
                    refine ⟨3349667087174823937099193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8932445565799530498931181 3349667087174823937099193)
                    ·
                      refine ⟨2512250315381117952824395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3349667087174823937099193 2512250315381117952824395)
                      ·
                        rfl

theorem cell23_4892590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 1, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 1, 2, 2, 1, 3, 2].length) (baseStart_4892590 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4892590 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4892590 prefixEnd_4892590 := by exact prefixLift 4892590
  have htrace : WordTrace (prefixWord ++ tailWord_4892590) baseStart_4892590 baseEnd_4892590 := by
    simpa [prefixWord, tailWord_4892590, baseEnd_4892590] using wordTrace_append hprefix tailTrace_4892590
  have hstable : (prefixWord ++ tailWord_4892590).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4892590).length < 2 ^ (prefixWord ++ tailWord_4892590).sum := by decide
  have hdescent : baseEnd_4892590 < baseStart_4892590 := by decide
  rcases family_descends (prefixWord ++ tailWord_4892590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4892605 : List Nat := [1, 4, 1, 2, 3, 1, 2, 1, 1, 7]
def baseStart_4892605 : Nat := 118140960795 + 4892605 * 2 ^ 59
def prefixEnd_4892605 : Nat := 4983230072969 + 3 ^ 40 * 4892605 * 2
def baseEnd_4892605 : Nat := 837419339196978464712275

theorem tailTrace_4892605 : CollatzResearch.WordTrace tailWord_4892605 prefixEnd_4892605 837419339196978464712275 := by
  unfold tailWord_4892605
  simp only [CollatzResearch.WordTrace]
  refine ⟨178447964439935150254359269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118965309626623433502906179 178447964439935150254359269)
  ·
    refine ⟨33458993332487840672692363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 178447964439935150254359269 33458993332487840672692363)
    ·
      refine ⟨50188489998731761009038545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33458993332487840672692363 50188489998731761009038545)
      ·
        refine ⟨37641367499048820756778909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50188489998731761009038545 37641367499048820756778909)
        ·
          refine ⟨14115512812143307783792091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37641367499048820756778909 14115512812143307783792091)
          ·
            refine ⟨21173269218214961675688137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14115512812143307783792091 21173269218214961675688137)
            ·
              refine ⟨15879951913661221256766103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21173269218214961675688137 15879951913661221256766103)
              ·
                refine ⟨23819927870491831885149155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15879951913661221256766103 23819927870491831885149155)
                ·
                  refine ⟨35729891805737747827723733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23819927870491831885149155 35729891805737747827723733)
                  ·
                    refine ⟨837419339196978464712275, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 35729891805737747827723733 837419339196978464712275)
                    ·
                      rfl

theorem cell23_4892605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 2, 1, 1, 7].length) (baseStart_4892605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4892605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4892605 prefixEnd_4892605 := by exact prefixLift 4892605
  have htrace : WordTrace (prefixWord ++ tailWord_4892605) baseStart_4892605 baseEnd_4892605 := by
    simpa [prefixWord, tailWord_4892605, baseEnd_4892605] using wordTrace_append hprefix tailTrace_4892605
  have hstable : (prefixWord ++ tailWord_4892605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4892605).length < 2 ^ (prefixWord ++ tailWord_4892605).sum := by decide
  have hdescent : baseEnd_4892605 < baseStart_4892605 := by decide
  rcases family_descends (prefixWord ++ tailWord_4892605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4892626 : List Nat := [3, 2, 2, 3, 2, 1, 3, 2, 5]
def baseStart_4892626 : Nat := 118140960795 + 4892626 * 2 ^ 59
def prefixEnd_4892626 : Nat := 4983230072969 + 3 ^ 40 * 4892626 * 2
def baseEnd_4892626 : Nat := 279140977853853312441581

theorem tailTrace_4892626 : CollatzResearch.WordTrace tailWord_4892626 prefixEnd_4892626 279140977853853312441581 := by
  unfold tailWord_4892626
  simp only [CollatzResearch.WordTrace]
  refine ⟨44612182593214767710218433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 118965820248572713893915821 44612182593214767710218433)
  ·
    refine ⟨33459136944911075782663825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44612182593214767710218433 33459136944911075782663825)
    ·
      refine ⟨25094352708683306836997869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33459136944911075782663825 25094352708683306836997869)
      ·
        refine ⟨9410382265756240063874201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25094352708683306836997869 9410382265756240063874201)
        ·
          refine ⟨7057786699317180047905651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9410382265756240063874201 7057786699317180047905651)
          ·
            refine ⟨10586680048975770071858477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7057786699317180047905651 10586680048975770071858477)
            ·
              refine ⟨3970005018365913776946929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10586680048975770071858477 3970005018365913776946929)
              ·
                refine ⟨2977503763774435332710197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3970005018365913776946929 2977503763774435332710197)
                ·
                  refine ⟨279140977853853312441581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2977503763774435332710197 279140977853853312441581)
                  ·
                    rfl

theorem cell23_4892626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 1, 3, 2, 5].length) (baseStart_4892626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4892626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4892626 prefixEnd_4892626 := by exact prefixLift 4892626
  have htrace : WordTrace (prefixWord ++ tailWord_4892626) baseStart_4892626 baseEnd_4892626 := by
    simpa [prefixWord, tailWord_4892626, baseEnd_4892626] using wordTrace_append hprefix tailTrace_4892626
  have hstable : (prefixWord ++ tailWord_4892626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4892626).length < 2 ^ (prefixWord ++ tailWord_4892626).sum := by decide
  have hdescent : baseEnd_4892626 < baseStart_4892626 := by decide
  rcases family_descends (prefixWord ++ tailWord_4892626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4892709 : List Nat := [1, 3, 1, 2, 2, 4, 1, 2, 3, 1, 3]
def baseStart_4892709 : Nat := 118140960795 + 4892709 * 2 ^ 59
def prefixEnd_4892709 : Nat := 4983230072969 + 3 ^ 40 * 4892709 * 2
def baseEnd_4892709 : Nat := 2512311419579002987236347

theorem tailTrace_4892709 : CollatzResearch.WordTrace tailWord_4892709 prefixEnd_4892709 2512311419579002987236347 := by
  unfold tailWord_4892709
  simp only [CollatzResearch.WordTrace]
  refine ⟨178451757631558376016145181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118967838421038917344096787 178451757631558376016145181)
  ·
    refine ⟨66919409111834391006054443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 178451757631558376016145181 66919409111834391006054443)
    ·
      refine ⟨100379113667751586509081665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66919409111834391006054443 100379113667751586509081665)
      ·
        refine ⟨75284335250813689881811249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 100379113667751586509081665 75284335250813689881811249)
        ·
          refine ⟨56463251438110267411358437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 75284335250813689881811249 56463251438110267411358437)
          ·
            refine ⟨10586859644645675139629707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 56463251438110267411358437 10586859644645675139629707)
            ·
              refine ⟨15880289466968512709444561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10586859644645675139629707 15880289466968512709444561)
              ·
                refine ⟨11910217100226384532083421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15880289466968512709444561 11910217100226384532083421)
                ·
                  refine ⟨4466331412584894199531283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11910217100226384532083421 4466331412584894199531283)
                  ·
                    refine ⟨6699497118877341299296925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4466331412584894199531283 6699497118877341299296925)
                    ·
                      refine ⟨2512311419579002987236347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6699497118877341299296925 2512311419579002987236347)
                      ·
                        rfl

theorem cell23_4892709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 4, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 4, 1, 2, 3, 1, 3].length) (baseStart_4892709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4892709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4892709 prefixEnd_4892709 := by exact prefixLift 4892709
  have htrace : WordTrace (prefixWord ++ tailWord_4892709) baseStart_4892709 baseEnd_4892709 := by
    simpa [prefixWord, tailWord_4892709, baseEnd_4892709] using wordTrace_append hprefix tailTrace_4892709
  have hstable : (prefixWord ++ tailWord_4892709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4892709).length < 2 ^ (prefixWord ++ tailWord_4892709).sum := by decide
  have hdescent : baseEnd_4892709 < baseStart_4892709 := by decide
  rcases family_descends (prefixWord ++ tailWord_4892709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4892729 : List Nat := [1, 2, 1, 5, 3, 1, 1, 3, 1, 5]
def baseStart_4892729 : Nat := 118140960795 + 4892729 * 2 ^ 59
def prefixEnd_4892729 : Nat := 4983230072969 + 3 ^ 40 * 4892729 * 2
def baseEnd_4892729 : Nat := 837440563064030969662085

theorem tailTrace_4892729 : CollatzResearch.WordTrace tailWord_4892729 prefixEnd_4892729 837440563064030969662085 := by
  unfold tailWord_4892729
  simp only [CollatzResearch.WordTrace]
  refine ⟨178452487091485919431873241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118968324727657279621248827 178452487091485919431873241)
  ·
    refine ⟨133839365318614439573904931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 178452487091485919431873241 133839365318614439573904931)
    ·
      refine ⟨200759047977921659360857397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 133839365318614439573904931 200759047977921659360857397)
      ·
        refine ⟨18821160747930155565080381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 200759047977921659360857397 18821160747930155565080381)
        ·
          refine ⟨7057935280473808336905143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18821160747930155565080381 7057935280473808336905143)
          ·
            refine ⟨10586902920710712505357715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7057935280473808336905143 10586902920710712505357715)
            ·
              refine ⟨15880354381066068758036573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10586902920710712505357715 15880354381066068758036573)
              ·
                refine ⟨5955132892899775784263715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15880354381066068758036573 5955132892899775784263715)
                ·
                  refine ⟨8932699339349663676395573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5955132892899775784263715 8932699339349663676395573)
                  ·
                    refine ⟨837440563064030969662085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8932699339349663676395573 837440563064030969662085)
                    ·
                      rfl

theorem cell23_4892729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 1, 1, 3, 1, 5].length) (baseStart_4892729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4892729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4892729 prefixEnd_4892729 := by exact prefixLift 4892729
  have htrace : WordTrace (prefixWord ++ tailWord_4892729) baseStart_4892729 baseEnd_4892729 := by
    simpa [prefixWord, tailWord_4892729, baseEnd_4892729] using wordTrace_append hprefix tailTrace_4892729
  have hstable : (prefixWord ++ tailWord_4892729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4892729).length < 2 ^ (prefixWord ++ tailWord_4892729).sum := by decide
  have hdescent : baseEnd_4892729 < baseStart_4892729 := by decide
  rcases family_descends (prefixWord ++ tailWord_4892729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4892745 : List Nat := [1, 2, 1, 1, 2, 2, 4, 2, 1, 1, 6]
def baseStart_4892745 : Nat := 118140960795 + 4892745 * 2 ^ 59
def prefixEnd_4892745 : Nat := 4983230072969 + 3 ^ 40 * 4892745 * 2
def baseEnd_4892745 : Nat := 2512329904882564846386181

theorem tailTrace_4892745 : CollatzResearch.WordTrace tailWord_4892745 prefixEnd_4892745 2512329904882564846386181 := by
  unfold tailWord_4892745
  simp only [CollatzResearch.WordTrace]
  refine ⟨178453070659427954164455689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118968713772951969442970459 178453070659427954164455689)
  ·
    refine ⟨133839802994570965623341767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 178453070659427954164455689 133839802994570965623341767)
    ·
      refine ⟨200759704491856448435012651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 133839802994570965623341767 200759704491856448435012651)
      ·
        refine ⟨301139556737784672652518977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 200759704491856448435012651 301139556737784672652518977)
        ·
          refine ⟨225854667553338504489389233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 301139556737784672652518977 225854667553338504489389233)
          ·
            refine ⟨169391000665003878367041925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 225854667553338504489389233 169391000665003878367041925)
            ·
              refine ⟨31760812624688227193820361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 169391000665003878367041925 31760812624688227193820361)
              ·
                refine ⟨23820609468516170395365271, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31760812624688227193820361 23820609468516170395365271)
                ·
                  refine ⟨35730914202774255593047907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23820609468516170395365271 35730914202774255593047907)
                  ·
                    refine ⟨53596371304161383389571861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 35730914202774255593047907 53596371304161383389571861)
                    ·
                      refine ⟨2512329904882564846386181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 53596371304161383389571861 2512329904882564846386181)
                      ·
                        rfl

theorem cell23_4892745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 4, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 4, 2, 1, 1, 6].length) (baseStart_4892745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4892745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4892745 prefixEnd_4892745 := by exact prefixLift 4892745
  have htrace : WordTrace (prefixWord ++ tailWord_4892745) baseStart_4892745 baseEnd_4892745 := by
    simpa [prefixWord, tailWord_4892745, baseEnd_4892745] using wordTrace_append hprefix tailTrace_4892745
  have hstable : (prefixWord ++ tailWord_4892745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4892745).length < 2 ^ (prefixWord ++ tailWord_4892745).sum := by decide
  have hdescent : baseEnd_4892745 < baseStart_4892745 := by decide
  rcases family_descends (prefixWord ++ tailWord_4892745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4892772 : List Nat := [2, 3, 1, 1, 2, 1, 6, 7]
def baseStart_4892772 : Nat := 118140960795 + 4892772 * 2 ^ 59
def prefixEnd_4892772 : Nat := 4983230072969 + 3 ^ 40 * 4892772 * 2
def baseEnd_4892772 : Nat := 93049769217045786694391

theorem tailTrace_4892772 : CollatzResearch.WordTrace tailWord_4892772 prefixEnd_4892772 93049769217045786694391 := by
  unfold tailWord_4892772
  simp only [CollatzResearch.WordTrace]
  refine ⟨89227027715165068887844285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118969370286886758517125713 89227027715165068887844285)
  ·
    refine ⟨33460135393186900832941607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 89227027715165068887844285 33460135393186900832941607)
    ·
      refine ⟨50190203089780351249412411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33460135393186900832941607 50190203089780351249412411)
      ·
        refine ⟨75285304634670526874118617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50190203089780351249412411 75285304634670526874118617)
        ·
          refine ⟨56463978476002895155588963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 75285304634670526874118617 56463978476002895155588963)
          ·
            refine ⟨84695967714004342733383445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56463978476002895155588963 84695967714004342733383445)
            ·
              refine ⟨3970123486593953565627349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 84695967714004342733383445 3970123486593953565627349)
              ·
                refine ⟨93049769217045786694391, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3970123486593953565627349 93049769217045786694391)
                ·
                  rfl

theorem cell23_4892772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 6, 7].length) (baseStart_4892772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4892772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4892772 prefixEnd_4892772 := by exact prefixLift 4892772
  have htrace : WordTrace (prefixWord ++ tailWord_4892772) baseStart_4892772 baseEnd_4892772 := by
    simpa [prefixWord, tailWord_4892772, baseEnd_4892772] using wordTrace_append hprefix tailTrace_4892772
  have hstable : (prefixWord ++ tailWord_4892772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4892772).length < 2 ^ (prefixWord ++ tailWord_4892772).sum := by decide
  have hdescent : baseEnd_4892772 < baseStart_4892772 := by decide
  rcases family_descends (prefixWord ++ tailWord_4892772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4892783 : List Nat := [1, 1, 2, 1, 3, 4, 3, 3, 1, 2, 2]
def baseStart_4892783 : Nat := 118140960795 + 4892783 * 2 ^ 59
def prefixEnd_4892783 : Nat := 4983230072969 + 3 ^ 40 * 4892783 * 2
def baseEnd_4892783 : Nat := 2512349417147435697711007

theorem tailTrace_4892783 : CollatzResearch.WordTrace tailWord_4892783 prefixEnd_4892783 2512349417147435697711007 := by
  unfold tailWord_4892783
  simp only [CollatzResearch.WordTrace]
  refine ⟨178454456633290286654339003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118969637755526857769559335 178454456633290286654339003)
  ·
    refine ⟨267681684949935429981508505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 178454456633290286654339003 267681684949935429981508505)
    ·
      refine ⟨200761263712451572486131379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 267681684949935429981508505 200761263712451572486131379)
      ·
        refine ⟨301141895568677358729197069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 200761263712451572486131379 301141895568677358729197069)
        ·
          refine ⟨112928210838254009523448901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 301141895568677358729197069 112928210838254009523448901)
          ·
            refine ⟨21174039532172626785646669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 112928210838254009523448901 21174039532172626785646669)
            ·
              refine ⟨7940264824564735044617501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21174039532172626785646669 7940264824564735044617501)
              ·
                refine ⟨2977599309211775641731563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7940264824564735044617501 2977599309211775641731563)
                ·
                  refine ⟨4466398963817663462597345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2977599309211775641731563 4466398963817663462597345)
                  ·
                    refine ⟨3349799222863247596948009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4466398963817663462597345 3349799222863247596948009)
                    ·
                      refine ⟨2512349417147435697711007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3349799222863247596948009 2512349417147435697711007)
                      ·
                        rfl

theorem cell23_4892783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 3, 3, 1, 2, 2].length) (baseStart_4892783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4892783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4892783 prefixEnd_4892783 := by exact prefixLift 4892783
  have htrace : WordTrace (prefixWord ++ tailWord_4892783) baseStart_4892783 baseEnd_4892783 := by
    simpa [prefixWord, tailWord_4892783, baseEnd_4892783] using wordTrace_append hprefix tailTrace_4892783
  have hstable : (prefixWord ++ tailWord_4892783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4892783).length < 2 ^ (prefixWord ++ tailWord_4892783).sum := by decide
  have hdescent : baseEnd_4892783 < baseStart_4892783 := by decide
  rcases family_descends (prefixWord ++ tailWord_4892783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4892809 : List Nat := [1, 2, 1, 1, 4, 2, 2, 2, 3, 3, 2]
def baseStart_4892809 : Nat := 118140960795 + 4892809 * 2 ^ 59
def prefixEnd_4892809 : Nat := 4983230072969 + 3 ^ 40 * 4892809 * 2
def baseEnd_4892809 : Nat := 2512362767644452595985887

theorem tailTrace_4892809 : CollatzResearch.WordTrace tailWord_4892809 prefixEnd_4892809 2512362767644452595985887 := by
  unfold tailWord_4892809
  simp only [CollatzResearch.WordTrace]
  refine ⟨178455404931196093094785481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118970269954130728729856987 178455404931196093094785481)
  ·
    refine ⟨133841553698397069821089111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 178455404931196093094785481 133841553698397069821089111)
    ·
      refine ⟨200762330547595604731633667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 133841553698397069821089111 200762330547595604731633667)
      ·
        refine ⟨301143495821393407097450501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 200762330547595604731633667 301143495821393407097450501)
        ·
          refine ⟨56464405466511263830771969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 301143495821393407097450501 56464405466511263830771969)
          ·
            refine ⟨42348304099883447873078977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56464405466511263830771969 42348304099883447873078977)
            ·
              refine ⟨31761228074912585904809233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42348304099883447873078977 31761228074912585904809233)
              ·
                refine ⟨23820921056184439428606925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31761228074912585904809233 23820921056184439428606925)
                ·
                  refine ⟨8932845396069164785727597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23820921056184439428606925 8932845396069164785727597)
                  ·
                    refine ⟨3349817023525936794647849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8932845396069164785727597 3349817023525936794647849)
                    ·
                      refine ⟨2512362767644452595985887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3349817023525936794647849 2512362767644452595985887)
                      ·
                        rfl

theorem cell23_4892809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 2, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 2, 2, 3, 3, 2].length) (baseStart_4892809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4892809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4892809 prefixEnd_4892809 := by exact prefixLift 4892809
  have htrace : WordTrace (prefixWord ++ tailWord_4892809) baseStart_4892809 baseEnd_4892809 := by
    simpa [prefixWord, tailWord_4892809, baseEnd_4892809] using wordTrace_append hprefix tailTrace_4892809
  have hstable : (prefixWord ++ tailWord_4892809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4892809).length < 2 ^ (prefixWord ++ tailWord_4892809).sum := by decide
  have hdescent : baseEnd_4892809 < baseStart_4892809 := by decide
  rcases family_descends (prefixWord ++ tailWord_4892809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4892820 : List Nat := [2, 4, 2, 3, 1, 2, 1, 2, 1, 2, 3]
def baseStart_4892820 : Nat := 118140960795 + 4892820 * 2 ^ 59
def prefixEnd_4892820 : Nat := 4983230072969 + 3 ^ 40 * 4892820 * 2
def baseEnd_4892820 : Nat := 2512368415931652052948337

theorem tailTrace_4892820 : CollatzResearch.WordTrace tailWord_4892820 prefixEnd_4892820 2512368415931652052948337 := by
  unfold tailWord_4892820
  simp only [CollatzResearch.WordTrace]
  refine ⟨89227903067078120986717957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118970537422770827982290609 89227903067078120986717957)
  ·
    refine ⟨16730231825077147685009617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 89227903067078120986717957 16730231825077147685009617)
    ·
      refine ⟨12547673868807860763757213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16730231825077147685009617 12547673868807860763757213)
      ·
        refine ⟨4705377700802947786408955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12547673868807860763757213 4705377700802947786408955)
        ·
          refine ⟨7058066551204421679613433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4705377700802947786408955 7058066551204421679613433)
          ·
            refine ⟨5293549913403316259710075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7058066551204421679613433 5293549913403316259710075)
            ·
              refine ⟨7940324870104974389565113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5293549913403316259710075 7940324870104974389565113)
              ·
                refine ⟨5955243652578730792173835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7940324870104974389565113 5955243652578730792173835)
                ·
                  refine ⟨8932865478868096188260753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5955243652578730792173835 8932865478868096188260753)
                  ·
                    refine ⟨6699649109151072141195565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8932865478868096188260753 6699649109151072141195565)
                    ·
                      refine ⟨2512368415931652052948337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6699649109151072141195565 2512368415931652052948337)
                      ·
                        rfl

theorem cell23_4892820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 2, 1, 2, 1, 2, 3].length) (baseStart_4892820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4892820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4892820 prefixEnd_4892820 := by exact prefixLift 4892820
  have htrace : WordTrace (prefixWord ++ tailWord_4892820) baseStart_4892820 baseEnd_4892820 := by
    simpa [prefixWord, tailWord_4892820, baseEnd_4892820] using wordTrace_append hprefix tailTrace_4892820
  have hstable : (prefixWord ++ tailWord_4892820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4892820).length < 2 ^ (prefixWord ++ tailWord_4892820).sum := by decide
  have hdescent : baseEnd_4892820 < baseStart_4892820 := by decide
  rcases family_descends (prefixWord ++ tailWord_4892820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4892866 : List Nat := [3, 5, 1, 1, 1, 1, 1, 1, 1, 8]
def baseStart_4892866 : Nat := 118140960795 + 4892866 * 2 ^ 59
def prefixEnd_4892866 : Nat := 4983230072969 + 3 ^ 40 * 4892866 * 2
def baseEnd_4892866 : Nat := 837464012013919624324375

theorem tailTrace_4892866 : CollatzResearch.WordTrace tailWord_4892866 prefixEnd_4892866 837464012013919624324375 := by
  unfold tailWord_4892866
  simp only [CollatzResearch.WordTrace]
  refine ⟨44614370972997397957402613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 118971655927993061219740301 44614370972997397957402613)
  ·
    refine ⟨4182597278718506058506495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 44614370972997397957402613 4182597278718506058506495)
    ·
      refine ⟨6273895918077759087759743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4182597278718506058506495 6273895918077759087759743)
      ·
        refine ⟨9410843877116638631639615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6273895918077759087759743 9410843877116638631639615)
        ·
          refine ⟨14116265815674957947459423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9410843877116638631639615 14116265815674957947459423)
          ·
            refine ⟨21174398723512436921189135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14116265815674957947459423 21174398723512436921189135)
            ·
              refine ⟨31761598085268655381783703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21174398723512436921189135 31761598085268655381783703)
              ·
                refine ⟨47642397127902983072675555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31761598085268655381783703 47642397127902983072675555)
                ·
                  refine ⟨71463595691854474609013333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 47642397127902983072675555 71463595691854474609013333)
                  ·
                    refine ⟨837464012013919624324375, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 71463595691854474609013333 837464012013919624324375)
                    ·
                      rfl

theorem cell23_4892866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 1, 1, 1, 8].length) (baseStart_4892866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4892866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4892866 prefixEnd_4892866 := by exact prefixLift 4892866
  have htrace : WordTrace (prefixWord ++ tailWord_4892866) baseStart_4892866 baseEnd_4892866 := by
    simpa [prefixWord, tailWord_4892866, baseEnd_4892866] using wordTrace_append hprefix tailTrace_4892866
  have hstable : (prefixWord ++ tailWord_4892866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4892866).length < 2 ^ (prefixWord ++ tailWord_4892866).sum := by decide
  have hdescent : baseEnd_4892866 < baseStart_4892866 := by decide
  rcases family_descends (prefixWord ++ tailWord_4892866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4892939 : List Nat := [1, 1, 1, 1, 5, 2, 1, 4, 3, 4]
def baseStart_4892939 : Nat := 118140960795 + 4892939 * 2 ^ 59
def prefixEnd_4892939 : Nat := 4983230072969 + 3 ^ 40 * 4892939 * 2
def baseEnd_4892939 : Nat := 837476506709845695786763

theorem tailTrace_4892939 : CollatzResearch.WordTrace tailWord_4892939 prefixEnd_4892939 837476506709845695786763 := by
  unfold tailWord_4892939
  simp only [CollatzResearch.WordTrace]
  refine ⟨178460146420725125297017871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118973430947150083531345247 178460146420725125297017871)
  ·
    refine ⟨267690219631087687945526807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 178460146420725125297017871 267690219631087687945526807)
    ·
      refine ⟨401535329446631531918290211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 267690219631087687945526807 401535329446631531918290211)
      ·
        refine ⟨602302994169947297877435317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 401535329446631531918290211 602302994169947297877435317)
        ·
          refine ⟨56465905703432559176009561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 602302994169947297877435317 56465905703432559176009561)
          ·
            refine ⟨42349429277574419382007171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56465905703432559176009561 42349429277574419382007171)
            ·
              refine ⟨63524143916361629073010757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42349429277574419382007171 63524143916361629073010757)
              ·
                refine ⟨11910776984317805451189517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 63524143916361629073010757 11910776984317805451189517)
                ·
                  refine ⟨4466541369119177044196069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11910776984317805451189517 4466541369119177044196069)
                  ·
                    refine ⟨837476506709845695786763, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4466541369119177044196069 837476506709845695786763)
                    ·
                      rfl

theorem cell23_4892939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 1, 4, 3, 4].length) (baseStart_4892939 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4892939 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4892939 prefixEnd_4892939 := by exact prefixLift 4892939
  have htrace : WordTrace (prefixWord ++ tailWord_4892939) baseStart_4892939 baseEnd_4892939 := by
    simpa [prefixWord, tailWord_4892939, baseEnd_4892939] using wordTrace_append hprefix tailTrace_4892939
  have hstable : (prefixWord ++ tailWord_4892939).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4892939).length < 2 ^ (prefixWord ++ tailWord_4892939).sum := by decide
  have hdescent : baseEnd_4892939 < baseStart_4892939 := by decide
  rcases family_descends (prefixWord ++ tailWord_4892939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4892949 : List Nat := [1, 3, 2, 1, 2, 1, 4, 1, 1, 4, 3]
def baseStart_4892949 : Nat := 118140960795 + 4892949 * 2 ^ 59
def prefixEnd_4892949 : Nat := 4983230072969 + 3 ^ 40 * 4892949 * 2
def baseEnd_4892949 : Nat := 2512434654936082048235243

theorem tailTrace_4892949 : CollatzResearch.WordTrace tailWord_4892949 prefixEnd_4892949 2512434654936082048235243 := by
  unfold tailWord_4892949
  simp only [CollatzResearch.WordTrace]
  refine ⟨178460511150688897004881901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118973674100459264669921267 178460511150688897004881901)
  ·
    refine ⟨66922691681508336376830713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 178460511150688897004881901 66922691681508336376830713)
    ·
      refine ⟨50192018761131252282623035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66922691681508336376830713 50192018761131252282623035)
      ·
        refine ⟨75288028141696878423934553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50192018761131252282623035 75288028141696878423934553)
        ·
          refine ⟨56466021106272658817950915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 75288028141696878423934553 56466021106272658817950915)
          ·
            refine ⟨84699031659408988226926373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56466021106272658817950915 84699031659408988226926373)
            ·
              refine ⟨15881068436139185292548695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 84699031659408988226926373 15881068436139185292548695)
              ·
                refine ⟨23821602654208777938823043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15881068436139185292548695 23821602654208777938823043)
                ·
                  refine ⟨35732403981313166908234565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23821602654208777938823043 35732403981313166908234565)
                  ·
                    refine ⟨6699825746496218795293981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 35732403981313166908234565 6699825746496218795293981)
                    ·
                      refine ⟨2512434654936082048235243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6699825746496218795293981 2512434654936082048235243)
                      ·
                        rfl

theorem cell23_4892949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 4, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 4, 1, 1, 4, 3].length) (baseStart_4892949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4892949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4892949 prefixEnd_4892949 := by exact prefixLift 4892949
  have htrace : WordTrace (prefixWord ++ tailWord_4892949) baseStart_4892949 baseEnd_4892949 := by
    simpa [prefixWord, tailWord_4892949, baseEnd_4892949] using wordTrace_append hprefix tailTrace_4892949
  have hstable : (prefixWord ++ tailWord_4892949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4892949).length < 2 ^ (prefixWord ++ tailWord_4892949).sum := by decide
  have hdescent : baseEnd_4892949 < baseStart_4892949 := by decide
  rcases family_descends (prefixWord ++ tailWord_4892949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4892952 : List Nat := [2, 1, 2, 3, 1, 2, 1, 1, 10]
def baseStart_4892952 : Nat := 118140960795 + 4892952 * 2 ^ 59
def prefixEnd_4892952 : Nat := 4983230072969 + 3 ^ 40 * 4892952 * 2
def baseEnd_4892952 : Nat := 279159577264227281833081

theorem tailTrace_4892952 : CollatzResearch.WordTrace tailWord_4892952 prefixEnd_4892952 279159577264227281833081 := by
  unfold tailWord_4892952
  simp only [CollatzResearch.WordTrace]
  refine ⟨89230310284839014258620555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118973747046452019011494073 89230310284839014258620555)
  ·
    refine ⟨133845465427258521387930833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89230310284839014258620555 133845465427258521387930833)
    ·
      refine ⟨100384099070443891040948125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 133845465427258521387930833 100384099070443891040948125)
      ·
        refine ⟨37644037151416459140355547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 100384099070443891040948125 37644037151416459140355547)
        ·
          refine ⟨56466055727124688710533321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37644037151416459140355547 56466055727124688710533321)
          ·
            refine ⟨42349541795343516532899991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56466055727124688710533321 42349541795343516532899991)
            ·
              refine ⟨63524312693015274799349987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42349541795343516532899991 63524312693015274799349987)
              ·
                refine ⟨95286469039522912199024981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 63524312693015274799349987 95286469039522912199024981)
                ·
                  refine ⟨279159577264227281833081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 95286469039522912199024981 279159577264227281833081)
                  ·
                    rfl

theorem cell23_4892952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 1, 1, 10].length) (baseStart_4892952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4892952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4892952 prefixEnd_4892952 := by exact prefixLift 4892952
  have htrace : WordTrace (prefixWord ++ tailWord_4892952) baseStart_4892952 baseEnd_4892952 := by
    simpa [prefixWord, tailWord_4892952, baseEnd_4892952] using wordTrace_append hprefix tailTrace_4892952
  have hstable : (prefixWord ++ tailWord_4892952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4892952).length < 2 ^ (prefixWord ++ tailWord_4892952).sum := by decide
  have hdescent : baseEnd_4892952 < baseStart_4892952 := by decide
  rcases family_descends (prefixWord ++ tailWord_4892952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4892972 : List Nat := [2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 8]
def baseStart_4892972 : Nat := 118140960795 + 4892972 * 2 ^ 59
def prefixEnd_4892972 : Nat := 4983230072969 + 3 ^ 40 * 4892972 * 2
def baseEnd_4892972 : Nat := 2512446464991135458247637

theorem tailTrace_4892972 : CollatzResearch.WordTrace tailWord_4892972 prefixEnd_4892972 2512446464991135458247637 := by
  unfold tailWord_4892972
  simp only [CollatzResearch.WordTrace]
  refine ⟨89230675014802785966484585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118974233353070381288646113 89230675014802785966484585)
  ·
    refine ⟨66923006261102089474863439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89230675014802785966484585 66923006261102089474863439)
    ·
      refine ⟨100384509391653134212295159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66923006261102089474863439 100384509391653134212295159)
      ·
        refine ⟨150576764087479701318442739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100384509391653134212295159 150576764087479701318442739)
        ·
          refine ⟨225865146131219551977664109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 150576764087479701318442739 225865146131219551977664109)
          ·
            refine ⟨84699429799207331991624041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 225865146131219551977664109 84699429799207331991624041)
            ·
              refine ⟨63524572349405498993718031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 84699429799207331991624041 63524572349405498993718031)
              ·
                refine ⟨95286858524108248490577047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 63524572349405498993718031 95286858524108248490577047)
                ·
                  refine ⟨142930287786162372735865571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 95286858524108248490577047 142930287786162372735865571)
                  ·
                    refine ⟨214395431679243559103798357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 142930287786162372735865571 214395431679243559103798357)
                    ·
                      refine ⟨2512446464991135458247637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 214395431679243559103798357 2512446464991135458247637)
                      ·
                        rfl

theorem cell23_4892972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 8].length) (baseStart_4892972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4892972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4892972 prefixEnd_4892972 := by exact prefixLift 4892972
  have htrace : WordTrace (prefixWord ++ tailWord_4892972) baseStart_4892972 baseEnd_4892972 := by
    simpa [prefixWord, tailWord_4892972, baseEnd_4892972] using wordTrace_append hprefix tailTrace_4892972
  have hstable : (prefixWord ++ tailWord_4892972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4892972).length < 2 ^ (prefixWord ++ tailWord_4892972).sum := by decide
  have hdescent : baseEnd_4892972 < baseStart_4892972 := by decide
  rcases family_descends (prefixWord ++ tailWord_4892972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4892986 : List Nat := [3, 1, 1, 1, 4, 2, 4, 1, 6]
def baseStart_4892986 : Nat := 118140960795 + 4892986 * 2 ^ 59
def prefixEnd_4892986 : Nat := 4983230072969 + 3 ^ 40 * 4892986 * 2
def baseEnd_4892986 : Nat := 279161517080033155941397

theorem tailTrace_4892986 : CollatzResearch.WordTrace tailWord_4892986 prefixEnd_4892986 279161517080033155941397 := by
  unfold tailWord_4892986
  simp only [CollatzResearch.WordTrace]
  refine ⟨44615465162888713080994703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 118974573767703234882652541 44615465162888713080994703)
  ·
    refine ⟨66923197744333069621492055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44615465162888713080994703 66923197744333069621492055)
    ·
      refine ⟨100384796616499604432238083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66923197744333069621492055 100384796616499604432238083)
      ·
        refine ⟨150577194924749406648357125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100384796616499604432238083 150577194924749406648357125)
        ·
          refine ⟨28233224048390513746566961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 150577194924749406648357125 28233224048390513746566961)
          ·
            refine ⟨21174918036292885309925221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28233224048390513746566961 21174918036292885309925221)
            ·
              refine ⟨3970297131804915995610979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21174918036292885309925221 3970297131804915995610979)
              ·
                refine ⟨5955445697707373993416469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3970297131804915995610979 5955445697707373993416469)
                ·
                  refine ⟨279161517080033155941397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5955445697707373993416469 279161517080033155941397)
                  ·
                    rfl

theorem cell23_4892986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 4, 1, 6].length) (baseStart_4892986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4892986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4892986 prefixEnd_4892986 := by exact prefixLift 4892986
  have htrace : WordTrace (prefixWord ++ tailWord_4892986) baseStart_4892986 baseEnd_4892986 := by
    simpa [prefixWord, tailWord_4892986, baseEnd_4892986] using wordTrace_append hprefix tailTrace_4892986
  have hstable : (prefixWord ++ tailWord_4892986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4892986).length < 2 ^ (prefixWord ++ tailWord_4892986).sum := by decide
  have hdescent : baseEnd_4892986 < baseStart_4892986 := by decide
  rcases family_descends (prefixWord ++ tailWord_4892986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4892992 : List Nat := [2, 1, 1, 2, 2, 1, 2, 1, 1, 3, 7]
def baseStart_4892992 : Nat := 118140960795 + 4892992 * 2 ^ 59
def prefixEnd_4892992 : Nat := 4983230072969 + 3 ^ 40 * 4892992 * 2
def baseEnd_4892992 : Nat := 2512456734604225379997545

theorem tailTrace_4892992 : CollatzResearch.WordTrace tailWord_4892992 prefixEnd_4892992 2512456734604225379997545 := by
  unfold tailWord_4892992
  simp only [CollatzResearch.WordTrace]
  refine ⟨89231039744766557674348615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118974719659688743565798153 89231039744766557674348615)
  ·
    refine ⟨133846559617149836511522923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89231039744766557674348615 133846559617149836511522923)
    ·
      refine ⟨200769839425724754767284385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 133846559617149836511522923 200769839425724754767284385)
      ·
        refine ⟨150577379569293566075463289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 200769839425724754767284385 150577379569293566075463289)
        ·
          refine ⟨112933034676970174556597467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 150577379569293566075463289 112933034676970174556597467)
          ·
            refine ⟨169399552015455261834896201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 112933034676970174556597467 169399552015455261834896201)
            ·
              refine ⟨127049664011591446376172151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 169399552015455261834896201 127049664011591446376172151)
              ·
                refine ⟨190574496017387169564258227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 127049664011591446376172151 190574496017387169564258227)
                ·
                  refine ⟨285861744026080754346387341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 190574496017387169564258227 285861744026080754346387341)
                  ·
                    refine ⟨107198154009780282879895253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 285861744026080754346387341 107198154009780282879895253)
                    ·
                      refine ⟨2512456734604225379997545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 107198154009780282879895253 2512456734604225379997545)
                      ·
                        rfl

theorem cell23_4892992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 1, 1, 3, 7].length) (baseStart_4892992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4892992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4892992 prefixEnd_4892992 := by exact prefixLift 4892992
  have htrace : WordTrace (prefixWord ++ tailWord_4892992) baseStart_4892992 baseEnd_4892992 := by
    simpa [prefixWord, tailWord_4892992, baseEnd_4892992] using wordTrace_append hprefix tailTrace_4892992
  have hstable : (prefixWord ++ tailWord_4892992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4892992).length < 2 ^ (prefixWord ++ tailWord_4892992).sum := by decide
  have hdescent : baseEnd_4892992 < baseStart_4892992 := by decide
  rcases family_descends (prefixWord ++ tailWord_4892992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4892999 : List Nat := [1, 1, 4, 1, 2, 2, 3, 1, 3, 5]
def baseStart_4892999 : Nat := 118140960795 + 4892999 * 2 ^ 59
def prefixEnd_4892999 : Nat := 4983230072969 + 3 ^ 40 * 4892999 * 2
def baseEnd_4892999 : Nat := 837486776322935617536671

theorem tailTrace_4892999 : CollatzResearch.WordTrace tailWord_4892999 prefixEnd_4892999 837486776322935617536671 := by
  unfold tailWord_4892999
  simp only [CollatzResearch.WordTrace]
  refine ⟨178462334800507755544202051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118974889867005170362801367 178462334800507755544202051)
  ·
    refine ⟨267693502200761633316303077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 178462334800507755544202051 267693502200761633316303077)
    ·
      refine ⟨50192531662642806246806827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 267693502200761633316303077 50192531662642806246806827)
      ·
        refine ⟨75288797493964209370210241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50192531662642806246806827 75288797493964209370210241)
        ·
          refine ⟨56466598120473157027657681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 75288797493964209370210241 56466598120473157027657681)
          ·
            refine ⟨42349948590354867770743261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56466598120473157027657681 42349948590354867770743261)
            ·
              refine ⟨15881230721383075414028723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 42349948590354867770743261 15881230721383075414028723)
              ·
                refine ⟨23821846082074613121043085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15881230721383075414028723 23821846082074613121043085)
                ·
                  refine ⟨8933192280777979920391157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23821846082074613121043085 8933192280777979920391157)
                  ·
                    refine ⟨837486776322935617536671, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8933192280777979920391157 837486776322935617536671)
                    ·
                      rfl

theorem cell23_4892999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 3, 1, 3, 5].length) (baseStart_4892999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4892999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4892999 prefixEnd_4892999 := by exact prefixLift 4892999
  have htrace : WordTrace (prefixWord ++ tailWord_4892999) baseStart_4892999 baseEnd_4892999 := by
    simpa [prefixWord, tailWord_4892999, baseEnd_4892999] using wordTrace_append hprefix tailTrace_4892999
  have hstable : (prefixWord ++ tailWord_4892999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4892999).length < 2 ^ (prefixWord ++ tailWord_4892999).sum := by decide
  have hdescent : baseEnd_4892999 < baseStart_4892999 := by decide
  rcases family_descends (prefixWord ++ tailWord_4892999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4893053 : List Nat := [1, 4, 1, 1, 2, 3, 1, 1, 5, 2, 2]
def baseStart_4893053 : Nat := 118140960795 + 4893053 * 2 ^ 59
def prefixEnd_4893053 : Nat := 4983230072969 + 3 ^ 40 * 4893053 * 2
def baseEnd_4893053 : Nat := 2512488056924149641334765

theorem tailTrace_4893053 : CollatzResearch.WordTrace tailWord_4893053 prefixEnd_4893053 2512488056924149641334765 := by
  unfold tailWord_4893053
  simp only [CollatzResearch.WordTrace]
  refine ⟨178464304342312122766667813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118976202894874748511111875 178464304342312122766667813)
  ·
    refine ⟨33462057064183523018750215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 178464304342312122766667813 33462057064183523018750215)
    ·
      refine ⟨50193085596275284528125323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33462057064183523018750215 50193085596275284528125323)
      ·
        refine ⟨75289628394412926792187985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50193085596275284528125323 75289628394412926792187985)
        ·
          refine ⟨56467221295809695094140989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 75289628394412926792187985 56467221295809695094140989)
          ·
            refine ⟨21175207985928635660302871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 56467221295809695094140989 21175207985928635660302871)
            ·
              refine ⟨31762811978892953490454307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21175207985928635660302871 31762811978892953490454307)
              ·
                refine ⟨47644217968339430235681461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31762811978892953490454307 47644217968339430235681461)
                ·
                  refine ⟨4466645434531821584595137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 47644217968339430235681461 4466645434531821584595137)
                  ·
                    refine ⟨3349984075898866188446353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4466645434531821584595137 3349984075898866188446353)
                    ·
                      refine ⟨2512488056924149641334765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3349984075898866188446353 2512488056924149641334765)
                      ·
                        rfl

theorem cell23_4893053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 1, 1, 5, 2, 2].length) (baseStart_4893053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4893053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4893053 prefixEnd_4893053 := by exact prefixLift 4893053
  have htrace : WordTrace (prefixWord ++ tailWord_4893053) baseStart_4893053 baseEnd_4893053 := by
    simpa [prefixWord, tailWord_4893053, baseEnd_4893053] using wordTrace_append hprefix tailTrace_4893053
  have hstable : (prefixWord ++ tailWord_4893053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4893053).length < 2 ^ (prefixWord ++ tailWord_4893053).sum := by decide
  have hdescent : baseEnd_4893053 < baseStart_4893053 := by decide
  rcases family_descends (prefixWord ++ tailWord_4893053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4893070 : List Nat := [4, 1, 1, 4, 1, 1, 4, 1, 1, 1, 4]
def baseStart_4893070 : Nat := 118140960795 + 4893070 * 2 ^ 59
def prefixEnd_4893070 : Nat := 4983230072969 + 3 ^ 40 * 4893070 * 2
def baseEnd_4893070 : Nat := 2512496786095276074822187

theorem tailTrace_4893070 : CollatzResearch.WordTrace tailWord_4893070 prefixEnd_4893070 2512496786095276074822187 := by
  unfold tailWord_4893070
  simp only [CollatzResearch.WordTrace]
  refine ⟨22308115547906316833754583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 118976616255500356446691109 22308115547906316833754583)
  ·
    refine ⟨33462173321859475250631875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22308115547906316833754583 33462173321859475250631875)
    ·
      refine ⟨50193259982789212875947813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33462173321859475250631875 50193259982789212875947813)
      ·
        refine ⟨9411236246772977414240215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 50193259982789212875947813 9411236246772977414240215)
        ·
          refine ⟨14116854370159466121360323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9411236246772977414240215 14116854370159466121360323)
          ·
            refine ⟨21175281555239199182040485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14116854370159466121360323 21175281555239199182040485)
            ·
              refine ⟨3970365291607349846632591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21175281555239199182040485 3970365291607349846632591)
              ·
                refine ⟨5955547937411024769948887, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3970365291607349846632591 5955547937411024769948887)
                ·
                  refine ⟨8933321906116537154923331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5955547937411024769948887 8933321906116537154923331)
                  ·
                    refine ⟨13399982859174805732384997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8933321906116537154923331 13399982859174805732384997)
                    ·
                      refine ⟨2512496786095276074822187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13399982859174805732384997 2512496786095276074822187)
                      ·
                        rfl

theorem cell23_4893070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 4, 1, 1, 1, 4].length) (baseStart_4893070 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4893070 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4893070 prefixEnd_4893070 := by exact prefixLift 4893070
  have htrace : WordTrace (prefixWord ++ tailWord_4893070) baseStart_4893070 baseEnd_4893070 := by
    simpa [prefixWord, tailWord_4893070, baseEnd_4893070] using wordTrace_append hprefix tailTrace_4893070
  have hstable : (prefixWord ++ tailWord_4893070).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4893070).length < 2 ^ (prefixWord ++ tailWord_4893070).sum := by decide
  have hdescent : baseEnd_4893070 < baseStart_4893070 := by decide
  rcases family_descends (prefixWord ++ tailWord_4893070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4893076 : List Nat := [2, 4, 2, 1, 3, 1, 10]
def baseStart_4893076 : Nat := 118140960795 + 4893076 * 2 ^ 59
def prefixEnd_4893076 : Nat := 4983230072969 + 3 ^ 40 * 4893076 * 2
def baseEnd_4893076 : Nat := 31018516876286457424039

theorem tailTrace_4893076 : CollatzResearch.WordTrace tailWord_4893076 prefixEnd_4893076 31018516876286457424039 := by
  unfold tailWord_4893076
  simp only [CollatzResearch.WordTrace]
  refine ⟨89232571610614398847377541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118976762147485865129836721 89232571610614398847377541)
  ·
    refine ⟨16731107176990199783883289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 89232571610614398847377541 16731107176990199783883289)
    ·
      refine ⟨12548330382742649837912467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16731107176990199783883289 12548330382742649837912467)
      ·
        refine ⟨18822495574113974756868701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12548330382742649837912467 18822495574113974756868701)
        ·
          refine ⟨7058435840292740533825763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18822495574113974756868701 7058435840292740533825763)
          ·
            refine ⟨10587653760439110800738645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7058435840292740533825763 10587653760439110800738645)
            ·
              refine ⟨31018516876286457424039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 10587653760439110800738645 31018516876286457424039)
              ·
                rfl

theorem cell23_4893076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 1, 10].length) (baseStart_4893076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4893076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4893076 prefixEnd_4893076 := by exact prefixLift 4893076
  have htrace : WordTrace (prefixWord ++ tailWord_4893076) baseStart_4893076 baseEnd_4893076 := by
    simpa [prefixWord, tailWord_4893076, baseEnd_4893076] using wordTrace_append hprefix tailTrace_4893076
  have hstable : (prefixWord ++ tailWord_4893076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4893076).length < 2 ^ (prefixWord ++ tailWord_4893076).sum := by decide
  have hdescent : baseEnd_4893076 < baseStart_4893076 := by decide
  rcases family_descends (prefixWord ++ tailWord_4893076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4893080 : List Nat := [2, 1, 2, 5, 1, 3, 1, 2, 2, 4]
def baseStart_4893080 : Nat := 118140960795 + 4893080 * 2 ^ 59
def prefixEnd_4893080 : Nat := 4983230072969 + 3 ^ 40 * 4893080 * 2
def baseEnd_4893080 : Nat := 837500640300607011899047

theorem tailTrace_4893080 : CollatzResearch.WordTrace tailWord_4893080 prefixEnd_4893080 837500640300607011899047 := by
  unfold tailWord_4893080
  simp only [CollatzResearch.WordTrace]
  refine ⟨89232644556607153188950347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118976859408809537585267129 89232644556607153188950347)
  ·
    refine ⟨133848966834910729783425521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89232644556607153188950347 133848966834910729783425521)
    ·
      refine ⟨100386725126183047337569141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 133848966834910729783425521 100386725126183047337569141)
      ·
        refine ⟨9411255480579660687897107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 100386725126183047337569141 9411255480579660687897107)
        ·
          refine ⟨14116883220869491031845661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9411255480579660687897107 14116883220869491031845661)
          ·
            refine ⟨5293831207826059136942123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14116883220869491031845661 5293831207826059136942123)
            ·
              refine ⟨7940746811739088705413185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5293831207826059136942123 7940746811739088705413185)
              ·
                refine ⟨5955560108804316529059889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7940746811739088705413185 5955560108804316529059889)
                ·
                  refine ⟨4466670081603237396794917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5955560108804316529059889 4466670081603237396794917)
                  ·
                    refine ⟨837500640300607011899047, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4466670081603237396794917 837500640300607011899047)
                    ·
                      rfl

theorem cell23_4893080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 3, 1, 2, 2, 4].length) (baseStart_4893080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4893080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4893080 prefixEnd_4893080 := by exact prefixLift 4893080
  have htrace : WordTrace (prefixWord ++ tailWord_4893080) baseStart_4893080 baseEnd_4893080 := by
    simpa [prefixWord, tailWord_4893080, baseEnd_4893080] using wordTrace_append hprefix tailTrace_4893080
  have hstable : (prefixWord ++ tailWord_4893080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4893080).length < 2 ^ (prefixWord ++ tailWord_4893080).sum := by decide
  have hdescent : baseEnd_4893080 < baseStart_4893080 := by decide
  rcases family_descends (prefixWord ++ tailWord_4893080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4893116 : List Nat := [2, 2, 2, 4, 1, 1, 1, 1, 2, 2, 5]
def baseStart_4893116 : Nat := 118140960795 + 4893116 * 2 ^ 59
def prefixEnd_4893116 : Nat := 4983230072969 + 3 ^ 40 * 4893116 * 2
def baseEnd_4893116 : Nat := 2512520406205382894846975

theorem tailTrace_4893116 : CollatzResearch.WordTrace tailWord_4893116 prefixEnd_4893116 2512520406205382894846975 := by
  unfold tailWord_4893116
  simp only [CollatzResearch.WordTrace]
  refine ⟨89233301070541942263105601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118977734760722589684140801 89233301070541942263105601)
  ·
    refine ⟨66924975802906456697329201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89233301070541942263105601 66924975802906456697329201)
    ·
      refine ⟨50193731852179842522996901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66924975802906456697329201 50193731852179842522996901)
      ·
        refine ⟨9411324722283720473061919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 50193731852179842522996901 9411324722283720473061919)
        ·
          refine ⟨14116987083425580709592879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9411324722283720473061919 14116987083425580709592879)
          ·
            refine ⟨21175480625138371064389319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14116987083425580709592879 21175480625138371064389319)
            ·
              refine ⟨31763220937707556596583979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21175480625138371064389319 31763220937707556596583979)
              ·
                refine ⟨47644831406561334894875969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31763220937707556596583979 47644831406561334894875969)
                ·
                  refine ⟨35733623554921001171156977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 47644831406561334894875969 35733623554921001171156977)
                  ·
                    refine ⟨26800217666190750878367733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 35733623554921001171156977 26800217666190750878367733)
                    ·
                      refine ⟨2512520406205382894846975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26800217666190750878367733 2512520406205382894846975)
                      ·
                        rfl

theorem cell23_4893116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 1, 1, 2, 2, 5].length) (baseStart_4893116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4893116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4893116 prefixEnd_4893116 := by exact prefixLift 4893116
  have htrace : WordTrace (prefixWord ++ tailWord_4893116) baseStart_4893116 baseEnd_4893116 := by
    simpa [prefixWord, tailWord_4893116, baseEnd_4893116] using wordTrace_append hprefix tailTrace_4893116
  have hstable : (prefixWord ++ tailWord_4893116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4893116).length < 2 ^ (prefixWord ++ tailWord_4893116).sum := by decide
  have hdescent : baseEnd_4893116 < baseStart_4893116 := by decide
  rcases family_descends (prefixWord ++ tailWord_4893116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4893129 : List Nat := [1, 2, 1, 1, 2, 1, 5, 1, 1, 3, 5]
def baseStart_4893129 : Nat := 118140960795 + 4893129 * 2 ^ 59
def prefixEnd_4893129 : Nat := 4983230072969 + 3 ^ 40 * 4893129 * 2
def baseEnd_4893129 : Nat := 2512527081453891343984415

theorem tailTrace_4893129 : CollatzResearch.WordTrace tailWord_4893129 prefixEnd_4893129 2512527081453891343984415 := by
  unfold tailWord_4893129
  simp only [CollatzResearch.WordTrace]
  refine ⟨178467076290036787746434441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118978050860024525164289627 178467076290036787746434441)
  ·
    refine ⟨133850307217527590809825831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 178467076290036787746434441 133850307217527590809825831)
    ·
      refine ⟨200775460826291386214738747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 133850307217527590809825831 200775460826291386214738747)
      ·
        refine ⟨301163191239437079322108121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 200775460826291386214738747 301163191239437079322108121)
        ·
          refine ⟨225872393429577809491581091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 301163191239437079322108121 225872393429577809491581091)
          ·
            refine ⟨338808590144366714237371637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 225872393429577809491581091 338808590144366714237371637)
            ·
              refine ⟨31763305326034379459753591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 338808590144366714237371637 31763305326034379459753591)
              ·
                refine ⟨47644957989051569189630387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31763305326034379459753591 47644957989051569189630387)
                ·
                  refine ⟨71467436983577353784445581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 47644957989051569189630387 71467436983577353784445581)
                  ·
                    refine ⟨26800288868841507669167093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 71467436983577353784445581 26800288868841507669167093)
                    ·
                      refine ⟨2512527081453891343984415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26800288868841507669167093 2512527081453891343984415)
                      ·
                        rfl

theorem cell23_4893129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 5, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 5, 1, 1, 3, 5].length) (baseStart_4893129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4893129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4893129 prefixEnd_4893129 := by exact prefixLift 4893129
  have htrace : WordTrace (prefixWord ++ tailWord_4893129) baseStart_4893129 baseEnd_4893129 := by
    simpa [prefixWord, tailWord_4893129, baseEnd_4893129] using wordTrace_append hprefix tailTrace_4893129
  have hstable : (prefixWord ++ tailWord_4893129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4893129).length < 2 ^ (prefixWord ++ tailWord_4893129).sum := by decide
  have hdescent : baseEnd_4893129 < baseStart_4893129 := by decide
  rcases family_descends (prefixWord ++ tailWord_4893129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4893146 : List Nat := [3, 1, 1, 2, 3, 1, 2, 1, 2, 4, 3]
def baseStart_4893146 : Nat := 118140960795 + 4893146 * 2 ^ 59
def prefixEnd_4893146 : Nat := 4983230072969 + 3 ^ 40 * 4893146 * 2
def baseEnd_4893146 : Nat := 2512535810625017777471837

theorem tailTrace_4893146 : CollatzResearch.WordTrace tailWord_4893146 prefixEnd_4893146 2512535810625017777471837 := by
  unfold tailWord_4893146
  simp only [CollatzResearch.WordTrace]
  refine ⟨44616924082743799912450823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 118978464220650133099868861 44616924082743799912450823)
  ·
    refine ⟨66925386124115699868676235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44616924082743799912450823 66925386124115699868676235)
    ·
      refine ⟨100388079186173549803014353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66925386124115699868676235 100388079186173549803014353)
      ·
        refine ⟨75291059389630162352260765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 100388079186173549803014353 75291059389630162352260765)
        ·
          refine ⟨28234147271111310882097787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 75291059389630162352260765 28234147271111310882097787)
          ·
            refine ⟨42351220906666966323146681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28234147271111310882097787 42351220906666966323146681)
            ·
              refine ⟨31763415680000224742360011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42351220906666966323146681 31763415680000224742360011)
              ·
                refine ⟨47645123520000337113540017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31763415680000224742360011 47645123520000337113540017)
                ·
                  refine ⟨35733842640000252835155013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 47645123520000337113540017 35733842640000252835155013)
                  ·
                    refine ⟨6700095495000047406591565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 35733842640000252835155013 6700095495000047406591565)
                    ·
                      refine ⟨2512535810625017777471837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6700095495000047406591565 2512535810625017777471837)
                      ·
                        rfl

theorem cell23_4893146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 2, 1, 2, 4, 3].length) (baseStart_4893146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4893146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4893146 prefixEnd_4893146 := by exact prefixLift 4893146
  have htrace : WordTrace (prefixWord ++ tailWord_4893146) baseStart_4893146 baseEnd_4893146 := by
    simpa [prefixWord, tailWord_4893146, baseEnd_4893146] using wordTrace_append hprefix tailTrace_4893146
  have hstable : (prefixWord ++ tailWord_4893146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4893146).length < 2 ^ (prefixWord ++ tailWord_4893146).sum := by decide
  have hdescent : baseEnd_4893146 < baseStart_4893146 := by decide
  rcases family_descends (prefixWord ++ tailWord_4893146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4893154 : List Nat := [3, 3, 3, 2, 1, 1, 1, 3, 2, 1, 3]
def baseStart_4893154 : Nat := 118140960795 + 4893154 * 2 ^ 59
def prefixEnd_4893154 : Nat := 4983230072969 + 3 ^ 40 * 4893154 * 2
def baseEnd_4893154 : Nat := 2512539918470253746171801

theorem tailTrace_4893154 : CollatzResearch.WordTrace tailWord_4893154 prefixEnd_4893154 2512539918470253746171801 := by
  unfold tailWord_4893154
  simp only [CollatzResearch.WordTrace]
  refine ⟨44616997028736554254023629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 118978658743297478010729677 44616997028736554254023629)
  ·
    refine ⟨16731373885776207845258861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44616997028736554254023629 16731373885776207845258861)
    ·
      refine ⟨6274265207166077941972073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16731373885776207845258861 6274265207166077941972073)
      ·
        refine ⟨4705698905374558456479055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6274265207166077941972073 4705698905374558456479055)
        ·
          refine ⟨7058548358061837684718583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4705698905374558456479055 7058548358061837684718583)
          ·
            refine ⟨10587822537092756527077875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7058548358061837684718583 10587822537092756527077875)
            ·
              refine ⟨15881733805639134790616813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10587822537092756527077875 15881733805639134790616813)
              ·
                refine ⟨5955650177114675546481305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15881733805639134790616813 5955650177114675546481305)
                ·
                  refine ⟨4466737632836006659860979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5955650177114675546481305 4466737632836006659860979)
                  ·
                    refine ⟨6700106449254009989791469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4466737632836006659860979 6700106449254009989791469)
                    ·
                      refine ⟨2512539918470253746171801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6700106449254009989791469 2512539918470253746171801)
                      ·
                        rfl

theorem cell23_4893154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 1, 1, 3, 2, 1, 3].length) (baseStart_4893154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4893154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4893154 prefixEnd_4893154 := by exact prefixLift 4893154
  have htrace : WordTrace (prefixWord ++ tailWord_4893154) baseStart_4893154 baseEnd_4893154 := by
    simpa [prefixWord, tailWord_4893154, baseEnd_4893154] using wordTrace_append hprefix tailTrace_4893154
  have hstable : (prefixWord ++ tailWord_4893154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4893154).length < 2 ^ (prefixWord ++ tailWord_4893154).sum := by decide
  have hdescent : baseEnd_4893154 < baseStart_4893154 := by decide
  rcases family_descends (prefixWord ++ tailWord_4893154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4893233 : List Nat := [1, 2, 2, 3, 1, 1, 5, 1, 2, 1, 4]
def baseStart_4893233 : Nat := 118140960795 + 4893233 * 2 ^ 59
def prefixEnd_4893233 : Nat := 4983230072969 + 3 ^ 40 * 4893233 * 2
def baseEnd_4893233 : Nat := 2512580483441958937083937

theorem tailTrace_4893233 : CollatzResearch.WordTrace tailWord_4893233 prefixEnd_4893233 2512580483441958937083937 := by
  unfold tailWord_4893233
  simp only [CollatzResearch.WordTrace]
  refine ⟨178470869481660013508220353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118980579654440009005480235 178470869481660013508220353)
  ·
    refine ⟨133853152111245010131165265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 178470869481660013508220353 133853152111245010131165265)
    ·
      refine ⟨100389864083433757598373949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 133853152111245010131165265 100389864083433757598373949)
      ·
        refine ⟨37646199031287659099390231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 100389864083433757598373949 37646199031287659099390231)
        ·
          refine ⟨56469298546931488649085347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37646199031287659099390231 56469298546931488649085347)
          ·
            refine ⟨84703947820397232973628021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56469298546931488649085347 84703947820397232973628021)
            ·
              refine ⟨7940995108162240591277627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 84703947820397232973628021 7940995108162240591277627)
              ·
                refine ⟨11911492662243360886916441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7940995108162240591277627 11911492662243360886916441)
                ·
                  refine ⟨8933619496682520665187331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11911492662243360886916441 8933619496682520665187331)
                  ·
                    refine ⟨13400429245023780997780997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8933619496682520665187331 13400429245023780997780997)
                    ·
                      refine ⟨2512580483441958937083937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13400429245023780997780997 2512580483441958937083937)
                      ·
                        rfl

theorem cell23_4893233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 5, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 5, 1, 2, 1, 4].length) (baseStart_4893233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4893233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4893233 prefixEnd_4893233 := by exact prefixLift 4893233
  have htrace : WordTrace (prefixWord ++ tailWord_4893233) baseStart_4893233 baseEnd_4893233 := by
    simpa [prefixWord, tailWord_4893233, baseEnd_4893233] using wordTrace_append hprefix tailTrace_4893233
  have hstable : (prefixWord ++ tailWord_4893233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4893233).length < 2 ^ (prefixWord ++ tailWord_4893233).sum := by decide
  have hdescent : baseEnd_4893233 < baseStart_4893233 := by decide
  rcases family_descends (prefixWord ++ tailWord_4893233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4893260 : List Nat := [2, 2, 1, 3, 1, 2, 1, 6, 1, 4]
def baseStart_4893260 : Nat := 118140960795 + 4893260 * 2 ^ 59
def prefixEnd_4893260 : Nat := 4983230072969 + 3 ^ 40 * 4893260 * 2
def baseEnd_4893260 : Nat := 837531449139876777148771

theorem tailTrace_4893260 : CollatzResearch.WordTrace tailWord_4893260 prefixEnd_4893260 837531449139876777148771 := by
  unfold tailWord_4893260
  simp only [CollatzResearch.WordTrace]
  refine ⟨89235927126281098559726617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118981236168374798079635489 89235927126281098559726617)
  ·
    refine ⟨66926945344710823919794963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89235927126281098559726617 66926945344710823919794963)
    ·
      refine ⟨100390418017066235879692445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66926945344710823919794963 100390418017066235879692445)
      ·
        refine ⟨37646406756399838454884667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 100390418017066235879692445 37646406756399838454884667)
        ·
          refine ⟨56469610134599757682327001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37646406756399838454884667 56469610134599757682327001)
          ·
            refine ⟨42352207600949818261745251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56469610134599757682327001 42352207600949818261745251)
            ·
              refine ⟨63528311401424727392617877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42352207600949818261745251 63528311401424727392617877)
              ·
                refine ⟨2977889596941784096528963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 63528311401424727392617877 2977889596941784096528963)
                ·
                  refine ⟨4466834395412676144793445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2977889596941784096528963 4466834395412676144793445)
                  ·
                    refine ⟨837531449139876777148771, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4466834395412676144793445 837531449139876777148771)
                    ·
                      rfl

theorem cell23_4893260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 1, 6, 1, 4].length) (baseStart_4893260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4893260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4893260 prefixEnd_4893260 := by exact prefixLift 4893260
  have htrace : WordTrace (prefixWord ++ tailWord_4893260) baseStart_4893260 baseEnd_4893260 := by
    simpa [prefixWord, tailWord_4893260, baseEnd_4893260] using wordTrace_append hprefix tailTrace_4893260
  have hstable : (prefixWord ++ tailWord_4893260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4893260).length < 2 ^ (prefixWord ++ tailWord_4893260).sum := by decide
  have hdescent : baseEnd_4893260 < baseStart_4893260 := by decide
  rcases family_descends (prefixWord ++ tailWord_4893260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4893294 : List Nat := [4, 1, 2, 2, 2, 3, 1, 3, 1, 4]
def baseStart_4893294 : Nat := 118140960795 + 4893294 * 2 ^ 59
def prefixEnd_4893294 : Nat := 4983230072969 + 3 ^ 40 * 4893294 * 2
def baseEnd_4893294 : Nat := 837537268587294399473719

theorem tailTrace_4893294 : CollatzResearch.WordTrace tailWord_4893294 prefixEnd_4893294 837537268587294399473719 := by
  unfold tailWord_4893294
  simp only [CollatzResearch.WordTrace]
  refine ⟨22309136791804877615773867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 118982062889626013950793957 22309136791804877615773867)
  ·
    refine ⟨33463705187707316423660801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22309136791804877615773867 33463705187707316423660801)
    ·
      refine ⟨25097778890780487317745601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33463705187707316423660801 25097778890780487317745601)
      ·
        refine ⟨18823334168085365488309201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25097778890780487317745601 18823334168085365488309201)
        ·
          refine ⟨14117500626064024116231901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18823334168085365488309201 14117500626064024116231901)
          ·
            refine ⟨5294062734774009043586963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14117500626064024116231901 5294062734774009043586963)
            ·
              refine ⟨7941094102161013565380445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5294062734774009043586963 7941094102161013565380445)
              ·
                refine ⟨2977910288310380087017667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7941094102161013565380445 2977910288310380087017667)
                ·
                  refine ⟨4466865432465570130526501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2977910288310380087017667 4466865432465570130526501)
                  ·
                    refine ⟨837537268587294399473719, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4466865432465570130526501 837537268587294399473719)
                    ·
                      rfl

theorem cell23_4893294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 3, 1, 3, 1, 4].length) (baseStart_4893294 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4893294 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4893294 prefixEnd_4893294 := by exact prefixLift 4893294
  have htrace : WordTrace (prefixWord ++ tailWord_4893294) baseStart_4893294 baseEnd_4893294 := by
    simpa [prefixWord, tailWord_4893294, baseEnd_4893294] using wordTrace_append hprefix tailTrace_4893294
  have hstable : (prefixWord ++ tailWord_4893294).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4893294).length < 2 ^ (prefixWord ++ tailWord_4893294).sum := by decide
  have hdescent : baseEnd_4893294 < baseStart_4893294 := by decide
  rcases family_descends (prefixWord ++ tailWord_4893294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4893303 : List Nat := [1, 1, 3, 1, 1, 3, 4, 3, 1, 5]
def baseStart_4893303 : Nat := 118140960795 + 4893303 * 2 ^ 59
def prefixEnd_4893303 : Nat := 4983230072969 + 3 ^ 40 * 4893303 * 2
def baseEnd_4893303 : Nat := 837538809029257887736205

theorem tailTrace_4893303 : CollatzResearch.WordTrace tailWord_4893303 prefixEnd_4893303 837538809029257887736205 := by
  unfold tailWord_4893303
  simp only [CollatzResearch.WordTrace]
  refine ⟨178473422591406415463268563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118982281727604276975512375 178473422591406415463268563)
  ·
    refine ⟨267710133887109623194902845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 178473422591406415463268563 267710133887109623194902845)
    ·
      refine ⟨100391300207666108698088567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 267710133887109623194902845 100391300207666108698088567)
      ·
        refine ⟨150586950311499163047132851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100391300207666108698088567 150586950311499163047132851)
        ·
          refine ⟨225880425467248744570699277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 150586950311499163047132851 225880425467248744570699277)
          ·
            refine ⟨84705159550218279214012229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 225880425467248744570699277 84705159550218279214012229)
            ·
              refine ⟨15882217415665927352627293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 84705159550218279214012229 15882217415665927352627293)
              ·
                refine ⟨5955831530874722757235235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15882217415665927352627293 5955831530874722757235235)
                ·
                  refine ⟨8933747296312084135852853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5955831530874722757235235 8933747296312084135852853)
                  ·
                    refine ⟨837538809029257887736205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8933747296312084135852853 837538809029257887736205)
                    ·
                      rfl

theorem cell23_4893303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 4, 3, 1, 5].length) (baseStart_4893303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4893303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4893303 prefixEnd_4893303 := by exact prefixLift 4893303
  have htrace : WordTrace (prefixWord ++ tailWord_4893303) baseStart_4893303 baseEnd_4893303 := by
    simpa [prefixWord, tailWord_4893303, baseEnd_4893303] using wordTrace_append hprefix tailTrace_4893303
  have hstable : (prefixWord ++ tailWord_4893303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4893303).length < 2 ^ (prefixWord ++ tailWord_4893303).sum := by decide
  have hdescent : baseEnd_4893303 < baseStart_4893303 := by decide
  rcases family_descends (prefixWord ++ tailWord_4893303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4893306 : List Nat := [3, 1, 1, 1, 1, 1, 1, 2, 1, 7, 4]
def baseStart_4893306 : Nat := 118140960795 + 4893306 * 2 ^ 59
def prefixEnd_4893306 : Nat := 4983230072969 + 3 ^ 40 * 4893306 * 2
def baseEnd_4893306 : Nat := 2512617967529737151471101

theorem tailTrace_4893306 : CollatzResearch.WordTrace tailWord_4893306 prefixEnd_4893306 2512617967529737151471101 := by
  unfold tailWord_4893306
  simp only [CollatzResearch.WordTrace]
  refine ⟨44618383002598886743906943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 118982354673597031317085181 44618383002598886743906943)
  ·
    refine ⟨66927574503898330115860415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44618383002598886743906943 66927574503898330115860415)
    ·
      refine ⟨100391361755847495173790623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66927574503898330115860415 100391361755847495173790623)
      ·
        refine ⟨150587042633771242760685935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100391361755847495173790623 150587042633771242760685935)
        ·
          refine ⟨225880563950656864141028903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 150587042633771242760685935 225880563950656864141028903)
          ·
            refine ⟨338820845925985296211543355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 225880563950656864141028903 338820845925985296211543355)
            ·
              refine ⟨508231268888977944317315033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 338820845925985296211543355 508231268888977944317315033)
              ·
                refine ⟨381173451666733458237986275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 508231268888977944317315033 381173451666733458237986275)
                ·
                  refine ⟨571760177500100187356979413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 381173451666733458237986275 571760177500100187356979413)
                  ·
                    refine ⟨13400629160158598141179205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 571760177500100187356979413 13400629160158598141179205)
                    ·
                      refine ⟨2512617967529737151471101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13400629160158598141179205 2512617967529737151471101)
                      ·
                        rfl

theorem cell23_4893306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 2, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 2, 1, 7, 4].length) (baseStart_4893306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4893306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4893306 prefixEnd_4893306 := by exact prefixLift 4893306
  have htrace : WordTrace (prefixWord ++ tailWord_4893306) baseStart_4893306 baseEnd_4893306 := by
    simpa [prefixWord, tailWord_4893306, baseEnd_4893306] using wordTrace_append hprefix tailTrace_4893306
  have hstable : (prefixWord ++ tailWord_4893306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4893306).length < 2 ^ (prefixWord ++ tailWord_4893306).sum := by decide
  have hdescent : baseEnd_4893306 < baseStart_4893306 := by decide
  rcases family_descends (prefixWord ++ tailWord_4893306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4893317 : List Nat := [1, 3, 1, 1, 4, 4, 1, 1, 3, 1, 3]
def baseStart_4893317 : Nat := 118140960795 + 4893317 * 2 ^ 59
def prefixEnd_4893317 : Nat := 4983230072969 + 3 ^ 40 * 4893317 * 2
def baseEnd_4893317 : Nat := 2512623615816936608433551

theorem tailTrace_4893317 : CollatzResearch.WordTrace tailWord_4893317 prefixEnd_4893317 2512623615816936608433551 := by
  unfold tailWord_4893317
  simp only [CollatzResearch.WordTrace]
  refine ⟨178473933213355695854278205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118982622142237130569518803 178473933213355695854278205)
  ·
    refine ⟨66927724955008385945354327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 178473933213355695854278205 66927724955008385945354327)
    ·
      refine ⟨100391587432512578918031491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66927724955008385945354327 100391587432512578918031491)
      ·
        refine ⟨150587381148768868377047237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100391587432512578918031491 150587381148768868377047237)
        ·
          refine ⟨28235133965394162820696357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 150587381148768868377047237 28235133965394162820696357)
          ·
            refine ⟨5294087618511405528880567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 28235133965394162820696357 5294087618511405528880567)
            ·
              refine ⟨7941131427767108293320851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5294087618511405528880567 7941131427767108293320851)
              ·
                refine ⟨11911697141650662439981277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7941131427767108293320851 11911697141650662439981277)
                ·
                  refine ⟨4466886428118998414992979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11911697141650662439981277 4466886428118998414992979)
                  ·
                    refine ⟨6700329642178497622489469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4466886428118998414992979 6700329642178497622489469)
                    ·
                      refine ⟨2512623615816936608433551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6700329642178497622489469 2512623615816936608433551)
                      ·
                        rfl

theorem cell23_4893317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 4, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 4, 1, 1, 3, 1, 3].length) (baseStart_4893317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4893317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4893317 prefixEnd_4893317 := by exact prefixLift 4893317
  have htrace : WordTrace (prefixWord ++ tailWord_4893317) baseStart_4893317 baseEnd_4893317 := by
    simpa [prefixWord, tailWord_4893317, baseEnd_4893317] using wordTrace_append hprefix tailTrace_4893317
  have hstable : (prefixWord ++ tailWord_4893317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4893317).length < 2 ^ (prefixWord ++ tailWord_4893317).sum := by decide
  have hdescent : baseEnd_4893317 < baseStart_4893317 := by decide
  rcases family_descends (prefixWord ++ tailWord_4893317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4893323 : List Nat := [1, 1, 1, 1, 4, 1, 2, 2, 2, 6, 2]
def baseStart_4893323 : Nat := 118140960795 + 4893323 * 2 ^ 59
def prefixEnd_4893323 : Nat := 4983230072969 + 3 ^ 40 * 4893323 * 2
def baseEnd_4893323 : Nat := 2512626696700863584958523

theorem tailTrace_4893323 : CollatzResearch.WordTrace tailWord_4893323 prefixEnd_4893323 2512626696700863584958523 := by
  unfold tailWord_4893323
  simp only [CollatzResearch.WordTrace]
  refine ⟨178474152051333958878996623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118982768034222639252664415 178474152051333958878996623)
  ·
    refine ⟨267711228077000938318494935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 178474152051333958878996623 267711228077000938318494935)
    ·
      refine ⟨401566842115501407477742403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 267711228077000938318494935 401566842115501407477742403)
      ·
        refine ⟨602350263173252111216613605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 401566842115501407477742403 602350263173252111216613605)
        ·
          refine ⟨112940674344984770853115051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 602350263173252111216613605 112940674344984770853115051)
          ·
            refine ⟨169411011517477156279672577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 112940674344984770853115051 169411011517477156279672577)
            ·
              refine ⟨127058258638107867209754433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 169411011517477156279672577 127058258638107867209754433)
              ·
                refine ⟨95293693978580900407315825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 127058258638107867209754433 95293693978580900407315825)
                ·
                  refine ⟨71470270483935675305486869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 95293693978580900407315825 71470270483935675305486869)
                  ·
                    refine ⟨3350168928934484779944697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 71470270483935675305486869 3350168928934484779944697)
                    ·
                      refine ⟨2512626696700863584958523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3350168928934484779944697 2512626696700863584958523)
                      ·
                        rfl

theorem cell23_4893323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 2, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 2, 2, 6, 2].length) (baseStart_4893323 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4893323 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4893323 prefixEnd_4893323 := by exact prefixLift 4893323
  have htrace : WordTrace (prefixWord ++ tailWord_4893323) baseStart_4893323 baseEnd_4893323 := by
    simpa [prefixWord, tailWord_4893323, baseEnd_4893323] using wordTrace_append hprefix tailTrace_4893323
  have hstable : (prefixWord ++ tailWord_4893323).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4893323).length < 2 ^ (prefixWord ++ tailWord_4893323).sum := by decide
  have hdescent : baseEnd_4893323 < baseStart_4893323 := by decide
  rcases family_descends (prefixWord ++ tailWord_4893323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4893340 : List Nat := [2, 2, 3, 2, 2, 2, 1, 1, 3, 1, 4]
def baseStart_4893340 : Nat := 118140960795 + 4893340 * 2 ^ 59
def prefixEnd_4893340 : Nat := 4983230072969 + 3 ^ 40 * 4893340 * 2
def baseEnd_4893340 : Nat := 2512635425871990018445945

theorem tailTrace_4893340 : CollatzResearch.WordTrace tailWord_4893340 prefixEnd_4893340 2512635425871990018445945 := by
  unfold tailWord_4893340
  simp only [CollatzResearch.WordTrace]
  refine ⟨89237386046136185391182737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118983181394848247188243649 89237386046136185391182737)
  ·
    refine ⟨66928039534602139043387053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89237386046136185391182737 66928039534602139043387053)
    ·
      refine ⟨25098014825475802141270145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 66928039534602139043387053 25098014825475802141270145)
      ·
        refine ⟨18823511119106851605952609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25098014825475802141270145 18823511119106851605952609)
        ·
          refine ⟨14117633339330138704464457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18823511119106851605952609 14117633339330138704464457)
          ·
            refine ⟨10588225004497604028348343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14117633339330138704464457 10588225004497604028348343)
            ·
              refine ⟨15882337506746406042522515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10588225004497604028348343 15882337506746406042522515)
              ·
                refine ⟨23823506260119609063783773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15882337506746406042522515 23823506260119609063783773)
                ·
                  refine ⟨8933814847544853398918915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23823506260119609063783773 8933814847544853398918915)
                  ·
                    refine ⟨13400722271317280098378373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8933814847544853398918915 13400722271317280098378373)
                    ·
                      refine ⟨2512635425871990018445945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13400722271317280098378373 2512635425871990018445945)
                      ·
                        rfl

theorem cell23_4893340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 2, 1, 1, 3, 1, 4].length) (baseStart_4893340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4893340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4893340 prefixEnd_4893340 := by exact prefixLift 4893340
  have htrace : WordTrace (prefixWord ++ tailWord_4893340) baseStart_4893340 baseEnd_4893340 := by
    simpa [prefixWord, tailWord_4893340, baseEnd_4893340] using wordTrace_append hprefix tailTrace_4893340
  have hstable : (prefixWord ++ tailWord_4893340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4893340).length < 2 ^ (prefixWord ++ tailWord_4893340).sum := by decide
  have hdescent : baseEnd_4893340 < baseStart_4893340 := by decide
  rcases family_descends (prefixWord ++ tailWord_4893340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4893367 : List Nat := [1, 1, 3, 1, 6, 1, 2, 2, 2, 4]
def baseStart_4893367 : Nat := 118140960795 + 4893367 * 2 ^ 59
def prefixEnd_4893367 : Nat := 4983230072969 + 3 ^ 40 * 4893367 * 2
def baseEnd_4893367 : Nat := 837549763283220470936107

theorem tailTrace_4893367 : CollatzResearch.WordTrace tailWord_4893367 prefixEnd_4893367 837549763283220470936107 := by
  unfold tailWord_4893367
  simp only [CollatzResearch.WordTrace]
  refine ⟨178475756863174554393598355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118983837908783036262398903 178475756863174554393598355)
  ·
    refine ⟨267713635294761831590397533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 178475756863174554393598355 267713635294761831590397533)
    ·
      refine ⟨100392613235535686846399075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 267713635294761831590397533 100392613235535686846399075)
      ·
        refine ⟨150588919853303530269598613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100392613235535686846399075 150588919853303530269598613)
        ·
          refine ⟨7058855618123602981387435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 150588919853303530269598613 7058855618123602981387435)
          ·
            refine ⟨10588283427185404472081153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7058855618123602981387435 10588283427185404472081153)
            ·
              refine ⟨7941212570389053354060865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10588283427185404472081153 7941212570389053354060865)
              ·
                refine ⟨5955909427791790015545649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7941212570389053354060865 5955909427791790015545649)
                ·
                  refine ⟨4466932070843842511659237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5955909427791790015545649 4466932070843842511659237)
                  ·
                    refine ⟨837549763283220470936107, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4466932070843842511659237 837549763283220470936107)
                    ·
                      rfl

theorem cell23_4893367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 1, 2, 2, 2, 4].length) (baseStart_4893367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4893367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4893367 prefixEnd_4893367 := by exact prefixLift 4893367
  have htrace : WordTrace (prefixWord ++ tailWord_4893367) baseStart_4893367 baseEnd_4893367 := by
    simpa [prefixWord, tailWord_4893367, baseEnd_4893367] using wordTrace_append hprefix tailTrace_4893367
  have hstable : (prefixWord ++ tailWord_4893367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4893367).length < 2 ^ (prefixWord ++ tailWord_4893367).sum := by decide
  have hdescent : baseEnd_4893367 < baseStart_4893367 := by decide
  rcases family_descends (prefixWord ++ tailWord_4893367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4893380 : List Nat := [2, 3, 3, 1, 1, 4, 1, 8]
def baseStart_4893380 : Nat := 118140960795 + 4893380 * 2 ^ 59
def prefixEnd_4893380 : Nat := 4983230072969 + 3 ^ 40 * 4893380 * 2
def baseEnd_4893380 : Nat := 93061332040672957849843

theorem tailTrace_4893380 : CollatzResearch.WordTrace tailWord_4893380 prefixEnd_4893380 93061332040672957849843 := by
  unfold tailWord_4893380
  simp only [CollatzResearch.WordTrace]
  refine ⟨89238115506063728806910797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118984154008084971742547729 89238115506063728806910797)
  ·
    refine ⟨33464293314773898302591549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 89238115506063728806910797 33464293314773898302591549)
    ·
      refine ⟨12549109993040211863471831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33464293314773898302591549 12549109993040211863471831)
      ·
        refine ⟨18823664989560317795207747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12549109993040211863471831 18823664989560317795207747)
        ·
          refine ⟨28235497484340476692811621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18823664989560317795207747 28235497484340476692811621)
          ·
            refine ⟨5294155778313839379902179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 28235497484340476692811621 5294155778313839379902179)
            ·
              refine ⟨7941233667470759069853269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5294155778313839379902179 7941233667470759069853269)
              ·
                refine ⟨93061332040672957849843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7941233667470759069853269 93061332040672957849843)
                ·
                  rfl

theorem cell23_4893380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 4, 1, 8].length) (baseStart_4893380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4893380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4893380 prefixEnd_4893380 := by exact prefixLift 4893380
  have htrace : WordTrace (prefixWord ++ tailWord_4893380) baseStart_4893380 baseEnd_4893380 := by
    simpa [prefixWord, tailWord_4893380, baseEnd_4893380] using wordTrace_append hprefix tailTrace_4893380
  have hstable : (prefixWord ++ tailWord_4893380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4893380).length < 2 ^ (prefixWord ++ tailWord_4893380).sum := by decide
  have hdescent : baseEnd_4893380 < baseStart_4893380 := by decide
  rcases family_descends (prefixWord ++ tailWord_4893380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4893390 : List Nat := [4, 1, 1, 1, 3, 2, 1, 3, 1, 3, 3]
def baseStart_4893390 : Nat := 118140960795 + 4893390 * 2 ^ 59
def prefixEnd_4893390 : Nat := 4983230072969 + 3 ^ 40 * 4893390 * 2
def baseEnd_4893390 : Nat := 2512661099904714822820715

theorem tailTrace_4893390 : CollatzResearch.WordTrace tailWord_4893390 prefixEnd_4893390 2512661099904714822820715 := by
  unfold tailWord_4893390
  simp only [CollatzResearch.WordTrace]
  refine ⟨22309574467761403665210703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 118984397161394152881123749 22309574467761403665210703)
  ·
    refine ⟨33464361701642105497816055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22309574467761403665210703 33464361701642105497816055)
    ·
      refine ⟨50196542552463158246724083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33464361701642105497816055 50196542552463158246724083)
      ·
        refine ⟨75294813828694737370086125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50196542552463158246724083 75294813828694737370086125)
        ·
          refine ⟨28235555185760526513782297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 75294813828694737370086125 28235555185760526513782297)
          ·
            refine ⟨21176666389320394885336723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28235555185760526513782297 21176666389320394885336723)
            ·
              refine ⟨31764999583980592328005085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21176666389320394885336723 31764999583980592328005085)
              ·
                refine ⟨11911874843992722123001907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31764999583980592328005085 11911874843992722123001907)
                ·
                  refine ⟨17867812265989083184502861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11911874843992722123001907 17867812265989083184502861)
                  ·
                    refine ⟨6700429599745906194188573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17867812265989083184502861 6700429599745906194188573)
                    ·
                      refine ⟨2512661099904714822820715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6700429599745906194188573 2512661099904714822820715)
                      ·
                        rfl

theorem cell23_4893390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 1, 3, 1, 3, 3].length) (baseStart_4893390 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4893390 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4893390 prefixEnd_4893390 := by exact prefixLift 4893390
  have htrace : WordTrace (prefixWord ++ tailWord_4893390) baseStart_4893390 baseEnd_4893390 := by
    simpa [prefixWord, tailWord_4893390, baseEnd_4893390] using wordTrace_append hprefix tailTrace_4893390
  have hstable : (prefixWord ++ tailWord_4893390).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4893390).length < 2 ^ (prefixWord ++ tailWord_4893390).sum := by decide
  have hdescent : baseEnd_4893390 < baseStart_4893390 := by decide
  rcases family_descends (prefixWord ++ tailWord_4893390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4893397 : List Nat := [1, 3, 2, 5, 1, 1, 3, 7]
def baseStart_4893397 : Nat := 118140960795 + 4893397 * 2 ^ 59
def prefixEnd_4893397 : Nat := 4983230072969 + 3 ^ 40 * 4893397 * 2
def baseEnd_4893397 : Nat := 93061655343307270201229

theorem tailTrace_4893397 : CollatzResearch.WordTrace tailWord_4893397 prefixEnd_4893397 93061655343307270201229 := by
  unfold tailWord_4893397
  simp only [CollatzResearch.WordTrace]
  refine ⟨178476851053065869517190445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118984567368710579678126963 178476851053065869517190445)
  ·
    refine ⟨66928819144899701068946417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 178476851053065869517190445 66928819144899701068946417)
    ·
      refine ⟨50196614358674775801709813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66928819144899701068946417 50196614358674775801709813)
      ·
        refine ⟨4705932596125760231410295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 50196614358674775801709813 4705932596125760231410295)
        ·
          refine ⟨7058898894188640347115443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4705932596125760231410295 7058898894188640347115443)
          ·
            refine ⟨10588348341282960520673165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7058898894188640347115443 10588348341282960520673165)
            ·
              refine ⟨3970630627981110195252437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10588348341282960520673165 3970630627981110195252437)
              ·
                refine ⟨93061655343307270201229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3970630627981110195252437 93061655343307270201229)
                ·
                  rfl

theorem cell23_4893397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 1, 3, 7].length) (baseStart_4893397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4893397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4893397 prefixEnd_4893397 := by exact prefixLift 4893397
  have htrace : WordTrace (prefixWord ++ tailWord_4893397) baseStart_4893397 baseEnd_4893397 := by
    simpa [prefixWord, tailWord_4893397, baseEnd_4893397] using wordTrace_append hprefix tailTrace_4893397
  have hstable : (prefixWord ++ tailWord_4893397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4893397).length < 2 ^ (prefixWord ++ tailWord_4893397).sum := by decide
  have hdescent : baseEnd_4893397 < baseStart_4893397 := by decide
  rcases family_descends (prefixWord ++ tailWord_4893397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4893423 : List Nat := [1, 1, 2, 1, 5, 2, 1, 2, 2, 6]
def baseStart_4893423 : Nat := 118140960795 + 4893423 * 2 ^ 59
def prefixEnd_4893423 : Nat := 4983230072969 + 3 ^ 40 * 4893423 * 2
def baseEnd_4893423 : Nat := 837559348255437731236021

theorem tailTrace_4893423 : CollatzResearch.WordTrace tailWord_4893423 prefixEnd_4893423 837559348255437731236021 := by
  unfold tailWord_4893423
  simp only [CollatzResearch.WordTrace]
  refine ⟨178477799350971675957636923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118985199567314450638424615 178477799350971675957636923)
  ·
    refine ⟨267716699026457513936455385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 178477799350971675957636923 267716699026457513936455385)
    ·
      refine ⟨200787524269843135452341539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 267716699026457513936455385 200787524269843135452341539)
      ·
        refine ⟨301181286404764703178512309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 200787524269843135452341539 301181286404764703178512309)
        ·
          refine ⟨28235745600446690922985529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 301181286404764703178512309 28235745600446690922985529)
          ·
            refine ⟨21176809200335018192239147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28235745600446690922985529 21176809200335018192239147)
            ·
              refine ⟨31765213800502527288358721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21176809200335018192239147 31765213800502527288358721)
              ·
                refine ⟨23823910350376895466269041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31765213800502527288358721 23823910350376895466269041)
                ·
                  refine ⟨17867932762782671599701781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23823910350376895466269041 17867932762782671599701781)
                  ·
                    refine ⟨837559348255437731236021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17867932762782671599701781 837559348255437731236021)
                    ·
                      rfl

theorem cell23_4893423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 1, 2, 2, 6].length) (baseStart_4893423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4893423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4893423 prefixEnd_4893423 := by exact prefixLift 4893423
  have htrace : WordTrace (prefixWord ++ tailWord_4893423) baseStart_4893423 baseEnd_4893423 := by
    simpa [prefixWord, tailWord_4893423, baseEnd_4893423] using wordTrace_append hprefix tailTrace_4893423
  have hstable : (prefixWord ++ tailWord_4893423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4893423).length < 2 ^ (prefixWord ++ tailWord_4893423).sum := by decide
  have hdescent : baseEnd_4893423 < baseStart_4893423 := by decide
  rcases family_descends (prefixWord ++ tailWord_4893423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4893433 : List Nat := [1, 2, 1, 3, 1, 1, 1, 3, 1, 6, 3]
def baseStart_4893433 : Nat := 118140960795 + 4893433 * 2 ^ 59
def prefixEnd_4893433 : Nat := 4983230072969 + 3 ^ 40 * 4893433 * 2
def baseEnd_4893433 : Nat := 2512683179572858154583017

theorem tailTrace_4893433 : CollatzResearch.WordTrace tailWord_4893433 prefixEnd_4893433 2512683179572858154583017 := by
  unfold tailWord_4893433
  simp only [CollatzResearch.WordTrace]
  refine ⟨178478164080935447665500953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118985442720623631777000635 178478164080935447665500953)
  ·
    refine ⟨133858623060701585749125715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 178478164080935447665500953 133858623060701585749125715)
    ·
      refine ⟨200787934591052378623688573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 133858623060701585749125715 200787934591052378623688573)
      ·
        refine ⟨75295475471644641983883215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 200787934591052378623688573 75295475471644641983883215)
        ·
          refine ⟨112943213207466962975824823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75295475471644641983883215 112943213207466962975824823)
          ·
            refine ⟨169414819811200444463737235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 112943213207466962975824823 169414819811200444463737235)
            ·
              refine ⟨254122229716800666695605853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 169414819811200444463737235 254122229716800666695605853)
              ·
                refine ⟨95295836143800250010852195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 254122229716800666695605853 95295836143800250010852195)
                ·
                  refine ⟨142943754215700375016278293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 95295836143800250010852195 142943754215700375016278293)
                  ·
                    refine ⟨6700488478860955078888045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 142943754215700375016278293 6700488478860955078888045)
                    ·
                      refine ⟨2512683179572858154583017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6700488478860955078888045 2512683179572858154583017)
                      ·
                        rfl

theorem cell23_4893433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 3, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 3, 1, 6, 3].length) (baseStart_4893433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4893433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4893433 prefixEnd_4893433 := by exact prefixLift 4893433
  have htrace : WordTrace (prefixWord ++ tailWord_4893433) baseStart_4893433 baseEnd_4893433 := by
    simpa [prefixWord, tailWord_4893433, baseEnd_4893433] using wordTrace_append hprefix tailTrace_4893433
  have hstable : (prefixWord ++ tailWord_4893433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4893433).length < 2 ^ (prefixWord ++ tailWord_4893433).sum := by decide
  have hdescent : baseEnd_4893433 < baseStart_4893433 := by decide
  rcases family_descends (prefixWord ++ tailWord_4893433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4893483 : List Nat := [1, 1, 1, 1, 2, 1, 2, 5, 4, 5]
def baseStart_4893483 : Nat := 118140960795 + 4893483 * 2 ^ 59
def prefixEnd_4893483 : Nat := 4983230072969 + 3 ^ 40 * 4893483 * 2
def baseEnd_4893483 : Nat := 837569617868527652985929

theorem tailTrace_4893483 : CollatzResearch.WordTrace tailWord_4893483 prefixEnd_4893483 837569617868527652985929 := by
  unfold tailWord_4893483
  simp only [CollatzResearch.WordTrace]
  refine ⟨178479987730754306204821103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118986658487169537469880735 178479987730754306204821103)
  ·
    refine ⟨267719981596131459307231655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 178479987730754306204821103 267719981596131459307231655)
    ·
      refine ⟨401579972394197188960847483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 267719981596131459307231655 401579972394197188960847483)
      ·
        refine ⟨602369958591295783441271225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 401579972394197188960847483 602369958591295783441271225)
        ·
          refine ⟨451777468943471837580953419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 602369958591295783441271225 451777468943471837580953419)
          ·
            refine ⟨677666203415207756371430129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 451777468943471837580953419 677666203415207756371430129)
            ·
              refine ⟨508249652561405817278572597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 677666203415207756371430129 508249652561405817278572597)
              ·
                refine ⟨47648404927631795369866181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 508249652561405817278572597 47648404927631795369866181)
                ·
                  refine ⟨8934075923930961631849909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 47648404927631795369866181 8934075923930961631849909)
                  ·
                    refine ⟨837569617868527652985929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8934075923930961631849909 837569617868527652985929)
                    ·
                      rfl

theorem cell23_4893483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 5, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 5, 4, 5].length) (baseStart_4893483 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4893483 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4893483 prefixEnd_4893483 := by exact prefixLift 4893483
  have htrace : WordTrace (prefixWord ++ tailWord_4893483) baseStart_4893483 baseEnd_4893483 := by
    simpa [prefixWord, tailWord_4893483, baseEnd_4893483] using wordTrace_append hprefix tailTrace_4893483
  have hstable : (prefixWord ++ tailWord_4893483).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4893483).length < 2 ^ (prefixWord ++ tailWord_4893483).sum := by decide
  have hdescent : baseEnd_4893483 < baseStart_4893483 := by decide
  rcases family_descends (prefixWord ++ tailWord_4893483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4893498 : List Nat := [3, 1, 1, 1, 6, 2, 2, 1, 2, 2, 2]
def baseStart_4893498 : Nat := 118140960795 + 4893498 * 2 ^ 59
def prefixEnd_4893498 : Nat := 4983230072969 + 3 ^ 40 * 4893498 * 2
def baseEnd_4893498 : Nat := 2512716555815400400270219

theorem tailTrace_4893498 : CollatzResearch.WordTrace tailWord_4893498 prefixEnd_4893498 2512716555815400400270219 := by
  unfold tailWord_4893498
  simp only [CollatzResearch.WordTrace]
  refine ⟨44620133706424990941654287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 118987023217133309177744765 44620133706424990941654287)
  ·
    refine ⟨66930200559637486412481431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44620133706424990941654287 66930200559637486412481431)
    ·
      refine ⟨100395300839456229618722147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66930200559637486412481431 100395300839456229618722147)
      ·
        refine ⟨150592951259184344428083221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100395300839456229618722147 150592951259184344428083221)
        ·
          refine ⟨7059044590274266145066401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 150592951259184344428083221 7059044590274266145066401)
          ·
            refine ⟨5294283442705699608799801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7059044590274266145066401 5294283442705699608799801)
            ·
              refine ⟨3970712582029274706599851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5294283442705699608799801 3970712582029274706599851)
              ·
                refine ⟨5956068873043912059899777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3970712582029274706599851 5956068873043912059899777)
                ·
                  refine ⟨4467051654782934044924833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5956068873043912059899777 4467051654782934044924833)
                  ·
                    refine ⟨3350288741087200533693625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4467051654782934044924833 3350288741087200533693625)
                    ·
                      refine ⟨2512716555815400400270219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3350288741087200533693625 2512716555815400400270219)
                      ·
                        rfl

theorem cell23_4893498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 2, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 2, 2, 1, 2, 2, 2].length) (baseStart_4893498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4893498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4893498 prefixEnd_4893498 := by exact prefixLift 4893498
  have htrace : WordTrace (prefixWord ++ tailWord_4893498) baseStart_4893498 baseEnd_4893498 := by
    simpa [prefixWord, tailWord_4893498, baseEnd_4893498] using wordTrace_append hprefix tailTrace_4893498
  have hstable : (prefixWord ++ tailWord_4893498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4893498).length < 2 ^ (prefixWord ++ tailWord_4893498).sum := by decide
  have hdescent : baseEnd_4893498 < baseStart_4893498 := by decide
  rcases family_descends (prefixWord ++ tailWord_4893498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4893520 : List Nat := [2, 1, 1, 1, 1, 4, 3, 3, 2, 1, 4]
def baseStart_4893520 : Nat := 118140960795 + 4893520 * 2 ^ 59
def prefixEnd_4893520 : Nat := 4983230072969 + 3 ^ 40 * 4893520 * 2
def baseEnd_4893520 : Nat := 2512727852389799314195117

theorem tailTrace_4893520 : CollatzResearch.WordTrace tailWord_4893520 prefixEnd_4893520 2512727852389799314195117 := by
  unfold tailWord_4893520
  simp only [CollatzResearch.WordTrace]
  refine ⟨89240668615810130761959007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118987558154413507682612009 89240668615810130761959007)
  ·
    refine ⟨133861002923715196142938511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89240668615810130761959007 133861002923715196142938511)
    ·
      refine ⟨200791504385572794214407767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 133861002923715196142938511 200791504385572794214407767)
      ·
        refine ⟨301187256578359191321611651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 200791504385572794214407767 301187256578359191321611651)
        ·
          refine ⟨451780884867538786982417477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 301187256578359191321611651 451780884867538786982417477)
          ·
            refine ⟨84708915912663522559203277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 451780884867538786982417477 84708915912663522559203277)
            ·
              refine ⟨31765843467248820959701229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 84708915912663522559203277 31765843467248820959701229)
              ·
                refine ⟨11912191300218307859887961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31765843467248820959701229 11912191300218307859887961)
                ·
                  refine ⟨8934143475163730894915971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11912191300218307859887961 8934143475163730894915971)
                  ·
                    refine ⟨13401215212745596342373957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8934143475163730894915971 13401215212745596342373957)
                    ·
                      refine ⟨2512727852389799314195117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13401215212745596342373957 2512727852389799314195117)
                      ·
                        rfl

theorem cell23_4893520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 3, 3, 2, 1, 4].length) (baseStart_4893520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4893520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4893520 prefixEnd_4893520 := by exact prefixLift 4893520
  have htrace : WordTrace (prefixWord ++ tailWord_4893520) baseStart_4893520 baseEnd_4893520 := by
    simpa [prefixWord, tailWord_4893520, baseEnd_4893520] using wordTrace_append hprefix tailTrace_4893520
  have hstable : (prefixWord ++ tailWord_4893520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4893520).length < 2 ^ (prefixWord ++ tailWord_4893520).sum := by decide
  have hdescent : baseEnd_4893520 < baseStart_4893520 := by decide
  rcases family_descends (prefixWord ++ tailWord_4893520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4893538 : List Nat := [3, 3, 2, 1, 4, 1, 2, 2, 5]
def baseStart_4893538 : Nat := 118140960795 + 4893538 * 2 ^ 59
def prefixEnd_4893538 : Nat := 4983230072969 + 3 ^ 40 * 4893538 * 2
def baseEnd_4893538 : Nat := 279193010560175582641115

theorem tailTrace_4893538 : CollatzResearch.WordTrace tailWord_4893538 prefixEnd_4893538 279193010560175582641115 := by
  unfold tailWord_4893538
  simp only [CollatzResearch.WordTrace]
  refine ⟨44620498436388762649518317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 118987995830370033732048845 44620498436388762649518317)
  ·
    refine ⟨16732686913645785993569369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44620498436388762649518317 16732686913645785993569369)
    ·
      refine ⟨12549515185234339495177027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16732686913645785993569369 12549515185234339495177027)
      ·
        refine ⟨18824272777851509242765541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12549515185234339495177027 18824272777851509242765541)
        ·
          refine ⟨3529551145847157983018539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18824272777851509242765541 3529551145847157983018539)
          ·
            refine ⟨5294326718770736974527809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3529551145847157983018539 5294326718770736974527809)
            ·
              refine ⟨3970745039078052730895857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5294326718770736974527809 3970745039078052730895857)
              ·
                refine ⟨2978058779308539548171893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3970745039078052730895857 2978058779308539548171893)
                ·
                  refine ⟨279193010560175582641115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2978058779308539548171893 279193010560175582641115)
                  ·
                    rfl

theorem cell23_4893538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 4, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 4, 1, 2, 2, 5].length) (baseStart_4893538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4893538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4893538 prefixEnd_4893538 := by exact prefixLift 4893538
  have htrace : WordTrace (prefixWord ++ tailWord_4893538) baseStart_4893538 baseEnd_4893538 := by
    simpa [prefixWord, tailWord_4893538, baseEnd_4893538] using wordTrace_append hprefix tailTrace_4893538
  have hstable : (prefixWord ++ tailWord_4893538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4893538).length < 2 ^ (prefixWord ++ tailWord_4893538).sum := by decide
  have hdescent : baseEnd_4893538 < baseStart_4893538 := by decide
  rcases family_descends (prefixWord ++ tailWord_4893538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4893594 : List Nat := [3, 1, 1, 4, 3, 2, 1, 2, 6]
def baseStart_4893594 : Nat := 118140960795 + 4893594 * 2 ^ 59
def prefixEnd_4893594 : Nat := 4983230072969 + 3 ^ 40 * 4893594 * 2
def baseEnd_4893594 : Nat := 279196205550914669407753

theorem tailTrace_4893594 : CollatzResearch.WordTrace tailWord_4893594 prefixEnd_4893594 279196205550914669407753 := by
  unfold tailWord_4893594
  simp only [CollatzResearch.WordTrace]
  refine ⟨44621009058338043040527959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 118989357488901448108074557 44621009058338043040527959)
  ·
    refine ⟨66931513587507064560791939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44621009058338043040527959 66931513587507064560791939)
    ·
      refine ⟨100397270381260596841187909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66931513587507064560791939 100397270381260596841187909)
      ·
        refine ⟨18824488196486361907722733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 100397270381260596841187909 18824488196486361907722733)
        ·
          refine ⟨7059183073682385715396025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18824488196486361907722733 7059183073682385715396025)
          ·
            refine ⟨5294387305261789286547019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7059183073682385715396025 5294387305261789286547019)
            ·
              refine ⟨7941580957892683929820529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5294387305261789286547019 7941580957892683929820529)
              ·
                refine ⟨5956185718419512947365397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7941580957892683929820529 5956185718419512947365397)
                ·
                  refine ⟨279196205550914669407753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5956185718419512947365397 279196205550914669407753)
                  ·
                    rfl

theorem cell23_4893594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 2, 1, 2, 6].length) (baseStart_4893594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4893594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4893594 prefixEnd_4893594 := by exact prefixLift 4893594
  have htrace : WordTrace (prefixWord ++ tailWord_4893594) baseStart_4893594 baseEnd_4893594 := by
    simpa [prefixWord, tailWord_4893594, baseEnd_4893594] using wordTrace_append hprefix tailTrace_4893594
  have hstable : (prefixWord ++ tailWord_4893594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4893594).length < 2 ^ (prefixWord ++ tailWord_4893594).sum := by decide
  have hdescent : baseEnd_4893594 < baseStart_4893594 := by decide
  rcases family_descends (prefixWord ++ tailWord_4893594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4893604 : List Nat := [2, 3, 1, 2, 1, 2, 4, 1, 3, 1, 3]
def baseStart_4893604 : Nat := 118140960795 + 4893604 * 2 ^ 59
def prefixEnd_4893604 : Nat := 4983230072969 + 3 ^ 40 * 4893604 * 2
def baseEnd_4893604 : Nat := 2512770984764776985544731

theorem tailTrace_4893604 : CollatzResearch.WordTrace tailWord_4893604 prefixEnd_4893604 2512770984764776985544731 := by
  unfold tailWord_4893604
  simp only [CollatzResearch.WordTrace]
  refine ⟨89242200481657971934987933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118989600642210629246650577 89242200481657971934987933)
  ·
    refine ⟨33465825180621739475620475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 89242200481657971934987933 33465825180621739475620475)
    ·
      refine ⟨50198737770932609213430713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33465825180621739475620475 50198737770932609213430713)
      ·
        refine ⟨37649053328199456910073035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50198737770932609213430713 37649053328199456910073035)
        ·
          refine ⟨56473579992299185365109553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37649053328199456910073035 56473579992299185365109553)
          ·
            refine ⟨42355184994224389023832165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56473579992299185365109553 42355184994224389023832165)
            ·
              refine ⟨7941597186417072941968531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 42355184994224389023832165 7941597186417072941968531)
              ·
                refine ⟨11912395779625609412952797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7941597186417072941968531 11912395779625609412952797)
                ·
                  refine ⟨4467148417359603529857299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11912395779625609412952797 4467148417359603529857299)
                  ·
                    refine ⟨6700722626039405294785949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4467148417359603529857299 6700722626039405294785949)
                    ·
                      refine ⟨2512770984764776985544731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6700722626039405294785949 2512770984764776985544731)
                      ·
                        rfl

theorem cell23_4893604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 4, 1, 3, 1, 3].length) (baseStart_4893604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4893604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4893604 prefixEnd_4893604 := by exact prefixLift 4893604
  have htrace : WordTrace (prefixWord ++ tailWord_4893604) baseStart_4893604 baseEnd_4893604 := by
    simpa [prefixWord, tailWord_4893604, baseEnd_4893604] using wordTrace_append hprefix tailTrace_4893604
  have hstable : (prefixWord ++ tailWord_4893604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4893604).length < 2 ^ (prefixWord ++ tailWord_4893604).sum := by decide
  have hdescent : baseEnd_4893604 < baseStart_4893604 := by decide
  rcases family_descends (prefixWord ++ tailWord_4893604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4893647 : List Nat := [1, 1, 2, 1, 1, 7, 2, 1, 1, 1, 5]
def baseStart_4893647 : Nat := 118140960795 + 4893647 * 2 ^ 59
def prefixEnd_4893647 : Nat := 4983230072969 + 3 ^ 40 * 4893647 * 2
def baseEnd_4893647 : Nat := 2512793064432920317307033

theorem tailTrace_4893647 : CollatzResearch.WordTrace tailWord_4893647 prefixEnd_4893647 2512793064432920317307033 := by
  unfold tailWord_4893647
  simp only [CollatzResearch.WordTrace]
  refine ⟨178485969302160162213791195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118990646201440108142527463 178485969302160162213791195)
  ·
    refine ⟨267728953953240243320686793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 178485969302160162213791195 267728953953240243320686793)
    ·
      refine ⟨200796715464930182490515095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 267728953953240243320686793 200796715464930182490515095)
      ·
        refine ⟨301195073197395273735772643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 200796715464930182490515095 301195073197395273735772643)
        ·
          refine ⟨451792609796092910603658965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 301195073197395273735772643 451792609796092910603658965)
          ·
            refine ⟨10588889292095927592273257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 451792609796092910603658965 10588889292095927592273257)
            ·
              refine ⟨7941666969071945694204943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10588889292095927592273257 7941666969071945694204943)
              ·
                refine ⟨11912500453607918541307415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7941666969071945694204943 11912500453607918541307415)
                ·
                  refine ⟨17868750680411877811961123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11912500453607918541307415 17868750680411877811961123)
                  ·
                    refine ⟨26803126020617816717941685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17868750680411877811961123 26803126020617816717941685)
                    ·
                      refine ⟨2512793064432920317307033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26803126020617816717941685 2512793064432920317307033)
                      ·
                        rfl

theorem cell23_4893647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 7, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 7, 2, 1, 1, 1, 5].length) (baseStart_4893647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4893647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4893647 prefixEnd_4893647 := by exact prefixLift 4893647
  have htrace : WordTrace (prefixWord ++ tailWord_4893647) baseStart_4893647 baseEnd_4893647 := by
    simpa [prefixWord, tailWord_4893647, baseEnd_4893647] using wordTrace_append hprefix tailTrace_4893647
  have hstable : (prefixWord ++ tailWord_4893647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4893647).length < 2 ^ (prefixWord ++ tailWord_4893647).sum := by decide
  have hdescent : baseEnd_4893647 < baseStart_4893647 := by decide
  rcases family_descends (prefixWord ++ tailWord_4893647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4893671 : List Nat := [1, 1, 5, 2, 2, 1, 4, 1, 2, 4]
def baseStart_4893671 : Nat := 118140960795 + 4893671 * 2 ^ 59
def prefixEnd_4893671 : Nat := 4983230072969 + 3 ^ 40 * 4893671 * 2
def baseEnd_4893671 : Nat := 837601795989542741135641

theorem tailTrace_4893671 : CollatzResearch.WordTrace tailWord_4893671 prefixEnd_4893671 837601795989542741135641 := by
  unfold tailWord_4893671
  simp only [CollatzResearch.WordTrace]
  refine ⟨178486844654073214312664867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118991229769382142875109911 178486844654073214312664867)
  ·
    refine ⟨267730266981109821468997301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 178486844654073214312664867 267730266981109821468997301)
    ·
      refine ⟨25099712529479045762718497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 267730266981109821468997301 25099712529479045762718497)
      ·
        refine ⟨18824784397109284322038873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25099712529479045762718497 18824784397109284322038873)
        ·
          refine ⟨14118588297831963241529155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18824784397109284322038873 14118588297831963241529155)
          ·
            refine ⟨21177882446747944862293733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14118588297831963241529155 21177882446747944862293733)
            ·
              refine ⟨3970852958765239661680075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21177882446747944862293733 3970852958765239661680075)
              ·
                refine ⟨5956279438147859492520113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3970852958765239661680075 5956279438147859492520113)
                ·
                  refine ⟨4467209578610894619390085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5956279438147859492520113 4467209578610894619390085)
                  ·
                    refine ⟨837601795989542741135641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4467209578610894619390085 837601795989542741135641)
                    ·
                      rfl

theorem cell23_4893671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 4, 1, 2, 4].length) (baseStart_4893671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4893671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4893671 prefixEnd_4893671 := by exact prefixLift 4893671
  have htrace : WordTrace (prefixWord ++ tailWord_4893671) baseStart_4893671 baseEnd_4893671 := by
    simpa [prefixWord, tailWord_4893671, baseEnd_4893671] using wordTrace_append hprefix tailTrace_4893671
  have hstable : (prefixWord ++ tailWord_4893671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4893671).length < 2 ^ (prefixWord ++ tailWord_4893671).sum := by decide
  have hdescent : baseEnd_4893671 < baseStart_4893671 := by decide
  rcases family_descends (prefixWord ++ tailWord_4893671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4893678 : List Nat := [4, 1, 2, 1, 5, 1, 1, 2, 1, 1, 4]
def baseStart_4893678 : Nat := 118140960795 + 4893678 * 2 ^ 59
def prefixEnd_4893678 : Nat := 4983230072969 + 3 ^ 40 * 4893678 * 2
def baseEnd_4893678 : Nat := 2512808982333209696019391

theorem tailTrace_4893678 : CollatzResearch.WordTrace tailWord_4893678 prefixEnd_4893678 2512808982333209696019391 := by
  unfold tailWord_4893678
  simp only [CollatzResearch.WordTrace]
  refine ⟨22310887495630981813521211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 118991399976698569672113125 22310887495630981813521211)
  ·
    refine ⟨33466331243446472720281817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22310887495630981813521211 33466331243446472720281817)
    ·
      refine ⟨25099748432584854540211363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33466331243446472720281817 25099748432584854540211363)
      ·
        refine ⟨37649622648877281810317045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25099748432584854540211363 37649622648877281810317045)
        ·
          refine ⟨3529652123332245169717223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 37649622648877281810317045 3529652123332245169717223)
          ·
            refine ⟨5294478184998367754575835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3529652123332245169717223 5294478184998367754575835)
            ·
              refine ⟨7941717277497551631863753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5294478184998367754575835 7941717277497551631863753)
              ·
                refine ⟨5956287958123163723897815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7941717277497551631863753 5956287958123163723897815)
                ·
                  refine ⟨8934431937184745585846723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5956287958123163723897815 8934431937184745585846723)
                  ·
                    refine ⟨13401647905777118378770085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8934431937184745585846723 13401647905777118378770085)
                    ·
                      refine ⟨2512808982333209696019391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13401647905777118378770085 2512808982333209696019391)
                      ·
                        rfl

theorem cell23_4893678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 5, 1, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 5, 1, 1, 2, 1, 1, 4].length) (baseStart_4893678 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4893678 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4893678 prefixEnd_4893678 := by exact prefixLift 4893678
  have htrace : WordTrace (prefixWord ++ tailWord_4893678) baseStart_4893678 baseEnd_4893678 := by
    simpa [prefixWord, tailWord_4893678, baseEnd_4893678] using wordTrace_append hprefix tailTrace_4893678
  have hstable : (prefixWord ++ tailWord_4893678).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4893678).length < 2 ^ (prefixWord ++ tailWord_4893678).sum := by decide
  have hdescent : baseEnd_4893678 < baseStart_4893678 := by decide
  rcases family_descends (prefixWord ++ tailWord_4893678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4893681 : List Nat := [1, 2, 2, 2, 4, 3, 1, 2, 1, 2, 3]
def baseStart_4893681 : Nat := 118140960795 + 4893681 * 2 ^ 59
def prefixEnd_4893681 : Nat := 4983230072969 + 3 ^ 40 * 4893681 * 2
def baseEnd_4893681 : Nat := 2512810522775173184281877

theorem tailTrace_4893681 : CollatzResearch.WordTrace tailWord_4893681 prefixEnd_4893681 2512810522775173184281877 := by
  unfold tailWord_4893681
  simp only [CollatzResearch.WordTrace]
  refine ⟨178487209384036986020528897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118991472922691324013685931 178487209384036986020528897)
  ·
    refine ⟨133865407038027739515396673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 178487209384036986020528897 133865407038027739515396673)
    ·
      refine ⟨100399055278520804636547505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 133865407038027739515396673 100399055278520804636547505)
      ·
        refine ⟨75299291458890603477410629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 100399055278520804636547505 75299291458890603477410629)
        ·
          refine ⟨14118617148541988152014493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 75299291458890603477410629 14118617148541988152014493)
          ·
            refine ⟨5294481430703245557005435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14118617148541988152014493 5294481430703245557005435)
            ·
              refine ⟨7941722146054868335508153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5294481430703245557005435 7941722146054868335508153)
              ·
                refine ⟨5956291609541151251631115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7941722146054868335508153 5956291609541151251631115)
                ·
                  refine ⟨8934437414311726877446673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5956291609541151251631115 8934437414311726877446673)
                  ·
                    refine ⟨6700828060733795158085005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8934437414311726877446673 6700828060733795158085005)
                    ·
                      refine ⟨2512810522775173184281877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6700828060733795158085005 2512810522775173184281877)
                      ·
                        rfl

theorem cell23_4893681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 3, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 3, 1, 2, 1, 2, 3].length) (baseStart_4893681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4893681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4893681 prefixEnd_4893681 := by exact prefixLift 4893681
  have htrace : WordTrace (prefixWord ++ tailWord_4893681) baseStart_4893681 baseEnd_4893681 := by
    simpa [prefixWord, tailWord_4893681, baseEnd_4893681] using wordTrace_append hprefix tailTrace_4893681
  have hstable : (prefixWord ++ tailWord_4893681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4893681).length < 2 ^ (prefixWord ++ tailWord_4893681).sum := by decide
  have hdescent : baseEnd_4893681 < baseStart_4893681 := by decide
  rcases family_descends (prefixWord ++ tailWord_4893681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4893690 : List Nat := [3, 1, 1, 1, 1, 2, 1, 3, 1, 4, 5]
def baseStart_4893690 : Nat := 118140960795 + 4893690 * 2 ^ 59
def prefixEnd_4893690 : Nat := 4983230072969 + 3 ^ 40 * 4893690 * 2
def baseEnd_4893690 : Nat := 2512815144101063649069335

theorem tailTrace_4893690 : CollatzResearch.WordTrace tailWord_4893690 prefixEnd_4893690 2512815144101063649069335 := by
  unfold tailWord_4893690
  simp only [CollatzResearch.WordTrace]
  refine ⟨44621884410251095139401631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 118991691760669587038404349 44621884410251095139401631)
  ·
    refine ⟨66932826615376642709102447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44621884410251095139401631 66932826615376642709102447)
    ·
      refine ⟨100399239923064964063653671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66932826615376642709102447 100399239923064964063653671)
      ·
        refine ⟨150598859884597446095480507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100399239923064964063653671 150598859884597446095480507)
        ·
          refine ⟨225898289826896169143220761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 150598859884597446095480507 225898289826896169143220761)
          ·
            refine ⟨169423717370172126857415571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 225898289826896169143220761 169423717370172126857415571)
            ·
              refine ⟨254135576055258190286123357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 169423717370172126857415571 254135576055258190286123357)
              ·
                refine ⟨95300841020721821357296259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 254135576055258190286123357 95300841020721821357296259)
                ·
                  refine ⟨142951261531082732035944389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 95300841020721821357296259 142951261531082732035944389)
                  ·
                    refine ⟨26803361537078012256739573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 142951261531082732035944389 26803361537078012256739573)
                    ·
                      refine ⟨2512815144101063649069335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26803361537078012256739573 2512815144101063649069335)
                      ·
                        rfl

theorem cell23_4893690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 3, 1, 4, 5].length) (baseStart_4893690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4893690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4893690 prefixEnd_4893690 := by exact prefixLift 4893690
  have htrace : WordTrace (prefixWord ++ tailWord_4893690) baseStart_4893690 baseEnd_4893690 := by
    simpa [prefixWord, tailWord_4893690, baseEnd_4893690] using wordTrace_append hprefix tailTrace_4893690
  have hstable : (prefixWord ++ tailWord_4893690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4893690).length < 2 ^ (prefixWord ++ tailWord_4893690).sum := by decide
  have hdescent : baseEnd_4893690 < baseStart_4893690 := by decide
  rcases family_descends (prefixWord ++ tailWord_4893690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4893698 : List Nat := [3, 4, 1, 3, 1, 2, 1, 1, 1, 1, 5]
def baseStart_4893698 : Nat := 118140960795 + 4893698 * 2 ^ 59
def prefixEnd_4893698 : Nat := 4983230072969 + 3 ^ 40 * 4893698 * 2
def baseEnd_4893698 : Nat := 2512819251946299617769299

theorem tailTrace_4893698 : CollatzResearch.WordTrace tailWord_4893698 prefixEnd_4893698 2512819251946299617769299 := by
  unfold tailWord_4893698
  simp only [CollatzResearch.WordTrace]
  refine ⟨44621957356243849480974437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 118991886283316931949265165 44621957356243849480974437)
  ·
    refine ⟨8366617004295721777682707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 44621957356243849480974437 8366617004295721777682707)
    ·
      refine ⟨12549925506443582666524061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8366617004295721777682707 12549925506443582666524061)
      ·
        refine ⟨4706222064916343499946523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12549925506443582666524061 4706222064916343499946523)
        ·
          refine ⟨7059333097374515249919785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4706222064916343499946523 7059333097374515249919785)
          ·
            refine ⟨5294499823030886437439839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7059333097374515249919785 5294499823030886437439839)
            ·
              refine ⟨7941749734546329656159759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5294499823030886437439839 7941749734546329656159759)
              ·
                refine ⟨11912624601819494484239639, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7941749734546329656159759 11912624601819494484239639)
                ·
                  refine ⟨17868936902729241726359459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11912624601819494484239639 17868936902729241726359459)
                  ·
                    refine ⟨26803405354093862589539189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17868936902729241726359459 26803405354093862589539189)
                    ·
                      refine ⟨2512819251946299617769299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26803405354093862589539189 2512819251946299617769299)
                      ·
                        rfl

theorem cell23_4893698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 2, 1, 1, 1, 1, 5].length) (baseStart_4893698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4893698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4893698 prefixEnd_4893698 := by exact prefixLift 4893698
  have htrace : WordTrace (prefixWord ++ tailWord_4893698) baseStart_4893698 baseEnd_4893698 := by
    simpa [prefixWord, tailWord_4893698, baseEnd_4893698] using wordTrace_append hprefix tailTrace_4893698
  have hstable : (prefixWord ++ tailWord_4893698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4893698).length < 2 ^ (prefixWord ++ tailWord_4893698).sum := by decide
  have hdescent : baseEnd_4893698 < baseStart_4893698 := by decide
  rcases family_descends (prefixWord ++ tailWord_4893698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4893717 : List Nat := [1, 3, 2, 1, 4, 1, 1, 1, 2, 3, 4]
def baseStart_4893717 : Nat := 118140960795 + 4893717 * 2 ^ 59
def prefixEnd_4893717 : Nat := 4983230072969 + 3 ^ 40 * 4893717 * 2
def baseEnd_4893717 : Nat := 2512829008078735043431711

theorem tailTrace_4893717 : CollatzResearch.WordTrace tailWord_4893717 prefixEnd_4893717 2512829008078735043431711 := by
  unfold tailWord_4893717
  simp only [CollatzResearch.WordTrace]
  refine ⟨178488522411906564168839405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118992348274604376112559603 178488522411906564168839405)
  ·
    refine ⟨66933195904464961563314777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 178488522411906564168839405 66933195904464961563314777)
    ·
      refine ⟨50199896928348721172486083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66933195904464961563314777 50199896928348721172486083)
      ·
        refine ⟨75299845392523081758729125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50199896928348721172486083 75299845392523081758729125)
        ·
          refine ⟨14118721011098077829761711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 75299845392523081758729125 14118721011098077829761711)
          ·
            refine ⟨21178081516647116744642567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14118721011098077829761711 21178081516647116744642567)
            ·
              refine ⟨31767122274970675116963851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21178081516647116744642567 31767122274970675116963851)
              ·
                refine ⟨47650683412456012675445777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31767122274970675116963851 47650683412456012675445777)
                ·
                  refine ⟨35738012559342009506584333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 47650683412456012675445777 35738012559342009506584333)
                  ·
                    refine ⟨13401754709753253564969125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 35738012559342009506584333 13401754709753253564969125)
                    ·
                      refine ⟨2512829008078735043431711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13401754709753253564969125 2512829008078735043431711)
                      ·
                        rfl

theorem cell23_4893717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 1, 1, 2, 3, 4].length) (baseStart_4893717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4893717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4893717 prefixEnd_4893717 := by exact prefixLift 4893717
  have htrace : WordTrace (prefixWord ++ tailWord_4893717) baseStart_4893717 baseEnd_4893717 := by
    simpa [prefixWord, tailWord_4893717, baseEnd_4893717] using wordTrace_append hprefix tailTrace_4893717
  have hstable : (prefixWord ++ tailWord_4893717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4893717).length < 2 ^ (prefixWord ++ tailWord_4893717).sum := by decide
  have hdescent : baseEnd_4893717 < baseStart_4893717 := by decide
  rcases family_descends (prefixWord ++ tailWord_4893717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4893727 : List Nat := [1, 1, 2, 4, 1, 4, 1, 1, 2, 6]
def baseStart_4893727 : Nat := 118140960795 + 4893727 * 2 ^ 59
def prefixEnd_4893727 : Nat := 4983230072969 + 3 ^ 40 * 4893727 * 2
def baseEnd_4893727 : Nat := 837611380961760001435555

theorem tailTrace_4893727 : CollatzResearch.WordTrace tailWord_4893727 prefixEnd_4893727 837611380961760001435555 := by
  unfold tailWord_4893727
  simp only [CollatzResearch.WordTrace]
  refine ⟨178488887141870335876703435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118992591427913557251135623 178488887141870335876703435)
  ·
    refine ⟨267733330712805503815055153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 178488887141870335876703435 267733330712805503815055153)
    ·
      refine ⟨200799998034604127861291365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 267733330712805503815055153 200799998034604127861291365)
      ·
        refine ⟨37649999631488273973992131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 200799998034604127861291365 37649999631488273973992131)
        ·
          refine ⟨56474999447232410960988197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37649999631488273973992131 56474999447232410960988197)
          ·
            refine ⟨10589062396356077055185287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 56474999447232410960988197 10589062396356077055185287)
            ·
              refine ⟨15883593594534115582777931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10589062396356077055185287 15883593594534115582777931)
              ·
                refine ⟨23825390391801173374166897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15883593594534115582777931 23825390391801173374166897)
                ·
                  refine ⟨17869042793850880030625173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23825390391801173374166897 17869042793850880030625173)
                  ·
                    refine ⟨837611380961760001435555, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17869042793850880030625173 837611380961760001435555)
                    ·
                      rfl

theorem cell23_4893727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 4, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 4, 1, 1, 2, 6].length) (baseStart_4893727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4893727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4893727 prefixEnd_4893727 := by exact prefixLift 4893727
  have htrace : WordTrace (prefixWord ++ tailWord_4893727) baseStart_4893727 baseEnd_4893727 := by
    simpa [prefixWord, tailWord_4893727, baseEnd_4893727] using wordTrace_append hprefix tailTrace_4893727
  have hstable : (prefixWord ++ tailWord_4893727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4893727).length < 2 ^ (prefixWord ++ tailWord_4893727).sum := by decide
  have hdescent : baseEnd_4893727 < baseStart_4893727 := by decide
  rcases family_descends (prefixWord ++ tailWord_4893727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4893774 : List Nat := [4, 1, 1, 1, 1, 3, 1, 6, 5]
def baseStart_4893774 : Nat := 118140960795 + 4893774 * 2 ^ 59
def prefixEnd_4893774 : Nat := 4983230072969 + 3 ^ 40 * 4893774 * 2
def baseEnd_4893774 : Nat := 279206475164004591157661

theorem tailTrace_4893774 : CollatzResearch.WordTrace tailWord_4893774 prefixEnd_4893774 279206475164004591157661 := by
  unfold tailWord_4893774
  simp only [CollatzResearch.WordTrace]
  refine ⟨22311325171587507862958047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 118993734248466708602442917 22311325171587507862958047)
  ·
    refine ⟨33466987757381261794437071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22311325171587507862958047 33466987757381261794437071)
    ·
      refine ⟨50200481636071892691655607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33466987757381261794437071 50200481636071892691655607)
      ·
        refine ⟨75300722454107839037483411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50200481636071892691655607 75300722454107839037483411)
        ·
          refine ⟨112951083681161758556225117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75300722454107839037483411 112951083681161758556225117)
          ·
            refine ⟨42356656380435659458584419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 112951083681161758556225117 42356656380435659458584419)
            ·
              refine ⟨63534984570653489187876629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42356656380435659458584419 63534984570653489187876629)
              ·
                refine ⟨2978202401749382305681717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 63534984570653489187876629 2978202401749382305681717)
                ·
                  refine ⟨279206475164004591157661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2978202401749382305681717 279206475164004591157661)
                  ·
                    rfl

theorem cell23_4893774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 1, 6, 5].length) (baseStart_4893774 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4893774 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4893774 prefixEnd_4893774 := by exact prefixLift 4893774
  have htrace : WordTrace (prefixWord ++ tailWord_4893774) baseStart_4893774 baseEnd_4893774 := by
    simpa [prefixWord, tailWord_4893774, baseEnd_4893774] using wordTrace_append hprefix tailTrace_4893774
  have hstable : (prefixWord ++ tailWord_4893774).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4893774).length < 2 ^ (prefixWord ++ tailWord_4893774).sum := by decide
  have hdescent : baseEnd_4893774 < baseStart_4893774 := by decide
  rcases family_descends (prefixWord ++ tailWord_4893774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4893807 : List Nat := [1, 1, 2, 1, 3, 3, 1, 3, 1, 3, 4]
def baseStart_4893807 : Nat := 118140960795 + 4893807 * 2 ^ 59
def prefixEnd_4893807 : Nat := 4983230072969 + 3 ^ 40 * 4893807 * 2
def baseEnd_4893807 : Nat := 2512875221337639691306297

theorem tailTrace_4893807 : CollatzResearch.WordTrace tailWord_4893807 prefixEnd_4893807 2512875221337639691306297 := by
  unfold tailWord_4893807
  simp only [CollatzResearch.WordTrace]
  refine ⟨178491804981580509539615675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118994536654387006359743783 178491804981580509539615675)
  ·
    refine ⟨267737707472370764309423513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 178491804981580509539615675 267737707472370764309423513)
    ·
      refine ⟨200803280604278073232067635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 267737707472370764309423513 200803280604278073232067635)
      ·
        refine ⟨301204920906417109848101453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 200803280604278073232067635 301204920906417109848101453)
        ·
          refine ⟨112951845339906416193038045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 301204920906417109848101453 112951845339906416193038045)
          ·
            refine ⟨42356942002464906072389267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 112951845339906416193038045 42356942002464906072389267)
            ·
              refine ⟨63535413003697359108583901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42356942002464906072389267 63535413003697359108583901)
              ·
                refine ⟨23825779876386509665718963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 63535413003697359108583901 23825779876386509665718963)
                ·
                  refine ⟨35738669814579764498578445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23825779876386509665718963 35738669814579764498578445)
                  ·
                    refine ⟨13402001180467411686966917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 35738669814579764498578445 13402001180467411686966917)
                    ·
                      refine ⟨2512875221337639691306297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13402001180467411686966917 2512875221337639691306297)
                      ·
                        rfl

theorem cell23_4893807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 1, 3, 1, 3, 4].length) (baseStart_4893807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4893807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4893807 prefixEnd_4893807 := by exact prefixLift 4893807
  have htrace : WordTrace (prefixWord ++ tailWord_4893807) baseStart_4893807 baseEnd_4893807 := by
    simpa [prefixWord, tailWord_4893807, baseEnd_4893807] using wordTrace_append hprefix tailTrace_4893807
  have hstable : (prefixWord ++ tailWord_4893807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4893807).length < 2 ^ (prefixWord ++ tailWord_4893807).sum := by decide
  have hdescent : baseEnd_4893807 < baseStart_4893807 := by decide
  rcases family_descends (prefixWord ++ tailWord_4893807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4893814 : List Nat := [5, 1, 1, 2, 1, 1, 2, 2, 1, 2, 5]
def baseStart_4893814 : Nat := 118140960795 + 4893814 * 2 ^ 59
def prefixEnd_4893814 : Nat := 4983230072969 + 3 ^ 40 * 4893814 * 2
def baseEnd_4893814 : Nat := 2512878815702221163918765

theorem tailTrace_4893814 : CollatzResearch.WordTrace tailWord_4893814 prefixEnd_4893814 2512878815702221163918765 := by
  unfold tailWord_4893814
  simp only [CollatzResearch.WordTrace]
  refine ⟨11155753768284696858445031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 118994706861703433156746997 11155753768284696858445031)
  ·
    refine ⟨16733630652427045287667547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11155753768284696858445031 16733630652427045287667547)
    ·
      refine ⟨25100445978640567931501321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16733630652427045287667547 25100445978640567931501321)
      ·
        refine ⟨18825334483980425948625991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25100445978640567931501321 18825334483980425948625991)
        ·
          refine ⟨28238001725970638922938987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18825334483980425948625991 28238001725970638922938987)
          ·
            refine ⟨42357002588955958384408481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28238001725970638922938987 42357002588955958384408481)
            ·
              refine ⟨31767751941716968788306361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42357002588955958384408481 31767751941716968788306361)
              ·
                refine ⟨23825813956287726591229771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31767751941716968788306361 23825813956287726591229771)
                ·
                  refine ⟨35738720934431589886844657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23825813956287726591229771 35738720934431589886844657)
                  ·
                    refine ⟨26804040700823692415133493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 35738720934431589886844657 26804040700823692415133493)
                    ·
                      refine ⟨2512878815702221163918765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26804040700823692415133493 2512878815702221163918765)
                      ·
                        rfl

theorem cell23_4893814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 2, 2, 1, 2, 5].length) (baseStart_4893814 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4893814 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4893814 prefixEnd_4893814 := by exact prefixLift 4893814
  have htrace : WordTrace (prefixWord ++ tailWord_4893814) baseStart_4893814 baseEnd_4893814 := by
    simpa [prefixWord, tailWord_4893814, baseEnd_4893814] using wordTrace_append hprefix tailTrace_4893814
  have hstable : (prefixWord ++ tailWord_4893814).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4893814).length < 2 ^ (prefixWord ++ tailWord_4893814).sum := by decide
  have hdescent : baseEnd_4893814 < baseStart_4893814 := by decide
  rcases family_descends (prefixWord ++ tailWord_4893814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4893824 : List Nat := [2, 1, 1, 2, 1, 3, 2, 1, 4, 4, 2]
def baseStart_4893824 : Nat := 118140960795 + 4893824 * 2 ^ 59
def prefixEnd_4893824 : Nat := 4983230072969 + 3 ^ 40 * 4893824 * 2
def baseEnd_4893824 : Nat := 2512883950508766124793719

theorem tailTrace_4893824 : CollatzResearch.WordTrace tailWord_4893824 prefixEnd_4893824 2512883950508766124793719 := by
  unfold tailWord_4893824
  simp only [CollatzResearch.WordTrace]
  refine ⟨89246212511259460721492263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118994950015012614295323017 89246212511259460721492263)
  ·
    refine ⟨133869318766889191082238395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89246212511259460721492263 133869318766889191082238395)
    ·
      refine ⟨200803978150333786623357593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 133869318766889191082238395 200803978150333786623357593)
      ·
        refine ⟨150602983612750339967518195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 200803978150333786623357593 150602983612750339967518195)
        ·
          refine ⟨225904475419125509951277293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 150602983612750339967518195 225904475419125509951277293)
          ·
            refine ⟨84714178282172066231728985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 225904475419125509951277293 84714178282172066231728985)
            ·
              refine ⟨63535633711629049673796739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 84714178282172066231728985 63535633711629049673796739)
              ·
                refine ⟨95303450567443574510695109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 63535633711629049673796739 95303450567443574510695109)
                ·
                  refine ⟨17869396981395670220755333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 95303450567443574510695109 17869396981395670220755333)
                  ·
                    refine ⟨3350511934011688166391625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17869396981395670220755333 3350511934011688166391625)
                    ·
                      refine ⟨2512883950508766124793719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3350511934011688166391625 2512883950508766124793719)
                      ·
                        rfl

theorem cell23_4893824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 2, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 2, 1, 4, 4, 2].length) (baseStart_4893824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4893824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4893824 prefixEnd_4893824 := by exact prefixLift 4893824
  have htrace : WordTrace (prefixWord ++ tailWord_4893824) baseStart_4893824 baseEnd_4893824 := by
    simpa [prefixWord, tailWord_4893824, baseEnd_4893824] using wordTrace_append hprefix tailTrace_4893824
  have hstable : (prefixWord ++ tailWord_4893824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4893824).length < 2 ^ (prefixWord ++ tailWord_4893824).sum := by decide
  have hdescent : baseEnd_4893824 < baseStart_4893824 := by decide
  rcases family_descends (prefixWord ++ tailWord_4893824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4893858 : List Nat := [3, 3, 1, 3, 2, 1, 2, 1, 2, 1, 4]
def baseStart_4893858 : Nat := 118140960795 + 4893858 * 2 ^ 59
def prefixEnd_4893858 : Nat := 4983230072969 + 3 ^ 40 * 4893858 * 2
def baseEnd_4893858 : Nat := 2512901408851018991768563

theorem tailTrace_4893858 : CollatzResearch.WordTrace tailWord_4893858 prefixEnd_4893858 2512901408851018991768563 := by
  unfold tailWord_4893858
  simp only [CollatzResearch.WordTrace]
  refine ⟨44623416276098936312430557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 118995776736263830166481485 44623416276098936312430557)
  ·
    refine ⟨16733781103537101117161459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44623416276098936312430557 16733781103537101117161459)
    ·
      refine ⟨25100671655305651675742189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16733781103537101117161459 25100671655305651675742189)
      ·
        refine ⟨9412751870739619378403321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25100671655305651675742189 9412751870739619378403321)
        ·
          refine ⟨7059563903054714533802491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9412751870739619378403321 7059563903054714533802491)
          ·
            refine ⟨10589345854582071800703737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7059563903054714533802491 10589345854582071800703737)
            ·
              refine ⟨7942009390936553850527803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10589345854582071800703737 7942009390936553850527803)
              ·
                refine ⟨11913014086404830775791705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7942009390936553850527803 11913014086404830775791705)
                ·
                  refine ⟨8934760564803623081843779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11913014086404830775791705 8934760564803623081843779)
                  ·
                    refine ⟨13402140847205434622765669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8934760564803623081843779 13402140847205434622765669)
                    ·
                      refine ⟨2512901408851018991768563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13402140847205434622765669 2512901408851018991768563)
                      ·
                        rfl

theorem cell23_4893858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 1, 2, 1, 2, 1, 4].length) (baseStart_4893858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4893858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4893858 prefixEnd_4893858 := by exact prefixLift 4893858
  have htrace : WordTrace (prefixWord ++ tailWord_4893858) baseStart_4893858 baseEnd_4893858 := by
    simpa [prefixWord, tailWord_4893858, baseEnd_4893858] using wordTrace_append hprefix tailTrace_4893858
  have hstable : (prefixWord ++ tailWord_4893858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4893858).length < 2 ^ (prefixWord ++ tailWord_4893858).sum := by decide
  have hdescent : baseEnd_4893858 < baseStart_4893858 := by decide
  rcases family_descends (prefixWord ++ tailWord_4893858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4893861 : List Nat := [1, 3, 1, 2, 1, 5, 2, 1, 2, 2, 3]
def baseStart_4893861 : Nat := 118140960795 + 4893861 * 2 ^ 59
def prefixEnd_4893861 : Nat := 4983230072969 + 3 ^ 40 * 4893861 * 2
def baseEnd_4893861 : Nat := 2512902949292982480031049

theorem tailTrace_4893861 : CollatzResearch.WordTrace tailWord_4893861 prefixEnd_4893861 2512902949292982480031049 := by
  unfold tailWord_4893861
  simp only [CollatzResearch.WordTrace]
  refine ⟨178493774523384876762081437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118995849682256584508054291 178493774523384876762081437)
  ·
    refine ⟨66935165446269328785780539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 178493774523384876762081437 66935165446269328785780539)
    ·
      refine ⟨100402748169403993178670809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66935165446269328785780539 100402748169403993178670809)
      ·
        refine ⟨75302061127052994884003107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 100402748169403993178670809 75302061127052994884003107)
        ·
          refine ⟨112953091690579492326004661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75302061127052994884003107 112953091690579492326004661)
          ·
            refine ⟨10589352345991827405562937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 112953091690579492326004661 10589352345991827405562937)
            ·
              refine ⟨7942014259493870554172203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10589352345991827405562937 7942014259493870554172203)
              ·
                refine ⟨11913021389240805831258305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7942014259493870554172203 11913021389240805831258305)
                ·
                  refine ⟨8934766041930604373443729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11913021389240805831258305 8934766041930604373443729)
                  ·
                    refine ⟨6701074531447953280082797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8934766041930604373443729 6701074531447953280082797)
                    ·
                      refine ⟨2512902949292982480031049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6701074531447953280082797 2512902949292982480031049)
                      ·
                        rfl

theorem cell23_4893861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 5, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 5, 2, 1, 2, 2, 3].length) (baseStart_4893861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4893861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4893861 prefixEnd_4893861 := by exact prefixLift 4893861
  have htrace : WordTrace (prefixWord ++ tailWord_4893861) baseStart_4893861 baseEnd_4893861 := by
    simpa [prefixWord, tailWord_4893861, baseEnd_4893861] using wordTrace_append hprefix tailTrace_4893861
  have hstable : (prefixWord ++ tailWord_4893861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4893861).length < 2 ^ (prefixWord ++ tailWord_4893861).sum := by decide
  have hdescent : baseEnd_4893861 < baseStart_4893861 := by decide
  rcases family_descends (prefixWord ++ tailWord_4893861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4893907 : List Nat := [1, 1, 1, 2, 1, 1, 1, 4, 5, 6]
def baseStart_4893907 : Nat := 118140960795 + 4893907 * 2 ^ 59
def prefixEnd_4893907 : Nat := 4983230072969 + 3 ^ 40 * 4893907 * 2
def baseEnd_4893907 : Nat := 837642189801029766685279

theorem tailTrace_4893907 : CollatzResearch.WordTrace tailWord_4893907 prefixEnd_4893907 837642189801029766685279 := by
  unfold tailWord_4893907
  simp only [CollatzResearch.WordTrace]
  refine ⟨178495452281218226618255975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118996968187478817745503983 178495452281218226618255975)
  ·
    refine ⟨267743178421827339927383963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 178495452281218226618255975 267743178421827339927383963)
    ·
      refine ⟨401614767632741009891075945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 267743178421827339927383963 401614767632741009891075945)
      ·
        refine ⟨301211075724555757418306959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 401614767632741009891075945 301211075724555757418306959)
        ·
          refine ⟨451816613586833636127460439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 301211075724555757418306959 451816613586833636127460439)
          ·
            refine ⟨677724920380250454191190659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 451816613586833636127460439 677724920380250454191190659)
            ·
              refine ⟨1016587380570375681286785989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 677724920380250454191190659 1016587380570375681286785989)
              ·
                refine ⟨190610133856945440241272373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1016587380570375681286785989 190610133856945440241272373)
                ·
                  refine ⟨17869700049088635022619285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 190610133856945440241272373 17869700049088635022619285)
                  ·
                    refine ⟨837642189801029766685279, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17869700049088635022619285 837642189801029766685279)
                    ·
                      rfl

theorem cell23_4893907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 4, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 4, 5, 6].length) (baseStart_4893907 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4893907 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4893907 prefixEnd_4893907 := by exact prefixLift 4893907
  have htrace : WordTrace (prefixWord ++ tailWord_4893907) baseStart_4893907 baseEnd_4893907 := by
    simpa [prefixWord, tailWord_4893907, baseEnd_4893907] using wordTrace_append hprefix tailTrace_4893907
  have hstable : (prefixWord ++ tailWord_4893907).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4893907).length < 2 ^ (prefixWord ++ tailWord_4893907).sum := by decide
  have hdescent : baseEnd_4893907 < baseStart_4893907 := by decide
  rcases family_descends (prefixWord ++ tailWord_4893907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4893924 : List Nat := [2, 3, 1, 1, 1, 2, 4, 2, 1, 6]
def baseStart_4893924 : Nat := 118140960795 + 4893924 * 2 ^ 59
def prefixEnd_4893924 : Nat := 4983230072969 + 3 ^ 40 * 4893924 * 2
def baseEnd_4893924 : Nat := 837645099524738577847753

theorem tailTrace_4893924 : CollatzResearch.WordTrace tailWord_4893924 prefixEnd_4893924 837645099524738577847753 := by
  unfold tailWord_4893924
  simp only [CollatzResearch.WordTrace]
  refine ⟨89248036161078319260812413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118997381548104425681083217 89248036161078319260812413)
  ·
    refine ⟨33468013560404369722804655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 89248036161078319260812413 33468013560404369722804655)
    ·
      refine ⟨50202020340606554584206983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33468013560404369722804655 50202020340606554584206983)
      ·
        refine ⟨75303030510909831876310475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50202020340606554584206983 75303030510909831876310475)
        ·
          refine ⟨112954545766364747814465713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75303030510909831876310475 112954545766364747814465713)
          ·
            refine ⟨84715909324773560860849285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 112954545766364747814465713 84715909324773560860849285)
            ·
              refine ⟨15884232998395042661409241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 84715909324773560860849285 15884232998395042661409241)
              ·
                refine ⟨11913174748796281996056931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15884232998395042661409241 11913174748796281996056931)
                ·
                  refine ⟨17869762123194422994085397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11913174748796281996056931 17869762123194422994085397)
                  ·
                    refine ⟨837645099524738577847753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17869762123194422994085397 837645099524738577847753)
                    ·
                      rfl

theorem cell23_4893924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 4, 2, 1, 6].length) (baseStart_4893924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4893924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4893924 prefixEnd_4893924 := by exact prefixLift 4893924
  have htrace : WordTrace (prefixWord ++ tailWord_4893924) baseStart_4893924 baseEnd_4893924 := by
    simpa [prefixWord, tailWord_4893924, baseEnd_4893924] using wordTrace_append hprefix tailTrace_4893924
  have hstable : (prefixWord ++ tailWord_4893924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4893924).length < 2 ^ (prefixWord ++ tailWord_4893924).sum := by decide
  have hdescent : baseEnd_4893924 < baseStart_4893924 := by decide
  rcases family_descends (prefixWord ++ tailWord_4893924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4893931 : List Nat := [1, 1, 1, 1, 2, 7, 1, 3, 1, 1, 4]
def baseStart_4893931 : Nat := 118140960795 + 4893931 * 2 ^ 59
def prefixEnd_4893931 : Nat := 4983230072969 + 3 ^ 40 * 4893931 * 2
def baseEnd_4893931 : Nat := 2512938892938797206155727

theorem tailTrace_4893931 : CollatzResearch.WordTrace tailWord_4893931 prefixEnd_4893931 2512938892938797206155727 := by
  unfold tailWord_4893931
  simp only [CollatzResearch.WordTrace]
  refine ⟨178496327633131278717129647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118997551755420852478086431 178496327633131278717129647)
  ·
    refine ⟨267744491449696918075694471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 178496327633131278717129647 267744491449696918075694471)
    ·
      refine ⟨401616737174545377113541707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 267744491449696918075694471 401616737174545377113541707)
      ·
        refine ⟨602425105761818065670312561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 401616737174545377113541707 602425105761818065670312561)
        ·
          refine ⟨451818829321363549252734421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 602425105761818065670312561 451818829321363549252734421)
          ·
            refine ⟨10589503812219458185610963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 451818829321363549252734421 10589503812219458185610963)
            ·
              refine ⟨15884255718329187278416445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10589503812219458185610963 15884255718329187278416445)
              ·
                refine ⟨5956595894373445229406167, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15884255718329187278416445 5956595894373445229406167)
                ·
                  refine ⟨8934893841560167844109251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5956595894373445229406167 8934893841560167844109251)
                  ·
                    refine ⟨13402340762340251766163877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8934893841560167844109251 13402340762340251766163877)
                    ·
                      refine ⟨2512938892938797206155727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13402340762340251766163877 2512938892938797206155727)
                      ·
                        rfl

theorem cell23_4893931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 7, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 7, 1, 3, 1, 1, 4].length) (baseStart_4893931 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4893931 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4893931 prefixEnd_4893931 := by exact prefixLift 4893931
  have htrace : WordTrace (prefixWord ++ tailWord_4893931) baseStart_4893931 baseEnd_4893931 := by
    simpa [prefixWord, tailWord_4893931, baseEnd_4893931] using wordTrace_append hprefix tailTrace_4893931
  have hstable : (prefixWord ++ tailWord_4893931).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4893931).length < 2 ^ (prefixWord ++ tailWord_4893931).sum := by decide
  have hdescent : baseEnd_4893931 < baseStart_4893931 := by decide
  rcases family_descends (prefixWord ++ tailWord_4893931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4894015 : List Nat := [1, 1, 2, 2, 4, 2, 4, 1, 2, 1, 3]
def baseStart_4894015 : Nat := 118140960795 + 4894015 * 2 ^ 59
def prefixEnd_4894015 : Nat := 4983230072969 + 3 ^ 40 * 4894015 * 2
def baseEnd_4894015 : Nat := 2512982025313774877505341

theorem tailTrace_4894015 : CollatzResearch.WordTrace tailWord_4894015 prefixEnd_4894015 2512982025313774877505341 := by
  unfold tailWord_4894015
  simp only [CollatzResearch.WordTrace]
  refine ⟨178499391364826961063187499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118999594243217974042124999 178499391364826961063187499)
  ·
    refine ⟨267749087047240441594781249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 178499391364826961063187499 267749087047240441594781249)
    ·
      refine ⟨200811815285430331196085937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 267749087047240441594781249 200811815285430331196085937)
      ·
        refine ⟨150608861464072748397064453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 200811815285430331196085937 150608861464072748397064453)
        ·
          refine ⟨28239161524513640324449585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 150608861464072748397064453 28239161524513640324449585)
          ·
            refine ⟨21179371143385230243337189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28239161524513640324449585 21179371143385230243337189)
            ·
              refine ⟨3971132089384730670625723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21179371143385230243337189 3971132089384730670625723)
              ·
                refine ⟨5956698134077096005938585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3971132089384730670625723 5956698134077096005938585)
                ·
                  refine ⟨4467523600557822004453939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5956698134077096005938585 4467523600557822004453939)
                  ·
                    refine ⟨6701285400836733006680909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4467523600557822004453939 6701285400836733006680909)
                    ·
                      refine ⟨2512982025313774877505341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6701285400836733006680909 2512982025313774877505341)
                      ·
                        rfl

theorem cell23_4894015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 4, 1, 2, 1, 3].length) (baseStart_4894015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4894015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4894015 prefixEnd_4894015 := by exact prefixLift 4894015
  have htrace : WordTrace (prefixWord ++ tailWord_4894015) baseStart_4894015 baseEnd_4894015 := by
    simpa [prefixWord, tailWord_4894015, baseEnd_4894015] using wordTrace_append hprefix tailTrace_4894015
  have hstable : (prefixWord ++ tailWord_4894015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4894015).length < 2 ^ (prefixWord ++ tailWord_4894015).sum := by decide
  have hdescent : baseEnd_4894015 < baseStart_4894015 := by decide
  rcases family_descends (prefixWord ++ tailWord_4894015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4894021 : List Nat := [1, 3, 1, 1, 1, 2, 1, 2, 5, 4, 2]
def baseStart_4894021 : Nat := 118140960795 + 4894021 * 2 ^ 59
def prefixEnd_4894021 : Nat := 4983230072969 + 3 ^ 40 * 4894021 * 2
def baseEnd_4894021 : Nat := 2512985106197701854030313

theorem tailTrace_4894021 : CollatzResearch.WordTrace tailWord_4894021 prefixEnd_4894021 2512985106197701854030313 := by
  unfold tailWord_4894021
  simp only [CollatzResearch.WordTrace]
  refine ⟨178499610202805224087905917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118999740135203482725270611 178499610202805224087905917)
  ·
    refine ⟨66937353826051959032964719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 178499610202805224087905917 66937353826051959032964719)
    ·
      refine ⟨100406030739077938549447079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66937353826051959032964719 100406030739077938549447079)
      ·
        refine ⟨150609046108616907824170619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100406030739077938549447079 150609046108616907824170619)
        ·
          refine ⟨225913569162925361736255929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 150609046108616907824170619 225913569162925361736255929)
          ·
            refine ⟨169435176872194021302191947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 225913569162925361736255929 169435176872194021302191947)
            ·
              refine ⟨254152765308291031953287921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 169435176872194021302191947 254152765308291031953287921)
              ·
                refine ⟨190614573981218273964965941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 254152765308291031953287921 190614573981218273964965941)
                ·
                  refine ⟨17870116310739213184215557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 190614573981218273964965941 17870116310739213184215557)
                  ·
                    refine ⟨3350646808263602472040417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17870116310739213184215557 3350646808263602472040417)
                    ·
                      refine ⟨2512985106197701854030313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3350646808263602472040417 2512985106197701854030313)
                      ·
                        rfl

theorem cell23_4894021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 2, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 2, 5, 4, 2].length) (baseStart_4894021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4894021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4894021 prefixEnd_4894021 := by exact prefixLift 4894021
  have htrace : WordTrace (prefixWord ++ tailWord_4894021) baseStart_4894021 baseEnd_4894021 := by
    simpa [prefixWord, tailWord_4894021, baseEnd_4894021] using wordTrace_append hprefix tailTrace_4894021
  have hstable : (prefixWord ++ tailWord_4894021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4894021).length < 2 ^ (prefixWord ++ tailWord_4894021).sum := by decide
  have hdescent : baseEnd_4894021 < baseStart_4894021 := by decide
  rcases family_descends (prefixWord ++ tailWord_4894021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4894071 : List Nat := [1, 1, 3, 1, 1, 2, 5, 1, 2, 3, 3]
def baseStart_4894071 : Nat := 118140960795 + 4894071 * 2 ^ 59
def prefixEnd_4894071 : Nat := 4983230072969 + 3 ^ 40 * 4894071 * 2
def baseEnd_4894071 : Nat := 2513010780230426658405083

theorem tailTrace_4894071 : CollatzResearch.WordTrace tailWord_4894071 prefixEnd_4894071 2513010780230426658405083 := by
  unfold tailWord_4894071
  simp only [CollatzResearch.WordTrace]
  refine ⟨178501433852624082627226067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119000955901749388418150711 178501433852624082627226067)
  ·
    refine ⟨267752150778936123940839101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 178501433852624082627226067 267752150778936123940839101)
    ·
      refine ⟨100407056542101046477814663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 267752150778936123940839101 100407056542101046477814663)
      ·
        refine ⟨150610584813151569716721995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100407056542101046477814663 150610584813151569716721995)
        ·
          refine ⟨225915877219727354575082993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 150610584813151569716721995 225915877219727354575082993)
          ·
            refine ⟨169436907914795515931312245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 225915877219727354575082993 169436907914795515931312245)
            ·
              refine ⟨15884710117012079618560523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 169436907914795515931312245 15884710117012079618560523)
              ·
                refine ⟨23827065175518119427840785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15884710117012079618560523 23827065175518119427840785)
                ·
                  refine ⟨17870298881638589570880589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23827065175518119427840785 17870298881638589570880589)
                  ·
                    refine ⟨6701362080614471089080221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17870298881638589570880589 6701362080614471089080221)
                    ·
                      refine ⟨2513010780230426658405083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6701362080614471089080221 2513010780230426658405083)
                      ·
                        rfl

theorem cell23_4894071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 5, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 5, 1, 2, 3, 3].length) (baseStart_4894071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4894071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4894071 prefixEnd_4894071 := by exact prefixLift 4894071
  have htrace : WordTrace (prefixWord ++ tailWord_4894071) baseStart_4894071 baseEnd_4894071 := by
    simpa [prefixWord, tailWord_4894071, baseEnd_4894071] using wordTrace_append hprefix tailTrace_4894071
  have hstable : (prefixWord ++ tailWord_4894071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4894071).length < 2 ^ (prefixWord ++ tailWord_4894071).sum := by decide
  have hdescent : baseEnd_4894071 < baseStart_4894071 := by decide
  rcases family_descends (prefixWord ++ tailWord_4894071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4894074 : List Nat := [3, 1, 1, 1, 1, 1, 2, 3, 3, 7]
def baseStart_4894074 : Nat := 118140960795 + 4894074 * 2 ^ 59
def prefixEnd_4894074 : Nat := 4983230072969 + 3 ^ 40 * 4894074 * 2
def baseEnd_4894074 : Nat := 837670773557463382222523

theorem tailTrace_4894074 : CollatzResearch.WordTrace tailWord_4894074 prefixEnd_4894074 837670773557463382222523 := by
  unfold tailWord_4894074
  simp only [CollatzResearch.WordTrace]
  refine ⟨44625385817903303534896319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 119001028847742142759723517 44625385817903303534896319)
  ·
    refine ⟨66938078726854955302344479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44625385817903303534896319 66938078726854955302344479)
    ·
      refine ⟨100407118090282432953516719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66938078726854955302344479 100407118090282432953516719)
      ·
        refine ⟨150610677135423649430275079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100407118090282432953516719 150610677135423649430275079)
        ·
          refine ⟨225916015703135474145412619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 150610677135423649430275079 225916015703135474145412619)
          ·
            refine ⟨338874023554703211218118929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 225916015703135474145412619 338874023554703211218118929)
            ·
              refine ⟨254155517666027408413589197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 338874023554703211218118929 254155517666027408413589197)
              ·
                refine ⟨95308319124760278155095949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 254155517666027408413589197 95308319124760278155095949)
                ·
                  refine ⟨35740619671785104308160981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 95308319124760278155095949 35740619671785104308160981)
                  ·
                    refine ⟨837670773557463382222523, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 35740619671785104308160981 837670773557463382222523)
                    ·
                      rfl

theorem cell23_4894074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 3, 3, 7].length) (baseStart_4894074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4894074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4894074 prefixEnd_4894074 := by exact prefixLift 4894074
  have htrace : WordTrace (prefixWord ++ tailWord_4894074) baseStart_4894074 baseEnd_4894074 := by
    simpa [prefixWord, tailWord_4894074, baseEnd_4894074] using wordTrace_append hprefix tailTrace_4894074
  have hstable : (prefixWord ++ tailWord_4894074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4894074).length < 2 ^ (prefixWord ++ tailWord_4894074).sum := by decide
  have hdescent : baseEnd_4894074 < baseStart_4894074 := by decide
  rcases family_descends (prefixWord ++ tailWord_4894074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4894141 : List Nat := [1, 4, 1, 2, 2, 1, 1, 1, 2, 4, 4]
def baseStart_4894141 : Nat := 118140960795 + 4894141 * 2 ^ 59
def prefixEnd_4894141 : Nat := 4983230072969 + 3 ^ 40 * 4894141 * 2
def baseEnd_4894141 : Nat := 2513046723876241384529761

theorem tailTrace_4894141 : CollatzResearch.WordTrace tailWord_4894141 prefixEnd_4894141 2513046723876241384529761 := by
  unfold tailWord_4894141
  simp only [CollatzResearch.WordTrace]
  refine ⟨178503986962370484582274277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119002657974913656388182851 178503986962370484582274277)
  ·
    refine ⟨33469497555444465859176427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 178503986962370484582274277 33469497555444465859176427)
    ·
      refine ⟨50204246333166698788764641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33469497555444465859176427 50204246333166698788764641)
      ·
        refine ⟨37653184749875024091573481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50204246333166698788764641 37653184749875024091573481)
        ·
          refine ⟨28239888562406268068680111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37653184749875024091573481 28239888562406268068680111)
          ·
            refine ⟨42359832843609402103020167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28239888562406268068680111 42359832843609402103020167)
            ·
              refine ⟨63539749265414103154530251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42359832843609402103020167 63539749265414103154530251)
              ·
                refine ⟨95309623898121154731795377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 63539749265414103154530251 95309623898121154731795377)
                ·
                  refine ⟨71482217923590866048846533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 95309623898121154731795377 71482217923590866048846533)
                  ·
                    refine ⟨13402915860673287384158725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 71482217923590866048846533 13402915860673287384158725)
                    ·
                      refine ⟨2513046723876241384529761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13402915860673287384158725 2513046723876241384529761)
                      ·
                        rfl

theorem cell23_4894141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 1, 1, 2, 4, 4].length) (baseStart_4894141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4894141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4894141 prefixEnd_4894141 := by exact prefixLift 4894141
  have htrace : WordTrace (prefixWord ++ tailWord_4894141) baseStart_4894141 baseEnd_4894141 := by
    simpa [prefixWord, tailWord_4894141, baseEnd_4894141] using wordTrace_append hprefix tailTrace_4894141
  have hstable : (prefixWord ++ tailWord_4894141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4894141).length < 2 ^ (prefixWord ++ tailWord_4894141).sum := by decide
  have hdescent : baseEnd_4894141 < baseStart_4894141 := by decide
  rcases family_descends (prefixWord ++ tailWord_4894141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4894155 : List Nat := [1, 1, 1, 1, 3, 3, 5, 3, 1, 4]
def baseStart_4894155 : Nat := 118140960795 + 4894155 * 2 ^ 59
def prefixEnd_4894155 : Nat := 4983230072969 + 3 ^ 40 * 4894155 * 2
def baseEnd_4894155 : Nat := 837684637535134776584899

theorem tailTrace_4894155 : CollatzResearch.WordTrace tailWord_4894155 prefixEnd_4894155 837684637535134776584899 := by
  unfold tailWord_4894155
  simp only [CollatzResearch.WordTrace]
  refine ⟨178504497584319764973283919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119002998389546509982189279 178504497584319764973283919)
  ·
    refine ⟨267756746376479647459925879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 178504497584319764973283919 267756746376479647459925879)
    ·
      refine ⟨401635119564719471189888819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 267756746376479647459925879 401635119564719471189888819)
      ·
        refine ⟨602452679347079206784833229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 401635119564719471189888819 602452679347079206784833229)
        ·
          refine ⟨225919754755154702544312461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 602452679347079206784833229 225919754755154702544312461)
          ·
            refine ⟨84719908033183013454117173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 225919754755154702544312461 84719908033183013454117173)
            ·
              refine ⟨7942491378110907511323485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 84719908033183013454117173 7942491378110907511323485)
              ·
                refine ⟨2978434266791590316746307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7942491378110907511323485 2978434266791590316746307)
                ·
                  refine ⟨4467651400187385475119461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2978434266791590316746307 4467651400187385475119461)
                  ·
                    refine ⟨837684637535134776584899, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4467651400187385475119461 837684637535134776584899)
                    ·
                      rfl

theorem cell23_4894155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 5, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 5, 3, 1, 4].length) (baseStart_4894155 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4894155 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4894155 prefixEnd_4894155 := by exact prefixLift 4894155
  have htrace : WordTrace (prefixWord ++ tailWord_4894155) baseStart_4894155 baseEnd_4894155 := by
    simpa [prefixWord, tailWord_4894155, baseEnd_4894155] using wordTrace_append hprefix tailTrace_4894155
  have hstable : (prefixWord ++ tailWord_4894155).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4894155).length < 2 ^ (prefixWord ++ tailWord_4894155).sum := by decide
  have hdescent : baseEnd_4894155 < baseStart_4894155 := by decide
  rcases family_descends (prefixWord ++ tailWord_4894155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4894188 : List Nat := [2, 2, 1, 1, 2, 1, 2, 4, 1, 5, 2]
def baseStart_4894188 : Nat := 118140960795 + 4894188 * 2 ^ 59
def prefixEnd_4894188 : Nat := 4983230072969 + 3 ^ 40 * 4894188 * 2
def baseEnd_4894188 : Nat := 2513070857467002700642045

theorem tailTrace_4894188 : CollatzResearch.WordTrace tailWord_4894188 prefixEnd_4894188 2513070857467002700642045 := by
  unfold tailWord_4894188
  simp only [CollatzResearch.WordTrace]
  refine ⟨89252850596600105804617609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119003800795466807739490145 89252850596600105804617609)
  ·
    refine ⟨66939637947450079353463207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89252850596600105804617609 66939637947450079353463207)
    ·
      refine ⟨100409456921175119030194811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66939637947450079353463207 100409456921175119030194811)
      ·
        refine ⟨150614185381762678545292217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100409456921175119030194811 150614185381762678545292217)
        ·
          refine ⟨112960639036322008908969163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 150614185381762678545292217 112960639036322008908969163)
          ·
            refine ⟨169440958554483013363453745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 112960639036322008908969163 169440958554483013363453745)
            ·
              refine ⟨127080718915862260022590309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 169440958554483013363453745 127080718915862260022590309)
              ·
                refine ⟨23827634796724173754235683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 127080718915862260022590309 23827634796724173754235683)
                ·
                  refine ⟨35741452195086260631353525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23827634796724173754235683 35741452195086260631353525)
                  ·
                    refine ⟨3350761143289336934189393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 35741452195086260631353525 3350761143289336934189393)
                    ·
                      refine ⟨2513070857467002700642045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3350761143289336934189393 2513070857467002700642045)
                      ·
                        rfl

theorem cell23_4894188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 5, 2].length) (baseStart_4894188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4894188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4894188 prefixEnd_4894188 := by exact prefixLift 4894188
  have htrace : WordTrace (prefixWord ++ tailWord_4894188) baseStart_4894188 baseEnd_4894188 := by
    simpa [prefixWord, tailWord_4894188, baseEnd_4894188] using wordTrace_append hprefix tailTrace_4894188
  have hstable : (prefixWord ++ tailWord_4894188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4894188).length < 2 ^ (prefixWord ++ tailWord_4894188).sum := by decide
  have hdescent : baseEnd_4894188 < baseStart_4894188 := by decide
  rcases family_descends (prefixWord ++ tailWord_4894188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4894205 : List Nat := [1, 4, 1, 1, 1, 4, 1, 3, 2, 3, 2]
def baseStart_4894205 : Nat := 118140960795 + 4894205 * 2 ^ 59
def prefixEnd_4894205 : Nat := 4983230072969 + 3 ^ 40 * 4894205 * 2
def baseEnd_4894205 : Nat := 2513079586638129134129467

theorem tailTrace_4894205 : CollatzResearch.WordTrace tailWord_4894205 prefixEnd_4894205 2513079586638129134129467 := by
  unfold tailWord_4894205
  simp only [CollatzResearch.WordTrace]
  refine ⟨178506321234138623512604069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119004214156092415675069379 178506321234138623512604069)
  ·
    refine ⟨33469935231400991908613263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 178506321234138623512604069 33469935231400991908613263)
    ·
      refine ⟨50204902847101487862919895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33469935231400991908613263 50204902847101487862919895)
      ·
        refine ⟨75307354270652231794379843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50204902847101487862919895 75307354270652231794379843)
        ·
          refine ⟨112961031405978347691569765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75307354270652231794379843 112961031405978347691569765)
          ·
            refine ⟨21180193388620940192169331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 112961031405978347691569765 21180193388620940192169331)
            ·
              refine ⟨31770290082931410288253997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21180193388620940192169331 31770290082931410288253997)
              ·
                refine ⟨11913858781099278858095249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31770290082931410288253997 11913858781099278858095249)
                ·
                  refine ⟨8935394085824459143571437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11913858781099278858095249 8935394085824459143571437)
                  ·
                    refine ⟨3350772782184172178839289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8935394085824459143571437 3350772782184172178839289)
                    ·
                      refine ⟨2513079586638129134129467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3350772782184172178839289 2513079586638129134129467)
                      ·
                        rfl

theorem cell23_4894205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 1, 3, 2, 3, 2].length) (baseStart_4894205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4894205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4894205 prefixEnd_4894205 := by exact prefixLift 4894205
  have htrace : WordTrace (prefixWord ++ tailWord_4894205) baseStart_4894205 baseEnd_4894205 := by
    simpa [prefixWord, tailWord_4894205, baseEnd_4894205] using wordTrace_append hprefix tailTrace_4894205
  have hstable : (prefixWord ++ tailWord_4894205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4894205).length < 2 ^ (prefixWord ++ tailWord_4894205).sum := by decide
  have hdescent : baseEnd_4894205 < baseStart_4894205 := by decide
  rcases family_descends (prefixWord ++ tailWord_4894205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4894229 : List Nat := [1, 3, 2, 1, 3, 2, 4, 2, 1, 1, 3]
def baseStart_4894229 : Nat := 118140960795 + 4894229 * 2 ^ 59
def prefixEnd_4894229 : Nat := 4983230072969 + 3 ^ 40 * 4894229 * 2
def baseEnd_4894229 : Nat := 2513091910173837040229357

theorem tailTrace_4894229 : CollatzResearch.WordTrace tailWord_4894229 prefixEnd_4894229 2513091910173837040229357 := by
  unfold tailWord_4894229
  simp only [CollatzResearch.WordTrace]
  refine ⟨178507196586051675611477741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119004797724034450407651827 178507196586051675611477741)
  ·
    refine ⟨66940198719769378354304153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 178507196586051675611477741 66940198719769378354304153)
    ·
      refine ⟨50205149039827033765728115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66940198719769378354304153 50205149039827033765728115)
      ·
        refine ⟨75307723559740550648592173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50205149039827033765728115 75307723559740550648592173)
        ·
          refine ⟨28240396334902706493222065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 75307723559740550648592173 28240396334902706493222065)
          ·
            refine ⟨21180297251177029869916549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28240396334902706493222065 21180297251177029869916549)
            ·
              refine ⟨3971305734595693100609353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21180297251177029869916549 3971305734595693100609353)
              ·
                refine ⟨2978479300946769825457015, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3971305734595693100609353 2978479300946769825457015)
                ·
                  refine ⟨4467718951420154738185523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2978479300946769825457015 4467718951420154738185523)
                  ·
                    refine ⟨6701578427130232107278285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4467718951420154738185523 6701578427130232107278285)
                    ·
                      refine ⟨2513091910173837040229357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6701578427130232107278285 2513091910173837040229357)
                      ·
                        rfl

theorem cell23_4894229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 4, 2, 1, 1, 3].length) (baseStart_4894229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4894229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4894229 prefixEnd_4894229 := by exact prefixLift 4894229
  have htrace : WordTrace (prefixWord ++ tailWord_4894229) baseStart_4894229 baseEnd_4894229 := by
    simpa [prefixWord, tailWord_4894229, baseEnd_4894229] using wordTrace_append hprefix tailTrace_4894229
  have hstable : (prefixWord ++ tailWord_4894229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4894229).length < 2 ^ (prefixWord ++ tailWord_4894229).sum := by decide
  have hdescent : baseEnd_4894229 < baseStart_4894229 := by decide
  rcases family_descends (prefixWord ++ tailWord_4894229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4894269 : List Nat := [1, 4, 1, 3, 3, 2, 2, 1, 1, 1, 4]
def baseStart_4894269 : Nat := 118140960795 + 4894269 * 2 ^ 59
def prefixEnd_4894269 : Nat := 4983230072969 + 3 ^ 40 * 4894269 * 2
def baseEnd_4894269 : Nat := 2513112449400016883729173

theorem tailTrace_4894269 : CollatzResearch.WordTrace tailWord_4894269 prefixEnd_4894269 2513112449400016883729173 := by
  unfold tailWord_4894269
  simp only [CollatzResearch.WordTrace]
  refine ⟨178508655505906762442933861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119005770337271174961955907 178508655505906762442933861)
  ·
    refine ⟨33470372907357517958050099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 178508655505906762442933861 33470372907357517958050099)
    ·
      refine ⟨50205559361036276937075149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33470372907357517958050099 50205559361036276937075149)
      ·
        refine ⟨18827084760388603851403181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 50205559361036276937075149 18827084760388603851403181)
        ·
          refine ⟨7060156785145726444276193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18827084760388603851403181 7060156785145726444276193)
          ·
            refine ⟨5295117588859294833207145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7060156785145726444276193 5295117588859294833207145)
            ·
              refine ⟨3971338191644471124905359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5295117588859294833207145 3971338191644471124905359)
              ·
                refine ⟨5957007287466706687358039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3971338191644471124905359 5957007287466706687358039)
                ·
                  refine ⟨8935510931200060031037059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5957007287466706687358039 8935510931200060031037059)
                  ·
                    refine ⟨13403266396800090046555589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8935510931200060031037059 13403266396800090046555589)
                    ·
                      refine ⟨2513112449400016883729173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13403266396800090046555589 2513112449400016883729173)
                      ·
                        rfl

theorem cell23_4894269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 2, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 2, 2, 1, 1, 1, 4].length) (baseStart_4894269 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4894269 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4894269 prefixEnd_4894269 := by exact prefixLift 4894269
  have htrace : WordTrace (prefixWord ++ tailWord_4894269) baseStart_4894269 baseEnd_4894269 := by
    simpa [prefixWord, tailWord_4894269, baseEnd_4894269] using wordTrace_append hprefix tailTrace_4894269
  have hstable : (prefixWord ++ tailWord_4894269).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4894269).length < 2 ^ (prefixWord ++ tailWord_4894269).sum := by decide
  have hdescent : baseEnd_4894269 < baseStart_4894269 := by decide
  rcases family_descends (prefixWord ++ tailWord_4894269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4894279 : List Nat := [1, 1, 4, 1, 6, 1, 1, 2, 2, 4]
def baseStart_4894279 : Nat := 118140960795 + 4894279 * 2 ^ 59
def prefixEnd_4894279 : Nat := 4983230072969 + 3 ^ 40 * 4894279 * 2
def baseEnd_4894279 : Nat := 837705861402187281534709

theorem tailTrace_4894279 : CollatzResearch.WordTrace tailWord_4894279 prefixEnd_4894279 837705861402187281534709 := by
  unfold tailWord_4894279
  simp only [CollatzResearch.WordTrace]
  refine ⟨178509020235870534150797891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119006013490580356100531927 178509020235870534150797891)
  ·
    refine ⟨267763530353805801226196837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 178509020235870534150797891 267763530353805801226196837)
    ·
      refine ⟨50205661941338587729911907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 267763530353805801226196837 50205661941338587729911907)
      ·
        refine ⟨75308492912007881594867861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50205661941338587729911907 75308492912007881594867861)
        ·
          refine ⟨3530085605250369449759431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 75308492912007881594867861 3530085605250369449759431)
          ·
            refine ⟨5295128407875554174639147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3530085605250369449759431 5295128407875554174639147)
            ·
              refine ⟨7942692611813331261958721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5295128407875554174639147 7942692611813331261958721)
              ·
                refine ⟨5957019458859998446469041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7942692611813331261958721 5957019458859998446469041)
                ·
                  refine ⟨4467764594144998834851781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5957019458859998446469041 4467764594144998834851781)
                  ·
                    refine ⟨837705861402187281534709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4467764594144998834851781 837705861402187281534709)
                    ·
                      rfl

theorem cell23_4894279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 6, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 6, 1, 1, 2, 2, 4].length) (baseStart_4894279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4894279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4894279 prefixEnd_4894279 := by exact prefixLift 4894279
  have htrace : WordTrace (prefixWord ++ tailWord_4894279) baseStart_4894279 baseEnd_4894279 := by
    simpa [prefixWord, tailWord_4894279, baseEnd_4894279] using wordTrace_append hprefix tailTrace_4894279
  have hstable : (prefixWord ++ tailWord_4894279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4894279).length < 2 ^ (prefixWord ++ tailWord_4894279).sum := by decide
  have hdescent : baseEnd_4894279 < baseStart_4894279 := by decide
  rcases family_descends (prefixWord ++ tailWord_4894279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4894359 : List Nat := [1, 1, 3, 3, 2, 3, 1, 3, 2, 2, 2]
def baseStart_4894359 : Nat := 118140960795 + 4894359 * 2 ^ 59
def prefixEnd_4894359 : Nat := 4983230072969 + 3 ^ 40 * 4894359 * 2
def baseEnd_4894359 : Nat := 2513158662658921531603759

theorem tailTrace_4894359 : CollatzResearch.WordTrace tailWord_4894359 prefixEnd_4894359 2513158662658921531603759 := by
  unfold tailWord_4894359
  simp only [CollatzResearch.WordTrace]
  refine ⟨178511938075580707813710131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119007958717053805209140087 178511938075580707813710131)
  ·
    refine ⟨267767907113371061720565197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 178511938075580707813710131 267767907113371061720565197)
    ·
      refine ⟨100412965167514148145211949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 267767907113371061720565197 100412965167514148145211949)
      ·
        refine ⟨37654861937817805554454481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 100412965167514148145211949 37654861937817805554454481)
        ·
          refine ⟨28241146453363354165840861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37654861937817805554454481 28241146453363354165840861)
          ·
            refine ⟨10590429920011257812190323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28241146453363354165840861 10590429920011257812190323)
            ·
              refine ⟨15885644880016886718285485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10590429920011257812190323 15885644880016886718285485)
              ·
                refine ⟨5957116830006332519357057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15885644880016886718285485 5957116830006332519357057)
                ·
                  refine ⟨4467837622504749389517793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5957116830006332519357057 4467837622504749389517793)
                  ·
                    refine ⟨3350878216878562042138345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4467837622504749389517793 3350878216878562042138345)
                    ·
                      refine ⟨2513158662658921531603759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3350878216878562042138345 2513158662658921531603759)
                      ·
                        rfl

theorem cell23_4894359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 3, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 3, 1, 3, 2, 2, 2].length) (baseStart_4894359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4894359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4894359 prefixEnd_4894359 := by exact prefixLift 4894359
  have htrace : WordTrace (prefixWord ++ tailWord_4894359) baseStart_4894359 baseEnd_4894359 := by
    simpa [prefixWord, tailWord_4894359, baseEnd_4894359] using wordTrace_append hprefix tailTrace_4894359
  have hstable : (prefixWord ++ tailWord_4894359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4894359).length < 2 ^ (prefixWord ++ tailWord_4894359).sum := by decide
  have hdescent : baseEnd_4894359 < baseStart_4894359 := by decide
  rcases family_descends (prefixWord ++ tailWord_4894359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4894425 : List Nat := [1, 2, 1, 2, 3, 3, 1, 1, 5, 4]
def baseStart_4894425 : Nat := 118140960795 + 4894425 * 2 ^ 59
def prefixEnd_4894425 : Nat := 4983230072969 + 3 ^ 40 * 4894425 * 2
def baseEnd_4894425 : Nat := 837730850794039424459485

theorem tailTrace_4894425 : CollatzResearch.WordTrace tailWord_4894425 prefixEnd_4894425 837730850794039424459485 := by
  unfold tailWord_4894425
  simp only [CollatzResearch.WordTrace]
  refine ⟨178514345293341601085612729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119009563528894400723741819 178514345293341601085612729)
  ·
    refine ⟨133885758970006200814209547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 178514345293341601085612729 133885758970006200814209547)
    ·
      refine ⟨200828638455009301221314321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 133885758970006200814209547 200828638455009301221314321)
      ·
        refine ⟨150621478841256975915985741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 200828638455009301221314321 150621478841256975915985741)
        ·
          refine ⟨56483054565471365968494653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 150621478841256975915985741 56483054565471365968494653)
          ·
            refine ⟨21181145462051762238185495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 56483054565471365968494653 21181145462051762238185495)
            ·
              refine ⟨31771718193077643357278243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21181145462051762238185495 31771718193077643357278243)
              ·
                refine ⟨47657577289616465035917365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31771718193077643357278243 47657577289616465035917365)
                ·
                  refine ⟨4467897870901543597117253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 47657577289616465035917365 4467897870901543597117253)
                  ·
                    refine ⟨837730850794039424459485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4467897870901543597117253 837730850794039424459485)
                    ·
                      rfl

theorem cell23_4894425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 1, 1, 5, 4].length) (baseStart_4894425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4894425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4894425 prefixEnd_4894425 := by exact prefixLift 4894425
  have htrace : WordTrace (prefixWord ++ tailWord_4894425) baseStart_4894425 baseEnd_4894425 := by
    simpa [prefixWord, tailWord_4894425, baseEnd_4894425] using wordTrace_append hprefix tailTrace_4894425
  have hstable : (prefixWord ++ tailWord_4894425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4894425).length < 2 ^ (prefixWord ++ tailWord_4894425).sum := by decide
  have hdescent : baseEnd_4894425 < baseStart_4894425 := by decide
  rcases family_descends (prefixWord ++ tailWord_4894425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4894445 : List Nat := [1, 5, 1, 2, 1, 2, 1, 1, 2, 1, 6]
def baseStart_4894445 : Nat := 118140960795 + 4894445 * 2 ^ 59
def prefixEnd_4894445 : Nat := 4983230072969 + 3 ^ 40 * 4894445 * 2
def baseEnd_4894445 : Nat := 2513202821995208195128363

theorem tailTrace_4894445 : CollatzResearch.WordTrace tailWord_4894445 prefixEnd_4894445 2513202821995208195128363 := by
  unfold tailWord_4894445
  simp only [CollatzResearch.WordTrace]
  refine ⟨178515074753269144501340789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119010049835512763000893859 178515074753269144501340789)
  ·
    refine ⟨16735788258118982297000699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 178515074753269144501340789 16735788258118982297000699)
    ·
      refine ⟨25103682387178473445501049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16735788258118982297000699 25103682387178473445501049)
      ·
        refine ⟨18827761790383855084125787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25103682387178473445501049 18827761790383855084125787)
        ·
          refine ⟨28241642685575782626188681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18827761790383855084125787 28241642685575782626188681)
          ·
            refine ⟨21181232014181836969641511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28241642685575782626188681 21181232014181836969641511)
            ·
              refine ⟨31771848021272755454462267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21181232014181836969641511 31771848021272755454462267)
              ·
                refine ⟨47657772031909133181693401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31771848021272755454462267 47657772031909133181693401)
                ·
                  refine ⟨35743329023931849886270051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 47657772031909133181693401 35743329023931849886270051)
                  ·
                    refine ⟨53614993535897774829405077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 35743329023931849886270051 53614993535897774829405077)
                    ·
                      refine ⟨2513202821995208195128363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 53614993535897774829405077 2513202821995208195128363)
                      ·
                        rfl

theorem cell23_4894445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 1, 1, 2, 1, 6].length) (baseStart_4894445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4894445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4894445 prefixEnd_4894445 := by exact prefixLift 4894445
  have htrace : WordTrace (prefixWord ++ tailWord_4894445) baseStart_4894445 baseEnd_4894445 := by
    simpa [prefixWord, tailWord_4894445, baseEnd_4894445] using wordTrace_append hprefix tailTrace_4894445
  have hstable : (prefixWord ++ tailWord_4894445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4894445).length < 2 ^ (prefixWord ++ tailWord_4894445).sum := by decide
  have hdescent : baseEnd_4894445 < baseStart_4894445 := by decide
  rcases family_descends (prefixWord ++ tailWord_4894445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4894455 : List Nat := [1, 1, 3, 1, 1, 1, 7, 2, 6]
def baseStart_4894455 : Nat := 118140960795 + 4894455 * 2 ^ 59
def prefixEnd_4894455 : Nat := 4983230072969 + 3 ^ 40 * 4894455 * 2
def baseEnd_4894455 : Nat := 279245328533528128444813

theorem tailTrace_4894455 : CollatzResearch.WordTrace tailWord_4894455 prefixEnd_4894455 279245328533528128444813 := by
  unfold tailWord_4894455
  simp only [CollatzResearch.WordTrace]
  refine ⟨178515439483232916209204819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119010292988821944139469879 178515439483232916209204819)
  ·
    refine ⟨267773159224849374313807229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 178515439483232916209204819 267773159224849374313807229)
    ·
      refine ⟨100414934709318515367677711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 267773159224849374313807229 100414934709318515367677711)
      ·
        refine ⟨150622402063977773051516567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100414934709318515367677711 150622402063977773051516567)
        ·
          refine ⟨225933603095966659577274851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 150622402063977773051516567 225933603095966659577274851)
          ·
            refine ⟨338900404643949989365912277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 225933603095966659577274851 338900404643949989365912277)
            ·
              refine ⟨7942978233842577875763569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 338900404643949989365912277 7942978233842577875763569)
              ·
                refine ⟨5957233675381933406822677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7942978233842577875763569 5957233675381933406822677)
                ·
                  refine ⟨279245328533528128444813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5957233675381933406822677 279245328533528128444813)
                  ·
                    rfl

theorem cell23_4894455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 7, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 7, 2, 6].length) (baseStart_4894455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4894455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4894455 prefixEnd_4894455 := by exact prefixLift 4894455
  have htrace : WordTrace (prefixWord ++ tailWord_4894455) baseStart_4894455 baseEnd_4894455 := by
    simpa [prefixWord, tailWord_4894455, baseEnd_4894455] using wordTrace_append hprefix tailTrace_4894455
  have hstable : (prefixWord ++ tailWord_4894455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4894455).length < 2 ^ (prefixWord ++ tailWord_4894455).sum := by decide
  have hdescent : baseEnd_4894455 < baseStart_4894455 := by decide
  rcases family_descends (prefixWord ++ tailWord_4894455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4894472 : List Nat := [2, 1, 3, 2, 2, 1, 5, 1, 6]
def baseStart_4894472 : Nat := 118140960795 + 4894472 * 2 ^ 59
def prefixEnd_4894472 : Nat := 4983230072969 + 3 ^ 40 * 4894472 * 2
def baseEnd_4894472 : Nat := 279246298441431065498971

theorem tailTrace_4894472 : CollatzResearch.WordTrace tailWord_4894472 prefixEnd_4894472 279246298441431065498971 := by
  unfold tailWord_4894472
  simp only [CollatzResearch.WordTrace]
  refine ⟨89258029762085664056286835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119010706349447552075049113 89258029762085664056286835)
  ·
    refine ⟨133887044643128496084430253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89258029762085664056286835 133887044643128496084430253)
    ·
      refine ⟨50207641741173186031661345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 133887044643128496084430253 50207641741173186031661345)
      ·
        refine ⟨37655731305879889523746009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50207641741173186031661345 37655731305879889523746009)
        ·
          refine ⟨28241798479409917142809507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37655731305879889523746009 28241798479409917142809507)
          ·
            refine ⟨42362697719114875714214261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28241798479409917142809507 42362697719114875714214261)
            ·
              refine ⟨3971502911167019598207587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 42362697719114875714214261 3971502911167019598207587)
              ·
                refine ⟨5957254366750529397311381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3971502911167019598207587 5957254366750529397311381)
                ·
                  refine ⟨279246298441431065498971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5957254366750529397311381 279246298441431065498971)
                  ·
                    rfl

theorem cell23_4894472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 5, 1, 6].length) (baseStart_4894472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4894472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4894472 prefixEnd_4894472 := by exact prefixLift 4894472
  have htrace : WordTrace (prefixWord ++ tailWord_4894472) baseStart_4894472 baseEnd_4894472 := by
    simpa [prefixWord, tailWord_4894472, baseEnd_4894472] using wordTrace_append hprefix tailTrace_4894472
  have hstable : (prefixWord ++ tailWord_4894472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4894472).length < 2 ^ (prefixWord ++ tailWord_4894472).sum := by decide
  have hdescent : baseEnd_4894472 < baseStart_4894472 := by decide
  rcases family_descends (prefixWord ++ tailWord_4894472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4894492 : List Nat := [2, 2, 3, 1, 1, 2, 1, 3, 1, 5, 2]
def baseStart_4894492 : Nat := 118140960795 + 4894492 * 2 ^ 59
def prefixEnd_4894492 : Nat := 4983230072969 + 3 ^ 40 * 4894492 * 2
def baseEnd_4894492 : Nat := 2513226955585969511240647

theorem tailTrace_4894492 : CollatzResearch.WordTrace tailWord_4894492 prefixEnd_4894492 2513226955585969511240647 := by
  unfold tailWord_4894492
  simp only [CollatzResearch.WordTrace]
  refine ⟨89258394492049435764150865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119011192656065914352201153 89258394492049435764150865)
  ·
    refine ⟨66943795869037076823113149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89258394492049435764150865 66943795869037076823113149)
    ·
      refine ⟨25103923450888903808667431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 66943795869037076823113149 25103923450888903808667431)
      ·
        refine ⟨37655885176333355713001147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25103923450888903808667431 37655885176333355713001147)
        ·
          refine ⟨56483827764500033569501721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37655885176333355713001147 56483827764500033569501721)
          ·
            refine ⟨42362870823375025177126291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56483827764500033569501721 42362870823375025177126291)
            ·
              refine ⟨63544306235062537765689437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42362870823375025177126291 63544306235062537765689437)
              ·
                refine ⟨23829114838148451662133539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 63544306235062537765689437 23829114838148451662133539)
                ·
                  refine ⟨35743672257222677493200309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23829114838148451662133539 35743672257222677493200309)
                  ·
                    refine ⟨3350969274114626014987529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 35743672257222677493200309 3350969274114626014987529)
                    ·
                      refine ⟨2513226955585969511240647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3350969274114626014987529 2513226955585969511240647)
                      ·
                        rfl

theorem cell23_4894492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 1, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 1, 3, 1, 5, 2].length) (baseStart_4894492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4894492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4894492 prefixEnd_4894492 := by exact prefixLift 4894492
  have htrace : WordTrace (prefixWord ++ tailWord_4894492) baseStart_4894492 baseEnd_4894492 := by
    simpa [prefixWord, tailWord_4894492, baseEnd_4894492] using wordTrace_append hprefix tailTrace_4894492
  have hstable : (prefixWord ++ tailWord_4894492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4894492).length < 2 ^ (prefixWord ++ tailWord_4894492).sum := by decide
  have hdescent : baseEnd_4894492 < baseStart_4894492 := by decide
  rcases family_descends (prefixWord ++ tailWord_4894492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4894516 : List Nat := [2, 5, 1, 1, 2, 1, 3, 1, 3, 1, 3]
def baseStart_4894516 : Nat := 118140960795 + 4894516 * 2 ^ 59
def prefixEnd_4894516 : Nat := 4983230072969 + 3 ^ 40 * 4894516 * 2
def baseEnd_4894516 : Nat := 2513239279121677417340537

theorem tailTrace_4894516 : CollatzResearch.WordTrace tailWord_4894516 prefixEnd_4894516 2513239279121677417340537 := by
  unfold tailWord_4894516
  simp only [CollatzResearch.WordTrace]
  refine ⟨89258832168005961813587701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119011776224007949084783601 89258832168005961813587701)
  ·
    refine ⟨8368015515750558920023847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 89258832168005961813587701 8368015515750558920023847)
    ·
      refine ⟨12552023273625838380035771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8368015515750558920023847 12552023273625838380035771)
      ·
        refine ⟨18828034910438757570053657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12552023273625838380035771 18828034910438757570053657)
        ·
          refine ⟨14121026182829068177540243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18828034910438757570053657 14121026182829068177540243)
          ·
            refine ⟨21181539274243602266310365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14121026182829068177540243 21181539274243602266310365)
            ·
              refine ⟨7943077227841350849866387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21181539274243602266310365 7943077227841350849866387)
              ·
                refine ⟨11914615841762026274799581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7943077227841350849866387 11914615841762026274799581)
                ·
                  refine ⟨4467980940660759853049843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11914615841762026274799581 4467980940660759853049843)
                  ·
                    refine ⟨6701971410991139779574765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4467980940660759853049843 6701971410991139779574765)
                    ·
                      refine ⟨2513239279121677417340537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6701971410991139779574765 2513239279121677417340537)
                      ·
                        rfl

theorem cell23_4894516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 3, 1, 3, 1, 3].length) (baseStart_4894516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4894516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4894516 prefixEnd_4894516 := by exact prefixLift 4894516
  have htrace : WordTrace (prefixWord ++ tailWord_4894516) baseStart_4894516 baseEnd_4894516 := by
    simpa [prefixWord, tailWord_4894516, baseEnd_4894516] using wordTrace_append hprefix tailTrace_4894516
  have hstable : (prefixWord ++ tailWord_4894516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4894516).length < 2 ^ (prefixWord ++ tailWord_4894516).sum := by decide
  have hdescent : baseEnd_4894516 < baseStart_4894516 := by decide
  rcases family_descends (prefixWord ++ tailWord_4894516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4894535 : List Nat := [1, 1, 4, 1, 2, 1, 4, 1, 1, 1, 6]
def baseStart_4894535 : Nat := 118140960795 + 4894535 * 2 ^ 59
def prefixEnd_4894535 : Nat := 4983230072969 + 3 ^ 40 * 4894535 * 2
def baseEnd_4894535 : Nat := 2513249035254112843002949

theorem tailTrace_4894535 : CollatzResearch.WordTrace tailWord_4894535 prefixEnd_4894535 2513249035254112843002949 := by
  unfold tailWord_4894535
  simp only [CollatzResearch.WordTrace]
  refine ⟨178518357322943089872117059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119012238215295393248078039 178518357322943089872117059)
  ·
    refine ⟨267777535984414634808175589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 178518357322943089872117059 267777535984414634808175589)
    ·
      refine ⟨50208287997077744026532923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 267777535984414634808175589 50208287997077744026532923)
      ·
        refine ⟨75312431995616616039799385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50208287997077744026532923 75312431995616616039799385)
        ·
          refine ⟨56484323996712462029849539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 75312431995616616039799385 56484323996712462029849539)
          ·
            refine ⟨84726485995068693044774309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56484323996712462029849539 84726485995068693044774309)
            ·
              refine ⟨15886216124075379945895183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 84726485995068693044774309 15886216124075379945895183)
              ·
                refine ⟨23829324186113069918842775, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15886216124075379945895183 23829324186113069918842775)
                ·
                  refine ⟨35743986279169604878264163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23829324186113069918842775 35743986279169604878264163)
                  ·
                    refine ⟨53615979418754407317396245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 35743986279169604878264163 53615979418754407317396245)
                    ·
                      refine ⟨2513249035254112843002949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 53615979418754407317396245 2513249035254112843002949)
                      ·
                        rfl

theorem cell23_4894535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 4, 1, 1, 1, 6].length) (baseStart_4894535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4894535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4894535 prefixEnd_4894535 := by exact prefixLift 4894535
  have htrace : WordTrace (prefixWord ++ tailWord_4894535) baseStart_4894535 baseEnd_4894535 := by
    simpa [prefixWord, tailWord_4894535, baseEnd_4894535] using wordTrace_append hprefix tailTrace_4894535
  have hstable : (prefixWord ++ tailWord_4894535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4894535).length < 2 ^ (prefixWord ++ tailWord_4894535).sum := by decide
  have hdescent : baseEnd_4894535 < baseStart_4894535 := by decide
  rcases family_descends (prefixWord ++ tailWord_4894535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4894545 : List Nat := [1, 2, 2, 1, 5, 1, 2, 9]
def baseStart_4894545 : Nat := 118140960795 + 4894545 * 2 ^ 59
def prefixEnd_4894545 : Nat := 4983230072969 + 3 ^ 40 * 4894545 * 2
def baseEnd_4894545 : Nat := 93083487780024363106589

theorem tailTrace_4894545 : CollatzResearch.WordTrace tailWord_4894545 prefixEnd_4894545 93083487780024363106589 := by
  unfold tailWord_4894545
  simp only [CollatzResearch.WordTrace]
  refine ⟨178518722052906861579981089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119012481368604574386654059 178518722052906861579981089)
  ·
    refine ⟨133889041539680146184985817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 178518722052906861579981089 133889041539680146184985817)
    ·
      refine ⟨100416781154760109638739363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 133889041539680146184985817 100416781154760109638739363)
      ·
        refine ⟨150625171732140164458109045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100416781154760109638739363 150625171732140164458109045)
        ·
          refine ⟨14121109849888140417947723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 150625171732140164458109045 14121109849888140417947723)
          ·
            refine ⟨21181664774832210626921585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14121109849888140417947723 21181664774832210626921585)
            ·
              refine ⟨15886248581124157970191189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21181664774832210626921585 15886248581124157970191189)
              ·
                refine ⟨93083487780024363106589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 15886248581124157970191189 93083487780024363106589)
                ·
                  rfl

theorem cell23_4894545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 2, 9].length) (baseStart_4894545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4894545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4894545 prefixEnd_4894545 := by exact prefixLift 4894545
  have htrace : WordTrace (prefixWord ++ tailWord_4894545) baseStart_4894545 baseEnd_4894545 := by
    simpa [prefixWord, tailWord_4894545, baseEnd_4894545] using wordTrace_append hprefix tailTrace_4894545
  have hstable : (prefixWord ++ tailWord_4894545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4894545).length < 2 ^ (prefixWord ++ tailWord_4894545).sum := by decide
  have hdescent : baseEnd_4894545 < baseStart_4894545 := by decide
  rcases family_descends (prefixWord ++ tailWord_4894545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4894623 : List Nat := [1, 1, 2, 5, 3, 2, 1, 2, 2, 1, 3]
def baseStart_4894623 : Nat := 118140960795 + 4894623 * 2 ^ 59
def prefixEnd_4894623 : Nat := 4983230072969 + 3 ^ 40 * 4894623 * 2
def baseEnd_4894623 : Nat := 2513294221551708498702545

theorem tailTrace_4894623 : CollatzResearch.WordTrace tailWord_4894623 prefixEnd_4894623 2513294221551708498702545 := by
  unfold tailWord_4894623
  simp only [CollatzResearch.WordTrace]
  refine ⟨178521566946624280901320523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119014377964416187267547015 178521566946624280901320523)
  ·
    refine ⟨267782350419936421351980785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 178521566946624280901320523 267782350419936421351980785)
    ·
      refine ⟨200836762814952316013985589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 267782350419936421351980785 200836762814952316013985589)
      ·
        refine ⟨18828446513901779626311149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 200836762814952316013985589 18828446513901779626311149)
        ·
          refine ⟨7060667442713167359866681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18828446513901779626311149 7060667442713167359866681)
          ·
            refine ⟨5295500582034875519900011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7060667442713167359866681 5295500582034875519900011)
            ·
              refine ⟨7943250873052313279850017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5295500582034875519900011 7943250873052313279850017)
              ·
                refine ⟨5957438154789234959887513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7943250873052313279850017 5957438154789234959887513)
                ·
                  refine ⟨4468078616091926219915635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5957438154789234959887513 4468078616091926219915635)
                  ·
                    refine ⟨6702117924137889329873453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4468078616091926219915635 6702117924137889329873453)
                    ·
                      refine ⟨2513294221551708498702545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6702117924137889329873453 2513294221551708498702545)
                      ·
                        rfl

theorem cell23_4894623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 2, 1, 2, 2, 1, 3].length) (baseStart_4894623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4894623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4894623 prefixEnd_4894623 := by exact prefixLift 4894623
  have htrace : WordTrace (prefixWord ++ tailWord_4894623) baseStart_4894623 baseEnd_4894623 := by
    simpa [prefixWord, tailWord_4894623, baseEnd_4894623] using wordTrace_append hprefix tailTrace_4894623
  have hstable : (prefixWord ++ tailWord_4894623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4894623).length < 2 ^ (prefixWord ++ tailWord_4894623).sum := by decide
  have hdescent : baseEnd_4894623 < baseStart_4894623 := by decide
  rcases family_descends (prefixWord ++ tailWord_4894623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4894692 : List Nat := [2, 3, 1, 1, 1, 1, 5, 1, 1, 2, 5]
def baseStart_4894692 : Nat := 118140960795 + 4894692 * 2 ^ 59
def prefixEnd_4894692 : Nat := 4983230072969 + 3 ^ 40 * 4894692 * 2
def baseEnd_4894692 : Nat := 2513329651716868728739727

theorem tailTrace_4894692 : CollatzResearch.WordTrace tailWord_4894692 prefixEnd_4894692 2513329651716868728739727 := by
  unfold tailWord_4894692
  simp only [CollatzResearch.WordTrace]
  refine ⟨89262041791687152842791165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119016055722249537123721553 89262041791687152842791165)
  ·
    refine ⟨33473265671882682316046687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 89262041791687152842791165 33473265671882682316046687)
    ·
      refine ⟨50209898507824023474070031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33473265671882682316046687 50209898507824023474070031)
      ·
        refine ⟨75314847761736035211105047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50209898507824023474070031 75314847761736035211105047)
        ·
          refine ⟨112972271642604052816657571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75314847761736035211105047 112972271642604052816657571)
          ·
            refine ⟨169458407463906079224986357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 112972271642604052816657571 169458407463906079224986357)
            ·
              refine ⟨15886725699741194927342471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 169458407463906079224986357 15886725699741194927342471)
              ·
                refine ⟨23830088549611792391013707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15886725699741194927342471 23830088549611792391013707)
                ·
                  refine ⟨35745132824417688586520561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23830088549611792391013707 35745132824417688586520561)
                  ·
                    refine ⟨26808849618313266439890421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 35745132824417688586520561 26808849618313266439890421)
                    ·
                      refine ⟨2513329651716868728739727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26808849618313266439890421 2513329651716868728739727)
                      ·
                        rfl

theorem cell23_4894692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 5, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 5, 1, 1, 2, 5].length) (baseStart_4894692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4894692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4894692 prefixEnd_4894692 := by exact prefixLift 4894692
  have htrace : WordTrace (prefixWord ++ tailWord_4894692) baseStart_4894692 baseEnd_4894692 := by
    simpa [prefixWord, tailWord_4894692, baseEnd_4894692] using wordTrace_append hprefix tailTrace_4894692
  have hstable : (prefixWord ++ tailWord_4894692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4894692).length < 2 ^ (prefixWord ++ tailWord_4894692).sum := by decide
  have hdescent : baseEnd_4894692 < baseStart_4894692 := by decide
  rcases family_descends (prefixWord ++ tailWord_4894692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4894732 : List Nat := [2, 2, 1, 2, 3, 1, 2, 1, 2, 1, 6]
def baseStart_4894732 : Nat := 118140960795 + 4894732 * 2 ^ 59
def prefixEnd_4894732 : Nat := 4983230072969 + 3 ^ 40 * 4894732 * 2
def baseEnd_4894732 : Nat := 2513350190943048572239543

theorem tailTrace_4894732 : CollatzResearch.WordTrace tailWord_4894732 prefixEnd_4894732 2513350190943048572239543 := by
  unfold tailWord_4894732
  simp only [CollatzResearch.WordTrace]
  refine ⟨89262771251614696258519225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119017028335486261678025633 89262771251614696258519225)
  ·
    refine ⟨66947078438711022193889419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89262771251614696258519225 66947078438711022193889419)
    ·
      refine ⟨100420617658066533290834129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66947078438711022193889419 100420617658066533290834129)
      ·
        refine ⟨75315463243549899968125597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 100420617658066533290834129 75315463243549899968125597)
        ·
          refine ⟨28243298716331212488047099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 75315463243549899968125597 28243298716331212488047099)
          ·
            refine ⟨42364948074496818732070649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28243298716331212488047099 42364948074496818732070649)
            ·
              refine ⟨31773711055872614049052987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42364948074496818732070649 31773711055872614049052987)
              ·
                refine ⟨47660566583808921073579481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31773711055872614049052987 47660566583808921073579481)
                ·
                  refine ⟨35745424937856690805184611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 47660566583808921073579481 35745424937856690805184611)
                  ·
                    refine ⟨53618137406785036207776917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 35745424937856690805184611 53618137406785036207776917)
                    ·
                      refine ⟨2513350190943048572239543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 53618137406785036207776917 2513350190943048572239543)
                      ·
                        rfl

theorem cell23_4894732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 2, 1, 2, 1, 6].length) (baseStart_4894732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4894732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4894732 prefixEnd_4894732 := by exact prefixLift 4894732
  have htrace : WordTrace (prefixWord ++ tailWord_4894732) baseStart_4894732 baseEnd_4894732 := by
    simpa [prefixWord, tailWord_4894732, baseEnd_4894732] using wordTrace_append hprefix tailTrace_4894732
  have hstable : (prefixWord ++ tailWord_4894732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4894732).length < 2 ^ (prefixWord ++ tailWord_4894732).sum := by decide
  have hdescent : baseEnd_4894732 < baseStart_4894732 := by decide
  rcases family_descends (prefixWord ++ tailWord_4894732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4894739 : List Nat := [1, 1, 1, 2, 1, 4, 4, 2, 2, 2, 3]
def baseStart_4894739 : Nat := 118140960795 + 4894739 * 2 ^ 59
def prefixEnd_4894739 : Nat := 4983230072969 + 3 ^ 40 * 4894739 * 2
def baseEnd_4894739 : Nat := 2513353785307630044852011

theorem tailTrace_4894739 : CollatzResearch.WordTrace tailWord_4894739 prefixEnd_4894739 2513353785307630044852011 := by
  unfold tailWord_4894739
  simp only [CollatzResearch.WordTrace]
  refine ⟨178525797814204032712543271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119017198542802688475028847 178525797814204032712543271)
  ·
    refine ⟨267788696721306049068814907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 178525797814204032712543271 267788696721306049068814907)
    ·
      refine ⟨401683045081959073603222361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 267788696721306049068814907 401683045081959073603222361)
      ·
        refine ⟨301262283811469305202416771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 401683045081959073603222361 301262283811469305202416771)
        ·
          refine ⟨451893425717203957803625157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 301262283811469305202416771 451893425717203957803625157)
          ·
            refine ⟨84730017321975742088179717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 451893425717203957803625157 84730017321975742088179717)
            ·
              refine ⟨15886878247870451641533697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 84730017321975742088179717 15886878247870451641533697)
              ·
                refine ⟨11915158685902838731150273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15886878247870451641533697 11915158685902838731150273)
                ·
                  refine ⟨8936369014427129048362705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11915158685902838731150273 8936369014427129048362705)
                  ·
                    refine ⟨6702276760820346786272029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8936369014427129048362705 6702276760820346786272029)
                    ·
                      refine ⟨2513353785307630044852011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6702276760820346786272029 2513353785307630044852011)
                      ·
                        rfl

theorem cell23_4894739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 4, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 4, 2, 2, 2, 3].length) (baseStart_4894739 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4894739 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4894739 prefixEnd_4894739 := by exact prefixLift 4894739
  have htrace : WordTrace (prefixWord ++ tailWord_4894739) baseStart_4894739 baseEnd_4894739 := by
    simpa [prefixWord, tailWord_4894739, baseEnd_4894739] using wordTrace_append hprefix tailTrace_4894739
  have hstable : (prefixWord ++ tailWord_4894739).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4894739).length < 2 ^ (prefixWord ++ tailWord_4894739).sum := by decide
  have hdescent : baseEnd_4894739 < baseStart_4894739 := by decide
  rcases family_descends (prefixWord ++ tailWord_4894739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4894779 : List Nat := [1, 1, 1, 1, 1, 2, 1, 7, 1, 5, 2]
def baseStart_4894779 : Nat := 118140960795 + 4894779 * 2 ^ 59
def prefixEnd_4894779 : Nat := 4983230072969 + 3 ^ 40 * 4894779 * 2
def baseEnd_4894779 : Nat := 2513374324533809888351827

theorem tailTrace_4894779 : CollatzResearch.WordTrace tailWord_4894779 prefixEnd_4894779 2513374324533809888351827 := by
  unfold tailWord_4894779
  simp only [CollatzResearch.WordTrace]
  refine ⟨178527256734059119543999391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119018171156039413029332927 178527256734059119543999391)
  ·
    refine ⟨267790885101088679315999087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 178527256734059119543999391 267790885101088679315999087)
    ·
      refine ⟨401686327651633018973998631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 267790885101088679315999087 401686327651633018973998631)
      ·
        refine ⟨602529491477449528460997947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 401686327651633018973998631 602529491477449528460997947)
        ·
          refine ⟨903794237216174292691496921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 602529491477449528460997947 903794237216174292691496921)
          ·
            refine ⟨677845677912130719518622691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 903794237216174292691496921 677845677912130719518622691)
            ·
              refine ⟨1016768516868196079277934037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 677845677912130719518622691 1016768516868196079277934037)
              ·
                refine ⟨23830512114098345608076579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1016768516868196079277934037 23830512114098345608076579)
                ·
                  refine ⟨35745768171147518412114869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23830512114098345608076579 35745768171147518412114869)
                  ·
                    refine ⟨3351165766045079851135769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 35745768171147518412114869 3351165766045079851135769)
                    ·
                      refine ⟨2513374324533809888351827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3351165766045079851135769 2513374324533809888351827)
                      ·
                        rfl

theorem cell23_4894779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 7, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 7, 1, 5, 2].length) (baseStart_4894779 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4894779 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4894779 prefixEnd_4894779 := by exact prefixLift 4894779
  have htrace : WordTrace (prefixWord ++ tailWord_4894779) baseStart_4894779 baseEnd_4894779 := by
    simpa [prefixWord, tailWord_4894779, baseEnd_4894779] using wordTrace_append hprefix tailTrace_4894779
  have hstable : (prefixWord ++ tailWord_4894779).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4894779).length < 2 ^ (prefixWord ++ tailWord_4894779).sum := by decide
  have hdescent : baseEnd_4894779 < baseStart_4894779 := by decide
  rcases family_descends (prefixWord ++ tailWord_4894779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4894796 : List Nat := [2, 2, 1, 3, 1, 1, 2, 4, 2, 3, 2]
def baseStart_4894796 : Nat := 118140960795 + 4894796 * 2 ^ 59
def prefixEnd_4894796 : Nat := 4983230072969 + 3 ^ 40 * 4894796 * 2
def baseEnd_4894796 : Nat := 2513383053704936321839249

theorem tailTrace_4894796 : CollatzResearch.WordTrace tailWord_4894796 prefixEnd_4894796 2513383053704936321839249 := by
  unfold tailWord_4894796
  simp only [CollatzResearch.WordTrace]
  refine ⟨89263938387498765723684121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119018584516665020964912161 89263938387498765723684121)
  ·
    refine ⟨66947953790624074292763091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89263938387498765723684121 66947953790624074292763091)
    ·
      refine ⟨100421930685936111439144637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66947953790624074292763091 100421930685936111439144637)
      ·
        refine ⟨37658224007226041789679239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 100421930685936111439144637 37658224007226041789679239)
        ·
          refine ⟨56487336010839062684518859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37658224007226041789679239 56487336010839062684518859)
          ·
            refine ⟨84731004016258594026778289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56487336010839062684518859 84731004016258594026778289)
            ·
              refine ⟨63548253012193945520083717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 84731004016258594026778289 63548253012193945520083717)
              ·
                refine ⟨11915297439786364785015697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 63548253012193945520083717 11915297439786364785015697)
                ·
                  refine ⟨8936473079839773588761773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11915297439786364785015697 8936473079839773588761773)
                  ·
                    refine ⟨3351177404939915095785665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8936473079839773588761773 3351177404939915095785665)
                    ·
                      refine ⟨2513383053704936321839249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3351177404939915095785665 2513383053704936321839249)
                      ·
                        rfl

theorem cell23_4894796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 2, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 2, 4, 2, 3, 2].length) (baseStart_4894796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4894796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4894796 prefixEnd_4894796 := by exact prefixLift 4894796
  have htrace : WordTrace (prefixWord ++ tailWord_4894796) baseStart_4894796 baseEnd_4894796 := by
    simpa [prefixWord, tailWord_4894796, baseEnd_4894796] using wordTrace_append hprefix tailTrace_4894796
  have hstable : (prefixWord ++ tailWord_4894796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4894796).length < 2 ^ (prefixWord ++ tailWord_4894796).sum := by decide
  have hdescent : baseEnd_4894796 < baseStart_4894796 := by decide
  rcases family_descends (prefixWord ++ tailWord_4894796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4894813 : List Nat := [1, 4, 4, 1, 1, 1, 1, 2, 1, 5, 2]
def baseStart_4894813 : Nat := 118140960795 + 4894813 * 2 ^ 59
def prefixEnd_4894813 : Nat := 4983230072969 + 3 ^ 40 * 4894813 * 2
def baseEnd_4894813 : Nat := 2513391782876062755326671

theorem tailTrace_4894813 : CollatzResearch.WordTrace tailWord_4894813 prefixEnd_4894813 2513391782876062755326671 := by
  unfold tailWord_4894813
  simp only [CollatzResearch.WordTrace]
  refine ⟨178528496815935943350737093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119018997877290628900491395 178528496815935943350737093)
  ·
    refine ⟨33474093152987989378263205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 178528496815935943350737093 33474093152987989378263205)
    ·
      refine ⟨6276392466185248008424351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 33474093152987989378263205 6276392466185248008424351)
      ·
        refine ⟨9414588699277872012636527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6276392466185248008424351 9414588699277872012636527)
        ·
          refine ⟨14121883048916808018954791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9414588699277872012636527 14121883048916808018954791)
          ·
            refine ⟨21182824573375212028432187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14121883048916808018954791 21182824573375212028432187)
            ·
              refine ⟨31774236860062818042648281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21182824573375212028432187 31774236860062818042648281)
              ·
                refine ⟨23830677645047113531986211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31774236860062818042648281 23830677645047113531986211)
                ·
                  refine ⟨35746016467570670297979317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23830677645047113531986211 35746016467570670297979317)
                  ·
                    refine ⟨3351189043834750340435561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 35746016467570670297979317 3351189043834750340435561)
                    ·
                      refine ⟨2513391782876062755326671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3351189043834750340435561 2513391782876062755326671)
                      ·
                        rfl

theorem cell23_4894813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 1, 2, 1, 5, 2].length) (baseStart_4894813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4894813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4894813 prefixEnd_4894813 := by exact prefixLift 4894813
  have htrace : WordTrace (prefixWord ++ tailWord_4894813) baseStart_4894813 baseEnd_4894813 := by
    simpa [prefixWord, tailWord_4894813, baseEnd_4894813] using wordTrace_append hprefix tailTrace_4894813
  have hstable : (prefixWord ++ tailWord_4894813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4894813).length < 2 ^ (prefixWord ++ tailWord_4894813).sum := by decide
  have hdescent : baseEnd_4894813 < baseStart_4894813 := by decide
  rcases family_descends (prefixWord ++ tailWord_4894813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4894819 : List Nat := [1, 1, 1, 5, 1, 1, 5, 1, 1, 6]
def baseStart_4894819 : Nat := 118140960795 + 4894819 * 2 ^ 59
def prefixEnd_4894819 : Nat := 4983230072969 + 3 ^ 40 * 4894819 * 2
def baseEnd_4894819 : Nat := 837798287919996577283881

theorem tailTrace_4894819 : CollatzResearch.WordTrace tailWord_4894819 prefixEnd_4894819 837798287919996577283881 := by
  unfold tailWord_4894819
  simp only [CollatzResearch.WordTrace]
  refine ⟨178528715653914206375455511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119019143769276137583637007 178528715653914206375455511)
  ·
    refine ⟨267793073480871309563183267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 178528715653914206375455511 267793073480871309563183267)
    ·
      refine ⟨401689610221306964344774901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 267793073480871309563183267 401689610221306964344774901)
      ·
        refine ⟨37658400958247527907322647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 401689610221306964344774901 37658400958247527907322647)
        ·
          refine ⟨56487601437371291860983971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37658400958247527907322647 56487601437371291860983971)
          ·
            refine ⟨84731402156056937791475957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56487601437371291860983971 84731402156056937791475957)
            ·
              refine ⟨7943568952130337917950871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 84731402156056937791475957 7943568952130337917950871)
              ·
                refine ⟨11915353428195506876926307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7943568952130337917950871 11915353428195506876926307)
                ·
                  refine ⟨17873030142293260315389461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11915353428195506876926307 17873030142293260315389461)
                  ·
                    refine ⟨837798287919996577283881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17873030142293260315389461 837798287919996577283881)
                    ·
                      rfl

theorem cell23_4894819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 5, 1, 1, 6].length) (baseStart_4894819 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4894819 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4894819 prefixEnd_4894819 := by exact prefixLift 4894819
  have htrace : WordTrace (prefixWord ++ tailWord_4894819) baseStart_4894819 baseEnd_4894819 := by
    simpa [prefixWord, tailWord_4894819, baseEnd_4894819] using wordTrace_append hprefix tailTrace_4894819
  have hstable : (prefixWord ++ tailWord_4894819).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4894819).length < 2 ^ (prefixWord ++ tailWord_4894819).sum := by decide
  have hdescent : baseEnd_4894819 < baseStart_4894819 := by decide
  rcases family_descends (prefixWord ++ tailWord_4894819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4894829 : List Nat := [1, 5, 1, 1, 2, 1, 1, 2, 3, 1, 5]
def baseStart_4894829 : Nat := 118140960795 + 4894829 * 2 ^ 59
def prefixEnd_4894829 : Nat := 4983230072969 + 3 ^ 40 * 4894829 * 2
def baseEnd_4894829 : Nat := 2513399998566534692726597

theorem tailTrace_4894829 : CollatzResearch.WordTrace tailWord_4894829 prefixEnd_4894829 2513399998566534692726597 := by
  unfold tailWord_4894829
  simp only [CollatzResearch.WordTrace]
  refine ⟨178529080383877978083319541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119019386922585318722213027 178529080383877978083319541)
  ·
    refine ⟨16737101285988560445311207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 178529080383877978083319541 16737101285988560445311207)
    ·
      refine ⟨25105651928982840667966811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16737101285988560445311207 25105651928982840667966811)
      ·
        refine ⟨37658477893474261001950217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25105651928982840667966811 37658477893474261001950217)
        ·
          refine ⟨28243858420105695751462663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37658477893474261001950217 28243858420105695751462663)
          ·
            refine ⟨42365787630158543627193995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28243858420105695751462663 42365787630158543627193995)
            ·
              refine ⟨63548681445237815440790993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42365787630158543627193995 63548681445237815440790993)
              ·
                refine ⟨47661511083928361580593245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 63548681445237815440790993 47661511083928361580593245)
                ·
                  refine ⟨17873066656473135592722467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 47661511083928361580593245 17873066656473135592722467)
                  ·
                    refine ⟨26809599984709703389083701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17873066656473135592722467 26809599984709703389083701)
                    ·
                      refine ⟨2513399998566534692726597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26809599984709703389083701 2513399998566534692726597)
                      ·
                        rfl

theorem cell23_4894829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 1, 2, 3, 1, 5].length) (baseStart_4894829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4894829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4894829 prefixEnd_4894829 := by exact prefixLift 4894829
  have htrace : WordTrace (prefixWord ++ tailWord_4894829) baseStart_4894829 baseEnd_4894829 := by
    simpa [prefixWord, tailWord_4894829, baseEnd_4894829] using wordTrace_append hprefix tailTrace_4894829
  have hstable : (prefixWord ++ tailWord_4894829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4894829).length < 2 ^ (prefixWord ++ tailWord_4894829).sum := by decide
  have hdescent : baseEnd_4894829 < baseStart_4894829 := by decide
  rcases family_descends (prefixWord ++ tailWord_4894829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4894876 : List Nat := [2, 2, 3, 2, 1, 1, 2, 3, 1, 3, 3]
def baseStart_4894876 : Nat := 118140960795 + 4894876 * 2 ^ 59
def prefixEnd_4894876 : Nat := 4983230072969 + 3 ^ 40 * 4894876 * 2
def baseEnd_4894876 : Nat := 2513424132157296008838881

theorem tailTrace_4894876 : CollatzResearch.WordTrace tailWord_4894876 prefixEnd_4894876 2513424132157296008838881 := by
  unfold tailWord_4894876
  simp only [CollatzResearch.WordTrace]
  refine ⟨89265397307353852555140241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119020529743138470073520321 89265397307353852555140241)
  ·
    refine ⟨66949047980515389416355181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89265397307353852555140241 66949047980515389416355181)
    ·
      refine ⟨25105892992693271031133193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 66949047980515389416355181 25105892992693271031133193)
      ·
        refine ⟨18829419744519953273349895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25105892992693271031133193 18829419744519953273349895)
        ·
          refine ⟨28244129616779929910024843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18829419744519953273349895 28244129616779929910024843)
          ·
            refine ⟨42366194425169894865037265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28244129616779929910024843 42366194425169894865037265)
            ·
              refine ⟨31774645818877421148777949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42366194425169894865037265 31774645818877421148777949)
              ·
                refine ⟨11915492182079032930791731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31774645818877421148777949 11915492182079032930791731)
                ·
                  refine ⟨17873238273118549396187597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11915492182079032930791731 17873238273118549396187597)
                  ·
                    refine ⟨6702464352419456023570349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17873238273118549396187597 6702464352419456023570349)
                    ·
                      refine ⟨2513424132157296008838881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6702464352419456023570349 2513424132157296008838881)
                      ·
                        rfl

theorem cell23_4894876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 2, 3, 1, 3, 3].length) (baseStart_4894876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4894876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4894876 prefixEnd_4894876 := by exact prefixLift 4894876
  have htrace : WordTrace (prefixWord ++ tailWord_4894876) baseStart_4894876 baseEnd_4894876 := by
    simpa [prefixWord, tailWord_4894876, baseEnd_4894876] using wordTrace_append hprefix tailTrace_4894876
  have hstable : (prefixWord ++ tailWord_4894876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4894876).length < 2 ^ (prefixWord ++ tailWord_4894876).sum := by decide
  have hdescent : baseEnd_4894876 < baseStart_4894876 := by decide
  rcases family_descends (prefixWord ++ tailWord_4894876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4894893 : List Nat := [1, 5, 2, 1, 2, 2, 1, 2, 1, 3, 3]
def baseStart_4894893 : Nat := 118140960795 + 4894893 * 2 ^ 59
def prefixEnd_4894893 : Nat := 4983230072969 + 3 ^ 40 * 4894893 * 2
def baseEnd_4894893 : Nat := 2513432861328422442326303

theorem tailTrace_4894893 : CollatzResearch.WordTrace tailWord_4894893 prefixEnd_4894893 2513432861328422442326303 := by
  unfold tailWord_4894893
  simp only [CollatzResearch.WordTrace]
  refine ⟨178531414655646117013649333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119020943103764078009099555 178531414655646117013649333)
  ·
    refine ⟨16737320123966823470029625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 178531414655646117013649333 16737320123966823470029625)
    ·
      refine ⟨12552990092975117602522219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16737320123966823470029625 12552990092975117602522219)
      ·
        refine ⟨18829485139462676403783329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12552990092975117602522219 18829485139462676403783329)
        ·
          refine ⟨14122113854597007302837497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18829485139462676403783329 14122113854597007302837497)
          ·
            refine ⟨10591585390947755477128123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14122113854597007302837497 10591585390947755477128123)
            ·
              refine ⟨15887378086421633215692185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10591585390947755477128123 15887378086421633215692185)
              ·
                refine ⟨11915533564816224911769139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15887378086421633215692185 11915533564816224911769139)
                ·
                  refine ⟨17873300347224337367653709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11915533564816224911769139 17873300347224337367653709)
                  ·
                    refine ⟨6702487630209126512870141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17873300347224337367653709 6702487630209126512870141)
                    ·
                      refine ⟨2513432861328422442326303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6702487630209126512870141 2513432861328422442326303)
                      ·
                        rfl

theorem cell23_4894893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 2, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 2, 1, 2, 1, 3, 3].length) (baseStart_4894893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4894893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4894893 prefixEnd_4894893 := by exact prefixLift 4894893
  have htrace : WordTrace (prefixWord ++ tailWord_4894893) baseStart_4894893 baseEnd_4894893 := by
    simpa [prefixWord, tailWord_4894893, baseEnd_4894893] using wordTrace_append hprefix tailTrace_4894893
  have hstable : (prefixWord ++ tailWord_4894893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4894893).length < 2 ^ (prefixWord ++ tailWord_4894893).sum := by decide
  have hdescent : baseEnd_4894893 < baseStart_4894893 := by decide
  rcases family_descends (prefixWord ++ tailWord_4894893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4894900 : List Nat := [2, 5, 3, 1, 2, 10]
def baseStart_4894900 : Nat := 118140960795 + 4894900 * 2 ^ 59
def prefixEnd_4894900 : Nat := 4983230072969 + 3 ^ 40 * 4894900 * 2
def baseEnd_4894900 : Nat := 10343359899971209526497

theorem tailTrace_4894900 : CollatzResearch.WordTrace tailWord_4894900 prefixEnd_4894900 10343359899971209526497 := by
  unfold tailWord_4894900
  simp only [CollatzResearch.WordTrace]
  refine ⟨89265834983310378604577077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119021113311080504806102769 89265834983310378604577077)
  ·
    refine ⟨8368672029685347994179101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 89265834983310378604577077 8368672029685347994179101)
    ·
      refine ⟨3138252011132005497817163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8368672029685347994179101 3138252011132005497817163)
      ·
        refine ⟨4707378016698008246725745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3138252011132005497817163 4707378016698008246725745)
        ·
          refine ⟨3530533512523506185044309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4707378016698008246725745 3530533512523506185044309)
          ·
            refine ⟨10343359899971209526497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 3530533512523506185044309 10343359899971209526497)
            ·
              rfl

theorem cell23_4894900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 2, 10].length) (baseStart_4894900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4894900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4894900 prefixEnd_4894900 := by exact prefixLift 4894900
  have htrace : WordTrace (prefixWord ++ tailWord_4894900) baseStart_4894900 baseEnd_4894900 := by
    simpa [prefixWord, tailWord_4894900, baseEnd_4894900] using wordTrace_append hprefix tailTrace_4894900
  have hstable : (prefixWord ++ tailWord_4894900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4894900).length < 2 ^ (prefixWord ++ tailWord_4894900).sum := by decide
  have hdescent : baseEnd_4894900 < baseStart_4894900 := by decide
  rcases family_descends (prefixWord ++ tailWord_4894900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4894909 : List Nat := [1, 4, 1, 2, 1, 1, 1, 4, 2, 6]
def baseStart_4894909 : Nat := 118140960795 + 4894909 * 2 ^ 59
def prefixEnd_4894909 : Nat := 4983230072969 + 3 ^ 40 * 4894909 * 2
def baseEnd_4894909 : Nat := 837813692339631459908743

theorem tailTrace_4894909 : CollatzResearch.WordTrace tailWord_4894909 prefixEnd_4894909 837813692339631459908743 := by
  unfold tailWord_4894909
  simp only [CollatzResearch.WordTrace]
  refine ⟨178531998223588151746231781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119021332149058767830821187 178531998223588151746231781)
  ·
    refine ⟨33474749666922778452418459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 178531998223588151746231781 33474749666922778452418459)
    ·
      refine ⟨50212124500384167678627689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33474749666922778452418459 50212124500384167678627689)
      ·
        refine ⟨37659093375288125758970767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50212124500384167678627689 37659093375288125758970767)
        ·
          refine ⟨56488640062932188638456151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37659093375288125758970767 56488640062932188638456151)
          ·
            refine ⟨84732960094398282957684227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56488640062932188638456151 84732960094398282957684227)
            ·
              refine ⟨127099440141597424436526341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 84732960094398282957684227 127099440141597424436526341)
              ·
                refine ⟨23831145026549517081848689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 127099440141597424436526341 23831145026549517081848689)
                ·
                  refine ⟨17873358769912137811386517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23831145026549517081848689 17873358769912137811386517)
                  ·
                    refine ⟨837813692339631459908743, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17873358769912137811386517 837813692339631459908743)
                    ·
                      rfl

theorem cell23_4894909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 4, 2, 6].length) (baseStart_4894909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4894909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4894909 prefixEnd_4894909 := by exact prefixLift 4894909
  have htrace : WordTrace (prefixWord ++ tailWord_4894909) baseStart_4894909 baseEnd_4894909 := by
    simpa [prefixWord, tailWord_4894909, baseEnd_4894909] using wordTrace_append hprefix tailTrace_4894909
  have hstable : (prefixWord ++ tailWord_4894909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4894909).length < 2 ^ (prefixWord ++ tailWord_4894909).sum := by decide
  have hdescent : baseEnd_4894909 < baseStart_4894909 := by decide
  rcases family_descends (prefixWord ++ tailWord_4894909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4894916 : List Nat := [2, 3, 3, 1, 2, 1, 1, 1, 2, 3, 4]
def baseStart_4894916 : Nat := 118140960795 + 4894916 * 2 ^ 59
def prefixEnd_4894916 : Nat := 4983230072969 + 3 ^ 40 * 4894916 * 2
def baseEnd_4894916 : Nat := 2513444671383475852338697

theorem tailTrace_4894916 : CollatzResearch.WordTrace tailWord_4894916 prefixEnd_4894916 2513444671383475852338697 := by
  unfold tailWord_4894916
  simp only [CollatzResearch.WordTrace]
  refine ⟨89266126767281395970868301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119021502356375194627824401 89266126767281395970868301)
  ·
    refine ⟨33474797537730523489075613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 89266126767281395970868301 33474797537730523489075613)
    ·
      refine ⟨12553049076648946308403355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33474797537730523489075613 12553049076648946308403355)
      ·
        refine ⟨18829573614973419462605033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12553049076648946308403355 18829573614973419462605033)
        ·
          refine ⟨14122180211230064596953775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18829573614973419462605033 14122180211230064596953775)
          ·
            refine ⟨21183270316845096895430663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14122180211230064596953775 21183270316845096895430663)
            ·
              refine ⟨31774905475267645343145995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21183270316845096895430663 31774905475267645343145995)
              ·
                refine ⟨47662358212901468014718993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31774905475267645343145995 47662358212901468014718993)
                ·
                  refine ⟨35746768659676101011039245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 47662358212901468014718993 35746768659676101011039245)
                  ·
                    refine ⟨13405038247378537879139717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 35746768659676101011039245 13405038247378537879139717)
                    ·
                      refine ⟨2513444671383475852338697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13405038247378537879139717 2513444671383475852338697)
                      ·
                        rfl

theorem cell23_4894916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 1, 1, 2, 3, 4].length) (baseStart_4894916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4894916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4894916 prefixEnd_4894916 := by exact prefixLift 4894916
  have htrace : WordTrace (prefixWord ++ tailWord_4894916) baseStart_4894916 baseEnd_4894916 := by
    simpa [prefixWord, tailWord_4894916, baseEnd_4894916] using wordTrace_append hprefix tailTrace_4894916
  have hstable : (prefixWord ++ tailWord_4894916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4894916).length < 2 ^ (prefixWord ++ tailWord_4894916).sum := by decide
  have hdescent : baseEnd_4894916 < baseStart_4894916 := by decide
  rcases family_descends (prefixWord ++ tailWord_4894916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4894926 : List Nat := [4, 1, 1, 1, 4, 2, 1, 1, 2, 6]
def baseStart_4894926 : Nat := 118140960795 + 4894926 * 2 ^ 59
def prefixEnd_4894926 : Nat := 4983230072969 + 3 ^ 40 * 4894926 * 2
def baseEnd_4894926 : Nat := 837816602063340271071217

theorem tailTrace_4894926 : CollatzResearch.WordTrace tailWord_4894926 prefixEnd_4894926 837816602063340271071217 := by
  unfold tailWord_4894926
  simp only [CollatzResearch.WordTrace]
  refine ⟨22316577283065820456200079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 119021745509684375766400421 22316577283065820456200079)
  ·
    refine ⟨33474865924598730684300119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22316577283065820456200079 33474865924598730684300119)
    ·
      refine ⟨50212298886898096026450179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33474865924598730684300119 50212298886898096026450179)
      ·
        refine ⟨75318448330347144039675269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50212298886898096026450179 75318448330347144039675269)
        ·
          refine ⟨14122209061940089507439113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 75318448330347144039675269 14122209061940089507439113)
          ·
            refine ⟨10591656796455067130579335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14122209061940089507439113 10591656796455067130579335)
            ·
              refine ⟨15887485194682600695869003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10591656796455067130579335 15887485194682600695869003)
              ·
                refine ⟨23831227792023901043803505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15887485194682600695869003 23831227792023901043803505)
                ·
                  refine ⟨17873420844017925782852629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23831227792023901043803505 17873420844017925782852629)
                  ·
                    refine ⟨837816602063340271071217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17873420844017925782852629 837816602063340271071217)
                    ·
                      rfl

theorem cell23_4894926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 2, 1, 1, 2, 6].length) (baseStart_4894926 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4894926 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4894926 prefixEnd_4894926 := by exact prefixLift 4894926
  have htrace : WordTrace (prefixWord ++ tailWord_4894926) baseStart_4894926 baseEnd_4894926 := by
    simpa [prefixWord, tailWord_4894926, baseEnd_4894926] using wordTrace_append hprefix tailTrace_4894926
  have hstable : (prefixWord ++ tailWord_4894926).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4894926).length < 2 ^ (prefixWord ++ tailWord_4894926).sum := by decide
  have hdescent : baseEnd_4894926 < baseStart_4894926 := by decide
  rcases family_descends (prefixWord ++ tailWord_4894926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4894929 : List Nat := [1, 2, 2, 1, 2, 2, 3, 1, 1, 4, 4]
def baseStart_4894929 : Nat := 118140960795 + 4894929 * 2 ^ 59
def prefixEnd_4894929 : Nat := 4983230072969 + 3 ^ 40 * 4894929 * 2
def baseEnd_4894929 : Nat := 2513451346631984301476137

theorem tailTrace_4894929 : CollatzResearch.WordTrace tailWord_4894929 prefixEnd_4894929 2513451346631984301476137 := by
  unfold tailWord_4894929
  simp only [CollatzResearch.WordTrace]
  refine ⟨178532727683515695161959841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119021818455677130107973227 178532727683515695161959841)
  ·
    refine ⟨133899545762636771371469881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 178532727683515695161959841 133899545762636771371469881)
    ·
      refine ⟨100424659321977578528602411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 133899545762636771371469881 100424659321977578528602411)
      ·
        refine ⟨150636988982966367792903617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100424659321977578528602411 150636988982966367792903617)
        ·
          refine ⟨112977741737224775844677713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 150636988982966367792903617 112977741737224775844677713)
          ·
            refine ⟨84733306302918581883508285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 112977741737224775844677713 84733306302918581883508285)
            ·
              refine ⟨31774989863594468206315607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 84733306302918581883508285 31774989863594468206315607)
              ·
                refine ⟨47662484795391702309473411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31774989863594468206315607 47662484795391702309473411)
                ·
                  refine ⟨71493727193087553464210117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 47662484795391702309473411 71493727193087553464210117)
                  ·
                    refine ⟨13405073848703916274539397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 71493727193087553464210117 13405073848703916274539397)
                    ·
                      refine ⟨2513451346631984301476137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13405073848703916274539397 2513451346631984301476137)
                      ·
                        rfl

theorem cell23_4894929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 3, 1, 1, 4, 4].length) (baseStart_4894929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4894929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4894929 prefixEnd_4894929 := by exact prefixLift 4894929
  have htrace : WordTrace (prefixWord ++ tailWord_4894929) baseStart_4894929 baseEnd_4894929 := by
    simpa [prefixWord, tailWord_4894929, baseEnd_4894929] using wordTrace_append hprefix tailTrace_4894929
  have hstable : (prefixWord ++ tailWord_4894929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4894929).length < 2 ^ (prefixWord ++ tailWord_4894929).sum := by decide
  have hdescent : baseEnd_4894929 < baseStart_4894929 := by decide
  rcases family_descends (prefixWord ++ tailWord_4894929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4894976 : List Nat := [2, 1, 1, 2, 1, 1, 4, 1, 1, 7, 2]
def baseStart_4894976 : Nat := 118140960795 + 4894976 * 2 ^ 59
def prefixEnd_4894976 : Nat := 4983230072969 + 3 ^ 40 * 4894976 * 2
def baseEnd_4894976 : Nat := 2513475480222745617588421

theorem tailTrace_4894976 : CollatzResearch.WordTrace tailWord_4894976 prefixEnd_4894976 2513475480222745617588421 := by
  unfold tailWord_4894976
  simp only [CollatzResearch.WordTrace]
  refine ⟨89267220957172711094460391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119022961276230281459280521 89267220957172711094460391)
  ·
    refine ⟨133900831435759066641690587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89267220957172711094460391 133900831435759066641690587)
    ·
      refine ⟨200851247153638599962535881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 133900831435759066641690587 200851247153638599962535881)
      ·
        refine ⟨150638435365228949971901911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 200851247153638599962535881 150638435365228949971901911)
        ·
          refine ⟨225957653047843424957852867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 150638435365228949971901911 225957653047843424957852867)
          ·
            refine ⟨338936479571765137436779301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 225957653047843424957852867 338936479571765137436779301)
            ·
              refine ⟨63550589919705963269396119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 338936479571765137436779301 63550589919705963269396119)
              ·
                refine ⟨95325884879558944904094179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 63550589919705963269396119 95325884879558944904094179)
                ·
                  refine ⟨142988827319338417356141269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 95325884879558944904094179 142988827319338417356141269)
                  ·
                    refine ⟨3351300640296994156784561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 142988827319338417356141269 3351300640296994156784561)
                    ·
                      refine ⟨2513475480222745617588421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3351300640296994156784561 2513475480222745617588421)
                      ·
                        rfl

theorem cell23_4894976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 1, 1, 7, 2].length) (baseStart_4894976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4894976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4894976 prefixEnd_4894976 := by exact prefixLift 4894976
  have htrace : WordTrace (prefixWord ++ tailWord_4894976) baseStart_4894976 baseEnd_4894976 := by
    simpa [prefixWord, tailWord_4894976, baseEnd_4894976] using wordTrace_append hprefix tailTrace_4894976
  have hstable : (prefixWord ++ tailWord_4894976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4894976).length < 2 ^ (prefixWord ++ tailWord_4894976).sum := by decide
  have hdescent : baseEnd_4894976 < baseStart_4894976 := by decide
  rcases family_descends (prefixWord ++ tailWord_4894976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4894979 : List Nat := [1, 1, 1, 3, 2, 3, 2, 1, 1, 1, 7]
def baseStart_4894979 : Nat := 118140960795 + 4894979 * 2 ^ 59
def prefixEnd_4894979 : Nat := 4983230072969 + 3 ^ 40 * 4894979 * 2
def baseEnd_4894979 : Nat := 2513477020664709105850907

theorem tailTrace_4894979 : CollatzResearch.WordTrace tailWord_4894979 prefixEnd_4894979 2513477020664709105850907 := by
  unfold tailWord_4894979
  simp only [CollatzResearch.WordTrace]
  refine ⟨178534551333334553701279991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119023034222223035800853327 178534551333334553701279991)
  ·
    refine ⟨267801827000001830551919987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 178534551333334553701279991 267801827000001830551919987)
    ·
      refine ⟨401702740500002745827879981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 267801827000001830551919987 401702740500002745827879981)
      ·
        refine ⟨150638527687501029685454993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 401702740500002745827879981 150638527687501029685454993)
        ·
          refine ⟨112978895765625772264091245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 150638527687501029685454993 112978895765625772264091245)
          ·
            refine ⟨42367085912109664599034217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 112978895765625772264091245 42367085912109664599034217)
            ·
              refine ⟨31775314434082248449275663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42367085912109664599034217 31775314434082248449275663)
              ·
                refine ⟨47662971651123372673913495, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31775314434082248449275663 47662971651123372673913495)
                ·
                  refine ⟨71494457476685059010870243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 47662971651123372673913495 71494457476685059010870243)
                  ·
                    refine ⟨107241686215027588516305365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 71494457476685059010870243 107241686215027588516305365)
                    ·
                      refine ⟨2513477020664709105850907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 107241686215027588516305365 2513477020664709105850907)
                      ·
                        rfl

theorem cell23_4894979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 2, 1, 1, 1, 7].length) (baseStart_4894979 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4894979 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4894979 prefixEnd_4894979 := by exact prefixLift 4894979
  have htrace : WordTrace (prefixWord ++ tailWord_4894979) baseStart_4894979 baseEnd_4894979 := by
    simpa [prefixWord, tailWord_4894979, baseEnd_4894979] using wordTrace_append hprefix tailTrace_4894979
  have hstable : (prefixWord ++ tailWord_4894979).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4894979).length < 2 ^ (prefixWord ++ tailWord_4894979).sum := by decide
  have hdescent : baseEnd_4894979 < baseStart_4894979 := by decide
  rcases family_descends (prefixWord ++ tailWord_4894979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4895060 : List Nat := [2, 4, 1, 1, 2, 3, 2, 1, 2, 2, 3]
def baseStart_4895060 : Nat := 118140960795 + 4895060 * 2 ^ 59
def prefixEnd_4895060 : Nat := 4983230072969 + 3 ^ 40 * 4895060 * 2
def baseEnd_4895060 : Nat := 2513518612597723288938035

theorem tailTrace_4895060 : CollatzResearch.WordTrace tailWord_4895060 prefixEnd_4895060 2513518612597723288938035 := by
  unfold tailWord_4895060
  simp only [CollatzResearch.WordTrace]
  refine ⟨89268752823020552267489317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119025003764027403023319089 89268752823020552267489317)
  ·
    refine ⟨16737891154316353550154247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 89268752823020552267489317 16737891154316353550154247)
    ·
      refine ⟨25106836731474530325231371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16737891154316353550154247 25106836731474530325231371)
      ·
        refine ⟨37660255097211795487847057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25106836731474530325231371 37660255097211795487847057)
        ·
          refine ⟨28245191322908846615885293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37660255097211795487847057 28245191322908846615885293)
          ·
            refine ⟨10591946746090817480956985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28245191322908846615885293 10591946746090817480956985)
            ·
              refine ⟨7943960059568113110717739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10591946746090817480956985 7943960059568113110717739)
              ·
                refine ⟨11915940089352169666076609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7943960059568113110717739 11915940089352169666076609)
                ·
                  refine ⟨8936955067014127249557457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11915940089352169666076609 8936955067014127249557457)
                  ·
                    refine ⟨6702716300260595437168093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8936955067014127249557457 6702716300260595437168093)
                    ·
                      refine ⟨2513518612597723288938035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6702716300260595437168093 2513518612597723288938035)
                      ·
                        rfl

theorem cell23_4895060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 3, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 3, 2, 1, 2, 2, 3].length) (baseStart_4895060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4895060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4895060 prefixEnd_4895060 := by exact prefixLift 4895060
  have htrace : WordTrace (prefixWord ++ tailWord_4895060) baseStart_4895060 baseEnd_4895060 := by
    simpa [prefixWord, tailWord_4895060, baseEnd_4895060] using wordTrace_append hprefix tailTrace_4895060
  have hstable : (prefixWord ++ tailWord_4895060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4895060).length < 2 ^ (prefixWord ++ tailWord_4895060).sum := by decide
  have hdescent : baseEnd_4895060 < baseStart_4895060 := by decide
  rcases family_descends (prefixWord ++ tailWord_4895060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4895084 : List Nat := [2, 2, 1, 1, 6, 2, 2, 2, 1, 4]
def baseStart_4895084 : Nat := 118140960795 + 4895084 * 2 ^ 59
def prefixEnd_4895084 : Nat := 4983230072969 + 3 ^ 40 * 4895084 * 2
def baseEnd_4895084 : Nat := 837843645377810398345975

theorem tailTrace_4895084 : CollatzResearch.WordTrace tailWord_4895084 prefixEnd_4895084 837843645377810398345975 := by
  unfold tailWord_4895084
  simp only [CollatzResearch.WordTrace]
  refine ⟨89269190498977078316926153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119025587331969437755901537 89269190498977078316926153)
  ·
    refine ⟨66951892874232808737694615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89269190498977078316926153 66951892874232808737694615)
    ·
      refine ⟨100427839311349213106541923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66951892874232808737694615 100427839311349213106541923)
      ·
        refine ⟨150641758967023819659812885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100427839311349213106541923 150641758967023819659812885)
        ·
          refine ⟨7061332451579241546553729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 150641758967023819659812885 7061332451579241546553729)
          ·
            refine ⟨5295999338684431159915297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7061332451579241546553729 5295999338684431159915297)
            ·
              refine ⟨3971999504013323369936473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5295999338684431159915297 3971999504013323369936473)
              ·
                refine ⟨2978999628009992527452355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3971999504013323369936473 2978999628009992527452355)
                ·
                  refine ⟨4468499442014988791178533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2978999628009992527452355 4468499442014988791178533)
                  ·
                    refine ⟨837843645377810398345975, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4468499442014988791178533 837843645377810398345975)
                    ·
                      rfl

theorem cell23_4895084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 2, 2, 2, 1, 4].length) (baseStart_4895084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4895084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4895084 prefixEnd_4895084 := by exact prefixLift 4895084
  have htrace : WordTrace (prefixWord ++ tailWord_4895084) baseStart_4895084 baseEnd_4895084 := by
    simpa [prefixWord, tailWord_4895084, baseEnd_4895084] using wordTrace_append hprefix tailTrace_4895084
  have hstable : (prefixWord ++ tailWord_4895084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4895084).length < 2 ^ (prefixWord ++ tailWord_4895084).sum := by decide
  have hdescent : baseEnd_4895084 < baseStart_4895084 := by decide
  rcases family_descends (prefixWord ++ tailWord_4895084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4895093 : List Nat := [1, 3, 4, 1, 2, 1, 1, 2, 3, 5]
def baseStart_4895093 : Nat := 118140960795 + 4895093 * 2 ^ 59
def prefixEnd_4895093 : Nat := 4983230072969 + 3 ^ 40 * 4895093 * 2
def baseEnd_4895093 : Nat := 837845185819773886608461

theorem tailTrace_4895093 : CollatzResearch.WordTrace tailWord_4895093 prefixEnd_4895093 837845185819773886608461 := by
  unfold tailWord_4895093
  simp only [CollatzResearch.WordTrace]
  refine ⟨178538709254921551170929933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119025806169947700780619955 178538709254921551170929933)
  ·
    refine ⟨66952015970595581689098725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 178538709254921551170929933 66952015970595581689098725)
    ·
      refine ⟨12553502994486671566706011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 66952015970595581689098725 12553502994486671566706011)
      ·
        refine ⟨18830254491730007350059017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12553502994486671566706011 18830254491730007350059017)
        ·
          refine ⟨14122690868797505512544263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18830254491730007350059017 14122690868797505512544263)
          ·
            refine ⟨21184036303196258268816395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14122690868797505512544263 21184036303196258268816395)
            ·
              refine ⟨31776054454794387403224593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21184036303196258268816395 31776054454794387403224593)
              ·
                refine ⟨23832040841095790552418445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31776054454794387403224593 23832040841095790552418445)
                ·
                  refine ⟨8937015315410921457156917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23832040841095790552418445 8937015315410921457156917)
                  ·
                    refine ⟨837845185819773886608461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8937015315410921457156917 837845185819773886608461)
                    ·
                      rfl

theorem cell23_4895093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 1, 2, 3, 5].length) (baseStart_4895093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4895093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4895093 prefixEnd_4895093 := by exact prefixLift 4895093
  have htrace : WordTrace (prefixWord ++ tailWord_4895093) baseStart_4895093 baseEnd_4895093 := by
    simpa [prefixWord, tailWord_4895093, baseEnd_4895093] using wordTrace_append hprefix tailTrace_4895093
  have hstable : (prefixWord ++ tailWord_4895093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4895093).length < 2 ^ (prefixWord ++ tailWord_4895093).sum := by decide
  have hdescent : baseEnd_4895093 < baseStart_4895093 := by decide
  rcases family_descends (prefixWord ++ tailWord_4895093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4895113 : List Nat := [1, 2, 1, 1, 6, 1, 2, 1, 3, 1, 4]
def baseStart_4895113 : Nat := 118140960795 + 4895113 * 2 ^ 59
def prefixEnd_4895113 : Nat := 4983230072969 + 3 ^ 40 * 4895113 * 2
def baseEnd_4895113 : Nat := 2513545827072411581575291

theorem tailTrace_4895113 : CollatzResearch.WordTrace tailWord_4895113 prefixEnd_4895113 2513545827072411581575291 := by
  unfold tailWord_4895113
  simp only [CollatzResearch.WordTrace]
  refine ⟨178539438714849094586657993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119026292476566063057771995 178539438714849094586657993)
  ·
    refine ⟨133904579036136820939993495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 178539438714849094586657993 133904579036136820939993495)
    ·
      refine ⟨200856868554205231409990243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 133904579036136820939993495 200856868554205231409990243)
      ·
        refine ⟨301285302831307847114985365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 200856868554205231409990243 301285302831307847114985365)
        ·
          refine ⟨14122748570217555333514939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 301285302831307847114985365 14122748570217555333514939)
          ·
            refine ⟨21184122855326333000272409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14122748570217555333514939 21184122855326333000272409)
            ·
              refine ⟨15888092141494749750204307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21184122855326333000272409 15888092141494749750204307)
              ·
                refine ⟨23832138212242124625306461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15888092141494749750204307 23832138212242124625306461)
                ·
                  refine ⟨8937051829590796734489923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23832138212242124625306461 8937051829590796734489923)
                  ·
                    refine ⟨13405577744386195101734885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8937051829590796734489923 13405577744386195101734885)
                    ·
                      refine ⟨2513545827072411581575291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13405577744386195101734885 2513545827072411581575291)
                      ·
                        rfl

theorem cell23_4895113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 2, 1, 3, 1, 4].length) (baseStart_4895113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4895113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4895113 prefixEnd_4895113 := by exact prefixLift 4895113
  have htrace : WordTrace (prefixWord ++ tailWord_4895113) baseStart_4895113 baseEnd_4895113 := by
    simpa [prefixWord, tailWord_4895113, baseEnd_4895113] using wordTrace_append hprefix tailTrace_4895113
  have hstable : (prefixWord ++ tailWord_4895113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4895113).length < 2 ^ (prefixWord ++ tailWord_4895113).sum := by decide
  have hdescent : baseEnd_4895113 < baseStart_4895113 := by decide
  rcases family_descends (prefixWord ++ tailWord_4895113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4895130 : List Nat := [3, 1, 1, 4, 1, 3, 1, 3, 1, 1, 4]
def baseStart_4895130 : Nat := 118140960795 + 4895130 * 2 ^ 59
def prefixEnd_4895130 : Nat := 4983230072969 + 3 ^ 40 * 4895130 * 2
def baseEnd_4895130 : Nat := 2513554556243538015062713

theorem tailTrace_4895130 : CollatzResearch.WordTrace tailWord_4895130 prefixEnd_4895130 2513554556243538015062713 := by
  unfold tailWord_4895130
  simp only [CollatzResearch.WordTrace]
  refine ⟨44635014688946876622506711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 119026705837191670993351229 44635014688946876622506711)
  ·
    refine ⟨66952522033420314933760067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44635014688946876622506711 66952522033420314933760067)
    ·
      refine ⟨100428783050130472400640101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66952522033420314933760067 100428783050130472400640101)
      ·
        refine ⟨18830396821899463575120019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 100428783050130472400640101 18830396821899463575120019)
        ·
          refine ⟨28245595232849195362680029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18830396821899463575120019 28245595232849195362680029)
          ·
            refine ⟨10592098212318448261005011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28245595232849195362680029 10592098212318448261005011)
            ·
              refine ⟨15888147318477672391507517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10592098212318448261005011 15888147318477672391507517)
              ·
                refine ⟨5958055244429127146815319, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15888147318477672391507517 5958055244429127146815319)
                ·
                  refine ⟨8937082866643690720222979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5958055244429127146815319 8937082866643690720222979)
                  ·
                    refine ⟨13405624299965536080334469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8937082866643690720222979 13405624299965536080334469)
                    ·
                      refine ⟨2513554556243538015062713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13405624299965536080334469 2513554556243538015062713)
                      ·
                        rfl

theorem cell23_4895130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 3, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 3, 1, 3, 1, 1, 4].length) (baseStart_4895130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4895130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4895130 prefixEnd_4895130 := by exact prefixLift 4895130
  have htrace : WordTrace (prefixWord ++ tailWord_4895130) baseStart_4895130 baseEnd_4895130 := by
    simpa [prefixWord, tailWord_4895130, baseEnd_4895130] using wordTrace_append hprefix tailTrace_4895130
  have hstable : (prefixWord ++ tailWord_4895130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4895130).length < 2 ^ (prefixWord ++ tailWord_4895130).sum := by decide
  have hdescent : baseEnd_4895130 < baseStart_4895130 := by decide
  rcases family_descends (prefixWord ++ tailWord_4895130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4895136 : List Nat := [2, 1, 1, 4, 1, 4, 10]
def baseStart_4895136 : Nat := 118140960795 + 4895136 * 2 ^ 59
def prefixEnd_4895136 : Nat := 4983230072969 + 3 ^ 40 * 4895136 * 2
def baseEnd_4895136 : Nat := 31031575767005740636885

theorem tailTrace_4895136 : CollatzResearch.WordTrace tailWord_4895136 prefixEnd_4895136 31031575767005740636885 := by
  unfold tailWord_4895136
  simp only [CollatzResearch.WordTrace]
  refine ⟨89270138796882884757372631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119026851729177179676496841 89270138796882884757372631)
  ·
    refine ⟨133905208195324327136058947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89270138796882884757372631 133905208195324327136058947)
    ·
      refine ⟨200857812292986490704088421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 133905208195324327136058947 200857812292986490704088421)
      ·
        refine ⟨37660839804934967007016579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 200857812292986490704088421 37660839804934967007016579)
        ·
          refine ⟨56491259707402450510524869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37660839804934967007016579 56491259707402450510524869)
          ·
            refine ⟨10592111195137959470723413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 56491259707402450510524869 10592111195137959470723413)
            ·
              refine ⟨31031575767005740636885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 10592111195137959470723413 31031575767005740636885)
              ·
                rfl

theorem cell23_4895136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 4, 10].length) (baseStart_4895136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4895136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4895136 prefixEnd_4895136 := by exact prefixLift 4895136
  have htrace : WordTrace (prefixWord ++ tailWord_4895136) baseStart_4895136 baseEnd_4895136 := by
    simpa [prefixWord, tailWord_4895136, baseEnd_4895136] using wordTrace_append hprefix tailTrace_4895136
  have hstable : (prefixWord ++ tailWord_4895136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4895136).length < 2 ^ (prefixWord ++ tailWord_4895136).sum := by decide
  have hdescent : baseEnd_4895136 < baseStart_4895136 := by decide
  rcases family_descends (prefixWord ++ tailWord_4895136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4895140 : List Nat := [2, 3, 1, 2, 1, 1, 5, 2, 2, 4]
def baseStart_4895140 : Nat := 118140960795 + 4895140 * 2 ^ 59
def prefixEnd_4895140 : Nat := 4983230072969 + 3 ^ 40 * 4895140 * 2
def baseEnd_4895140 : Nat := 837853230350027658645889

theorem tailTrace_4895140 : CollatzResearch.WordTrace tailWord_4895140 prefixEnd_4895140 837853230350027658645889 := by
  unfold tailWord_4895140
  simp only [CollatzResearch.WordTrace]
  refine ⟨89270211742875639098945437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119026948990500852131927249 89270211742875639098945437)
  ·
    refine ⟨33476329403578364662104539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 89270211742875639098945437 33476329403578364662104539)
    ·
      refine ⟨50214494105367546993156809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33476329403578364662104539 50214494105367546993156809)
      ·
        refine ⟨37660870579025660244867607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50214494105367546993156809 37660870579025660244867607)
        ·
          refine ⟨56491305868538490367301411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37660870579025660244867607 56491305868538490367301411)
          ·
            refine ⟨84736958802807735550952117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56491305868538490367301411 84736958802807735550952117)
            ·
              refine ⟨7944089887763225207901761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 84736958802807735550952117 7944089887763225207901761)
              ·
                refine ⟨5958067415822418905926321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7944089887763225207901761 5958067415822418905926321)
                ·
                  refine ⟨4468550561866814179444741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5958067415822418905926321 4468550561866814179444741)
                  ·
                    refine ⟨837853230350027658645889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4468550561866814179444741 837853230350027658645889)
                    ·
                      rfl

theorem cell23_4895140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 5, 2, 2, 4].length) (baseStart_4895140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4895140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4895140 prefixEnd_4895140 := by exact prefixLift 4895140
  have htrace : WordTrace (prefixWord ++ tailWord_4895140) baseStart_4895140 baseEnd_4895140 := by
    simpa [prefixWord, tailWord_4895140, baseEnd_4895140] using wordTrace_append hprefix tailTrace_4895140
  have hstable : (prefixWord ++ tailWord_4895140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4895140).length < 2 ^ (prefixWord ++ tailWord_4895140).sum := by decide
  have hdescent : baseEnd_4895140 < baseStart_4895140 := by decide
  rcases family_descends (prefixWord ++ tailWord_4895140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4895157 : List Nat := [1, 3, 3, 2, 4, 1, 1, 1, 1, 6]
def baseStart_4895157 : Nat := 118140960795 + 4895157 * 2 ^ 59
def prefixEnd_4895157 : Nat := 4983230072969 + 3 ^ 40 * 4895157 * 2
def baseEnd_4895157 : Nat := 837856140073736469808363

theorem tailTrace_4895157 : CollatzResearch.WordTrace tailWord_4895157 prefixEnd_4895157 837856140073736469808363 := by
  unfold tailWord_4895157
  simp only [CollatzResearch.WordTrace]
  refine ⟨178541043526689690101259725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119027362351126460067506483 178541043526689690101259725)
  ·
    refine ⟨66952891322508633787972397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 178541043526689690101259725 66952891322508633787972397)
    ·
      refine ⟨25107334245940737670489649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 66952891322508633787972397 25107334245940737670489649)
      ·
        refine ⟨18830500684455553252867237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25107334245940737670489649 18830500684455553252867237)
        ·
          refine ⟨3530718878335416234912607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18830500684455553252867237 3530718878335416234912607)
          ·
            refine ⟨5296078317503124352368911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3530718878335416234912607 5296078317503124352368911)
            ·
              refine ⟨7944117476254686528553367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5296078317503124352368911 7944117476254686528553367)
              ·
                refine ⟨11916176214382029792830051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7944117476254686528553367 11916176214382029792830051)
                ·
                  refine ⟨17874264321573044689245077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11916176214382029792830051 17874264321573044689245077)
                  ·
                    refine ⟨837856140073736469808363, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17874264321573044689245077 837856140073736469808363)
                    ·
                      rfl

theorem cell23_4895157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 4, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 4, 1, 1, 1, 1, 6].length) (baseStart_4895157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4895157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4895157 prefixEnd_4895157 := by exact prefixLift 4895157
  have htrace : WordTrace (prefixWord ++ tailWord_4895157) baseStart_4895157 baseEnd_4895157 := by
    simpa [prefixWord, tailWord_4895157, baseEnd_4895157] using wordTrace_append hprefix tailTrace_4895157
  have hstable : (prefixWord ++ tailWord_4895157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4895157).length < 2 ^ (prefixWord ++ tailWord_4895157).sum := by decide
  have hdescent : baseEnd_4895157 < baseStart_4895157 := by decide
  rcases family_descends (prefixWord ++ tailWord_4895157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4895173 : List Nat := [1, 3, 1, 1, 1, 1, 1, 1, 4, 7, 2]
def baseStart_4895173 : Nat := 118140960795 + 4895173 * 2 ^ 59
def prefixEnd_4895173 : Nat := 4983230072969 + 3 ^ 40 * 4895173 * 2
def baseEnd_4895173 : Nat := 2513576635911681346825015

theorem tailTrace_4895173 : CollatzResearch.WordTrace tailWord_4895173 prefixEnd_4895173 2513576635911681346825015 := by
  unfold tailWord_4895173
  simp only [CollatzResearch.WordTrace]
  refine ⟨178541627094631724833842173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119027751396421149889228115 178541627094631724833842173)
  ·
    refine ⟨66953110160486896812690815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 178541627094631724833842173 66953110160486896812690815)
    ·
      refine ⟨100429665240730345219036223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66953110160486896812690815 100429665240730345219036223)
      ·
        refine ⟨150644497861095517828554335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100429665240730345219036223 150644497861095517828554335)
        ·
          refine ⟨225966746791643276742831503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 150644497861095517828554335 225966746791643276742831503)
          ·
            refine ⟨338950120187464915114247255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 225966746791643276742831503 338950120187464915114247255)
            ·
              refine ⟨508425180281197372671370883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 338950120187464915114247255 508425180281197372671370883)
              ·
                refine ⟨762637770421796059007056325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 508425180281197372671370883 762637770421796059007056325)
                ·
                  refine ⟨142994581954086761063823061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 762637770421796059007056325 142994581954086761063823061)
                  ·
                    refine ⟨3351435514548908462433353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 142994581954086761063823061 3351435514548908462433353)
                    ·
                      refine ⟨2513576635911681346825015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3351435514548908462433353 2513576635911681346825015)
                      ·
                        rfl

theorem cell23_4895173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 1, 4, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 1, 4, 7, 2].length) (baseStart_4895173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4895173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4895173 prefixEnd_4895173 := by exact prefixLift 4895173
  have htrace : WordTrace (prefixWord ++ tailWord_4895173) baseStart_4895173 baseEnd_4895173 := by
    simpa [prefixWord, tailWord_4895173, baseEnd_4895173] using wordTrace_append hprefix tailTrace_4895173
  have hstable : (prefixWord ++ tailWord_4895173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4895173).length < 2 ^ (prefixWord ++ tailWord_4895173).sum := by decide
  have hdescent : baseEnd_4895173 < baseStart_4895173 := by decide
  rcases family_descends (prefixWord ++ tailWord_4895173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4895197 : List Nat := [1, 4, 3, 1, 1, 1, 2, 4, 2, 1, 3]
def baseStart_4895197 : Nat := 118140960795 + 4895197 * 2 ^ 59
def prefixEnd_4895197 : Nat := 4983230072969 + 3 ^ 40 * 4895197 * 2
def baseEnd_4895197 : Nat := 2513588959447389252924905

theorem tailTrace_4895197 : CollatzResearch.WordTrace tailWord_4895197 prefixEnd_4895197 2513588959447389252924905 := by
  unfold tailWord_4895197
  simp only [CollatzResearch.WordTrace]
  refine ⟨178542502446544776932715845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119028334964363184621810563 178542502446544776932715845)
  ·
    refine ⟨33476719208727145674884221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 178542502446544776932715845 33476719208727145674884221)
    ·
      refine ⟨12553769703272679628081583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33476719208727145674884221 12553769703272679628081583)
      ·
        refine ⟨18830654554909019442122375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12553769703272679628081583 18830654554909019442122375)
        ·
          refine ⟨28245981832363529163183563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18830654554909019442122375 28245981832363529163183563)
          ·
            refine ⟨42368972748545293744775345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28245981832363529163183563 42368972748545293744775345)
            ·
              refine ⟨31776729561408970308581509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42368972748545293744775345 31776729561408970308581509)
              ·
                refine ⟨5958136792764181932859033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 31776729561408970308581509 5958136792764181932859033)
                ·
                  refine ⟨4468602594573136449644275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5958136792764181932859033 4468602594573136449644275)
                  ·
                    refine ⟨6702903891859704674466413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4468602594573136449644275 6702903891859704674466413)
                    ·
                      refine ⟨2513588959447389252924905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6702903891859704674466413 2513588959447389252924905)
                      ·
                        rfl

theorem cell23_4895197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 2, 4, 2, 1, 3].length) (baseStart_4895197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4895197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4895197 prefixEnd_4895197 := by exact prefixLift 4895197
  have htrace : WordTrace (prefixWord ++ tailWord_4895197) baseStart_4895197 baseEnd_4895197 := by
    simpa [prefixWord, tailWord_4895197, baseEnd_4895197] using wordTrace_append hprefix tailTrace_4895197
  have hstable : (prefixWord ++ tailWord_4895197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4895197).length < 2 ^ (prefixWord ++ tailWord_4895197).sum := by decide
  have hdescent : baseEnd_4895197 < baseStart_4895197 := by decide
  rcases family_descends (prefixWord ++ tailWord_4895197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4895214 : List Nat := [4, 1, 2, 1, 2, 2, 4, 1, 2, 1, 3]
def baseStart_4895214 : Nat := 118140960795 + 4895214 * 2 ^ 59
def prefixEnd_4895214 : Nat := 4983230072969 + 3 ^ 40 * 4895214 * 2
def baseEnd_4895214 : Nat := 2513597688618515686412327

theorem tailTrace_4895214 : CollatzResearch.WordTrace tailWord_4895214 prefixEnd_4895214 2513597688618515686412327 := by
  unfold tailWord_4895214
  simp only [CollatzResearch.WordTrace]
  refine ⟨22317890310935398604510587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 119028748324988792557389797 22317890310935398604510587)
  ·
    refine ⟨33476835466403097906765881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22317890310935398604510587 33476835466403097906765881)
    ·
      refine ⟨25107626599802323430074411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33476835466403097906765881 25107626599802323430074411)
      ·
        refine ⟨37661439899703485145111617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25107626599802323430074411 37661439899703485145111617)
        ·
          refine ⟨28246079924777613858833713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37661439899703485145111617 28246079924777613858833713)
          ·
            refine ⟨21184559943583210394125285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28246079924777613858833713 21184559943583210394125285)
            ·
              refine ⟨3972104989421851948898491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21184559943583210394125285 3972104989421851948898491)
              ·
                refine ⟨5958157484132777923347737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3972104989421851948898491 5958157484132777923347737)
                ·
                  refine ⟨4468618113099583442510803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5958157484132777923347737 4468618113099583442510803)
                  ·
                    refine ⟨6702927169649375163766205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4468618113099583442510803 6702927169649375163766205)
                    ·
                      refine ⟨2513597688618515686412327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6702927169649375163766205 2513597688618515686412327)
                      ·
                        rfl

theorem cell23_4895214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 4, 1, 2, 1, 3].length) (baseStart_4895214 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4895214 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4895214 prefixEnd_4895214 := by exact prefixLift 4895214
  have htrace : WordTrace (prefixWord ++ tailWord_4895214) baseStart_4895214 baseEnd_4895214 := by
    simpa [prefixWord, tailWord_4895214, baseEnd_4895214] using wordTrace_append hprefix tailTrace_4895214
  have hstable : (prefixWord ++ tailWord_4895214).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4895214).length < 2 ^ (prefixWord ++ tailWord_4895214).sum := by decide
  have hdescent : baseEnd_4895214 < baseStart_4895214 := by decide
  rcases family_descends (prefixWord ++ tailWord_4895214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4895271 : List Nat := [1, 1, 7, 2, 1, 1, 2, 1, 1, 4, 2]
def baseStart_4895271 : Nat := 118140960795 + 4895271 * 2 ^ 59
def prefixEnd_4895271 : Nat := 4983230072969 + 3 ^ 40 * 4895271 * 2
def baseEnd_4895271 : Nat := 2513626957015821963399565

theorem tailTrace_4895271 : CollatzResearch.WordTrace tailWord_4895271 prefixEnd_4895271 2513626957015821963399565 := by
  unfold tailWord_4895271
  simp only [CollatzResearch.WordTrace]
  refine ⟨178545201448276687570909667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119030134298851125047273111 178545201448276687570909667)
  ·
    refine ⟨267817802172415031356364501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 178545201448276687570909667 267817802172415031356364501)
    ·
      refine ⟨6276979738415977297414793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 267817802172415031356364501 6276979738415977297414793)
      ·
        refine ⟨4707734803811982973061095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6276979738415977297414793 4707734803811982973061095)
        ·
          refine ⟨7061602205717974459591643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4707734803811982973061095 7061602205717974459591643)
          ·
            refine ⟨10592403308576961689387465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7061602205717974459591643 10592403308576961689387465)
            ·
              refine ⟨7944302481432721267040599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10592403308576961689387465 7944302481432721267040599)
              ·
                refine ⟨11916453722149081900560899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7944302481432721267040599 11916453722149081900560899)
                ·
                  refine ⟨17874680583223622850841349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11916453722149081900560899 17874680583223622850841349)
                  ·
                    refine ⟨3351502609354429284532753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17874680583223622850841349 3351502609354429284532753)
                    ·
                      refine ⟨2513626957015821963399565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3351502609354429284532753 2513626957015821963399565)
                      ·
                        rfl

theorem cell23_4895271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 1, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 1, 2, 1, 1, 4, 2].length) (baseStart_4895271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4895271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4895271 prefixEnd_4895271 := by exact prefixLift 4895271
  have htrace : WordTrace (prefixWord ++ tailWord_4895271) baseStart_4895271 baseEnd_4895271 := by
    simpa [prefixWord, tailWord_4895271, baseEnd_4895271] using wordTrace_append hprefix tailTrace_4895271
  have hstable : (prefixWord ++ tailWord_4895271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4895271).length < 2 ^ (prefixWord ++ tailWord_4895271).sum := by decide
  have hdescent : baseEnd_4895271 < baseStart_4895271 := by decide
  rcases family_descends (prefixWord ++ tailWord_4895271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4895290 : List Nat := [3, 1, 1, 1, 3, 3, 3, 1, 2, 5]
def baseStart_4895290 : Nat := 118140960795 + 4895290 * 2 ^ 59
def prefixEnd_4895290 : Nat := 4983230072969 + 3 ^ 40 * 4895290 * 2
def baseEnd_4895290 : Nat := 837878904382752463020659

theorem tailTrace_4895290 : CollatzResearch.WordTrace tailWord_4895290 prefixEnd_4895290 837878904382752463020659 := by
  unfold tailWord_4895290
  simp only [CollatzResearch.WordTrace]
  refine ⟨44636473608801963453962831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 119030596290138569210567549 44636473608801963453962831)
  ·
    refine ⟨66954710413202945180944247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44636473608801963453962831 66954710413202945180944247)
    ·
      refine ⟨100432065619804417771416371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66954710413202945180944247 100432065619804417771416371)
      ·
        refine ⟨150648098429706626657124557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100432065619804417771416371 150648098429706626657124557)
        ·
          refine ⟨56493036911139984996421709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 150648098429706626657124557 56493036911139984996421709)
          ·
            refine ⟨21184888841677494373658141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 56493036911139984996421709 21184888841677494373658141)
            ·
              refine ⟨7944333315629060390121803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21184888841677494373658141 7944333315629060390121803)
              ·
                refine ⟨11916499973443590585182705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7944333315629060390121803 11916499973443590585182705)
                ·
                  refine ⟨8937374980082692938887029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11916499973443590585182705 8937374980082692938887029)
                  ·
                    refine ⟨837878904382752463020659, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8937374980082692938887029 837878904382752463020659)
                    ·
                      rfl

theorem cell23_4895290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 3, 1, 2, 5].length) (baseStart_4895290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4895290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4895290 prefixEnd_4895290 := by exact prefixLift 4895290
  have htrace : WordTrace (prefixWord ++ tailWord_4895290) baseStart_4895290 baseEnd_4895290 := by
    simpa [prefixWord, tailWord_4895290, baseEnd_4895290] using wordTrace_append hprefix tailTrace_4895290
  have hstable : (prefixWord ++ tailWord_4895290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4895290).length < 2 ^ (prefixWord ++ tailWord_4895290).sum := by decide
  have hdescent : baseEnd_4895290 < baseStart_4895290 := by decide
  rcases family_descends (prefixWord ++ tailWord_4895290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4895310 : List Nat := [4, 1, 1, 1, 1, 2, 2, 4, 2, 1, 4]
def baseStart_4895310 : Nat := 118140960795 + 4895310 * 2 ^ 59
def prefixEnd_4895310 : Nat := 4983230072969 + 3 ^ 40 * 4895310 * 2
def baseEnd_4895310 : Nat := 2513646982761347310811885

theorem tailTrace_4895310 : CollatzResearch.WordTrace tailWord_4895310 prefixEnd_4895310 2513646982761347310811885 := by
  unfold tailWord_4895310
  simp only [CollatzResearch.WordTrace]
  refine ⟨22318327986891924653947423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 119031082596756931487719589 22318327986891924653947423)
  ·
    refine ⟨33477491980337886980921135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22318327986891924653947423 33477491980337886980921135)
    ·
      refine ⟨50216237970506830471381703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33477491980337886980921135 50216237970506830471381703)
      ·
        refine ⟨75324356955760245707072555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50216237970506830471381703 75324356955760245707072555)
        ·
          refine ⟨112986535433640368560608833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75324356955760245707072555 112986535433640368560608833)
          ·
            refine ⟨84739901575230276420456625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 112986535433640368560608833 84739901575230276420456625)
            ·
              refine ⟨63554926181422707315342469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 84739901575230276420456625 63554926181422707315342469)
              ·
                refine ⟨11916548659016757621626713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 63554926181422707315342469 11916548659016757621626713)
                ·
                  refine ⟨8937411494262568216220035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11916548659016757621626713 8937411494262568216220035)
                  ·
                    refine ⟨13406117241393852324330053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8937411494262568216220035 13406117241393852324330053)
                    ·
                      refine ⟨2513646982761347310811885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13406117241393852324330053 2513646982761347310811885)
                      ·
                        rfl

theorem cell23_4895310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 2, 4, 2, 1, 4].length) (baseStart_4895310 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4895310 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4895310 prefixEnd_4895310 := by exact prefixLift 4895310
  have htrace : WordTrace (prefixWord ++ tailWord_4895310) baseStart_4895310 baseEnd_4895310 := by
    simpa [prefixWord, tailWord_4895310, baseEnd_4895310] using wordTrace_append hprefix tailTrace_4895310
  have hstable : (prefixWord ++ tailWord_4895310).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4895310).length < 2 ^ (prefixWord ++ tailWord_4895310).sum := by decide
  have hdescent : baseEnd_4895310 < baseStart_4895310 := by decide
  rcases family_descends (prefixWord ++ tailWord_4895310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4895320 : List Nat := [2, 1, 2, 2, 1, 2, 3, 3, 3, 4]
def baseStart_4895320 : Nat := 118140960795 + 4895320 * 2 ^ 59
def prefixEnd_4895320 : Nat := 4983230072969 + 3 ^ 40 * 4895320 * 2
def baseEnd_4895320 : Nat := 837884039189297423895613

theorem tailTrace_4895320 : CollatzResearch.WordTrace tailWord_4895320 prefixEnd_4895320 837884039189297423895613 := by
  unfold tailWord_4895320
  simp only [CollatzResearch.WordTrace]
  refine ⟨89273494312549584469721707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119031325750066112626295609 89273494312549584469721707)
  ·
    refine ⟨133910241468824376704582561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89273494312549584469721707 133910241468824376704582561)
    ·
      refine ⟨100432681101618282528436921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 133910241468824376704582561 100432681101618282528436921)
      ·
        refine ⟨75324510826213711896327691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 100432681101618282528436921 75324510826213711896327691)
        ·
          refine ⟨112986766239320567844491537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75324510826213711896327691 112986766239320567844491537)
          ·
            refine ⟨84740074679490425883368653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 112986766239320567844491537 84740074679490425883368653)
            ·
              refine ⟨31777528004808909706263245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 84740074679490425883368653 31777528004808909706263245)
              ·
                refine ⟨11916573001803341139848717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31777528004808909706263245 11916573001803341139848717)
                ·
                  refine ⟨4468714875676252927443269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11916573001803341139848717 4468714875676252927443269)
                  ·
                    refine ⟨837884039189297423895613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4468714875676252927443269 837884039189297423895613)
                    ·
                      rfl

theorem cell23_4895320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 3, 3, 3, 4].length) (baseStart_4895320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4895320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4895320 prefixEnd_4895320 := by exact prefixLift 4895320
  have htrace : WordTrace (prefixWord ++ tailWord_4895320) baseStart_4895320 baseEnd_4895320 := by
    simpa [prefixWord, tailWord_4895320, baseEnd_4895320] using wordTrace_append hprefix tailTrace_4895320
  have hstable : (prefixWord ++ tailWord_4895320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4895320).length < 2 ^ (prefixWord ++ tailWord_4895320).sum := by decide
  have hdescent : baseEnd_4895320 < baseStart_4895320 := by decide
  rcases family_descends (prefixWord ++ tailWord_4895320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4895423 : List Nat := [1, 1, 2, 2, 2, 15]
def baseStart_4895423 : Nat := 118140960795 + 4895423 * 2 ^ 59
def prefixEnd_4895423 : Nat := 4983230072969 + 3 ^ 40 * 4895423 * 2
def baseEnd_4895423 : Nat := 10344465045577388348555

theorem tailTrace_4895423 : CollatzResearch.WordTrace tailWord_4895423 prefixEnd_4895423 10344465045577388348555 := by
  unfold tailWord_4895423
  simp only [CollatzResearch.WordTrace]
  refine ⟨178550745343726017530442923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119033830229150678353628615 178550745343726017530442923)
  ·
    refine ⟨267826118015589026295664385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 178550745343726017530442923 267826118015589026295664385)
    ·
      refine ⟨200869588511691769721748289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 267826118015589026295664385 200869588511691769721748289)
      ·
        refine ⟨150652191383768827291311217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 200869588511691769721748289 150652191383768827291311217)
        ·
          refine ⟨112989143537826620468483413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 150652191383768827291311217 112989143537826620468483413)
          ·
            refine ⟨10344465045577388348555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 15 112989143537826620468483413 10344465045577388348555)
            ·
              rfl

theorem cell23_4895423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 15].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 15].length) (baseStart_4895423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4895423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4895423 prefixEnd_4895423 := by exact prefixLift 4895423
  have htrace : WordTrace (prefixWord ++ tailWord_4895423) baseStart_4895423 baseEnd_4895423 := by
    simpa [prefixWord, tailWord_4895423, baseEnd_4895423] using wordTrace_append hprefix tailTrace_4895423
  have hstable : (prefixWord ++ tailWord_4895423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4895423).length < 2 ^ (prefixWord ++ tailWord_4895423).sum := by decide
  have hdescent : baseEnd_4895423 < baseStart_4895423 := by decide
  rcases family_descends (prefixWord ++ tailWord_4895423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4895428 : List Nat := [2, 3, 3, 1, 1, 2, 4, 2, 1, 1, 3]
def baseStart_4895428 : Nat := 118140960795 + 4895428 * 2 ^ 59
def prefixEnd_4895428 : Nat := 4983230072969 + 3 ^ 40 * 4895428 * 2
def baseEnd_4895428 : Nat := 2513707573478577849136343

theorem tailTrace_4895428 : CollatzResearch.WordTrace tailWord_4895428 prefixEnd_4895428 2513707573478577849136343 := by
  unfold tailWord_4895428
  simp only [CollatzResearch.WordTrace]
  refine ⟨89275463854353951692187469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119033951805805268922916625 89275463854353951692187469)
  ·
    refine ⟨33478298945382731884570301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 89275463854353951692187469 33478298945382731884570301)
    ·
      refine ⟨12554362104518524456713863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33478298945382731884570301 12554362104518524456713863)
      ·
        refine ⟨18831543156777786685070795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12554362104518524456713863 18831543156777786685070795)
        ·
          refine ⟨28247314735166680027606193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18831543156777786685070795 28247314735166680027606193)
          ·
            refine ⟨21185486051375010020704645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28247314735166680027606193 21185486051375010020704645)
            ·
              refine ⟨3972278634632814378882121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21185486051375010020704645 3972278634632814378882121)
              ·
                refine ⟨2979208975974610784161591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3972278634632814378882121 2979208975974610784161591)
                ·
                  refine ⟨4468813463961916176242387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2979208975974610784161591 4468813463961916176242387)
                  ·
                    refine ⟨6703220195942874264363581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4468813463961916176242387 6703220195942874264363581)
                    ·
                      refine ⟨2513707573478577849136343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6703220195942874264363581 2513707573478577849136343)
                      ·
                        rfl

theorem cell23_4895428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 4, 2, 1, 1, 3].length) (baseStart_4895428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4895428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4895428 prefixEnd_4895428 := by exact prefixLift 4895428
  have htrace : WordTrace (prefixWord ++ tailWord_4895428) baseStart_4895428 baseEnd_4895428 := by
    simpa [prefixWord, tailWord_4895428, baseEnd_4895428] using wordTrace_append hprefix tailTrace_4895428
  have hstable : (prefixWord ++ tailWord_4895428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4895428).length < 2 ^ (prefixWord ++ tailWord_4895428).sum := by decide
  have hdescent : baseEnd_4895428 < baseStart_4895428 := by decide
  rcases family_descends (prefixWord ++ tailWord_4895428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4895444 : List Nat := [2, 4, 1, 3, 2, 1, 2, 1, 1, 6]
def baseStart_4895444 : Nat := 118140960795 + 4895444 * 2 ^ 59
def prefixEnd_4895444 : Nat := 4983230072969 + 3 ^ 40 * 4895444 * 2
def baseEnd_4895444 : Nat := 837905263056349928845423

theorem tailTrace_4895444 : CollatzResearch.WordTrace tailWord_4895444 prefixEnd_4895444 837905263056349928845423 := by
  unfold tailWord_4895444
  simp only [CollatzResearch.WordTrace]
  refine ⟨89275755638324969058478693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119034340851099958744638257 89275755638324969058478693)
  ·
    refine ⟨16739204182185931698464755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 89275755638324969058478693 16739204182185931698464755)
    ·
      refine ⟨25108806273278897547697133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16739204182185931698464755 25108806273278897547697133)
      ·
        refine ⟨9415802352479586580386425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25108806273278897547697133 9415802352479586580386425)
        ·
          refine ⟨7061851764359689935289819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9415802352479586580386425 7061851764359689935289819)
          ·
            refine ⟨10592777646539534902934729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7061851764359689935289819 10592777646539534902934729)
            ·
              refine ⟨7944583234904651177201047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10592777646539534902934729 7944583234904651177201047)
              ·
                refine ⟨11916874852356976765801571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7944583234904651177201047 11916874852356976765801571)
                ·
                  refine ⟨17875312278535465148702357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11916874852356976765801571 17875312278535465148702357)
                  ·
                    refine ⟨837905263056349928845423, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17875312278535465148702357 837905263056349928845423)
                    ·
                      rfl

theorem cell23_4895444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 1, 2, 1, 1, 6].length) (baseStart_4895444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4895444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4895444 prefixEnd_4895444 := by exact prefixLift 4895444
  have htrace : WordTrace (prefixWord ++ tailWord_4895444) baseStart_4895444 baseEnd_4895444 := by
    simpa [prefixWord, tailWord_4895444, baseEnd_4895444] using wordTrace_append hprefix tailTrace_4895444
  have hstable : (prefixWord ++ tailWord_4895444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4895444).length < 2 ^ (prefixWord ++ tailWord_4895444).sum := by decide
  have hdescent : baseEnd_4895444 < baseStart_4895444 := by decide
  rcases family_descends (prefixWord ++ tailWord_4895444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4895447 : List Nat := [1, 1, 3, 2, 1, 5, 2, 1, 1, 2, 4]
def baseStart_4895447 : Nat := 118140960795 + 4895447 * 2 ^ 59
def prefixEnd_4895447 : Nat := 4983230072969 + 3 ^ 40 * 4895447 * 2
def baseEnd_4895447 : Nat := 2513717329611013274798755

theorem tailTrace_4895447 : CollatzResearch.WordTrace tailWord_4895447 prefixEnd_4895447 2513717329611013274798755 := by
  unfold tailWord_4895447
  simp only [CollatzResearch.WordTrace]
  refine ⟨178551620695639069629316595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119034413797092713086211063 178551620695639069629316595)
  ·
    refine ⟨267827431043458604443974893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 178551620695639069629316595 267827431043458604443974893)
    ·
      refine ⟨100435286641296976666490585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 267827431043458604443974893 100435286641296976666490585)
      ·
        refine ⟨75326464980972732499867939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 100435286641296976666490585 75326464980972732499867939)
        ·
          refine ⟨112989697471459098749801909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75326464980972732499867939 112989697471459098749801909)
          ·
            refine ⟨10592784137949290507793929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 112989697471459098749801909 10592784137949290507793929)
            ·
              refine ⟨7944588103461967880845447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10592784137949290507793929 7944588103461967880845447)
              ·
                refine ⟨11916882155192951821268171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7944588103461967880845447 11916882155192951821268171)
                ·
                  refine ⟨17875323232789427731902257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11916882155192951821268171 17875323232789427731902257)
                  ·
                    refine ⟨13406492424592070798926693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17875323232789427731902257 13406492424592070798926693)
                    ·
                      refine ⟨2513717329611013274798755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13406492424592070798926693 2513717329611013274798755)
                      ·
                        rfl

theorem cell23_4895447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 5, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 5, 2, 1, 1, 2, 4].length) (baseStart_4895447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4895447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4895447 prefixEnd_4895447 := by exact prefixLift 4895447
  have htrace : WordTrace (prefixWord ++ tailWord_4895447) baseStart_4895447 baseEnd_4895447 := by
    simpa [prefixWord, tailWord_4895447, baseEnd_4895447] using wordTrace_append hprefix tailTrace_4895447
  have hstable : (prefixWord ++ tailWord_4895447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4895447).length < 2 ^ (prefixWord ++ tailWord_4895447).sum := by decide
  have hdescent : baseEnd_4895447 < baseStart_4895447 := by decide
  rcases family_descends (prefixWord ++ tailWord_4895447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4895457 : List Nat := [1, 2, 3, 1, 4, 2, 3, 7]
def baseStart_4895457 : Nat := 118140960795 + 4895457 * 2 ^ 59
def prefixEnd_4895457 : Nat := 4983230072969 + 3 ^ 40 * 4895457 * 2
def baseEnd_4895457 : Nat := 93100832015465119839767

theorem tailTrace_4895457 : CollatzResearch.WordTrace tailWord_4895457 prefixEnd_4895457 93100832015465119839767 := by
  unfold tailWord_4895457
  simp only [CollatzResearch.WordTrace]
  refine ⟨178551985425602841337180625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119034656950401894224787083 178551985425602841337180625)
  ·
    refine ⟨133913989069202131002885469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 178551985425602841337180625 133913989069202131002885469)
    ·
      refine ⟨50217745900950799126082051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 133913989069202131002885469 50217745900950799126082051)
      ·
        refine ⟨75326618851426198689123077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50217745900950799126082051 75326618851426198689123077)
        ·
          refine ⟨14123741034642412254210577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 75326618851426198689123077 14123741034642412254210577)
          ·
            refine ⟨10592805775981809190657933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14123741034642412254210577 10592805775981809190657933)
            ·
              refine ⟨3972302165993178446496725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10592805775981809190657933 3972302165993178446496725)
              ·
                refine ⟨93100832015465119839767, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3972302165993178446496725 93100832015465119839767)
                ·
                  rfl

theorem cell23_4895457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 2, 3, 7].length) (baseStart_4895457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4895457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4895457 prefixEnd_4895457 := by exact prefixLift 4895457
  have htrace : WordTrace (prefixWord ++ tailWord_4895457) baseStart_4895457 baseEnd_4895457 := by
    simpa [prefixWord, tailWord_4895457, baseEnd_4895457] using wordTrace_append hprefix tailTrace_4895457
  have hstable : (prefixWord ++ tailWord_4895457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4895457).length < 2 ^ (prefixWord ++ tailWord_4895457).sum := by decide
  have hdescent : baseEnd_4895457 < baseStart_4895457 := by decide
  rcases family_descends (prefixWord ++ tailWord_4895457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4895467 : List Nat := [1, 1, 1, 1, 2, 4, 1, 4, 4, 1, 3]
def baseStart_4895467 : Nat := 118140960795 + 4895467 * 2 ^ 59
def prefixEnd_4895467 : Nat := 4983230072969 + 3 ^ 40 * 4895467 * 2
def baseEnd_4895467 : Nat := 2513727599224103196548663

theorem tailTrace_4895467 : CollatzResearch.WordTrace tailWord_4895467 prefixEnd_4895467 2513727599224103196548663 := by
  unfold tailWord_4895467
  simp only [CollatzResearch.WordTrace]
  refine ⟨178552350155566613045044655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119034900103711075363363103 178552350155566613045044655)
  ·
    refine ⟨267828525233349919567566983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 178552350155566613045044655 267828525233349919567566983)
    ·
      refine ⟨401742787850024879351350475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 267828525233349919567566983 401742787850024879351350475)
      ·
        refine ⟨602614181775037319027025713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 401742787850024879351350475 602614181775037319027025713)
        ·
          refine ⟨451960636331277989270269285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 602614181775037319027025713 451960636331277989270269285)
          ·
            refine ⟨84742619312114622988175491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 451960636331277989270269285 84742619312114622988175491)
            ·
              refine ⟨127113928968171934482263237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 84742619312114622988175491 127113928968171934482263237)
              ·
                refine ⟨23833861681532237715424357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 127113928968171934482263237 23833861681532237715424357)
                ·
                  refine ⟨4468849065287294571642067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23833861681532237715424357 4468849065287294571642067)
                  ·
                    refine ⟨6703273597930941857463101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4468849065287294571642067 6703273597930941857463101)
                    ·
                      refine ⟨2513727599224103196548663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6703273597930941857463101 2513727599224103196548663)
                      ·
                        rfl

theorem cell23_4895467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 4, 4, 1, 3].length) (baseStart_4895467 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4895467 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4895467 prefixEnd_4895467 := by exact prefixLift 4895467
  have htrace : WordTrace (prefixWord ++ tailWord_4895467) baseStart_4895467 baseEnd_4895467 := by
    simpa [prefixWord, tailWord_4895467, baseEnd_4895467] using wordTrace_append hprefix tailTrace_4895467
  have hstable : (prefixWord ++ tailWord_4895467).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4895467).length < 2 ^ (prefixWord ++ tailWord_4895467).sum := by decide
  have hdescent : baseEnd_4895467 < baseStart_4895467 := by decide
  rcases family_descends (prefixWord ++ tailWord_4895467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4895471 : List Nat := [1, 1, 2, 1, 5, 4, 2, 1, 1, 2, 3]
def baseStart_4895471 : Nat := 118140960795 + 4895471 * 2 ^ 59
def prefixEnd_4895471 : Nat := 4983230072969 + 3 ^ 40 * 4895471 * 2
def baseEnd_4895471 : Nat := 2513729653146721180898645

theorem tailTrace_4895471 : CollatzResearch.WordTrace tailWord_4895471 prefixEnd_4895471 2513729653146721180898645 := by
  unfold tailWord_4895471
  simp only [CollatzResearch.WordTrace]
  refine ⟨178552496047552121728190267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119034997365034747818793511 178552496047552121728190267)
  ·
    refine ⟨267828744071328182592285401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 178552496047552121728190267 267828744071328182592285401)
    ·
      refine ⟨200871558053496136944214051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 267828744071328182592285401 200871558053496136944214051)
      ·
        refine ⟨301307337080244205416321077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 200871558053496136944214051 301307337080244205416321077)
        ·
          refine ⟨28247562851272894257780101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 301307337080244205416321077 28247562851272894257780101)
          ·
            refine ⟨5296418034613667673333769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 28247562851272894257780101 5296418034613667673333769)
            ·
              refine ⟨3972313525960250755000327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5296418034613667673333769 3972313525960250755000327)
              ·
                refine ⟨5958470288940376132500491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3972313525960250755000327 5958470288940376132500491)
                ·
                  refine ⟨8937705433410564198750737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5958470288940376132500491 8937705433410564198750737)
                  ·
                    refine ⟨6703279075057923149063053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8937705433410564198750737 6703279075057923149063053)
                    ·
                      refine ⟨2513729653146721180898645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6703279075057923149063053 2513729653146721180898645)
                      ·
                        rfl

theorem cell23_4895471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 4, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 4, 2, 1, 1, 2, 3].length) (baseStart_4895471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4895471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4895471 prefixEnd_4895471 := by exact prefixLift 4895471
  have htrace : WordTrace (prefixWord ++ tailWord_4895471) baseStart_4895471 baseEnd_4895471 := by
    simpa [prefixWord, tailWord_4895471, baseEnd_4895471] using wordTrace_append hprefix tailTrace_4895471
  have hstable : (prefixWord ++ tailWord_4895471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4895471).length < 2 ^ (prefixWord ++ tailWord_4895471).sum := by decide
  have hdescent : baseEnd_4895471 < baseStart_4895471 := by decide
  rcases family_descends (prefixWord ++ tailWord_4895471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4895484 : List Nat := [2, 2, 2, 1, 3, 3, 1, 1, 4, 1, 3]
def baseStart_4895484 : Nat := 118140960795 + 4895484 * 2 ^ 59
def prefixEnd_4895484 : Nat := 4983230072969 + 3 ^ 40 * 4895484 * 2
def baseEnd_4895484 : Nat := 2513736328395229630036085

theorem tailTrace_4895484 : CollatzResearch.WordTrace tailWord_4895484 prefixEnd_4895484 2513736328395229630036085 := by
  unfold tailWord_4895484
  simp only [CollatzResearch.WordTrace]
  refine ⟨89276485098252512474206753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119035313464336683298942337 89276485098252512474206753)
  ·
    refine ⟨66957363823689384355655065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89276485098252512474206753 66957363823689384355655065)
    ·
      refine ⟨50218022867767038266741299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66957363823689384355655065 50218022867767038266741299)
      ·
        refine ⟨75327034301650557400111949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50218022867767038266741299 75327034301650557400111949)
        ·
          refine ⟨28247637863118959025041981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 75327034301650557400111949 28247637863118959025041981)
          ·
            refine ⟨10592864198669609634390743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28247637863118959025041981 10592864198669609634390743)
            ·
              refine ⟨15889296298004414451586115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10592864198669609634390743 15889296298004414451586115)
              ·
                refine ⟨23833944447006621677379173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15889296298004414451586115 23833944447006621677379173)
                ·
                  refine ⟨4468864583813741564508595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23833944447006621677379173 4468864583813741564508595)
                  ·
                    refine ⟨6703296875720612346762893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4468864583813741564508595 6703296875720612346762893)
                    ·
                      refine ⟨2513736328395229630036085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6703296875720612346762893 2513736328395229630036085)
                      ·
                        rfl

theorem cell23_4895484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 3, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 3, 1, 1, 4, 1, 3].length) (baseStart_4895484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4895484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4895484 prefixEnd_4895484 := by exact prefixLift 4895484
  have htrace : WordTrace (prefixWord ++ tailWord_4895484) baseStart_4895484 baseEnd_4895484 := by
    simpa [prefixWord, tailWord_4895484, baseEnd_4895484] using wordTrace_append hprefix tailTrace_4895484
  have hstable : (prefixWord ++ tailWord_4895484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4895484).length < 2 ^ (prefixWord ++ tailWord_4895484).sum := by decide
  have hdescent : baseEnd_4895484 < baseStart_4895484 := by decide
  rcases family_descends (prefixWord ++ tailWord_4895484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4895541 : List Nat := [1, 3, 3, 1, 3, 1, 2, 1, 4, 2, 2]
def baseStart_4895541 : Nat := 118140960795 + 4895541 * 2 ^ 59
def prefixEnd_4895541 : Nat := 4983230072969 + 3 ^ 40 * 4895541 * 2
def baseEnd_4895541 : Nat := 2513765596792535907023323

theorem tailTrace_4895541 : CollatzResearch.WordTrace tailWord_4895541 prefixEnd_4895541 2513765596792535907023323 := by
  unfold tailWord_4895541
  simp only [CollatzResearch.WordTrace]
  refine ⟨178555049157298523683238477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119036699438199015788825651 178555049157298523683238477)
  ·
    refine ⟨66958143433986946381214429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 178555049157298523683238477 66958143433986946381214429)
    ·
      refine ⟨25109303787745104892955411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 66958143433986946381214429 25109303787745104892955411)
      ·
        refine ⟨37663955681617657339433117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25109303787745104892955411 37663955681617657339433117)
        ·
          refine ⟨14123983380606621502287419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37663955681617657339433117 14123983380606621502287419)
          ·
            refine ⟨21185975070909932253431129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14123983380606621502287419 21185975070909932253431129)
            ·
              refine ⟨15889481303182449190073347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21185975070909932253431129 15889481303182449190073347)
              ·
                refine ⟨23834221954773673785110021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15889481303182449190073347 23834221954773673785110021)
                ·
                  refine ⟨4468916616520063834708129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23834221954773673785110021 4468916616520063834708129)
                  ·
                    refine ⟨3351687462390047876031097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4468916616520063834708129 3351687462390047876031097)
                    ·
                      refine ⟨2513765596792535907023323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3351687462390047876031097 2513765596792535907023323)
                      ·
                        rfl

theorem cell23_4895541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 2, 1, 4, 2, 2].length) (baseStart_4895541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4895541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4895541 prefixEnd_4895541 := by exact prefixLift 4895541
  have htrace : WordTrace (prefixWord ++ tailWord_4895541) baseStart_4895541 baseEnd_4895541 := by
    simpa [prefixWord, tailWord_4895541, baseEnd_4895541] using wordTrace_append hprefix tailTrace_4895541
  have hstable : (prefixWord ++ tailWord_4895541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4895541).length < 2 ^ (prefixWord ++ tailWord_4895541).sum := by decide
  have hdescent : baseEnd_4895541 < baseStart_4895541 := by decide
  rcases family_descends (prefixWord ++ tailWord_4895541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4895577 : List Nat := [1, 2, 1, 2, 2, 4, 1, 3, 2, 5]
def baseStart_4895577 : Nat := 118140960795 + 4895577 * 2 ^ 59
def prefixEnd_4895577 : Nat := 4983230072969 + 3 ^ 40 * 4895577 * 2
def baseEnd_4895577 : Nat := 837928027365365922057719

theorem tailTrace_4895577 : CollatzResearch.WordTrace tailWord_4895577 prefixEnd_4895577 837928027365365922057719 := by
  unfold tailWord_4895577
  simp only [CollatzResearch.WordTrace]
  refine ⟨178556362185168101831548985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119037574790112067887699323 178556362185168101831548985)
  ·
    refine ⟨133917271638876076373661739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 178556362185168101831548985 133917271638876076373661739)
    ·
      refine ⟨200875907458314114560492609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 133917271638876076373661739 200875907458314114560492609)
      ·
        refine ⟨150656930593735585920369457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 200875907458314114560492609 150656930593735585920369457)
        ·
          refine ⟨112992697945301689440277093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 150656930593735585920369457 112992697945301689440277093)
          ·
            refine ⟨21186130864744066770051955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 112992697945301689440277093 21186130864744066770051955)
            ·
              refine ⟨31779196297116100155077933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21186130864744066770051955 31779196297116100155077933)
              ·
                refine ⟨11917198611418537558154225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31779196297116100155077933 11917198611418537558154225)
                ·
                  refine ⟨8937898958563903168615669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11917198611418537558154225 8937898958563903168615669)
                  ·
                    refine ⟨837928027365365922057719, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8937898958563903168615669 837928027365365922057719)
                    ·
                      rfl

theorem cell23_4895577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 1, 3, 2, 5].length) (baseStart_4895577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4895577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4895577 prefixEnd_4895577 := by exact prefixLift 4895577
  have htrace : WordTrace (prefixWord ++ tailWord_4895577) baseStart_4895577 baseEnd_4895577 := by
    simpa [prefixWord, tailWord_4895577, baseEnd_4895577] using wordTrace_append hprefix tailTrace_4895577
  have hstable : (prefixWord ++ tailWord_4895577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4895577).length < 2 ^ (prefixWord ++ tailWord_4895577).sum := by decide
  have hdescent : baseEnd_4895577 < baseStart_4895577 := by decide
  rcases family_descends (prefixWord ++ tailWord_4895577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4895587 : List Nat := [1, 1, 1, 5, 3, 1, 1, 2, 1, 2, 5]
def baseStart_4895587 : Nat := 118140960795 + 4895587 * 2 ^ 59
def prefixEnd_4895587 : Nat := 4983230072969 + 3 ^ 40 * 4895587 * 2
def baseEnd_4895587 : Nat := 2513789216902642727048111

theorem tailTrace_4895587 : CollatzResearch.WordTrace tailWord_4895587 prefixEnd_4895587 2513789216902642727048111 := by
  unfold tailWord_4895587
  simp only [CollatzResearch.WordTrace]
  refine ⟨178556726915131873539413015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119037817943421249026275343 178556726915131873539413015)
  ·
    refine ⟨267835090372697810309119523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 178556726915131873539413015 267835090372697810309119523)
    ·
      refine ⟨401752635559046715463679285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 267835090372697810309119523 401752635559046715463679285)
      ·
        refine ⟨37664309583660629574719933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 401752635559046715463679285 37664309583660629574719933)
        ·
          refine ⟨14124116093872736090519975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37664309583660629574719933 14124116093872736090519975)
          ·
            refine ⟨21186174140809104135779963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14124116093872736090519975 21186174140809104135779963)
            ·
              refine ⟨31779261211213656203669945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21186174140809104135779963 31779261211213656203669945)
              ·
                refine ⟨23834445908410242152752459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31779261211213656203669945 23834445908410242152752459)
                ·
                  refine ⟨35751668862615363229128689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23834445908410242152752459 35751668862615363229128689)
                  ·
                    refine ⟨26813751646961522421846517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 35751668862615363229128689 26813751646961522421846517)
                    ·
                      refine ⟨2513789216902642727048111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26813751646961522421846517 2513789216902642727048111)
                      ·
                        rfl

theorem cell23_4895587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 1, 2, 1, 2, 5].length) (baseStart_4895587 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4895587 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4895587 prefixEnd_4895587 := by exact prefixLift 4895587
  have htrace : WordTrace (prefixWord ++ tailWord_4895587) baseStart_4895587 baseEnd_4895587 := by
    simpa [prefixWord, tailWord_4895587, baseEnd_4895587] using wordTrace_append hprefix tailTrace_4895587
  have hstable : (prefixWord ++ tailWord_4895587).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4895587).length < 2 ^ (prefixWord ++ tailWord_4895587).sum := by decide
  have hdescent : baseEnd_4895587 < baseStart_4895587 := by decide
  rcases family_descends (prefixWord ++ tailWord_4895587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4895597 : List Nat := [1, 5, 1, 1, 1, 1, 1, 2, 3, 3, 4]
def baseStart_4895597 : Nat := 118140960795 + 4895597 * 2 ^ 59
def prefixEnd_4895597 : Nat := 4983230072969 + 3 ^ 40 * 4895597 * 2
def baseEnd_4895597 : Nat := 2513794351709187687923065

theorem tailTrace_4895597 : CollatzResearch.WordTrace tailWord_4895597 prefixEnd_4895597 2513794351709187687923065 := by
  unfold tailWord_4895597
  simp only [CollatzResearch.WordTrace]
  refine ⟨178557091645095645247277045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119038061096730430164851363 178557091645095645247277045)
  ·
    refine ⟨16739727341727716741932223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 178557091645095645247277045 16739727341727716741932223)
    ·
      refine ⟨25109591012591575112898335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16739727341727716741932223 25109591012591575112898335)
      ·
        refine ⟨37664386518887362669347503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25109591012591575112898335 37664386518887362669347503)
        ·
          refine ⟨56496579778331044004021255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37664386518887362669347503 56496579778331044004021255)
          ·
            refine ⟨84744869667496566006031883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56496579778331044004021255 84744869667496566006031883)
            ·
              refine ⟨127117304501244849009047825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 84744869667496566006031883 127117304501244849009047825)
              ·
                refine ⟨95337978375933636756785869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 127117304501244849009047825 95337978375933636756785869)
                ·
                  refine ⟨35751741890975113783794701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 95337978375933636756785869 35751741890975113783794701)
                  ·
                    refine ⟨13406903209115667668923013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 35751741890975113783794701 13406903209115667668923013)
                    ·
                      refine ⟨2513794351709187687923065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13406903209115667668923013 2513794351709187687923065)
                      ·
                        rfl

theorem cell23_4895597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 2, 3, 3, 4].length) (baseStart_4895597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4895597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4895597 prefixEnd_4895597 := by exact prefixLift 4895597
  have htrace : WordTrace (prefixWord ++ tailWord_4895597) baseStart_4895597 baseEnd_4895597 := by
    simpa [prefixWord, tailWord_4895597, baseEnd_4895597] using wordTrace_append hprefix tailTrace_4895597
  have hstable : (prefixWord ++ tailWord_4895597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4895597).length < 2 ^ (prefixWord ++ tailWord_4895597).sum := by decide
  have hdescent : baseEnd_4895597 < baseStart_4895597 := by decide
  rcases family_descends (prefixWord ++ tailWord_4895597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4895607 : List Nat := [1, 1, 3, 1, 1, 2, 1, 2, 7, 4]
def baseStart_4895607 : Nat := 118140960795 + 4895607 * 2 ^ 59
def prefixEnd_4895607 : Nat := 4983230072969 + 3 ^ 40 * 4895607 * 2
def baseEnd_4895607 : Nat := 837933162171910882932673

theorem tailTrace_4895607 : CollatzResearch.WordTrace tailWord_4895607 prefixEnd_4895607 837933162171910882932673 := by
  unfold tailWord_4895607
  simp only [CollatzResearch.WordTrace]
  refine ⟨178557456375059416955141075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119038304250039611303427383 178557456375059416955141075)
  ·
    refine ⟨267836184562589125432711613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 178557456375059416955141075 267836184562589125432711613)
    ·
      refine ⟨100438569210970922037266855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 267836184562589125432711613 100438569210970922037266855)
      ·
        refine ⟨150657853816456383055900283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100438569210970922037266855 150657853816456383055900283)
        ·
          refine ⟨225986780724684574583850425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 150657853816456383055900283 225986780724684574583850425)
          ·
            refine ⟨169490085543513430937887819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 225986780724684574583850425 169490085543513430937887819)
            ·
              refine ⟨254235128315270146406831729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 169490085543513430937887819 254235128315270146406831729)
              ·
                refine ⟨190676346236452609805123797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 254235128315270146406831729 190676346236452609805123797)
                ·
                  refine ⟨4468976864916858042307589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 190676346236452609805123797 4468976864916858042307589)
                  ·
                    refine ⟨837933162171910882932673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4468976864916858042307589 837933162171910882932673)
                    ·
                      rfl

theorem cell23_4895607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 2, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 2, 7, 4].length) (baseStart_4895607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4895607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4895607 prefixEnd_4895607 := by exact prefixLift 4895607
  have htrace : WordTrace (prefixWord ++ tailWord_4895607) baseStart_4895607 baseEnd_4895607 := by
    simpa [prefixWord, tailWord_4895607, baseEnd_4895607] using wordTrace_append hprefix tailTrace_4895607
  have hstable : (prefixWord ++ tailWord_4895607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4895607).length < 2 ^ (prefixWord ++ tailWord_4895607).sum := by decide
  have hdescent : baseEnd_4895607 < baseStart_4895607 := by decide
  rcases family_descends (prefixWord ++ tailWord_4895607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4895624 : List Nat := [2, 1, 3, 3, 2, 1, 1, 1, 5, 4]
def baseStart_4895624 : Nat := 118140960795 + 4895624 * 2 ^ 59
def prefixEnd_4895624 : Nat := 4983230072969 + 3 ^ 40 * 4895624 * 2
def baseEnd_4895624 : Nat := 837936071895619694095147

theorem tailTrace_4895624 : CollatzResearch.WordTrace tailWord_4895624 prefixEnd_4895624 837936071895619694095147 := by
  unfold tailWord_4895624
  simp only [CollatzResearch.WordTrace]
  refine ⟨89279038207998914429254963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119038717610665219239006617 89279038207998914429254963)
  ·
    refine ⟨133918557311998371643882445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89279038207998914429254963 133918557311998371643882445)
    ·
      refine ⟨50219458991999389366455917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 133918557311998371643882445 50219458991999389366455917)
      ·
        refine ⟨18832297121999771012420969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 50219458991999389366455917 18832297121999771012420969)
        ·
          refine ⟨14124222841499828259315727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18832297121999771012420969 14124222841499828259315727)
          ·
            refine ⟨21186334262249742388973591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14124222841499828259315727 21186334262249742388973591)
            ·
              refine ⟨31779501393374613583460387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21186334262249742388973591 31779501393374613583460387)
              ·
                refine ⟨47669252090061920375190581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31779501393374613583460387 47669252090061920375190581)
                ·
                  refine ⟨4468992383443305035174117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 47669252090061920375190581 4468992383443305035174117)
                  ·
                    refine ⟨837936071895619694095147, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4468992383443305035174117 837936071895619694095147)
                    ·
                      rfl

theorem cell23_4895624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 1, 1, 5, 4].length) (baseStart_4895624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4895624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4895624 prefixEnd_4895624 := by exact prefixLift 4895624
  have htrace : WordTrace (prefixWord ++ tailWord_4895624) baseStart_4895624 baseEnd_4895624 := by
    simpa [prefixWord, tailWord_4895624, baseEnd_4895624] using wordTrace_append hprefix tailTrace_4895624
  have hstable : (prefixWord ++ tailWord_4895624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4895624).length < 2 ^ (prefixWord ++ tailWord_4895624).sum := by decide
  have hdescent : baseEnd_4895624 < baseStart_4895624 := by decide
  rcases family_descends (prefixWord ++ tailWord_4895624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4895667 : List Nat := [1, 1, 1, 2, 3, 1, 2, 4, 3, 5]
def baseStart_4895667 : Nat := 118140960795 + 4895667 * 2 ^ 59
def prefixEnd_4895667 : Nat := 4983230072969 + 3 ^ 40 * 4895667 * 2
def baseEnd_4895667 : Nat := 837943431785000804682581

theorem tailTrace_4895667 : CollatzResearch.WordTrace tailWord_4895667 prefixEnd_4895667 837943431785000804682581 := by
  unfold tailWord_4895667
  simp only [CollatzResearch.WordTrace]
  refine ⟨178559644754842047202325255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119039763169894698134883503 178559644754842047202325255)
  ·
    refine ⟨267839467132263070803487883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 178559644754842047202325255 267839467132263070803487883)
    ·
      refine ⟨401759200698394606205231825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 267839467132263070803487883 401759200698394606205231825)
      ·
        refine ⟨301319400523795954653923869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 401759200698394606205231825 301319400523795954653923869)
        ·
          refine ⟨112994775196423482995221451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 301319400523795954653923869 112994775196423482995221451)
          ·
            refine ⟨169492162794635224492832177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 112994775196423482995221451 169492162794635224492832177)
            ·
              refine ⟨127119122095976418369624133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 169492162794635224492832177 127119122095976418369624133)
              ·
                refine ⟨23834835392995578444304525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 127119122095976418369624133 23834835392995578444304525)
                ·
                  refine ⟨8938063272373341916614197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23834835392995578444304525 8938063272373341916614197)
                  ·
                    refine ⟨837943431785000804682581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8938063272373341916614197 837943431785000804682581)
                    ·
                      rfl

theorem cell23_4895667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 4, 3, 5].length) (baseStart_4895667 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4895667 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4895667 prefixEnd_4895667 := by exact prefixLift 4895667
  have htrace : WordTrace (prefixWord ++ tailWord_4895667) baseStart_4895667 baseEnd_4895667 := by
    simpa [prefixWord, tailWord_4895667, baseEnd_4895667] using wordTrace_append hprefix tailTrace_4895667
  have hstable : (prefixWord ++ tailWord_4895667).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4895667).length < 2 ^ (prefixWord ++ tailWord_4895667).sum := by decide
  have hdescent : baseEnd_4895667 < baseStart_4895667 := by decide
  rcases family_descends (prefixWord ++ tailWord_4895667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4895674 : List Nat := [3, 1, 1, 1, 2, 1, 3, 1, 3, 5, 2]
def baseStart_4895674 : Nat := 118140960795 + 4895674 * 2 ^ 59
def prefixEnd_4895674 : Nat := 4983230072969 + 3 ^ 40 * 4895674 * 2
def baseEnd_4895674 : Nat := 2513833889719583886660211

theorem tailTrace_4895674 : CollatzResearch.WordTrace tailWord_4895674 prefixEnd_4895674 2513833889719583886660211 := by
  unfold tailWord_4895674
  simp only [CollatzResearch.WordTrace]
  refine ⟨44639975016454171849457519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 119039933377211124931886717 44639975016454171849457519)
  ·
    refine ⟨66959962524681257774186279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44639975016454171849457519 66959962524681257774186279)
    ·
      refine ⟨100439943787021886661279419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66959962524681257774186279 100439943787021886661279419)
      ·
        refine ⟨150659915680532829991919129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100439943787021886661279419 150659915680532829991919129)
        ·
          refine ⟨112994936760399622493939347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 150659915680532829991919129 112994936760399622493939347)
          ·
            refine ⟨169492405140599433740909021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 112994936760399622493939347 169492405140599433740909021)
            ·
              refine ⟨63559651927724787652840883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 169492405140599433740909021 63559651927724787652840883)
              ·
                refine ⟨95339477891587181479261325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 63559651927724787652840883 95339477891587181479261325)
                ·
                  refine ⟨35752304209345193054722997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 95339477891587181479261325 35752304209345193054722997)
                  ·
                    refine ⟨3351778519626111848880281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 35752304209345193054722997 3351778519626111848880281)
                    ·
                      refine ⟨2513833889719583886660211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3351778519626111848880281 2513833889719583886660211)
                      ·
                        rfl

theorem cell23_4895674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 3, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 3, 1, 3, 5, 2].length) (baseStart_4895674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4895674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4895674 prefixEnd_4895674 := by exact prefixLift 4895674
  have htrace : WordTrace (prefixWord ++ tailWord_4895674) baseStart_4895674 baseEnd_4895674 := by
    simpa [prefixWord, tailWord_4895674, baseEnd_4895674] using wordTrace_append hprefix tailTrace_4895674
  have hstable : (prefixWord ++ tailWord_4895674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4895674).length < 2 ^ (prefixWord ++ tailWord_4895674).sum := by decide
  have hdescent : baseEnd_4895674 < baseStart_4895674 := by decide
  rcases family_descends (prefixWord ++ tailWord_4895674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4895697 : List Nat := [1, 2, 2, 1, 2, 1, 4, 1, 3, 6]
def baseStart_4895697 : Nat := 118140960795 + 4895697 * 2 ^ 59
def prefixEnd_4895697 : Nat := 4983230072969 + 3 ^ 40 * 4895697 * 2
def baseEnd_4895697 : Nat := 837948566591545765557535

theorem tailTrace_4895697 : CollatzResearch.WordTrace tailWord_4895697 prefixEnd_4895697 837948566591545765557535 := by
  unfold tailWord_4895697
  simp only [CollatzResearch.WordTrace]
  refine ⟨178560738944733362325917345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119040492629822241550611563 178560738944733362325917345)
  ·
    refine ⟨133920554208550021744438009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 178560738944733362325917345 133920554208550021744438009)
    ·
      refine ⟨100440415656412516308328507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 133920554208550021744438009 100440415656412516308328507)
      ·
        refine ⟨150660623484618774462492761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100440415656412516308328507 150660623484618774462492761)
        ·
          refine ⟨112995467613464080846869571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 150660623484618774462492761 112995467613464080846869571)
          ·
            refine ⟨169493201420196121270304357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 112995467613464080846869571 169493201420196121270304357)
            ·
              refine ⟨31779975266286772738182067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 169493201420196121270304357 31779975266286772738182067)
              ·
                refine ⟨47669962899430159107273101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31779975266286772738182067 47669962899430159107273101)
                ·
                  refine ⟨17876236087286309665227413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 47669962899430159107273101 17876236087286309665227413)
                  ·
                    refine ⟨837948566591545765557535, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17876236087286309665227413 837948566591545765557535)
                    ·
                      rfl

theorem cell23_4895697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 4, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 4, 1, 3, 6].length) (baseStart_4895697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4895697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4895697 prefixEnd_4895697 := by exact prefixLift 4895697
  have htrace : WordTrace (prefixWord ++ tailWord_4895697) baseStart_4895697 baseEnd_4895697 := by
    simpa [prefixWord, tailWord_4895697, baseEnd_4895697] using wordTrace_append hprefix tailTrace_4895697
  have hstable : (prefixWord ++ tailWord_4895697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4895697).length < 2 ^ (prefixWord ++ tailWord_4895697).sum := by decide
  have hdescent : baseEnd_4895697 < baseStart_4895697 := by decide
  rcases family_descends (prefixWord ++ tailWord_4895697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4895715 : List Nat := [1, 1, 1, 6, 1, 1, 5, 2, 1, 1, 3]
def baseStart_4895715 : Nat := 118140960795 + 4895715 * 2 ^ 59
def prefixEnd_4895715 : Nat := 4983230072969 + 3 ^ 40 * 4895715 * 2
def baseEnd_4895715 : Nat := 2513854942426418226247523

theorem tailTrace_4895715 : CollatzResearch.WordTrace tailWord_4895715 prefixEnd_4895715 2513854942426418226247523 := by
  unfold tailWord_4895715
  simp only [CollatzResearch.WordTrace]
  refine ⟨178561395458668151400072599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119040930305778767600048399 178561395458668151400072599)
  ·
    refine ⟨267842093188002227100108899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 178561395458668151400072599 267842093188002227100108899)
    ·
      refine ⟨401763139782003340650163349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 267842093188002227100108899 401763139782003340650163349)
      ·
        refine ⟨18832647177281406592976407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 401763139782003340650163349 18832647177281406592976407)
        ·
          refine ⟨28248970765922109889464611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18832647177281406592976407 28248970765922109889464611)
          ·
            refine ⟨42373456148883164834196917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28248970765922109889464611 42373456148883164834196917)
            ·
              refine ⟨3972511513957796703205961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 42373456148883164834196917 3972511513957796703205961)
              ·
                refine ⟨2979383635468347527404471, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3972511513957796703205961 2979383635468347527404471)
                ·
                  refine ⟨4469075453202521291106707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2979383635468347527404471 4469075453202521291106707)
                  ·
                    refine ⟨6703613179803781936660061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4469075453202521291106707 6703613179803781936660061)
                    ·
                      refine ⟨2513854942426418226247523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6703613179803781936660061 2513854942426418226247523)
                      ·
                        rfl

theorem cell23_4895715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 5, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 5, 2, 1, 1, 3].length) (baseStart_4895715 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4895715 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4895715 prefixEnd_4895715 := by exact prefixLift 4895715
  have htrace : WordTrace (prefixWord ++ tailWord_4895715) baseStart_4895715 baseEnd_4895715 := by
    simpa [prefixWord, tailWord_4895715, baseEnd_4895715] using wordTrace_append hprefix tailTrace_4895715
  have hstable : (prefixWord ++ tailWord_4895715).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4895715).length < 2 ^ (prefixWord ++ tailWord_4895715).sum := by decide
  have hdescent : baseEnd_4895715 < baseStart_4895715 := by decide
  rcases family_descends (prefixWord ++ tailWord_4895715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4895727 : List Nat := [1, 1, 2, 1, 4, 3, 1, 10]
def baseStart_4895727 : Nat := 118140960795 + 4895727 * 2 ^ 59
def prefixEnd_4895727 : Nat := 4983230072969 + 3 ^ 40 * 4895727 * 2
def baseEnd_4895727 : Nat := 93105966822010080714721

theorem tailTrace_4895727 : CollatzResearch.WordTrace tailWord_4895727 prefixEnd_4895727 93105966822010080714721 := by
  unfold tailWord_4895727
  simp only [CollatzResearch.WordTrace]
  refine ⟨178561833134624677449509435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119041222089749784966339623 178561833134624677449509435)
  ·
    refine ⟨267842749701937016174264153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 178561833134624677449509435 267842749701937016174264153)
    ·
      refine ⟨200882062276452762130698115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 267842749701937016174264153 200882062276452762130698115)
      ·
        refine ⟨301323093414679143196047173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 200882062276452762130698115 301323093414679143196047173)
        ·
          refine ⟨56498080015252339349258845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 301323093414679143196047173 56498080015252339349258845)
          ·
            refine ⟨21186780005719627255972067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 56498080015252339349258845 21186780005719627255972067)
            ·
              refine ⟨31780170008579440883958101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21186780005719627255972067 31780170008579440883958101)
              ·
                refine ⟨93105966822010080714721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 31780170008579440883958101 93105966822010080714721)
                ·
                  rfl

theorem cell23_4895727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 1, 10].length) (baseStart_4895727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4895727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4895727 prefixEnd_4895727 := by exact prefixLift 4895727
  have htrace : WordTrace (prefixWord ++ tailWord_4895727) baseStart_4895727 baseEnd_4895727 := by
    simpa [prefixWord, tailWord_4895727, baseEnd_4895727] using wordTrace_append hprefix tailTrace_4895727
  have hstable : (prefixWord ++ tailWord_4895727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4895727).length < 2 ^ (prefixWord ++ tailWord_4895727).sum := by decide
  have hdescent : baseEnd_4895727 < baseStart_4895727 := by decide
  rcases family_descends (prefixWord ++ tailWord_4895727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4895772 : List Nat := [2, 2, 3, 1, 4, 1, 1, 4, 1, 2, 2]
def baseStart_4895772 : Nat := 118140960795 + 4895772 * 2 ^ 59
def prefixEnd_4895772 : Nat := 4983230072969 + 3 ^ 40 * 4895772 * 2
def baseEnd_4895772 : Nat := 2513884210823724503234761

theorem tailTrace_4895772 : CollatzResearch.WordTrace tailWord_4895772 prefixEnd_4895772 2513884210823724503234761 := by
  unfold tailWord_4895772
  simp only [CollatzResearch.WordTrace]
  refine ⟨89281737209730825067448785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119042316279641100089931713 89281737209730825067448785)
  ·
    refine ⟨66961302907298118800586589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89281737209730825067448785 66961302907298118800586589)
    ·
      refine ⟨25110488590236794550219971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 66961302907298118800586589 25110488590236794550219971)
      ·
        refine ⟨37665732885355191825329957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25110488590236794550219971 37665732885355191825329957)
        ·
          refine ⟨7062324916004098467249367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 37665732885355191825329957 7062324916004098467249367)
          ·
            refine ⟨10593487374006147700874051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7062324916004098467249367 10593487374006147700874051)
            ·
              refine ⟨15890231061009221551311077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10593487374006147700874051 15890231061009221551311077)
              ·
                refine ⟨2979418323939229040870827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15890231061009221551311077 2979418323939229040870827)
                ·
                  refine ⟨4469127485908843561306241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2979418323939229040870827 4469127485908843561306241)
                  ·
                    refine ⟨3351845614431632670979681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4469127485908843561306241 3351845614431632670979681)
                    ·
                      refine ⟨2513884210823724503234761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3351845614431632670979681 2513884210823724503234761)
                      ·
                        rfl

theorem cell23_4895772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 1, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 1, 1, 4, 1, 2, 2].length) (baseStart_4895772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4895772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4895772 prefixEnd_4895772 := by exact prefixLift 4895772
  have htrace : WordTrace (prefixWord ++ tailWord_4895772) baseStart_4895772 baseEnd_4895772 := by
    simpa [prefixWord, tailWord_4895772, baseEnd_4895772] using wordTrace_append hprefix tailTrace_4895772
  have hstable : (prefixWord ++ tailWord_4895772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4895772).length < 2 ^ (prefixWord ++ tailWord_4895772).sum := by decide
  have hdescent : baseEnd_4895772 < baseStart_4895772 := by decide
  rcases family_descends (prefixWord ++ tailWord_4895772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4895781 : List Nat := [1, 3, 1, 2, 2, 2, 1, 1, 5, 3, 2]
def baseStart_4895781 : Nat := 118140960795 + 4895781 * 2 ^ 59
def prefixEnd_4895781 : Nat := 4983230072969 + 3 ^ 40 * 4895781 * 2
def baseEnd_4895781 : Nat := 2513888832149614968022219

theorem tailTrace_4895781 : CollatzResearch.WordTrace tailWord_4895781 prefixEnd_4895781 2513888832149614968022219 := by
  unfold tailWord_4895781
  simp only [CollatzResearch.WordTrace]
  refine ⟨178563802676429044671975197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119042535117619363114650131 178563802676429044671975197)
  ·
    refine ⟨66961426003660891751990699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 178563802676429044671975197 66961426003660891751990699)
    ·
      refine ⟨100442139005491337627986049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66961426003660891751990699 100442139005491337627986049)
      ·
        refine ⟨75331604254118503220989537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 100442139005491337627986049 75331604254118503220989537)
        ·
          refine ⟨56498703190588877415742153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 75331604254118503220989537 56498703190588877415742153)
          ·
            refine ⟨42374027392941658061806615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56498703190588877415742153 42374027392941658061806615)
            ·
              refine ⟨63561041089412487092709923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42374027392941658061806615 63561041089412487092709923)
              ·
                refine ⟨95341561634118730639064885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 63561041089412487092709923 95341561634118730639064885)
                ·
                  refine ⟨8938271403198630997412333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 95341561634118730639064885 8938271403198630997412333)
                  ·
                    refine ⟨3351851776199486624029625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8938271403198630997412333 3351851776199486624029625)
                    ·
                      refine ⟨2513888832149614968022219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3351851776199486624029625 2513888832149614968022219)
                      ·
                        rfl

theorem cell23_4895781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 1, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 1, 1, 5, 3, 2].length) (baseStart_4895781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4895781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4895781 prefixEnd_4895781 := by exact prefixLift 4895781
  have htrace : WordTrace (prefixWord ++ tailWord_4895781) baseStart_4895781 baseEnd_4895781 := by
    simpa [prefixWord, tailWord_4895781, baseEnd_4895781] using wordTrace_append hprefix tailTrace_4895781
  have hstable : (prefixWord ++ tailWord_4895781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4895781).length < 2 ^ (prefixWord ++ tailWord_4895781).sum := by decide
  have hdescent : baseEnd_4895781 < baseStart_4895781 := by decide
  rcases family_descends (prefixWord ++ tailWord_4895781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4895794 : List Nat := [3, 2, 1, 1, 2, 2, 1, 2, 2, 3, 4]
def baseStart_4895794 : Nat := 118140960795 + 4895794 * 2 ^ 59
def prefixEnd_4895794 : Nat := 4983230072969 + 3 ^ 40 * 4895794 * 2
def baseEnd_4895794 : Nat := 2513895507398123417159659

theorem tailTrace_4895794 : CollatzResearch.WordTrace tailWord_4895794 prefixEnd_4895794 2513895507398123417159659 := by
  unfold tailWord_4895794
  simp only [CollatzResearch.WordTrace]
  refine ⟨44641069206345486973049609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 119042851216921298594798957 44641069206345486973049609)
  ·
    refine ⟨33480801904759115229787207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44641069206345486973049609 33480801904759115229787207)
    ·
      refine ⟨50221202857138672844680811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33480801904759115229787207 50221202857138672844680811)
      ·
        refine ⟨75331804285708009267021217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50221202857138672844680811 75331804285708009267021217)
        ·
          refine ⟨56498853214281006950265913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 75331804285708009267021217 56498853214281006950265913)
          ·
            refine ⟨42374139910710755212699435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56498853214281006950265913 42374139910710755212699435)
            ·
              refine ⟨63561209866066132819049153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42374139910710755212699435 63561209866066132819049153)
              ·
                refine ⟨47670907399549599614286865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 63561209866066132819049153 47670907399549599614286865)
                ·
                  refine ⟨35753180549662199710715149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 47670907399549599614286865 35753180549662199710715149)
                  ·
                    refine ⟨13407442706123324891518181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 35753180549662199710715149 13407442706123324891518181)
                    ·
                      refine ⟨2513895507398123417159659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13407442706123324891518181 2513895507398123417159659)
                      ·
                        rfl

theorem cell23_4895794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 1, 2, 2, 3, 4].length) (baseStart_4895794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4895794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4895794 prefixEnd_4895794 := by exact prefixLift 4895794
  have htrace : WordTrace (prefixWord ++ tailWord_4895794) baseStart_4895794 baseEnd_4895794 := by
    simpa [prefixWord, tailWord_4895794, baseEnd_4895794] using wordTrace_append hprefix tailTrace_4895794
  have hstable : (prefixWord ++ tailWord_4895794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4895794).length < 2 ^ (prefixWord ++ tailWord_4895794).sum := by decide
  have hdescent : baseEnd_4895794 < baseStart_4895794 := by decide
  rcases family_descends (prefixWord ++ tailWord_4895794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4895811 : List Nat := [1, 1, 1, 3, 1, 2, 3, 4, 1, 4, 2]
def baseStart_4895811 : Nat := 118140960795 + 4895811 * 2 ^ 59
def prefixEnd_4895811 : Nat := 4983230072969 + 3 ^ 40 * 4895811 * 2
def baseEnd_4895811 : Nat := 2513904236569249850647081

theorem tailTrace_4895811 : CollatzResearch.WordTrace tailWord_4895811 prefixEnd_4895811 2513904236569249850647081 := by
  unfold tailWord_4895811
  simp only [CollatzResearch.WordTrace]
  refine ⟨178564896866320359795567287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119043264577546906530378191 178564896866320359795567287)
  ·
    refine ⟨267847345299480539693350931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 178564896866320359795567287 267847345299480539693350931)
    ·
      refine ⟨401771017949220809540026397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 267847345299480539693350931 401771017949220809540026397)
      ·
        refine ⟨150664131730957803577509899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 401771017949220809540026397 150664131730957803577509899)
        ·
          refine ⟨225996197596436705366264849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 150664131730957803577509899 225996197596436705366264849)
          ·
            refine ⟨169497148197327529024698637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 225996197596436705366264849 169497148197327529024698637)
            ·
              refine ⟨63561430573997823384261989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 169497148197327529024698637 63561430573997823384261989)
              ·
                refine ⟨11917768232624591884549123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 63561430573997823384261989 11917768232624591884549123)
                ·
                  refine ⟨17876652348936887826823685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11917768232624591884549123 17876652348936887826823685)
                  ·
                    refine ⟨3351872315425666467529441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17876652348936887826823685 3351872315425666467529441)
                    ·
                      refine ⟨2513904236569249850647081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3351872315425666467529441 2513904236569249850647081)
                      ·
                        rfl

theorem cell23_4895811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 3, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 3, 4, 1, 4, 2].length) (baseStart_4895811 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4895811 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4895811 prefixEnd_4895811 := by exact prefixLift 4895811
  have htrace : WordTrace (prefixWord ++ tailWord_4895811) baseStart_4895811 baseEnd_4895811 := by
    simpa [prefixWord, tailWord_4895811, baseEnd_4895811] using wordTrace_append hprefix tailTrace_4895811
  have hstable : (prefixWord ++ tailWord_4895811).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4895811).length < 2 ^ (prefixWord ++ tailWord_4895811).sum := by decide
  have hdescent : baseEnd_4895811 < baseStart_4895811 := by decide
  rcases family_descends (prefixWord ++ tailWord_4895811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4895815 : List Nat := [1, 1, 4, 1, 3, 2, 4, 1, 1, 3, 2]
def baseStart_4895815 : Nat := 118140960795 + 4895815 * 2 ^ 59
def prefixEnd_4895815 : Nat := 4983230072969 + 3 ^ 40 * 4895815 * 2
def baseEnd_4895815 : Nat := 2513906290491867834997063

theorem tailTrace_4895815 : CollatzResearch.WordTrace tailWord_4895815 prefixEnd_4895815 2513906290491867834997063 := by
  unfold tailWord_4895815
  simp only [CollatzResearch.WordTrace]
  refine ⟨178565042758305868478712899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119043361838870578985808599 178565042758305868478712899)
  ·
    refine ⟨267847564137458802718069349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 178565042758305868478712899 267847564137458802718069349)
    ·
      refine ⟨50221418275773525509638003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 267847564137458802718069349 50221418275773525509638003)
      ·
        refine ⟨75332127413660288264457005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50221418275773525509638003 75332127413660288264457005)
        ·
          refine ⟨28249547780122608099171377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 75332127413660288264457005 28249547780122608099171377)
          ·
            refine ⟨21187160835091956074378533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28249547780122608099171377 21187160835091956074378533)
            ·
              refine ⟨3972592656579741763945975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21187160835091956074378533 3972592656579741763945975)
              ·
                refine ⟨5958888984869612645918963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3972592656579741763945975 5958888984869612645918963)
                ·
                  refine ⟨8938333477304418968878445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5958888984869612645918963 8938333477304418968878445)
                  ·
                    refine ⟨3351875053989157113329417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8938333477304418968878445 3351875053989157113329417)
                    ·
                      refine ⟨2513906290491867834997063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3351875053989157113329417 2513906290491867834997063)
                      ·
                        rfl

theorem cell23_4895815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 4, 1, 1, 3, 2].length) (baseStart_4895815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4895815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4895815 prefixEnd_4895815 := by exact prefixLift 4895815
  have htrace : WordTrace (prefixWord ++ tailWord_4895815) baseStart_4895815 baseEnd_4895815 := by
    simpa [prefixWord, tailWord_4895815, baseEnd_4895815] using wordTrace_append hprefix tailTrace_4895815
  have hstable : (prefixWord ++ tailWord_4895815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4895815).length < 2 ^ (prefixWord ++ tailWord_4895815).sum := by decide
  have hdescent : baseEnd_4895815 < baseStart_4895815 := by decide
  rcases family_descends (prefixWord ++ tailWord_4895815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4895821 : List Nat := [1, 6, 1, 1, 1, 2, 1, 2, 2, 6]
def baseStart_4895821 : Nat := 118140960795 + 4895821 * 2 ^ 59
def prefixEnd_4895821 : Nat := 4983230072969 + 3 ^ 40 * 4895821 * 2
def baseEnd_4895821 : Nat := 837969790458598270507345

theorem tailTrace_4895821 : CollatzResearch.WordTrace tailWord_4895821 prefixEnd_4895821 837969790458598270507345 := by
  unfold tailWord_4895821
  simp only [CollatzResearch.WordTrace]
  refine ⟨178565261596284131503431317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119043507730856087668954211 178565261596284131503431317)
  ·
    refine ⟨8370246637325818664223343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 178565261596284131503431317 8370246637325818664223343)
    ·
      refine ⟨12555369955988727996335015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8370246637325818664223343 12555369955988727996335015)
      ·
        refine ⟨18833054933983091994502523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12555369955988727996335015 18833054933983091994502523)
        ·
          refine ⟨28249582400974637991753785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18833054933983091994502523 28249582400974637991753785)
          ·
            refine ⟨21187186800730978493815339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28249582400974637991753785 21187186800730978493815339)
            ·
              refine ⟨31780780201096467740723009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21187186800730978493815339 31780780201096467740723009)
              ·
                refine ⟨23835585150822350805542257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31780780201096467740723009 23835585150822350805542257)
                ·
                  refine ⟨17876688863116763104156693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23835585150822350805542257 17876688863116763104156693)
                  ·
                    refine ⟨837969790458598270507345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17876688863116763104156693 837969790458598270507345)
                    ·
                      rfl

theorem cell23_4895821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 1, 2, 2, 6].length) (baseStart_4895821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4895821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4895821 prefixEnd_4895821 := by exact prefixLift 4895821
  have htrace : WordTrace (prefixWord ++ tailWord_4895821) baseStart_4895821 baseEnd_4895821 := by
    simpa [prefixWord, tailWord_4895821, baseEnd_4895821] using wordTrace_append hprefix tailTrace_4895821
  have hstable : (prefixWord ++ tailWord_4895821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4895821).length < 2 ^ (prefixWord ++ tailWord_4895821).sum := by decide
  have hdescent : baseEnd_4895821 < baseStart_4895821 := by decide
  rcases family_descends (prefixWord ++ tailWord_4895821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4895864 : List Nat := [2, 1, 2, 1, 1, 1, 6, 1, 1, 7]
def baseStart_4895864 : Nat := 118140960795 + 4895864 * 2 ^ 59
def prefixEnd_4895864 : Nat := 4983230072969 + 3 ^ 40 * 4895864 * 2
def baseEnd_4895864 : Nat := 837977150347979381094779

theorem tailTrace_4895864 : CollatzResearch.WordTrace tailWord_4895864 prefixEnd_4895864 837977150347979381094779 := by
  unfold tailWord_4895864
  simp only [CollatzResearch.WordTrace]
  refine ⟨89283414967564174923623323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119044553290085566564831097 89283414967564174923623323)
  ·
    refine ⟨133925122451346262385434985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89283414967564174923623323 133925122451346262385434985)
    ·
      refine ⟨100443841838509696789076239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 133925122451346262385434985 100443841838509696789076239)
      ·
        refine ⟨150665762757764545183614359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100443841838509696789076239 150665762757764545183614359)
        ·
          refine ⟨225998644136646817775421539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 150665762757764545183614359 225998644136646817775421539)
          ·
            refine ⟨338997966204970226663132309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 225998644136646817775421539 338997966204970226663132309)
            ·
              refine ⟨15890529665857979374834327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 338997966204970226663132309 15890529665857979374834327)
              ·
                refine ⟨23835794498786969062251491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15890529665857979374834327 23835794498786969062251491)
                ·
                  refine ⟨35753691748180453593377237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23835794498786969062251491 35753691748180453593377237)
                  ·
                    refine ⟨837977150347979381094779, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 35753691748180453593377237 837977150347979381094779)
                    ·
                      rfl

theorem cell23_4895864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 6, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 6, 1, 1, 7].length) (baseStart_4895864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4895864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4895864 prefixEnd_4895864 := by exact prefixLift 4895864
  have htrace : WordTrace (prefixWord ++ tailWord_4895864) baseStart_4895864 baseEnd_4895864 := by
    simpa [prefixWord, tailWord_4895864, baseEnd_4895864] using wordTrace_append hprefix tailTrace_4895864
  have hstable : (prefixWord ++ tailWord_4895864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4895864).length < 2 ^ (prefixWord ++ tailWord_4895864).sum := by decide
  have hdescent : baseEnd_4895864 < baseStart_4895864 := by decide
  rcases family_descends (prefixWord ++ tailWord_4895864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4895881 : List Nat := [1, 2, 1, 1, 4, 4, 1, 2, 2, 5]
def baseStart_4895881 : Nat := 118140960795 + 4895881 * 2 ^ 59
def prefixEnd_4895881 : Nat := 4983230072969 + 3 ^ 40 * 4895881 * 2
def baseEnd_4895881 : Nat := 837980060071688192257253

theorem tailTrace_4895881 : CollatzResearch.WordTrace tailWord_4895881 prefixEnd_4895881 837980060071688192257253 := by
  unfold tailWord_4895881
  simp only [CollatzResearch.WordTrace]
  refine ⟨178567449976066761750615497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119044966650711174500410331 178567449976066761750615497)
  ·
    refine ⟨133925587482050071312961623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 178567449976066761750615497 133925587482050071312961623)
    ·
      refine ⟨200888381223075106969442435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 133925587482050071312961623 200888381223075106969442435)
      ·
        refine ⟨301332571834612660454163653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 200888381223075106969442435 301332571834612660454163653)
        ·
          refine ⟨56499857218989873835155685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 301332571834612660454163653 56499857218989873835155685)
          ·
            refine ⟨10593723228560601344091691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 56499857218989873835155685 10593723228560601344091691)
            ·
              refine ⟨15890584842840902016137537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10593723228560601344091691 15890584842840902016137537)
              ·
                refine ⟨11917938632130676512103153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15890584842840902016137537 11917938632130676512103153)
                ·
                  refine ⟨8938453974098007384077365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11917938632130676512103153 8938453974098007384077365)
                  ·
                    refine ⟨837980060071688192257253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8938453974098007384077365 837980060071688192257253)
                    ·
                      rfl

theorem cell23_4895881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 4, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 4, 1, 2, 2, 5].length) (baseStart_4895881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4895881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4895881 prefixEnd_4895881 := by exact prefixLift 4895881
  have htrace : WordTrace (prefixWord ++ tailWord_4895881) baseStart_4895881 baseEnd_4895881 := by
    simpa [prefixWord, tailWord_4895881, baseEnd_4895881] using wordTrace_append hprefix tailTrace_4895881
  have hstable : (prefixWord ++ tailWord_4895881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4895881).length < 2 ^ (prefixWord ++ tailWord_4895881).sum := by decide
  have hdescent : baseEnd_4895881 < baseStart_4895881 := by decide
  rcases family_descends (prefixWord ++ tailWord_4895881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4895901 : List Nat := [1, 4, 2, 1, 1, 2, 1, 2, 4, 1, 4]
def baseStart_4895901 : Nat := 118140960795 + 4895901 * 2 ^ 59
def prefixEnd_4895901 : Nat := 4983230072969 + 3 ^ 40 * 4895901 * 2
def baseEnd_4895901 : Nat := 2513950449828154498521667

theorem tailTrace_4895901 : CollatzResearch.WordTrace tailWord_4895901 prefixEnd_4895901 2513950449828154498521667 := by
  unfold tailWord_4895901
  simp only [CollatzResearch.WordTrace]
  refine ⟨178568179435994305166343557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119045452957329536777562371 178568179435994305166343557)
  ·
    refine ⟨33481533644248932218689417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 178568179435994305166343557 33481533644248932218689417)
    ·
      refine ⟨25111150233186699164017063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33481533644248932218689417 25111150233186699164017063)
      ·
        refine ⟨37666725349780048746025595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25111150233186699164017063 37666725349780048746025595)
        ·
          refine ⟨56500088024670073119038393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37666725349780048746025595 56500088024670073119038393)
          ·
            refine ⟨42375066018502554839278795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56500088024670073119038393 42375066018502554839278795)
            ·
              refine ⟨63562599027753832258918193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42375066018502554839278795 63562599027753832258918193)
              ·
                refine ⟨47671949270815374194188645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 63562599027753832258918193 47671949270815374194188645)
                ·
                  refine ⟨8938490488277882661410371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 47671949270815374194188645 8938490488277882661410371)
                  ·
                    refine ⟨13407735732416823992115557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8938490488277882661410371 13407735732416823992115557)
                    ·
                      refine ⟨2513950449828154498521667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13407735732416823992115557 2513950449828154498521667)
                      ·
                        rfl

theorem cell23_4895901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 1, 2, 4, 1, 4].length) (baseStart_4895901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4895901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4895901 prefixEnd_4895901 := by exact prefixLift 4895901
  have htrace : WordTrace (prefixWord ++ tailWord_4895901) baseStart_4895901 baseEnd_4895901 := by
    simpa [prefixWord, tailWord_4895901, baseEnd_4895901] using wordTrace_append hprefix tailTrace_4895901
  have hstable : (prefixWord ++ tailWord_4895901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4895901).length < 2 ^ (prefixWord ++ tailWord_4895901).sum := by decide
  have hdescent : baseEnd_4895901 < baseStart_4895901 := by decide
  rcases family_descends (prefixWord ++ tailWord_4895901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4895968 : List Nat := [2, 1, 1, 3, 1, 4, 1, 1, 5, 1, 3]
def baseStart_4895968 : Nat := 118140960795 + 4895968 * 2 ^ 59
def prefixEnd_4895968 : Nat := 4983230072969 + 3 ^ 40 * 4895968 * 2
def baseEnd_4895968 : Nat := 2513984853032005736383859

theorem tailTrace_4895968 : CollatzResearch.WordTrace tailWord_4895968 prefixEnd_4895968 2513984853032005736383859 := by
  unfold tailWord_4895968
  simp only [CollatzResearch.WordTrace]
  refine ⟨89285311563375787804516279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119047082084501050406021705 89285311563375787804516279)
  ·
    refine ⟨133927967345063681706774419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89285311563375787804516279 133927967345063681706774419)
    ·
      refine ⟨200891951017595522560161629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 133927967345063681706774419 200891951017595522560161629)
      ·
        refine ⟨75334481631598320960060611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 200891951017595522560161629 75334481631598320960060611)
        ·
          refine ⟨113001722447397481440090917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75334481631598320960060611 113001722447397481440090917)
          ·
            refine ⟨21187822958887027770017047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 113001722447397481440090917 21187822958887027770017047)
            ·
              refine ⟨31781734438330541655025571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21187822958887027770017047 31781734438330541655025571)
              ·
                refine ⟨47672601657495812482538357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31781734438330541655025571 47672601657495812482538357)
                ·
                  refine ⟨4469306405390232420237971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 47672601657495812482538357 4469306405390232420237971)
                  ·
                    refine ⟨6703959608085348630356957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4469306405390232420237971 6703959608085348630356957)
                    ·
                      refine ⟨2513984853032005736383859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6703959608085348630356957 2513984853032005736383859)
                      ·
                        rfl

theorem cell23_4895968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 1, 1, 5, 1, 3].length) (baseStart_4895968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4895968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4895968 prefixEnd_4895968 := by exact prefixLift 4895968
  have htrace : WordTrace (prefixWord ++ tailWord_4895968) baseStart_4895968 baseEnd_4895968 := by
    simpa [prefixWord, tailWord_4895968, baseEnd_4895968] using wordTrace_append hprefix tailTrace_4895968
  have hstable : (prefixWord ++ tailWord_4895968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4895968).length < 2 ^ (prefixWord ++ tailWord_4895968).sum := by decide
  have hdescent : baseEnd_4895968 < baseStart_4895968 := by decide
  rcases family_descends (prefixWord ++ tailWord_4895968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4896011 : List Nat := [1, 1, 1, 1, 5, 3, 1, 1, 3, 1, 5]
def baseStart_4896011 : Nat := 118140960795 + 4896011 * 2 ^ 59
def prefixEnd_4896011 : Nat := 4983230072969 + 3 ^ 40 * 4896011 * 2
def baseEnd_4896011 : Nat := 2514006932700149068146161

theorem tailTrace_4896011 : CollatzResearch.WordTrace tailWord_4896011 prefixEnd_4896011 2514006932700149068146161 := by
  unfold tailWord_4896011
  simp only [CollatzResearch.WordTrace]
  refine ⟨178572191465595793952847887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119048127643730529301898591 178572191465595793952847887)
  ·
    refine ⟨267858287198393690929271831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 178572191465595793952847887 267858287198393690929271831)
    ·
      refine ⟨401787430797590536393907747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 267858287198393690929271831 401787430797590536393907747)
      ·
        refine ⟨602681146196385804590861621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 401787430797590536393907747 602681146196385804590861621)
        ·
          refine ⟨56501357455911169180393277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 602681146196385804590861621 56501357455911169180393277)
          ·
            refine ⟨21188009045966688442647479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 56501357455911169180393277 21188009045966688442647479)
            ·
              refine ⟨31782013568950032663971219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21188009045966688442647479 31782013568950032663971219)
              ·
                refine ⟨47673020353425048995956829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31782013568950032663971219 47673020353425048995956829)
                ·
                  refine ⟨17877382632534393373483811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 47673020353425048995956829 17877382632534393373483811)
                  ·
                    refine ⟨26816073948801590060225717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17877382632534393373483811 26816073948801590060225717)
                    ·
                      refine ⟨2514006932700149068146161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26816073948801590060225717 2514006932700149068146161)
                      ·
                        rfl

theorem cell23_4896011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 1, 1, 3, 1, 5].length) (baseStart_4896011 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4896011 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4896011 prefixEnd_4896011 := by exact prefixLift 4896011
  have htrace : WordTrace (prefixWord ++ tailWord_4896011) baseStart_4896011 baseEnd_4896011 := by
    simpa [prefixWord, tailWord_4896011, baseEnd_4896011] using wordTrace_append hprefix tailTrace_4896011
  have hstable : (prefixWord ++ tailWord_4896011).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4896011).length < 2 ^ (prefixWord ++ tailWord_4896011).sum := by decide
  have hdescent : baseEnd_4896011 < baseStart_4896011 := by decide
  rcases family_descends (prefixWord ++ tailWord_4896011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4896028 : List Nat := [2, 2, 3, 1, 1, 1, 2, 3, 3, 2, 3]
def baseStart_4896028 : Nat := 118140960795 + 4896028 * 2 ^ 59
def prefixEnd_4896028 : Nat := 4983230072969 + 3 ^ 40 * 4896028 * 2
def baseEnd_4896028 : Nat := 2514015661871275501633583

theorem tailTrace_4896028 : CollatzResearch.WordTrace tailWord_4896028 prefixEnd_4896028 2514015661871275501633583 := by
  unfold tailWord_4896028
  simp only [CollatzResearch.WordTrace]
  refine ⟨89286405753267102928108369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119048541004356137237477825 89286405753267102928108369)
  ·
    refine ⟨66964804314950327196081277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89286405753267102928108369 66964804314950327196081277)
    ·
      refine ⟨25111801618106372698530479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 66964804314950327196081277 25111801618106372698530479)
      ·
        refine ⟨37667702427159559047795719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25111801618106372698530479 37667702427159559047795719)
        ·
          refine ⟨56501553640739338571693579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37667702427159559047795719 56501553640739338571693579)
          ·
            refine ⟨84752330461109007857540369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56501553640739338571693579 84752330461109007857540369)
            ·
              refine ⟨63564247845831755893155277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 84752330461109007857540369 63564247845831755893155277)
              ·
                refine ⟨23836592942186908459933229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 63564247845831755893155277 23836592942186908459933229)
                ·
                  refine ⟨8938722353320090672474961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23836592942186908459933229 8938722353320090672474961)
                  ·
                    refine ⟨6704041764990068004356221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8938722353320090672474961 6704041764990068004356221)
                    ·
                      refine ⟨2514015661871275501633583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6704041764990068004356221 2514015661871275501633583)
                      ·
                        rfl

theorem cell23_4896028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 2, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 2, 3, 3, 2, 3].length) (baseStart_4896028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4896028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4896028 prefixEnd_4896028 := by exact prefixLift 4896028
  have htrace : WordTrace (prefixWord ++ tailWord_4896028) baseStart_4896028 baseEnd_4896028 := by
    simpa [prefixWord, tailWord_4896028, baseEnd_4896028] using wordTrace_append hprefix tailTrace_4896028
  have hstable : (prefixWord ++ tailWord_4896028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4896028).length < 2 ^ (prefixWord ++ tailWord_4896028).sum := by decide
  have hdescent : baseEnd_4896028 < baseStart_4896028 := by decide
  rcases family_descends (prefixWord ++ tailWord_4896028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4896045 : List Nat := [1, 5, 3, 1, 1, 1, 1, 3, 1, 1, 5]
def baseStart_4896045 : Nat := 118140960795 + 4896045 * 2 ^ 59
def prefixEnd_4896045 : Nat := 4983230072969 + 3 ^ 40 * 4896045 * 2
def baseEnd_4896045 : Nat := 2514024391042401935121005

theorem tailTrace_4896045 : CollatzResearch.WordTrace tailWord_4896045 prefixEnd_4896045 2514024391042401935121005 := by
  unfold tailWord_4896045
  simp only [CollatzResearch.WordTrace]
  refine ⟨178573431547472617759585589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119048954364981745173057059 178573431547472617759585589)
  ·
    refine ⟨16741259207575557914961149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 178573431547472617759585589 16741259207575557914961149)
    ·
      refine ⟨6277972202840834218110431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16741259207575557914961149 6277972202840834218110431)
      ·
        refine ⟨9416958304261251327165647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6277972202840834218110431 9416958304261251327165647)
        ·
          refine ⟨14125437456391876990748471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9416958304261251327165647 14125437456391876990748471)
          ·
            refine ⟨21188156184587815486122707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14125437456391876990748471 21188156184587815486122707)
            ·
              refine ⟨31782234276881723229184061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21188156184587815486122707 31782234276881723229184061)
              ·
                refine ⟨11918337853830646210944023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31782234276881723229184061 11918337853830646210944023)
                ·
                  refine ⟨17877506780745969316416035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11918337853830646210944023 17877506780745969316416035)
                  ·
                    refine ⟨26816260171118953974624053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17877506780745969316416035 26816260171118953974624053)
                    ·
                      refine ⟨2514024391042401935121005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26816260171118953974624053 2514024391042401935121005)
                      ·
                        rfl

theorem cell23_4896045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 1, 3, 1, 1, 5].length) (baseStart_4896045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4896045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4896045 prefixEnd_4896045 := by exact prefixLift 4896045
  have htrace : WordTrace (prefixWord ++ tailWord_4896045) baseStart_4896045 baseEnd_4896045 := by
    simpa [prefixWord, tailWord_4896045, baseEnd_4896045] using wordTrace_append hprefix tailTrace_4896045
  have hstable : (prefixWord ++ tailWord_4896045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4896045).length < 2 ^ (prefixWord ++ tailWord_4896045).sum := by decide
  have hdescent : baseEnd_4896045 < baseStart_4896045 := by decide
  rcases family_descends (prefixWord ++ tailWord_4896045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4896110 : List Nat := [4, 1, 2, 4, 1, 2, 2, 2, 1, 2, 2]
def baseStart_4896110 : Nat := 118140960795 + 4896110 * 2 ^ 59
def prefixEnd_4896110 : Nat := 4983230072969 + 3 ^ 40 * 4896110 * 2
def baseEnd_4896110 : Nat := 2514057767284944180808207

theorem tailTrace_4896110 : CollatzResearch.WordTrace tailWord_4896110 prefixEnd_4896110 2514057767284944180808207 := by
  unfold tailWord_4896110
  simp only [CollatzResearch.WordTrace]
  refine ⟨22321975286529641732587723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 119050534861491422573801189 22321975286529641732587723)
  ·
    refine ⟨33482962929794462598881585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22321975286529641732587723 33482962929794462598881585)
    ·
      refine ⟨25112222197345846949161189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33482962929794462598881585 25112222197345846949161189)
      ·
        refine ⟨4708541662002346302967723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 25112222197345846949161189 4708541662002346302967723)
        ·
          refine ⟨7062812493003519454451585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4708541662002346302967723 7062812493003519454451585)
          ·
            refine ⟨5297109369752639590838689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7062812493003519454451585 5297109369752639590838689)
            ·
              refine ⟨3972832027314479693129017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5297109369752639590838689 3972832027314479693129017)
              ·
                refine ⟨2979624020485859769846763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3972832027314479693129017 2979624020485859769846763)
                ·
                  refine ⟨4469436030728789654770145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2979624020485859769846763 4469436030728789654770145)
                  ·
                    refine ⟨3352077023046592241077609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4469436030728789654770145 3352077023046592241077609)
                    ·
                      refine ⟨2514057767284944180808207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3352077023046592241077609 2514057767284944180808207)
                      ·
                        rfl

theorem cell23_4896110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 2, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 2, 2, 2, 1, 2, 2].length) (baseStart_4896110 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4896110 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4896110 prefixEnd_4896110 := by exact prefixLift 4896110
  have htrace : WordTrace (prefixWord ++ tailWord_4896110) baseStart_4896110 baseEnd_4896110 := by
    simpa [prefixWord, tailWord_4896110, baseEnd_4896110] using wordTrace_append hprefix tailTrace_4896110
  have hstable : (prefixWord ++ tailWord_4896110).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4896110).length < 2 ^ (prefixWord ++ tailWord_4896110).sum := by decide
  have hdescent : baseEnd_4896110 < baseStart_4896110 := by decide
  rcases family_descends (prefixWord ++ tailWord_4896110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4896132 : List Nat := [2, 3, 2, 1, 1, 4, 2, 1, 1, 4, 2]
def baseStart_4896132 : Nat := 118140960795 + 4896132 * 2 ^ 59
def prefixEnd_4896132 : Nat := 4983230072969 + 3 ^ 40 * 4896132 * 2
def baseEnd_4896132 : Nat := 2514069063859343094733105

theorem tailTrace_4896132 : CollatzResearch.WordTrace tailWord_4896132 prefixEnd_4896132 2514069063859343094733105 := by
  unfold tailWord_4896132
  simp only [CollatzResearch.WordTrace]
  refine ⟨89288302349078715809001325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119051069798771621078668433 89288302349078715809001325)
  ·
    refine ⟨33483113380904518428375497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 89288302349078715809001325 33483113380904518428375497)
    ·
      refine ⟨25112335035678388821281623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33483113380904518428375497 25112335035678388821281623)
      ·
        refine ⟨37668502553517583231922435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25112335035678388821281623 37668502553517583231922435)
        ·
          refine ⟨56502753830276374847883653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37668502553517583231922435 56502753830276374847883653)
          ·
            refine ⟨10594266343176820283978185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 56502753830276374847883653 10594266343176820283978185)
            ·
              refine ⟨7945699757382615212983639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10594266343176820283978185 7945699757382615212983639)
              ·
                refine ⟨11918549636073922819475459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7945699757382615212983639 11918549636073922819475459)
                ·
                  refine ⟨17877824454110884229213189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11918549636073922819475459 17877824454110884229213189)
                  ·
                    refine ⟨3352092085145790792977473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17877824454110884229213189 3352092085145790792977473)
                    ·
                      refine ⟨2514069063859343094733105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3352092085145790792977473 2514069063859343094733105)
                      ·
                        rfl

theorem cell23_4896132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 4, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 4, 2, 1, 1, 4, 2].length) (baseStart_4896132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4896132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4896132 prefixEnd_4896132 := by exact prefixLift 4896132
  have htrace : WordTrace (prefixWord ++ tailWord_4896132) baseStart_4896132 baseEnd_4896132 := by
    simpa [prefixWord, tailWord_4896132, baseEnd_4896132] using wordTrace_append hprefix tailTrace_4896132
  have hstable : (prefixWord ++ tailWord_4896132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4896132).length < 2 ^ (prefixWord ++ tailWord_4896132).sum := by decide
  have hdescent : baseEnd_4896132 < baseStart_4896132 := by decide
  rcases family_descends (prefixWord ++ tailWord_4896132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4896225 : List Nat := [1, 2, 3, 1, 2, 3, 1, 1, 4, 2, 3]
def baseStart_4896225 : Nat := 118140960795 + 4896225 * 2 ^ 59
def prefixEnd_4896225 : Nat := 4983230072969 + 3 ^ 40 * 4896225 * 2
def baseEnd_4896225 : Nat := 2514116817560211230870177

theorem tailTrace_4896225 : CollatzResearch.WordTrace tailWord_4896225 prefixEnd_4896225 2514116817560211230870177 := by
  unfold tailWord_4896225
  simp only [CollatzResearch.WordTrace]
  refine ⟨178579996686820508501138129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119053331124547005667425419 178579996686820508501138129)
  ·
    refine ⟨133934997515115381375853597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 178579996686820508501138129 133934997515115381375853597)
    ·
      refine ⟨50225624068168268015945099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 133934997515115381375853597 50225624068168268015945099)
      ·
        refine ⟨75338436102252402023917649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50225624068168268015945099 75338436102252402023917649)
        ·
          refine ⟨56503827076689301517938237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 75338436102252402023917649 56503827076689301517938237)
          ·
            refine ⟨21188935153758488069226839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 56503827076689301517938237 21188935153758488069226839)
            ·
              refine ⟨31783402730637732103840259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21188935153758488069226839 31783402730637732103840259)
              ·
                refine ⟨47675104095956598155760389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31783402730637732103840259 47675104095956598155760389)
                ·
                  refine ⟨8939082017991862154205073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 47675104095956598155760389 8939082017991862154205073)
                  ·
                    refine ⟨6704311513493896615653805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8939082017991862154205073 6704311513493896615653805)
                    ·
                      refine ⟨2514116817560211230870177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6704311513493896615653805 2514116817560211230870177)
                      ·
                        rfl

theorem cell23_4896225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 1, 1, 4, 2, 3].length) (baseStart_4896225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4896225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4896225 prefixEnd_4896225 := by exact prefixLift 4896225
  have htrace : WordTrace (prefixWord ++ tailWord_4896225) baseStart_4896225 baseEnd_4896225 := by
    simpa [prefixWord, tailWord_4896225, baseEnd_4896225] using wordTrace_append hprefix tailTrace_4896225
  have hstable : (prefixWord ++ tailWord_4896225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4896225).length < 2 ^ (prefixWord ++ tailWord_4896225).sum := by decide
  have hdescent : baseEnd_4896225 < baseStart_4896225 := by decide
  rcases family_descends (prefixWord ++ tailWord_4896225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4896305 : List Nat := [1, 2, 2, 3, 1, 1, 1, 2, 6, 4]
def baseStart_4896305 : Nat := 118140960795 + 4896305 * 2 ^ 59
def prefixEnd_4896305 : Nat := 4983230072969 + 3 ^ 40 * 4896305 * 2
def baseEnd_4896305 : Nat := 838052632004190305956603

theorem tailTrace_4896305 : CollatzResearch.WordTrace tailWord_4896305 prefixEnd_4896305 838052632004190305956603 := by
  unfold tailWord_4896305
  simp only [CollatzResearch.WordTrace]
  refine ⟨178582914526530682164050369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119055276351020454776033579 178582914526530682164050369)
  ·
    refine ⟨133937185894898011623037777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 178582914526530682164050369 133937185894898011623037777)
    ·
      refine ⟨100452889421173508717278333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 133937185894898011623037777 100452889421173508717278333)
      ·
        refine ⟨37669833532940065768979375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 100452889421173508717278333 37669833532940065768979375)
        ·
          refine ⟨56504750299410098653469063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37669833532940065768979375 56504750299410098653469063)
          ·
            refine ⟨84757125449115147980203595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56504750299410098653469063 84757125449115147980203595)
            ·
              refine ⟨127135688173672721970305393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 84757125449115147980203595 127135688173672721970305393)
              ·
                refine ⟨95351766130254541477729045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 127135688173672721970305393 95351766130254541477729045)
                ·
                  refine ⟨4469614037355681631768549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 95351766130254541477729045 4469614037355681631768549)
                  ·
                    refine ⟨838052632004190305956603, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4469614037355681631768549 838052632004190305956603)
                    ·
                      rfl

theorem cell23_4896305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 2, 6, 4].length) (baseStart_4896305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4896305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4896305 prefixEnd_4896305 := by exact prefixLift 4896305
  have htrace : WordTrace (prefixWord ++ tailWord_4896305) baseStart_4896305 baseEnd_4896305 := by
    simpa [prefixWord, tailWord_4896305, baseEnd_4896305] using wordTrace_append hprefix tailTrace_4896305
  have hstable : (prefixWord ++ tailWord_4896305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4896305).length < 2 ^ (prefixWord ++ tailWord_4896305).sum := by decide
  have hdescent : baseEnd_4896305 < baseStart_4896305 := by decide
  rcases family_descends (prefixWord ++ tailWord_4896305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4896316 : List Nat := [2, 2, 2, 2, 4, 2, 1, 1, 2, 3, 2]
def baseStart_4896316 : Nat := 118140960795 + 4896316 * 2 ^ 59
def prefixEnd_4896316 : Nat := 4983230072969 + 3 ^ 40 * 4896316 * 2
def baseEnd_4896316 : Nat := 2514163544299770374832259

theorem tailTrace_4896316 : CollatzResearch.WordTrace tailWord_4896316 prefixEnd_4896316 2514163544299770374832259 := by
  unfold tailWord_4896316
  simp only [CollatzResearch.WordTrace]
  refine ⟨89291657864745415521350401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119055543819660554028467201 89291657864745415521350401)
  ·
    refine ⟨66968743398559061641012801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89291657864745415521350401 66968743398559061641012801)
    ·
      refine ⟨50226557548919296230759601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66968743398559061641012801 50226557548919296230759601)
      ·
        refine ⟨37669918161689472173069701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50226557548919296230759601 37669918161689472173069701)
        ·
          refine ⟨7063109655316776032450569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 37669918161689472173069701 7063109655316776032450569)
          ·
            refine ⟨5297332241487582024337927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7063109655316776032450569 5297332241487582024337927)
            ·
              refine ⟨7945998362231373036506891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5297332241487582024337927 7945998362231373036506891)
              ·
                refine ⟨11918997543347059554760337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7945998362231373036506891 11918997543347059554760337)
                ·
                  refine ⟨8939248157510294666070253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11918997543347059554760337 8939248157510294666070253)
                  ·
                    refine ⟨3352218059066360499776345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8939248157510294666070253 3352218059066360499776345)
                    ·
                      refine ⟨2514163544299770374832259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3352218059066360499776345 2514163544299770374832259)
                      ·
                        rfl

theorem cell23_4896316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 2, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 2, 1, 1, 2, 3, 2].length) (baseStart_4896316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4896316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4896316 prefixEnd_4896316 := by exact prefixLift 4896316
  have htrace : WordTrace (prefixWord ++ tailWord_4896316) baseStart_4896316 baseEnd_4896316 := by
    simpa [prefixWord, tailWord_4896316, baseEnd_4896316] using wordTrace_append hprefix tailTrace_4896316
  have hstable : (prefixWord ++ tailWord_4896316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4896316).length < 2 ^ (prefixWord ++ tailWord_4896316).sum := by decide
  have hdescent : baseEnd_4896316 < baseStart_4896316 := by decide
  rcases family_descends (prefixWord ++ tailWord_4896316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4896325 : List Nat := [1, 3, 1, 1, 1, 4, 1, 4, 1, 2, 4]
def baseStart_4896325 : Nat := 118140960795 + 4896325 * 2 ^ 59
def prefixEnd_4896325 : Nat := 4983230072969 + 3 ^ 40 * 4896325 * 2
def baseEnd_4896325 : Nat := 2514168165625660839619717

theorem tailTrace_4896325 : CollatzResearch.WordTrace tailWord_4896325 prefixEnd_4896325 2514168165625660839619717 := by
  unfold tailWord_4896325
  simp only [CollatzResearch.WordTrace]
  refine ⟨178583643986458225579778429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119055762657638817053185619 178583643986458225579778429)
  ·
    refine ⟨66968866494921834592416911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 178583643986458225579778429 66968866494921834592416911)
    ·
      refine ⟨100453299742382751888625367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66968866494921834592416911 100453299742382751888625367)
      ·
        refine ⟨150679949613574127832938051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100453299742382751888625367 150679949613574127832938051)
        ·
          refine ⟨226019924420361191749407077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 150679949613574127832938051 226019924420361191749407077)
          ·
            refine ⟨42378735828817723453013827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 226019924420361191749407077 42378735828817723453013827)
            ·
              refine ⟨63568103743226585179520741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42378735828817723453013827 63568103743226585179520741)
              ·
                refine ⟨11919019451854984721160139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 63568103743226585179520741 11919019451854984721160139)
                ·
                  refine ⟨17878529177782477081740209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11919019451854984721160139 17878529177782477081740209)
                  ·
                    refine ⟨13408896883336857811305157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17878529177782477081740209 13408896883336857811305157)
                    ·
                      refine ⟨2514168165625660839619717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13408896883336857811305157 2514168165625660839619717)
                      ·
                        rfl

theorem cell23_4896325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 1, 4, 1, 2, 4].length) (baseStart_4896325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4896325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4896325 prefixEnd_4896325 := by exact prefixLift 4896325
  have htrace : WordTrace (prefixWord ++ tailWord_4896325) baseStart_4896325 baseEnd_4896325 := by
    simpa [prefixWord, tailWord_4896325, baseEnd_4896325] using wordTrace_append hprefix tailTrace_4896325
  have hstable : (prefixWord ++ tailWord_4896325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4896325).length < 2 ^ (prefixWord ++ tailWord_4896325).sum := by decide
  have hdescent : baseEnd_4896325 < baseStart_4896325 := by decide
  rcases family_descends (prefixWord ++ tailWord_4896325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4896326 : List Nat := [6, 1, 1, 1, 3, 1, 1, 3, 1, 5]
def baseStart_4896326 : Nat := 118140960795 + 4896326 * 2 ^ 59
def prefixEnd_4896326 : Nat := 4983230072969 + 3 ^ 40 * 4896326 * 2
def baseEnd_4896326 : Nat := 838056226368771778569071

theorem tailTrace_4896326 : CollatzResearch.WordTrace tailWord_4896326 prefixEnd_4896326 838056226368771778569071 := by
  unfold tailWord_4896326
  simp only [CollatzResearch.WordTrace]
  refine ⟨5580740014357956335955151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 119055786972969735167043221 5580740014357956335955151)
  ·
    refine ⟨8371110021536934503932727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5580740014357956335955151 8371110021536934503932727)
    ·
      refine ⟨12556665032305401755899091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8371110021536934503932727 12556665032305401755899091)
      ·
        refine ⟨18834997548458102633848637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12556665032305401755899091 18834997548458102633848637)
        ·
          refine ⟨7063124080671788487693239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18834997548458102633848637 7063124080671788487693239)
          ·
            refine ⟨10594686121007682731539859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7063124080671788487693239 10594686121007682731539859)
            ·
              refine ⟨15892029181511524097309789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10594686121007682731539859 15892029181511524097309789)
              ·
                refine ⟨5959510943066821536491171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15892029181511524097309789 5959510943066821536491171)
                ·
                  refine ⟨8939266414600232304736757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5959510943066821536491171 8939266414600232304736757)
                  ·
                    refine ⟨838056226368771778569071, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8939266414600232304736757 838056226368771778569071)
                    ·
                      rfl

theorem cell23_4896326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 1, 1, 3, 1, 5].length) (baseStart_4896326 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4896326 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4896326 prefixEnd_4896326 := by exact prefixLift 4896326
  have htrace : WordTrace (prefixWord ++ tailWord_4896326) baseStart_4896326 baseEnd_4896326 := by
    simpa [prefixWord, tailWord_4896326, baseEnd_4896326] using wordTrace_append hprefix tailTrace_4896326
  have hstable : (prefixWord ++ tailWord_4896326).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4896326).length < 2 ^ (prefixWord ++ tailWord_4896326).sum := by decide
  have hdescent : baseEnd_4896326 < baseStart_4896326 := by decide
  rcases family_descends (prefixWord ++ tailWord_4896326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4896345 : List Nat := [1, 2, 1, 2, 2, 1, 1, 4, 3, 3, 3]
def baseStart_4896345 : Nat := 118140960795 + 4896345 * 2 ^ 59
def prefixEnd_4896345 : Nat := 4983230072969 + 3 ^ 40 * 4896345 * 2
def baseEnd_4896345 : Nat := 2514178435238750761369625

theorem tailTrace_4896345 : CollatzResearch.WordTrace tailWord_4896345 prefixEnd_4896345 2514178435238750761369625 := by
  unfold tailWord_4896345
  simp only [CollatzResearch.WordTrace]
  refine ⟨178584373446385768995506489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119056248964257179330337659 178584373446385768995506489)
  ·
    refine ⟨133938280084789326746629867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 178584373446385768995506489 133938280084789326746629867)
    ·
      refine ⟨200907420127183990119944801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 133938280084789326746629867 200907420127183990119944801)
      ·
        refine ⟨150680565095387992589958601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 200907420127183990119944801 150680565095387992589958601)
        ·
          refine ⟨113010423821540994442468951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 150680565095387992589958601 113010423821540994442468951)
          ·
            refine ⟨169515635732311491663703427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 113010423821540994442468951 169515635732311491663703427)
            ·
              refine ⟨254273453598467237495555141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 169515635732311491663703427 254273453598467237495555141)
              ·
                refine ⟨47676272549712607030416589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 254273453598467237495555141 47676272549712607030416589)
                ·
                  refine ⟨17878602206142227636406221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 47676272549712607030416589 17878602206142227636406221)
                  ·
                    refine ⟨6704475827303335363652333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17878602206142227636406221 6704475827303335363652333)
                    ·
                      refine ⟨2514178435238750761369625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6704475827303335363652333 2514178435238750761369625)
                      ·
                        rfl

theorem cell23_4896345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 4, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 4, 3, 3, 3].length) (baseStart_4896345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4896345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4896345 prefixEnd_4896345 := by exact prefixLift 4896345
  have htrace : WordTrace (prefixWord ++ tailWord_4896345) baseStart_4896345 baseEnd_4896345 := by
    simpa [prefixWord, tailWord_4896345, baseEnd_4896345] using wordTrace_append hprefix tailTrace_4896345
  have hstable : (prefixWord ++ tailWord_4896345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4896345).length < 2 ^ (prefixWord ++ tailWord_4896345).sum := by decide
  have hdescent : baseEnd_4896345 < baseStart_4896345 := by decide
  rcases family_descends (prefixWord ++ tailWord_4896345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4896366 : List Nat := [4, 1, 2, 2, 3, 1, 2, 2, 1, 2, 3]
def baseStart_4896366 : Nat := 118140960795 + 4896366 * 2 ^ 59
def prefixEnd_4896366 : Nat := 4983230072969 + 3 ^ 40 * 4896366 * 2
def baseEnd_4896366 : Nat := 2514189218332495179207029

theorem tailTrace_4896366 : CollatzResearch.WordTrace tailWord_4896366 prefixEnd_4896366 2514189218332495179207029 := by
  unfold tailWord_4896366
  simp only [CollatzResearch.WordTrace]
  refine ⟨22323142422413711197752619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 119056759586206459721347301 22323142422413711197752619)
  ·
    refine ⟨33484713633620566796628929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22323142422413711197752619 33484713633620566796628929)
    ·
      refine ⟨25113535225215425097471697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33484713633620566796628929 25113535225215425097471697)
      ·
        refine ⟨18835151418911568823103773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25113535225215425097471697 18835151418911568823103773)
        ·
          refine ⟨7063181782091838308663915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18835151418911568823103773 7063181782091838308663915)
          ·
            refine ⟨10594772673137757462995873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7063181782091838308663915 10594772673137757462995873)
            ·
              refine ⟨7946079504853318097246905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10594772673137757462995873 7946079504853318097246905)
              ·
                refine ⟨5959559628639988572935179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7946079504853318097246905 5959559628639988572935179)
                ·
                  refine ⟨8939339442959982859402769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5959559628639988572935179 8939339442959982859402769)
                  ·
                    refine ⟨6704504582219987144552077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8939339442959982859402769 6704504582219987144552077)
                    ·
                      refine ⟨2514189218332495179207029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6704504582219987144552077 2514189218332495179207029)
                      ·
                        rfl

theorem cell23_4896366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 1, 2, 2, 1, 2, 3].length) (baseStart_4896366 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4896366 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4896366 prefixEnd_4896366 := by exact prefixLift 4896366
  have htrace : WordTrace (prefixWord ++ tailWord_4896366) baseStart_4896366 baseEnd_4896366 := by
    simpa [prefixWord, tailWord_4896366, baseEnd_4896366] using wordTrace_append hprefix tailTrace_4896366
  have hstable : (prefixWord ++ tailWord_4896366).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4896366).length < 2 ^ (prefixWord ++ tailWord_4896366).sum := by decide
  have hdescent : baseEnd_4896366 < baseStart_4896366 := by decide
  rcases family_descends (prefixWord ++ tailWord_4896366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4896389 : List Nat := [1, 3, 1, 1, 4, 1, 1, 5, 1, 3, 2]
def baseStart_4896389 : Nat := 118140960795 + 4896389 * 2 ^ 59
def prefixEnd_4896389 : Nat := 4983230072969 + 3 ^ 40 * 4896389 * 2
def baseEnd_4896389 : Nat := 2514201028387548589219423

theorem tailTrace_4896389 : CollatzResearch.WordTrace tailWord_4896389 prefixEnd_4896389 2514201028387548589219423 := by
  unfold tailWord_4896389
  simp only [CollatzResearch.WordTrace]
  refine ⟨178585978258226364510108221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119057318838817576340072147 178585978258226364510108221)
  ·
    refine ⟨66969741846834886691290583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 178585978258226364510108221 66969741846834886691290583)
    ·
      refine ⟨100454612770252330036935875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66969741846834886691290583 100454612770252330036935875)
      ·
        refine ⟨150681919155378495055403813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100454612770252330036935875 150681919155378495055403813)
        ·
          refine ⟨28252859841633467822888215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 150681919155378495055403813 28252859841633467822888215)
          ·
            refine ⟨42379289762450201734332323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28252859841633467822888215 42379289762450201734332323)
            ·
              refine ⟨63568934643675302601498485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42379289762450201734332323 63568934643675302601498485)
              ·
                refine ⟨5959587622844559618890483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 63568934643675302601498485 5959587622844559618890483)
                ·
                  refine ⟨8939381434266839428335725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5959587622844559618890483 8939381434266839428335725)
                  ·
                    refine ⟨3352268037850064785625897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8939381434266839428335725 3352268037850064785625897)
                    ·
                      refine ⟨2514201028387548589219423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3352268037850064785625897 2514201028387548589219423)
                      ·
                        rfl

theorem cell23_4896389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 1, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 1, 5, 1, 3, 2].length) (baseStart_4896389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4896389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4896389 prefixEnd_4896389 := by exact prefixLift 4896389
  have htrace : WordTrace (prefixWord ++ tailWord_4896389) baseStart_4896389 baseEnd_4896389 := by
    simpa [prefixWord, tailWord_4896389, baseEnd_4896389] using wordTrace_append hprefix tailTrace_4896389
  have hstable : (prefixWord ++ tailWord_4896389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4896389).length < 2 ^ (prefixWord ++ tailWord_4896389).sum := by decide
  have hdescent : baseEnd_4896389 < baseStart_4896389 := by decide
  rcases family_descends (prefixWord ++ tailWord_4896389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4896470 : List Nat := [5, 2, 1, 3, 1, 1, 2, 1, 1, 4, 2]
def baseStart_4896470 : Nat := 118140960795 + 4896470 * 2 ^ 59
def prefixEnd_4896470 : Nat := 4983230072969 + 3 ^ 40 * 4896470 * 2
def baseEnd_4896470 : Nat := 2514242620320562772306551

theorem tailTrace_4896470 : CollatzResearch.WordTrace tailWord_4896470 prefixEnd_4896470 2514242620320562772306551 := by
  unfold tailWord_4896470
  simp only [CollatzResearch.WordTrace]
  refine ⟨11161808285683307208987929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 119059288380621943562537909 11161808285683307208987929)
  ·
    refine ⟨8371356214262480406740947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11161808285683307208987929 8371356214262480406740947)
    ·
      refine ⟨12557034321393720610111421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8371356214262480406740947 12557034321393720610111421)
      ·
        refine ⟨4708887870522645228791783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12557034321393720610111421 4708887870522645228791783)
        ·
          refine ⟨7063331805783967843187675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4708887870522645228791783 7063331805783967843187675)
          ·
            refine ⟨10594997708675951764781513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7063331805783967843187675 10594997708675951764781513)
            ·
              refine ⟨7946248281506963823586135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10594997708675951764781513 7946248281506963823586135)
              ·
                refine ⟨11919372422260445735379203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7946248281506963823586135 11919372422260445735379203)
                ·
                  refine ⟨17879058633390668603068805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11919372422260445735379203 17879058633390668603068805)
                  ·
                    refine ⟨3352323493760750363075401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17879058633390668603068805 3352323493760750363075401)
                    ·
                      refine ⟨2514242620320562772306551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3352323493760750363075401 2514242620320562772306551)
                      ·
                        rfl

theorem cell23_4896470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 1, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 1, 2, 1, 1, 4, 2].length) (baseStart_4896470 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4896470 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4896470 prefixEnd_4896470 := by exact prefixLift 4896470
  have htrace : WordTrace (prefixWord ++ tailWord_4896470) baseStart_4896470 baseEnd_4896470 := by
    simpa [prefixWord, tailWord_4896470, baseEnd_4896470] using wordTrace_append hprefix tailTrace_4896470
  have hstable : (prefixWord ++ tailWord_4896470).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4896470).length < 2 ^ (prefixWord ++ tailWord_4896470).sum := by decide
  have hdescent : baseEnd_4896470 < baseStart_4896470 := by decide
  rcases family_descends (prefixWord ++ tailWord_4896470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4896592 : List Nat := [2, 1, 1, 1, 1, 4, 1, 5, 1, 6]
def baseStart_4896592 : Nat := 118140960795 + 4896592 * 2 ^ 59
def prefixEnd_4896592 : Nat := 4983230072969 + 3 ^ 40 * 4896592 * 2
def baseEnd_4896592 : Nat := 838101754986803764993663

theorem tailTrace_4896592 : CollatzResearch.WordTrace tailWord_4896592 prefixEnd_4896592 838101754986803764993663 := by
  unfold tailWord_4896592
  simp only [CollatzResearch.WordTrace]
  refine ⟨89296691138245465089874015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119062254850993953453165353 89296691138245465089874015)
  ·
    refine ⟨133945036707368197634811023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89296691138245465089874015 133945036707368197634811023)
    ·
      refine ⟨200917555061052296452216535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 133945036707368197634811023 200917555061052296452216535)
      ·
        refine ⟨301376332591578444678324803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 200917555061052296452216535 301376332591578444678324803)
        ·
          refine ⟨452064498887367667017487205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 301376332591578444678324803 452064498887367667017487205)
          ·
            refine ⟨84762093541381437565778851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 452064498887367667017487205 84762093541381437565778851)
            ·
              refine ⟨127143140312072156348668277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 84762093541381437565778851 127143140312072156348668277)
              ·
                refine ⟨11919669404256764657687651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 127143140312072156348668277 11919669404256764657687651)
                ·
                  refine ⟨17879504106385146986531477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11919669404256764657687651 17879504106385146986531477)
                  ·
                    refine ⟨838101754986803764993663, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17879504106385146986531477 838101754986803764993663)
                    ·
                      rfl

theorem cell23_4896592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 5, 1, 6].length) (baseStart_4896592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4896592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4896592 prefixEnd_4896592 := by exact prefixLift 4896592
  have htrace : WordTrace (prefixWord ++ tailWord_4896592) baseStart_4896592 baseEnd_4896592 := by
    simpa [prefixWord, tailWord_4896592, baseEnd_4896592] using wordTrace_append hprefix tailTrace_4896592
  have hstable : (prefixWord ++ tailWord_4896592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4896592).length < 2 ^ (prefixWord ++ tailWord_4896592).sum := by decide
  have hdescent : baseEnd_4896592 < baseStart_4896592 := by decide
  rcases family_descends (prefixWord ++ tailWord_4896592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4896596 : List Nat := [2, 4, 1, 1, 3, 1, 3, 2, 1, 5]
def baseStart_4896596 : Nat := 118140960795 + 4896596 * 2 ^ 59
def prefixEnd_4896596 : Nat := 4983230072969 + 3 ^ 40 * 4896596 * 2
def baseEnd_4896596 : Nat := 838102439627676426443657

theorem tailTrace_4896596 : CollatzResearch.WordTrace tailWord_4896596 prefixEnd_4896596 838102439627676426443657 := by
  unfold tailWord_4896596
  simp only [CollatzResearch.WordTrace]
  refine ⟨89296764084238219431446821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119062352112317625908595761 89296764084238219431446821)
  ·
    refine ⟨16743143265794666143396279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 89296764084238219431446821 16743143265794666143396279)
    ·
      refine ⟨25114714898691999215094419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16743143265794666143396279 25114714898691999215094419)
      ·
        refine ⟨37672072348037998822641629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25114714898691999215094419 37672072348037998822641629)
        ·
          refine ⟨14127027130514249558490611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37672072348037998822641629 14127027130514249558490611)
          ·
            refine ⟨21190540695771374337735917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14127027130514249558490611 21190540695771374337735917)
            ·
              refine ⟨7946452760914265376650969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21190540695771374337735917 7946452760914265376650969)
              ·
                refine ⟨5959839570685699032488227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7946452760914265376650969 5959839570685699032488227)
                ·
                  refine ⟨8939759356028548548732341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5959839570685699032488227 8939759356028548548732341)
                  ·
                    refine ⟨838102439627676426443657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8939759356028548548732341 838102439627676426443657)
                    ·
                      rfl

theorem cell23_4896596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 3, 2, 1, 5].length) (baseStart_4896596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4896596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4896596 prefixEnd_4896596 := by exact prefixLift 4896596
  have htrace : WordTrace (prefixWord ++ tailWord_4896596) baseStart_4896596 baseEnd_4896596 := by
    simpa [prefixWord, tailWord_4896596, baseEnd_4896596] using wordTrace_append hprefix tailTrace_4896596
  have hstable : (prefixWord ++ tailWord_4896596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4896596).length < 2 ^ (prefixWord ++ tailWord_4896596).sum := by decide
  have hdescent : baseEnd_4896596 < baseStart_4896596 := by decide
  rcases family_descends (prefixWord ++ tailWord_4896596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4896629 : List Nat := [1, 3, 4, 1, 1, 1, 1, 2, 3, 2, 4]
def baseStart_4896629 : Nat := 118140960795 + 4896629 * 2 ^ 59
def prefixEnd_4896629 : Nat := 4983230072969 + 3 ^ 40 * 4896629 * 2
def baseEnd_4896629 : Nat := 2514324263744627650218319

theorem tailTrace_4896629 : CollatzResearch.WordTrace tailWord_4896629 prefixEnd_4896629 2514324263744627650218319 := by
  unfold tailWord_4896629
  simp only [CollatzResearch.WordTrace]
  refine ⟨178594731777356885498844941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119063154518237923665896627 178594731777356885498844941)
  ·
    refine ⟨66973024416508832062066853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 178594731777356885498844941 66973024416508832062066853)
    ·
      refine ⟨12557442078095406011637535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 66973024416508832062066853 12557442078095406011637535)
      ·
        refine ⟨18836163117143109017456303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12557442078095406011637535 18836163117143109017456303)
        ·
          refine ⟨28254244675714663526184455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18836163117143109017456303 28254244675714663526184455)
          ·
            refine ⟨42381367013571995289276683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28254244675714663526184455 42381367013571995289276683)
            ·
              refine ⟨63572050520357992933915025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42381367013571995289276683 63572050520357992933915025)
              ·
                refine ⟨47679037890268494700436269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 63572050520357992933915025 47679037890268494700436269)
                ·
                  refine ⟨17879639208850685512663601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 47679037890268494700436269 17879639208850685512663601)
                  ·
                    refine ⟨13409729406638014134497701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17879639208850685512663601 13409729406638014134497701)
                    ·
                      refine ⟨2514324263744627650218319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13409729406638014134497701 2514324263744627650218319)
                      ·
                        rfl

theorem cell23_4896629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 1, 2, 3, 2, 4].length) (baseStart_4896629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4896629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4896629 prefixEnd_4896629 := by exact prefixLift 4896629
  have htrace : WordTrace (prefixWord ++ tailWord_4896629) baseStart_4896629 baseEnd_4896629 := by
    simpa [prefixWord, tailWord_4896629, baseEnd_4896629] using wordTrace_append hprefix tailTrace_4896629
  have hstable : (prefixWord ++ tailWord_4896629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4896629).length < 2 ^ (prefixWord ++ tailWord_4896629).sum := by decide
  have hdescent : baseEnd_4896629 < baseStart_4896629 := by decide
  rcases family_descends (prefixWord ++ tailWord_4896629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4896650 : List Nat := [3, 1, 2, 4, 2, 1, 1, 2, 3, 2, 2]
def baseStart_4896650 : Nat := 118140960795 + 4896650 * 2 ^ 59
def prefixEnd_4896650 : Nat := 4983230072969 + 3 ^ 40 * 4896650 * 2
def baseEnd_4896650 : Nat := 2514335046838372068055723

theorem tailTrace_4896650 : CollatzResearch.WordTrace tailWord_4896650 prefixEnd_4896650 2514335046838372068055723 := by
  unfold tailWord_4896650
  simp only [CollatzResearch.WordTrace]
  refine ⟨44648874427570201521339851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 119063665140187204056906269 44648874427570201521339851)
  ·
    refine ⟨66973311641355302282009777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44648874427570201521339851 66973311641355302282009777)
    ·
      refine ⟨50229983731016476711507333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66973311641355302282009777 50229983731016476711507333)
      ·
        refine ⟨9418121949565589383407625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 50229983731016476711507333 9418121949565589383407625)
        ·
          refine ⟨7063591462174192037555719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9418121949565589383407625 7063591462174192037555719)
          ·
            refine ⟨10595387193261288056333579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7063591462174192037555719 10595387193261288056333579)
            ·
              refine ⟨15893080789891932084500369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10595387193261288056333579 15893080789891932084500369)
              ·
                refine ⟨11919810592418949063375277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15893080789891932084500369 11919810592418949063375277)
                ·
                  refine ⟨4469928972157105898765729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11919810592418949063375277 4469928972157105898765729)
                  ·
                    refine ⟨3352446729117829424074297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4469928972157105898765729 3352446729117829424074297)
                    ·
                      refine ⟨2514335046838372068055723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3352446729117829424074297 2514335046838372068055723)
                      ·
                        rfl

theorem cell23_4896650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 1, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 1, 1, 2, 3, 2, 2].length) (baseStart_4896650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4896650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4896650 prefixEnd_4896650 := by exact prefixLift 4896650
  have htrace : WordTrace (prefixWord ++ tailWord_4896650) baseStart_4896650 baseEnd_4896650 := by
    simpa [prefixWord, tailWord_4896650, baseEnd_4896650] using wordTrace_append hprefix tailTrace_4896650
  have hstable : (prefixWord ++ tailWord_4896650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4896650).length < 2 ^ (prefixWord ++ tailWord_4896650).sum := by decide
  have hdescent : baseEnd_4896650 < baseStart_4896650 := by decide
  rcases family_descends (prefixWord ++ tailWord_4896650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4896652 : List Nat := [2, 2, 1, 2, 1, 2, 1, 1, 4, 7]
def baseStart_4896652 : Nat := 118140960795 + 4896652 * 2 ^ 59
def prefixEnd_4896652 : Nat := 4983230072969 + 3 ^ 40 * 4896652 * 2
def baseEnd_4896652 : Nat := 838112024599893686743571

theorem tailTrace_4896652 : CollatzResearch.WordTrace tailWord_4896652 prefixEnd_4896652 838112024599893686743571 := by
  unfold tailWord_4896652
  simp only [CollatzResearch.WordTrace]
  refine ⟨89297785328136780213466105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119063713770849040284621473 89297785328136780213466105)
  ·
    refine ⟨66973338996102585160099579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89297785328136780213466105 66973338996102585160099579)
    ·
      refine ⟨100460008494153877740149369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66973338996102585160099579 100460008494153877740149369)
      ·
        refine ⟨75345006370615408305112027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 100460008494153877740149369 75345006370615408305112027)
        ·
          refine ⟨113017509555923112457668041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75345006370615408305112027 113017509555923112457668041)
          ·
            refine ⟨84763132166942334343251031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 113017509555923112457668041 84763132166942334343251031)
            ·
              refine ⟨127144698250413501514876547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 84763132166942334343251031 127144698250413501514876547)
              ·
                refine ⟨190717047375620252272314821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 127144698250413501514876547 190717047375620252272314821)
                ·
                  refine ⟨35759446382928797301059029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 190717047375620252272314821 35759446382928797301059029)
                  ·
                    refine ⟨838112024599893686743571, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 35759446382928797301059029 838112024599893686743571)
                    ·
                      rfl

theorem cell23_4896652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 1, 4, 7].length) (baseStart_4896652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4896652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4896652 prefixEnd_4896652 := by exact prefixLift 4896652
  have htrace : WordTrace (prefixWord ++ tailWord_4896652) baseStart_4896652 baseEnd_4896652 := by
    simpa [prefixWord, tailWord_4896652, baseEnd_4896652] using wordTrace_append hprefix tailTrace_4896652
  have hstable : (prefixWord ++ tailWord_4896652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4896652).length < 2 ^ (prefixWord ++ tailWord_4896652).sum := by decide
  have hdescent : baseEnd_4896652 < baseStart_4896652 := by decide
  rcases family_descends (prefixWord ++ tailWord_4896652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4896666 : List Nat := [3, 1, 1, 4, 2, 1, 2, 2, 1, 3, 3]
def baseStart_4896666 : Nat := 118140960795 + 4896666 * 2 ^ 59
def prefixEnd_4896666 : Nat := 4983230072969 + 3 ^ 40 * 4896666 * 2
def baseEnd_4896666 : Nat := 2514343262528844005455649

theorem tailTrace_4896666 : CollatzResearch.WordTrace tailWord_4896666 prefixEnd_4896666 2514343262528844005455649 := by
  unfold tailWord_4896666
  simp only [CollatzResearch.WordTrace]
  refine ⟨44649020319555710204485463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 119064054185481893878627901 44649020319555710204485463)
  ·
    refine ⟨66973530479333565306728195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44649020319555710204485463 66973530479333565306728195)
    ·
      refine ⟨100460295719000347960092293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66973530479333565306728195 100460295719000347960092293)
      ·
        refine ⟨18836305447312565242517305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 100460295719000347960092293 18836305447312565242517305)
        ·
          refine ⟨14127229085484423931887979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18836305447312565242517305 14127229085484423931887979)
          ·
            refine ⟨21190843628226635897831969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14127229085484423931887979 21190843628226635897831969)
            ·
              refine ⟨15893132721169976923373977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21190843628226635897831969 15893132721169976923373977)
              ·
                refine ⟨11919849540877482692530483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15893132721169976923373977 11919849540877482692530483)
                ·
                  refine ⟨17879774311316224038795725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11919849540877482692530483 17879774311316224038795725)
                  ·
                    refine ⟨6704915366743584014548397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17879774311316224038795725 6704915366743584014548397)
                    ·
                      refine ⟨2514343262528844005455649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6704915366743584014548397 2514343262528844005455649)
                      ·
                        rfl

theorem cell23_4896666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 2, 2, 1, 3, 3].length) (baseStart_4896666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4896666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4896666 prefixEnd_4896666 := by exact prefixLift 4896666
  have htrace : WordTrace (prefixWord ++ tailWord_4896666) baseStart_4896666 baseEnd_4896666 := by
    simpa [prefixWord, tailWord_4896666, baseEnd_4896666] using wordTrace_append hprefix tailTrace_4896666
  have hstable : (prefixWord ++ tailWord_4896666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4896666).length < 2 ^ (prefixWord ++ tailWord_4896666).sum := by decide
  have hdescent : baseEnd_4896666 < baseStart_4896666 := by decide
  rcases family_descends (prefixWord ++ tailWord_4896666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4896700 : List Nat := [2, 2, 2, 5, 1, 2, 1, 1, 1, 3, 3]
def baseStart_4896700 : Nat := 118140960795 + 4896700 * 2 ^ 59
def prefixEnd_4896700 : Nat := 4983230072969 + 3 ^ 40 * 4896700 * 2
def baseEnd_4896700 : Nat := 2514360720871096872430493

theorem tailTrace_4896700 : CollatzResearch.WordTrace tailWord_4896700 prefixEnd_4896700 2514360720871096872430493 := by
  unfold tailWord_4896700
  simp only [CollatzResearch.WordTrace]
  refine ⟨89298660680049832312339777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119064880906733109749786369 89298660680049832312339777)
  ·
    refine ⟨66973995510037374234254833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89298660680049832312339777 66973995510037374234254833)
    ·
      refine ⟨50230496632528030675691125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66973995510037374234254833 50230496632528030675691125)
      ·
        refine ⟨4709109059299502875846043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 50230496632528030675691125 4709109059299502875846043)
        ·
          refine ⟨7063663588949254313769065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4709109059299502875846043 7063663588949254313769065)
          ·
            refine ⟨5297747691711940735326799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7063663588949254313769065 5297747691711940735326799)
            ·
              refine ⟨7946621537567911102990199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5297747691711940735326799 7946621537567911102990199)
              ·
                refine ⟨11919932306351866654485299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7946621537567911102990199 11919932306351866654485299)
                ·
                  refine ⟨17879898459527799981727949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11919932306351866654485299 17879898459527799981727949)
                  ·
                    refine ⟨6704961922322924993147981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17879898459527799981727949 6704961922322924993147981)
                    ·
                      refine ⟨2514360720871096872430493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6704961922322924993147981 2514360720871096872430493)
                      ·
                        rfl

theorem cell23_4896700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 2, 1, 1, 1, 3, 3].length) (baseStart_4896700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4896700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4896700 prefixEnd_4896700 := by exact prefixLift 4896700
  have htrace : WordTrace (prefixWord ++ tailWord_4896700) baseStart_4896700 baseEnd_4896700 := by
    simpa [prefixWord, tailWord_4896700, baseEnd_4896700] using wordTrace_append hprefix tailTrace_4896700
  have hstable : (prefixWord ++ tailWord_4896700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4896700).length < 2 ^ (prefixWord ++ tailWord_4896700).sum := by decide
  have hdescent : baseEnd_4896700 < baseStart_4896700 := by decide
  rcases family_descends (prefixWord ++ tailWord_4896700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4896769 : List Nat := [1, 2, 4, 1, 2, 1, 1, 2, 1, 1, 7]
def baseStart_4896769 : Nat := 118140960795 + 4896769 * 2 ^ 59
def prefixEnd_4896769 : Nat := 4983230072969 + 3 ^ 40 * 4896769 * 2
def baseEnd_4896769 : Nat := 2514396151036257102467675

theorem tailTrace_4896769 : CollatzResearch.WordTrace tailWord_4896769 prefixEnd_4896769 2514396151036257102467675 := by
  unfold tailWord_4896769
  simp only [CollatzResearch.WordTrace]
  refine ⟨178599837996849689408941361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119066558664566459605960907 178599837996849689408941361)
  ·
    refine ⟨133949878497637267056706021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 178599837996849689408941361 133949878497637267056706021)
    ·
      refine ⟨25115602218306987573132379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 133949878497637267056706021 25115602218306987573132379)
      ·
        refine ⟨37673403327460481359698569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25115602218306987573132379 37673403327460481359698569)
        ·
          refine ⟨28255052495595361019773927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37673403327460481359698569 28255052495595361019773927)
          ·
            refine ⟨42382578743393041529660891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28255052495595361019773927 42382578743393041529660891)
            ·
              refine ⟨63573868115089562294491337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42382578743393041529660891 63573868115089562294491337)
              ·
                refine ⟨47680401086317171720868503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 63573868115089562294491337 47680401086317171720868503)
                ·
                  refine ⟨71520601629475757581302755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 47680401086317171720868503 71520601629475757581302755)
                  ·
                    refine ⟨107280902444213636371954133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 71520601629475757581302755 107280902444213636371954133)
                    ·
                      refine ⟨2514396151036257102467675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 107280902444213636371954133 2514396151036257102467675)
                      ·
                        rfl

theorem cell23_4896769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 1, 2, 1, 1, 7].length) (baseStart_4896769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4896769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4896769 prefixEnd_4896769 := by exact prefixLift 4896769
  have htrace : WordTrace (prefixWord ++ tailWord_4896769) baseStart_4896769 baseEnd_4896769 := by
    simpa [prefixWord, tailWord_4896769, baseEnd_4896769] using wordTrace_append hprefix tailTrace_4896769
  have hstable : (prefixWord ++ tailWord_4896769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4896769).length < 2 ^ (prefixWord ++ tailWord_4896769).sum := by decide
  have hdescent : baseEnd_4896769 < baseStart_4896769 := by decide
  rcases family_descends (prefixWord ++ tailWord_4896769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4896776 : List Nat := [2, 1, 3, 2, 1, 2, 4, 1, 2, 5]
def baseStart_4896776 : Nat := 118140960795 + 4896776 * 2 ^ 59
def prefixEnd_4896776 : Nat := 4983230072969 + 3 ^ 40 * 4896776 * 2
def baseEnd_4896776 : Nat := 838133248466946191693381

theorem tailTrace_4896776 : CollatzResearch.WordTrace tailWord_4896776 prefixEnd_4896776 838133248466946191693381 := by
  unfold tailWord_4896776
  simp only [CollatzResearch.WordTrace]
  refine ⟨89300046653912164802223091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119066728871882886402964121 89300046653912164802223091)
  ·
    refine ⟨133950069980868247203334637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89300046653912164802223091 133950069980868247203334637)
    ·
      refine ⟨50231276242825592701250489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 133950069980868247203334637 50231276242825592701250489)
      ·
        refine ⟨37673457182119194525937867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50231276242825592701250489 37673457182119194525937867)
        ·
          refine ⟨56510185773178791788906801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37673457182119194525937867 56510185773178791788906801)
          ·
            refine ⟨42382639329884093841680101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56510185773178791788906801 42382639329884093841680101)
            ·
              refine ⟨7946744874353267595315019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 42382639329884093841680101 7946744874353267595315019)
              ·
                refine ⟨11920117311529901392972529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7946744874353267595315019 11920117311529901392972529)
                ·
                  refine ⟨8940087983647426044729397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11920117311529901392972529 8940087983647426044729397)
                  ·
                    refine ⟨838133248466946191693381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8940087983647426044729397 838133248466946191693381)
                    ·
                      rfl

theorem cell23_4896776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 4, 1, 2, 5].length) (baseStart_4896776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4896776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4896776 prefixEnd_4896776 := by exact prefixLift 4896776
  have htrace : WordTrace (prefixWord ++ tailWord_4896776) baseStart_4896776 baseEnd_4896776 := by
    simpa [prefixWord, tailWord_4896776, baseEnd_4896776] using wordTrace_append hprefix tailTrace_4896776
  have hstable : (prefixWord ++ tailWord_4896776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4896776).length < 2 ^ (prefixWord ++ tailWord_4896776).sum := by decide
  have hdescent : baseEnd_4896776 < baseStart_4896776 := by decide
  rcases family_descends (prefixWord ++ tailWord_4896776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4896799 : List Nat := [1, 1, 2, 4, 1, 2, 1, 1, 2, 3, 5]
def baseStart_4896799 : Nat := 118140960795 + 4896799 * 2 ^ 59
def prefixEnd_4896799 : Nat := 4983230072969 + 3 ^ 40 * 4896799 * 2
def baseEnd_4896799 : Nat := 2514411555455891985092537

theorem tailTrace_4896799 : CollatzResearch.WordTrace tailWord_4896799 prefixEnd_4896799 2514411555455891985092537 := by
  unfold tailWord_4896799
  simp only [CollatzResearch.WordTrace]
  refine ⟨178600932186741004532533451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119067288124494003021688967 178600932186741004532533451)
  ·
    refine ⟨267901398280111506798800177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 178600932186741004532533451 267901398280111506798800177)
    ·
      refine ⟨200926048710083630099100133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 267901398280111506798800177 200926048710083630099100133)
      ·
        refine ⟨37673634133140680643581275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 200926048710083630099100133 37673634133140680643581275)
        ·
          refine ⟨56510451199711020965371913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37673634133140680643581275 56510451199711020965371913)
          ·
            refine ⟨42382838399783265724028935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56510451199711020965371913 42382838399783265724028935)
            ·
              refine ⟨63574257599674898586043403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42382838399783265724028935 63574257599674898586043403)
              ·
                refine ⟨95361386399512347879065105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 63574257599674898586043403 95361386399512347879065105)
                ·
                  refine ⟨71521039799634260909298829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 95361386399512347879065105 71521039799634260909298829)
                  ·
                    refine ⟨26820389924862847840987061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 71521039799634260909298829 26820389924862847840987061)
                    ·
                      refine ⟨2514411555455891985092537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26820389924862847840987061 2514411555455891985092537)
                      ·
                        rfl

theorem cell23_4896799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 1, 1, 2, 3, 5].length) (baseStart_4896799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4896799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4896799 prefixEnd_4896799 := by exact prefixLift 4896799
  have htrace : WordTrace (prefixWord ++ tailWord_4896799) baseStart_4896799 baseEnd_4896799 := by
    simpa [prefixWord, tailWord_4896799, baseEnd_4896799] using wordTrace_append hprefix tailTrace_4896799
  have hstable : (prefixWord ++ tailWord_4896799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4896799).length < 2 ^ (prefixWord ++ tailWord_4896799).sum := by decide
  have hdescent : baseEnd_4896799 < baseStart_4896799 := by decide
  rcases family_descends (prefixWord ++ tailWord_4896799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4896833 : List Nat := [1, 2, 5, 1, 2, 2, 1, 1, 1, 4, 3]
def baseStart_4896833 : Nat := 118140960795 + 4896833 * 2 ^ 59
def prefixEnd_4896833 : Nat := 4983230072969 + 3 ^ 40 * 4896833 * 2
def baseEnd_4896833 : Nat := 2514429013798144852067381

theorem tailTrace_4896833 : CollatzResearch.WordTrace tailWord_4896833 prefixEnd_4896833 2514429013798144852067381 := by
  unfold tailWord_4896833
  simp only [CollatzResearch.WordTrace]
  refine ⟨178602172268617828339271153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119068114845745218892847435 178602172268617828339271153)
  ·
    refine ⟨133951629201463371254453365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 178602172268617828339271153 133951629201463371254453365)
    ·
      refine ⟨12557965237637191055105003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 133951629201463371254453365 12557965237637191055105003)
      ·
        refine ⟨18836947856455786582657505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12557965237637191055105003 18836947856455786582657505)
        ·
          refine ⟨14127710892341839936993129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18836947856455786582657505 14127710892341839936993129)
          ·
            refine ⟨10595783169256379952744847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14127710892341839936993129 10595783169256379952744847)
            ·
              refine ⟨15893674753884569929117271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10595783169256379952744847 15893674753884569929117271)
              ·
                refine ⟨23840512130826854893675907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15893674753884569929117271 23840512130826854893675907)
                ·
                  refine ⟨35760768196240282340513861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23840512130826854893675907 35760768196240282340513861)
                  ·
                    refine ⟨6705144036795052938846349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 35760768196240282340513861 6705144036795052938846349)
                    ·
                      refine ⟨2514429013798144852067381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6705144036795052938846349 2514429013798144852067381)
                      ·
                        rfl

theorem cell23_4896833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 2, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 2, 1, 1, 1, 4, 3].length) (baseStart_4896833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4896833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4896833 prefixEnd_4896833 := by exact prefixLift 4896833
  have htrace : WordTrace (prefixWord ++ tailWord_4896833) baseStart_4896833 baseEnd_4896833 := by
    simpa [prefixWord, tailWord_4896833, baseEnd_4896833] using wordTrace_append hprefix tailTrace_4896833
  have hstable : (prefixWord ++ tailWord_4896833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4896833).length < 2 ^ (prefixWord ++ tailWord_4896833).sum := by decide
  have hdescent : baseEnd_4896833 < baseStart_4896833 := by decide
  rcases family_descends (prefixWord ++ tailWord_4896833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4896853 : List Nat := [1, 3, 2, 2, 1, 5, 1, 2, 6]
def baseStart_4896853 : Nat := 118140960795 + 4896853 * 2 ^ 59
def prefixEnd_4896853 : Nat := 4983230072969 + 3 ^ 40 * 4896853 * 2
def baseEnd_4896853 : Nat := 279382142601248308201921

theorem tailTrace_4896853 : CollatzResearch.WordTrace tailWord_4896853 prefixEnd_4896853 279382142601248308201921 := by
  unfold tailWord_4896853
  simp only [CollatzResearch.WordTrace]
  refine ⟨178602901728545371754999213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119068601152363581169999475 178602901728545371754999213)
  ·
    refine ⟨66976088148204514408124705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 178602901728545371754999213 66976088148204514408124705)
    ·
      refine ⟨50232066111153385806093529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66976088148204514408124705 50232066111153385806093529)
      ·
        refine ⟨37674049583365039354570147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50232066111153385806093529 37674049583365039354570147)
        ·
          refine ⟨56511074375047559031855221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37674049583365039354570147 56511074375047559031855221)
          ·
            refine ⟨5297913222660708659236427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 56511074375047559031855221 5297913222660708659236427)
            ·
              refine ⟨7946869833991062988854641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5297913222660708659236427 7946869833991062988854641)
              ·
                refine ⟨5960152375493297241640981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7946869833991062988854641 5960152375493297241640981)
                ·
                  refine ⟨279382142601248308201921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5960152375493297241640981 279382142601248308201921)
                  ·
                    rfl

theorem cell23_4896853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 5, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 5, 1, 2, 6].length) (baseStart_4896853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4896853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4896853 prefixEnd_4896853 := by exact prefixLift 4896853
  have htrace : WordTrace (prefixWord ++ tailWord_4896853) baseStart_4896853 baseEnd_4896853 := by
    simpa [prefixWord, tailWord_4896853, baseEnd_4896853] using wordTrace_append hprefix tailTrace_4896853
  have hstable : (prefixWord ++ tailWord_4896853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4896853).length < 2 ^ (prefixWord ++ tailWord_4896853).sum := by decide
  have hdescent : baseEnd_4896853 < baseStart_4896853 := by decide
  rcases family_descends (prefixWord ++ tailWord_4896853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4896903 : List Nat := [1, 1, 4, 2, 1, 1, 4, 3, 1, 1, 4]
def baseStart_4896903 : Nat := 118140960795 + 4896903 * 2 ^ 59
def prefixEnd_4896903 : Nat := 4983230072969 + 3 ^ 40 * 4896903 * 2
def baseEnd_4896903 : Nat := 2514464957443959578192059

theorem tailTrace_4896903 : CollatzResearch.WordTrace tailWord_4896903 prefixEnd_4896903 2514464957443959578192059 := by
  unfold tailWord_4896903
  simp only [CollatzResearch.WordTrace]
  refine ⟨178604725378364230294319363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119069816918909486862879575 178604725378364230294319363)
  ·
    refine ⟨267907088067546345441479045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 178604725378364230294319363 267907088067546345441479045)
    ·
      refine ⟨50232579012664939770277321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 267907088067546345441479045 50232579012664939770277321)
      ·
        refine ⟨37674434259498704827707991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50232579012664939770277321 37674434259498704827707991)
        ·
          refine ⟨56511651389248057241561987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37674434259498704827707991 56511651389248057241561987)
          ·
            refine ⟨84767477083872085862342981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56511651389248057241561987 84767477083872085862342981)
            ·
              refine ⟨15893901953226016099189309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 84767477083872085862342981 15893901953226016099189309)
              ·
                refine ⟨5960213232459756037195991, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15893901953226016099189309 5960213232459756037195991)
                ·
                  refine ⟨8940319848689634055793987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5960213232459756037195991 8940319848689634055793987)
                  ·
                    refine ⟨13410479773034451083690981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8940319848689634055793987 13410479773034451083690981)
                    ·
                      refine ⟨2514464957443959578192059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13410479773034451083690981 2514464957443959578192059)
                      ·
                        rfl

theorem cell23_4896903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 4, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 4, 3, 1, 1, 4].length) (baseStart_4896903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4896903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4896903 prefixEnd_4896903 := by exact prefixLift 4896903
  have htrace : WordTrace (prefixWord ++ tailWord_4896903) baseStart_4896903 baseEnd_4896903 := by
    simpa [prefixWord, tailWord_4896903, baseEnd_4896903] using wordTrace_append hprefix tailTrace_4896903
  have hstable : (prefixWord ++ tailWord_4896903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4896903).length < 2 ^ (prefixWord ++ tailWord_4896903).sum := by decide
  have hdescent : baseEnd_4896903 < baseStart_4896903 := by decide
  rcases family_descends (prefixWord ++ tailWord_4896903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4896914 : List Nat := [3, 2, 3, 1, 1, 1, 5, 2, 1, 1, 3]
def baseStart_4896914 : Nat := 118140960795 + 4896914 * 2 ^ 59
def prefixEnd_4896914 : Nat := 4983230072969 + 3 ^ 40 * 4896914 * 2
def baseEnd_4896914 : Nat := 2514470605731159035154509

theorem tailTrace_4896914 : CollatzResearch.WordTrace tailWord_4896914 prefixEnd_4896914 2514470605731159035154509 := by
  unfold tailWord_4896914
  simp only [CollatzResearch.WordTrace]
  refine ⟨44651281645331094793242449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 119070084387549586115313197 44651281645331094793242449)
  ·
    refine ⟨33488461233998321094931837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44651281645331094793242449 33488461233998321094931837)
    ·
      refine ⟨12558172962749370410599439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33488461233998321094931837 12558172962749370410599439)
      ·
        refine ⟨18837259444124055615899159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12558172962749370410599439 18837259444124055615899159)
        ·
          refine ⟨28255889166186083423848739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18837259444124055615899159 28255889166186083423848739)
          ·
            refine ⟨42383833749279125135773109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28255889166186083423848739 42383833749279125135773109)
            ·
              refine ⟨3973484413994917981478729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 42383833749279125135773109 3973484413994917981478729)
              ·
                refine ⟨2980113310496188486109047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3973484413994917981478729 2980113310496188486109047)
                ·
                  refine ⟨4470169965744282729163571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2980113310496188486109047 4470169965744282729163571)
                  ·
                    refine ⟨6705254948616424093745357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4470169965744282729163571 6705254948616424093745357)
                    ·
                      refine ⟨2514470605731159035154509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6705254948616424093745357 2514470605731159035154509)
                      ·
                        rfl

theorem cell23_4896914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 5, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 5, 2, 1, 1, 3].length) (baseStart_4896914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4896914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4896914 prefixEnd_4896914 := by exact prefixLift 4896914
  have htrace : WordTrace (prefixWord ++ tailWord_4896914) baseStart_4896914 baseEnd_4896914 := by
    simpa [prefixWord, tailWord_4896914, baseEnd_4896914] using wordTrace_append hprefix tailTrace_4896914
  have hstable : (prefixWord ++ tailWord_4896914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4896914).length < 2 ^ (prefixWord ++ tailWord_4896914).sum := by decide
  have hdescent : baseEnd_4896914 < baseStart_4896914 := by decide
  rcases family_descends (prefixWord ++ tailWord_4896914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4896953 : List Nat := [1, 2, 1, 4, 1, 2, 3, 2, 1, 3, 3]
def baseStart_4896953 : Nat := 118140960795 + 4896953 * 2 ^ 59
def prefixEnd_4896953 : Nat := 4983230072969 + 3 ^ 40 * 4896953 * 2
def baseEnd_4896953 : Nat := 2514490631476684382566829

theorem tailTrace_4896953 : CollatzResearch.WordTrace tailWord_4896953 prefixEnd_4896953 2514490631476684382566829 := by
  unfold tailWord_4896953
  simp only [CollatzResearch.WordTrace]
  refine ⟨178606549028183088833639513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119071032685455392555759675 178606549028183088833639513)
  ·
    refine ⟨133954911771137316625229635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 178606549028183088833639513 133954911771137316625229635)
    ·
      refine ⟨200932367656705974937844453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 133954911771137316625229635 200932367656705974937844453)
      ·
        refine ⟨37674818935632370300845835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 200932367656705974937844453 37674818935632370300845835)
        ·
          refine ⟨56512228403448555451268753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37674818935632370300845835 56512228403448555451268753)
          ·
            refine ⟨42384171302586416588451565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56512228403448555451268753 42384171302586416588451565)
            ·
              refine ⟨15894064238469906220669337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 42384171302586416588451565 15894064238469906220669337)
              ·
                refine ⟨11920548178852429665502003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15894064238469906220669337 11920548178852429665502003)
                ·
                  refine ⟨17880822268278644498253005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11920548178852429665502003 17880822268278644498253005)
                  ·
                    refine ⟨6705308350604491686844877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17880822268278644498253005 6705308350604491686844877)
                    ·
                      refine ⟨2514490631476684382566829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6705308350604491686844877 2514490631476684382566829)
                      ·
                        rfl

theorem cell23_4896953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 3, 2, 1, 3, 3].length) (baseStart_4896953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4896953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4896953 prefixEnd_4896953 := by exact prefixLift 4896953
  have htrace : WordTrace (prefixWord ++ tailWord_4896953) baseStart_4896953 baseEnd_4896953 := by
    simpa [prefixWord, tailWord_4896953, baseEnd_4896953] using wordTrace_append hprefix tailTrace_4896953
  have hstable : (prefixWord ++ tailWord_4896953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4896953).length < 2 ^ (prefixWord ++ tailWord_4896953).sum := by decide
  have hdescent : baseEnd_4896953 < baseStart_4896953 := by decide
  rcases family_descends (prefixWord ++ tailWord_4896953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4896986 : List Nat := [3, 1, 1, 2, 2, 1, 3, 1, 1, 8]
def baseStart_4896986 : Nat := 118140960795 + 4896986 * 2 ^ 59
def prefixEnd_4896986 : Nat := 4983230072969 + 3 ^ 40 * 4896986 * 2
def baseEnd_4896986 : Nat := 838169192112760917818059

theorem tailTrace_4896986 : CollatzResearch.WordTrace tailWord_4896986 prefixEnd_4896986 838169192112760917818059 := by
  unfold tailWord_4896986
  simp only [CollatzResearch.WordTrace]
  refine ⟨44651938159265883867397703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 119071835091375690313060541 44651938159265883867397703)
  ·
    refine ⟨66977907238898825801096555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44651938159265883867397703 66977907238898825801096555)
    ·
      refine ⟨100466860858348238701644833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66977907238898825801096555 100466860858348238701644833)
      ·
        refine ⟨75350145643761179026233625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 100466860858348238701644833 75350145643761179026233625)
        ·
          refine ⟨56512609232820884269675219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 75350145643761179026233625 56512609232820884269675219)
          ·
            refine ⟨84768913849231326404512829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56512609232820884269675219 84768913849231326404512829)
            ·
              refine ⟨31788342693461747401692311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 84768913849231326404512829 31788342693461747401692311)
              ·
                refine ⟨47682514040192621102538467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31788342693461747401692311 47682514040192621102538467)
                ·
                  refine ⟨71523771060288931653807701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 47682514040192621102538467 71523771060288931653807701)
                  ·
                    refine ⟨838169192112760917818059, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 71523771060288931653807701 838169192112760917818059)
                    ·
                      rfl

theorem cell23_4896986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 3, 1, 1, 8].length) (baseStart_4896986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4896986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4896986 prefixEnd_4896986 := by exact prefixLift 4896986
  have htrace : WordTrace (prefixWord ++ tailWord_4896986) baseStart_4896986 baseEnd_4896986 := by
    simpa [prefixWord, tailWord_4896986, baseEnd_4896986] using wordTrace_append hprefix tailTrace_4896986
  have hstable : (prefixWord ++ tailWord_4896986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4896986).length < 2 ^ (prefixWord ++ tailWord_4896986).sum := by decide
  have hdescent : baseEnd_4896986 < baseStart_4896986 := by decide
  rcases family_descends (prefixWord ++ tailWord_4896986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4896994 : List Nat := [3, 3, 4, 1, 1, 1, 3, 7]
def baseStart_4896994 : Nat := 118140960795 + 4896994 * 2 ^ 59
def prefixEnd_4896994 : Nat := 4983230072969 + 3 ^ 40 * 4896994 * 2
def baseEnd_4896994 : Nat := 93130062377167360079783

theorem tailTrace_4896994 : CollatzResearch.WordTrace tailWord_4896994 prefixEnd_4896994 93130062377167360079783 := by
  unfold tailWord_4896994
  simp only [CollatzResearch.WordTrace]
  refine ⟨44652011105258638208970509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 119072029614023035223921357 44652011105258638208970509)
  ·
    refine ⟨16744504164471989328363941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44652011105258638208970509 16744504164471989328363941)
    ·
      refine ⟨3139594530838497999068239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 16744504164471989328363941 3139594530838497999068239)
      ·
        refine ⟨4709391796257746998602359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3139594530838497999068239 4709391796257746998602359)
        ·
          refine ⟨7064087694386620497903539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4709391796257746998602359 7064087694386620497903539)
          ·
            refine ⟨10596131541579930746855309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7064087694386620497903539 10596131541579930746855309)
            ·
              refine ⟨3973549328092474030070741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10596131541579930746855309 3973549328092474030070741)
              ·
                refine ⟨93130062377167360079783, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3973549328092474030070741 93130062377167360079783)
                ·
                  rfl

theorem cell23_4896994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 1, 3, 7].length) (baseStart_4896994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4896994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4896994 prefixEnd_4896994 := by exact prefixLift 4896994
  have htrace : WordTrace (prefixWord ++ tailWord_4896994) baseStart_4896994 baseEnd_4896994 := by
    simpa [prefixWord, tailWord_4896994, baseEnd_4896994] using wordTrace_append hprefix tailTrace_4896994
  have hstable : (prefixWord ++ tailWord_4896994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4896994).length < 2 ^ (prefixWord ++ tailWord_4896994).sum := by decide
  have hdescent : baseEnd_4896994 < baseStart_4896994 := by decide
  rcases family_descends (prefixWord ++ tailWord_4896994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4897014 : List Nat := [5, 1, 1, 1, 1, 1, 6, 1, 1, 3, 2]
def baseStart_4897014 : Nat := 118140960795 + 4897014 * 2 ^ 59
def prefixEnd_4897014 : Nat := 4983230072969 + 3 ^ 40 * 4897014 * 2
def baseEnd_4897014 : Nat := 2514521953796608643904049

theorem tailTrace_4897014 : CollatzResearch.WordTrace tailWord_4897014 prefixEnd_4897014 2514521953796608643904049 := by
  unfold tailWord_4897014
  simp only [CollatzResearch.WordTrace]
  refine ⟨11163048367560131015725631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 119072515920641397501073397 11163048367560131015725631)
  ·
    refine ⟨16744572551340196523588447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11163048367560131015725631 16744572551340196523588447)
    ·
      refine ⟨25116858827010294785382671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16744572551340196523588447 25116858827010294785382671)
      ·
        refine ⟨37675288240515442178074007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25116858827010294785382671 37675288240515442178074007)
        ·
          refine ⟨56512932360773163267111011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37675288240515442178074007 56512932360773163267111011)
          ·
            refine ⟨84769398541159744900666517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56512932360773163267111011 84769398541159744900666517)
            ·
              refine ⟨3973565556616863042218743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 84769398541159744900666517 3973565556616863042218743)
              ·
                refine ⟨5960348334925294563328115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3973565556616863042218743 5960348334925294563328115)
                ·
                  refine ⟨8940522502387941844992173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5960348334925294563328115 8940522502387941844992173)
                  ·
                    refine ⟨3352695938395478191872065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8940522502387941844992173 3352695938395478191872065)
                    ·
                      refine ⟨2514521953796608643904049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3352695938395478191872065 2514521953796608643904049)
                      ·
                        rfl

theorem cell23_4897014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 6, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 6, 1, 1, 3, 2].length) (baseStart_4897014 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4897014 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4897014 prefixEnd_4897014 := by exact prefixLift 4897014
  have htrace : WordTrace (prefixWord ++ tailWord_4897014) baseStart_4897014 baseEnd_4897014 := by
    simpa [prefixWord, tailWord_4897014, baseEnd_4897014] using wordTrace_append hprefix tailTrace_4897014
  have hstable : (prefixWord ++ tailWord_4897014).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4897014).length < 2 ^ (prefixWord ++ tailWord_4897014).sum := by decide
  have hdescent : baseEnd_4897014 < baseStart_4897014 := by decide
  rcases family_descends (prefixWord ++ tailWord_4897014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4897033 : List Nat := [1, 2, 1, 1, 3, 5, 2, 1, 7]
def baseStart_4897033 : Nat := 118140960795 + 4897033 * 2 ^ 59
def prefixEnd_4897033 : Nat := 4983230072969 + 3 ^ 40 * 4897033 * 2
def baseEnd_4897033 : Nat := 279392412214338229951829

theorem tailTrace_4897033 : CollatzResearch.WordTrace tailWord_4897033 prefixEnd_4897033 279392412214338229951829 := by
  unfold tailWord_4897033
  simp only [CollatzResearch.WordTrace]
  refine ⟨178609466867893262496551753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119072977911928841664367835 178609466867893262496551753)
  ·
    refine ⟨133957100150919946872413815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 178609466867893262496551753 133957100150919946872413815)
    ·
      refine ⟨200935650226379920308620723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 133957100150919946872413815 200935650226379920308620723)
      ·
        refine ⟨301403475339569880462931085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 200935650226379920308620723 301403475339569880462931085)
        ·
          refine ⟨113026303252338705173599157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 301403475339569880462931085 113026303252338705173599157)
          ·
            refine ⟨10596215929906753610024921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 113026303252338705173599157 10596215929906753610024921)
            ·
              refine ⟨7947161947430065207518691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10596215929906753610024921 7947161947430065207518691)
              ·
                refine ⟨11920742921145097811278037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7947161947430065207518691 11920742921145097811278037)
                ·
                  refine ⟨279392412214338229951829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11920742921145097811278037 279392412214338229951829)
                  ·
                    rfl

theorem cell23_4897033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 5, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 5, 2, 1, 7].length) (baseStart_4897033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4897033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4897033 prefixEnd_4897033 := by exact prefixLift 4897033
  have htrace : WordTrace (prefixWord ++ tailWord_4897033) baseStart_4897033 baseEnd_4897033 := by
    simpa [prefixWord, tailWord_4897033, baseEnd_4897033] using wordTrace_append hprefix tailTrace_4897033
  have hstable : (prefixWord ++ tailWord_4897033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4897033).length < 2 ^ (prefixWord ++ tailWord_4897033).sum := by decide
  have hdescent : baseEnd_4897033 < baseStart_4897033 := by decide
  rcases family_descends (prefixWord ++ tailWord_4897033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4897100 : List Nat := [2, 2, 1, 3, 2, 1, 2, 1, 1, 6, 2]
def baseStart_4897100 : Nat := 118140960795 + 4897100 * 2 ^ 59
def prefixEnd_4897100 : Nat := 4983230072969 + 3 ^ 40 * 4897100 * 2
def baseEnd_4897100 : Nat := 2514566113132895307428653

theorem tailTrace_4897100 : CollatzResearch.WordTrace tailWord_4897100 prefixEnd_4897100 2514566113132895307428653 := by
  unfold tailWord_4897100
  simp only [CollatzResearch.WordTrace]
  refine ⟨89305955279325266469620377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119074607039100355292827169 89305955279325266469620377)
  ·
    refine ⟨66979466459493949852215283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89305955279325266469620377 66979466459493949852215283)
    ·
      refine ⟨100469199689240924778322925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66979466459493949852215283 100469199689240924778322925)
      ·
        refine ⟨37675949883465346791871097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 100469199689240924778322925 37675949883465346791871097)
        ·
          refine ⟨28256962412599010093903323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37675949883465346791871097 28256962412599010093903323)
          ·
            refine ⟨42385443618898515140854985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28256962412599010093903323 42385443618898515140854985)
            ·
              refine ⟨31789082714173886355641239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42385443618898515140854985 31789082714173886355641239)
              ·
                refine ⟨47683624071260829533461859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31789082714173886355641239 47683624071260829533461859)
                ·
                  refine ⟨71525436106891244300192789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 47683624071260829533461859 71525436106891244300192789)
                  ·
                    refine ⟨3352754817510527076571537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 71525436106891244300192789 3352754817510527076571537)
                    ·
                      refine ⟨2514566113132895307428653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3352754817510527076571537 2514566113132895307428653)
                      ·
                        rfl

theorem cell23_4897100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 2, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 2, 1, 1, 6, 2].length) (baseStart_4897100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4897100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4897100 prefixEnd_4897100 := by exact prefixLift 4897100
  have htrace : WordTrace (prefixWord ++ tailWord_4897100) baseStart_4897100 baseEnd_4897100 := by
    simpa [prefixWord, tailWord_4897100, baseEnd_4897100] using wordTrace_append hprefix tailTrace_4897100
  have hstable : (prefixWord ++ tailWord_4897100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4897100).length < 2 ^ (prefixWord ++ tailWord_4897100).sum := by decide
  have hdescent : baseEnd_4897100 < baseStart_4897100 := by decide
  rcases family_descends (prefixWord ++ tailWord_4897100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4897103 : List Nat := [1, 1, 2, 1, 1, 2, 1, 6, 1, 4, 3]
def baseStart_4897103 : Nat := 118140960795 + 4897103 * 2 ^ 59
def prefixEnd_4897103 : Nat := 4983230072969 + 3 ^ 40 * 4897103 * 2
def baseEnd_4897103 : Nat := 2514567653574858795691139

theorem tailTrace_4897103 : CollatzResearch.WordTrace tailWord_4897103 prefixEnd_4897103 2514567653574858795691139 := by
  unfold tailWord_4897103
  simp only [CollatzResearch.WordTrace]
  refine ⟨178612019977639664451599963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119074679985093109634399975 178612019977639664451599963)
  ·
    refine ⟨267918029966459496677399945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 178612019977639664451599963 267918029966459496677399945)
    ·
      refine ⟨200938522474844622508049959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 267918029966459496677399945 200938522474844622508049959)
      ·
        refine ⟨301407783712266933762074939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 200938522474844622508049959 301407783712266933762074939)
        ·
          refine ⟨452111675568400400643112409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 301407783712266933762074939 452111675568400400643112409)
          ·
            refine ⟨339083756676300300482334307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 452111675568400400643112409 339083756676300300482334307)
            ·
              refine ⟨508625635014450450723501461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 339083756676300300482334307 508625635014450450723501461)
              ·
                refine ⟨23841826641302364877664131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 508625635014450450723501461 23841826641302364877664131)
                ·
                  refine ⟨35762739961953547316496197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23841826641302364877664131 35762739961953547316496197)
                  ·
                    refine ⟨6705513742866290121843037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 35762739961953547316496197 6705513742866290121843037)
                    ·
                      refine ⟨2514567653574858795691139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6705513742866290121843037 2514567653574858795691139)
                      ·
                        rfl

theorem cell23_4897103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 6, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 6, 1, 4, 3].length) (baseStart_4897103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4897103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4897103 prefixEnd_4897103 := by exact prefixLift 4897103
  have htrace : WordTrace (prefixWord ++ tailWord_4897103) baseStart_4897103 baseEnd_4897103 := by
    simpa [prefixWord, tailWord_4897103, baseEnd_4897103] using wordTrace_append hprefix tailTrace_4897103
  have hstable : (prefixWord ++ tailWord_4897103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4897103).length < 2 ^ (prefixWord ++ tailWord_4897103).sum := by decide
  have hdescent : baseEnd_4897103 < baseStart_4897103 := by decide
  rcases family_descends (prefixWord ++ tailWord_4897103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4897184 : List Nat := [2, 1, 1, 4, 1, 3, 1, 5, 1, 1, 3]
def baseStart_4897184 : Nat := 118140960795 + 4897184 * 2 ^ 59
def prefixEnd_4897184 : Nat := 4983230072969 + 3 ^ 40 * 4897184 * 2
def baseEnd_4897184 : Nat := 2514609245507872978778267

theorem tailTrace_4897184 : CollatzResearch.WordTrace tailWord_4897184 prefixEnd_4897184 2514609245507872978778267 := by
  unfold tailWord_4897184
  simp only [CollatzResearch.WordTrace]
  refine ⟨89307487145173107642649303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119076649526897476856865737 89307487145173107642649303)
  ·
    refine ⟨133961230717759661463973955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89307487145173107642649303 133961230717759661463973955)
    ·
      refine ⟨200941846076639492195960933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 133961230717759661463973955 200941846076639492195960933)
      ·
        refine ⟨37676596139369904786742675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 200941846076639492195960933 37676596139369904786742675)
        ·
          refine ⟨56514894209054857180114013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37676596139369904786742675 56514894209054857180114013)
          ·
            refine ⟨21193085328395571442542755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 56514894209054857180114013 21193085328395571442542755)
            ·
              refine ⟨31789627992593357163814133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21193085328395571442542755 31789627992593357163814133)
              ·
                refine ⟨2980277624305627234107575, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 31789627992593357163814133 2980277624305627234107575)
                ·
                  refine ⟨4470416436458440851161363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2980277624305627234107575 4470416436458440851161363)
                  ·
                    refine ⟨6705624654687661276742045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4470416436458440851161363 6705624654687661276742045)
                    ·
                      refine ⟨2514609245507872978778267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6705624654687661276742045 2514609245507872978778267)
                      ·
                        rfl

theorem cell23_4897184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 1, 5, 1, 1, 3].length) (baseStart_4897184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4897184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4897184 prefixEnd_4897184 := by exact prefixLift 4897184
  have htrace : WordTrace (prefixWord ++ tailWord_4897184) baseStart_4897184 baseEnd_4897184 := by
    simpa [prefixWord, tailWord_4897184, baseEnd_4897184] using wordTrace_append hprefix tailTrace_4897184
  have hstable : (prefixWord ++ tailWord_4897184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4897184).length < 2 ^ (prefixWord ++ tailWord_4897184).sum := by decide
  have hdescent : baseEnd_4897184 < baseStart_4897184 := by decide
  rcases family_descends (prefixWord ++ tailWord_4897184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4897187 : List Nat := [1, 1, 1, 4, 1, 4, 4, 1, 1, 5]
def baseStart_4897187 : Nat := 118140960795 + 4897187 * 2 ^ 59
def prefixEnd_4897187 : Nat := 4983230072969 + 3 ^ 40 * 4897187 * 2
def baseEnd_4897187 : Nat := 838203595316612155680251

theorem tailTrace_4897187 : CollatzResearch.WordTrace tailWord_4897187 prefixEnd_4897187 838203595316612155680251 := by
  unfold tailWord_4897187
  simp only [CollatzResearch.WordTrace]
  refine ⟨178615083709335346797657815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119076722472890231198438543 178615083709335346797657815)
  ·
    refine ⟨267922625564003020196486723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 178615083709335346797657815 267922625564003020196486723)
    ·
      refine ⟨401883938346004530294730085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 267922625564003020196486723 401883938346004530294730085)
      ·
        refine ⟨75353238439875849430261891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 401883938346004530294730085 75353238439875849430261891)
        ·
          refine ⟨113029857659813774145392837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75353238439875849430261891 113029857659813774145392837)
          ·
            refine ⟨21193098311215082652261157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 113029857659813774145392837 21193098311215082652261157)
            ·
              refine ⟨3973705933352827997298967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21193098311215082652261157 3973705933352827997298967)
              ·
                refine ⟨5960558900029241995948451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3973705933352827997298967 5960558900029241995948451)
                ·
                  refine ⟨8940838350043862993922677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5960558900029241995948451 8940838350043862993922677)
                  ·
                    refine ⟨838203595316612155680251, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8940838350043862993922677 838203595316612155680251)
                    ·
                      rfl

theorem cell23_4897187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 4, 1, 1, 5].length) (baseStart_4897187 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4897187 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4897187 prefixEnd_4897187 := by exact prefixLift 4897187
  have htrace : WordTrace (prefixWord ++ tailWord_4897187) baseStart_4897187 baseEnd_4897187 := by
    simpa [prefixWord, tailWord_4897187, baseEnd_4897187] using wordTrace_append hprefix tailTrace_4897187
  have hstable : (prefixWord ++ tailWord_4897187).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4897187).length < 2 ^ (prefixWord ++ tailWord_4897187).sum := by decide
  have hdescent : baseEnd_4897187 < baseStart_4897187 := by decide
  rcases family_descends (prefixWord ++ tailWord_4897187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4897193 : List Nat := [1, 2, 1, 1, 1, 1, 3, 2, 5, 1, 5]
def baseStart_4897193 : Nat := 118140960795 + 4897193 * 2 ^ 59
def prefixEnd_4897193 : Nat := 4983230072969 + 3 ^ 40 * 4897193 * 2
def baseEnd_4897193 : Nat := 2514613866833763443565725

theorem tailTrace_4897193 : CollatzResearch.WordTrace tailWord_4897193 prefixEnd_4897193 2514613866833763443565725 := by
  unfold tailWord_4897193
  simp only [CollatzResearch.WordTrace]
  refine ⟨178615302547313609822376233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119076868364875739881584155 178615302547313609822376233)
  ·
    refine ⟨133961476910485207366782175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 178615302547313609822376233 133961476910485207366782175)
    ·
      refine ⟨200942215365727811050173263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 133961476910485207366782175 200942215365727811050173263)
      ·
        refine ⟨301413323048591716575259895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 200942215365727811050173263 301413323048591716575259895)
        ·
          refine ⟨452119984572887574862889843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 301413323048591716575259895 452119984572887574862889843)
          ·
            refine ⟨678179976859331362294334765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 452119984572887574862889843 678179976859331362294334765)
            ·
              refine ⟨254317491322249260860375537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 678179976859331362294334765 254317491322249260860375537)
              ·
                refine ⟨190738118491686945645281653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 254317491322249260860375537 190738118491686945645281653)
                ·
                  refine ⟨17881698608595651154245155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 190738118491686945645281653 17881698608595651154245155)
                  ·
                    refine ⟨26822547912893476731367733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17881698608595651154245155 26822547912893476731367733)
                    ·
                      refine ⟨2514613866833763443565725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26822547912893476731367733 2514613866833763443565725)
                      ·
                        rfl

theorem cell23_4897193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 2, 5, 1, 5].length) (baseStart_4897193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4897193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4897193 prefixEnd_4897193 := by exact prefixLift 4897193
  have htrace : WordTrace (prefixWord ++ tailWord_4897193) baseStart_4897193 baseEnd_4897193 := by
    simpa [prefixWord, tailWord_4897193, baseEnd_4897193] using wordTrace_append hprefix tailTrace_4897193
  have hstable : (prefixWord ++ tailWord_4897193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4897193).length < 2 ^ (prefixWord ++ tailWord_4897193).sum := by decide
  have hdescent : baseEnd_4897193 < baseStart_4897193 := by decide
  rcases family_descends (prefixWord ++ tailWord_4897193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4897203 : List Nat := [1, 1, 1, 2, 3, 1, 1, 1, 2, 6, 4]
def baseStart_4897203 : Nat := 118140960795 + 4897203 * 2 ^ 59
def prefixEnd_4897203 : Nat := 4983230072969 + 3 ^ 40 * 4897203 * 2
def baseEnd_4897203 : Nat := 2514619001640308404440679

theorem tailTrace_4897203 : CollatzResearch.WordTrace tailWord_4897203 prefixEnd_4897203 2514619001640308404440679 := by
  unfold tailWord_4897203
  simp only [CollatzResearch.WordTrace]
  refine ⟨178615667277277381530240263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119077111518184921020160175 178615667277277381530240263)
  ·
    refine ⟨267923500915916072295360395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 178615667277277381530240263 267923500915916072295360395)
    ·
      refine ⟨401885251373874108443040593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 267923500915916072295360395 401885251373874108443040593)
      ·
        refine ⟨301413938530405581332280445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 401885251373874108443040593 301413938530405581332280445)
        ·
          refine ⟨113030226948902092999605167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 301413938530405581332280445 113030226948902092999605167)
          ·
            refine ⟨169545340423353139499407751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 113030226948902092999605167 169545340423353139499407751)
            ·
              refine ⟨254318010635029709249111627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 169545340423353139499407751 254318010635029709249111627)
              ·
                refine ⟨381477015952544563873667441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 254318010635029709249111627 381477015952544563873667441)
                ·
                  refine ⟨286107761964408422905250581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 381477015952544563873667441 286107761964408422905250581)
                  ·
                    refine ⟨13411301342081644823683621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 286107761964408422905250581 13411301342081644823683621)
                    ·
                      refine ⟨2514619001640308404440679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13411301342081644823683621 2514619001640308404440679)
                      ·
                        rfl

theorem cell23_4897203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 1, 2, 6, 4].length) (baseStart_4897203 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4897203 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4897203 prefixEnd_4897203 := by exact prefixLift 4897203
  have htrace : WordTrace (prefixWord ++ tailWord_4897203) baseStart_4897203 baseEnd_4897203 := by
    simpa [prefixWord, tailWord_4897203, baseEnd_4897203] using wordTrace_append hprefix tailTrace_4897203
  have hstable : (prefixWord ++ tailWord_4897203).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4897203).length < 2 ^ (prefixWord ++ tailWord_4897203).sum := by decide
  have hdescent : baseEnd_4897203 < baseStart_4897203 := by decide
  rcases family_descends (prefixWord ++ tailWord_4897203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4897210 : List Nat := [3, 1, 1, 1, 2, 1, 1, 3, 5, 2, 3]
def baseStart_4897210 : Nat := 118140960795 + 4897210 * 2 ^ 59
def prefixEnd_4897210 : Nat := 4983230072969 + 3 ^ 40 * 4897210 * 2
def baseEnd_4897210 : Nat := 2514622596004889877053147

theorem tailTrace_4897210 : CollatzResearch.WordTrace tailWord_4897210 prefixEnd_4897210 2514622596004889877053147 := by
  unfold tailWord_4897210
  simp only [CollatzResearch.WordTrace]
  refine ⟨44653980647063005431436271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 119077281725501347817163389 44653980647063005431436271)
  ·
    refine ⟨66980970970594508147154407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44653980647063005431436271 66980970970594508147154407)
    ·
      refine ⟨100471456455891762220731611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66980970970594508147154407 100471456455891762220731611)
      ·
        refine ⟨150707184683837643331097417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100471456455891762220731611 150707184683837643331097417)
        ·
          refine ⟨113030388512878232498323063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 150707184683837643331097417 113030388512878232498323063)
          ·
            refine ⟨169545582769317348747484595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 113030388512878232498323063 169545582769317348747484595)
            ·
              refine ⟨254318374153976023121226893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 169545582769317348747484595 254318374153976023121226893)
              ·
                refine ⟨95369390307741008670460085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 254318374153976023121226893 95369390307741008670460085)
                ·
                  refine ⟨8940880341350719562855633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 95369390307741008670460085 8940880341350719562855633)
                  ·
                    refine ⟨6705660256013039672141725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8940880341350719562855633 6705660256013039672141725)
                    ·
                      refine ⟨2514622596004889877053147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6705660256013039672141725 2514622596004889877053147)
                      ·
                        rfl

theorem cell23_4897210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 3, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 3, 5, 2, 3].length) (baseStart_4897210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4897210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4897210 prefixEnd_4897210 := by exact prefixLift 4897210
  have htrace : WordTrace (prefixWord ++ tailWord_4897210) baseStart_4897210 baseEnd_4897210 := by
    simpa [prefixWord, tailWord_4897210, baseEnd_4897210] using wordTrace_append hprefix tailTrace_4897210
  have hstable : (prefixWord ++ tailWord_4897210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4897210).length < 2 ^ (prefixWord ++ tailWord_4897210).sum := by decide
  have hdescent : baseEnd_4897210 < baseStart_4897210 := by decide
  rcases family_descends (prefixWord ++ tailWord_4897210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4897224 : List Nat := [2, 1, 3, 1, 3, 2, 2, 2, 3, 2, 2]
def baseStart_4897224 : Nat := 118140960795 + 4897224 * 2 ^ 59
def prefixEnd_4897224 : Nat := 4983230072969 + 3 ^ 40 * 4897224 * 2
def baseEnd_4897224 : Nat := 2514629784734052822278083

theorem tailTrace_4897224 : CollatzResearch.WordTrace tailWord_4897224 prefixEnd_4897224 2514629784734052822278083 := by
  unfold tailWord_4897224
  simp only [CollatzResearch.WordTrace]
  refine ⟨89308216605100651058377363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119077622140134201411169817 89308216605100651058377363)
  ·
    refine ⟨133962324907650976587566045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89308216605100651058377363 133962324907650976587566045)
    ·
      refine ⟨50235871840369116220337267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 133962324907650976587566045 50235871840369116220337267)
      ·
        refine ⟨75353807760553674330505901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50235871840369116220337267 75353807760553674330505901)
        ·
          refine ⟨28257677910207627873939713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 75353807760553674330505901 28257677910207627873939713)
          ·
            refine ⟨21193258432655720905454785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28257677910207627873939713 21193258432655720905454785)
            ·
              refine ⟨15894943824491790679091089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21193258432655720905454785 15894943824491790679091089)
              ·
                refine ⟨11921207868368843009318317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15894943824491790679091089 11921207868368843009318317)
                ·
                  refine ⟨4470452950638316128494369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11921207868368843009318317 4470452950638316128494369)
                  ·
                    refine ⟨3352839712978737096370777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4470452950638316128494369 3352839712978737096370777)
                    ·
                      refine ⟨2514629784734052822278083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3352839712978737096370777 2514629784734052822278083)
                      ·
                        rfl

theorem cell23_4897224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 2, 2, 3, 2, 2].length) (baseStart_4897224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4897224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4897224 prefixEnd_4897224 := by exact prefixLift 4897224
  have htrace : WordTrace (prefixWord ++ tailWord_4897224) baseStart_4897224 baseEnd_4897224 := by
    simpa [prefixWord, tailWord_4897224, baseEnd_4897224] using wordTrace_append hprefix tailTrace_4897224
  have hstable : (prefixWord ++ tailWord_4897224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4897224).length < 2 ^ (prefixWord ++ tailWord_4897224).sum := by decide
  have hdescent : baseEnd_4897224 < baseStart_4897224 := by decide
  rcases family_descends (prefixWord ++ tailWord_4897224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4897233 : List Nat := [1, 2, 2, 1, 2, 1, 1, 2, 1, 4, 6]
def baseStart_4897233 : Nat := 118140960795 + 4897233 * 2 ^ 59
def prefixEnd_4897233 : Nat := 4983230072969 + 3 ^ 40 * 4897233 * 2
def baseEnd_4897233 : Nat := 2514634406059943287065541

theorem tailTrace_4897233 : CollatzResearch.WordTrace tailWord_4897233 prefixEnd_4897233 2514634406059943287065541 := by
  unfold tailWord_4897233
  simp only [CollatzResearch.WordTrace]
  refine ⟨178616761467168696653832353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119077840978112464435888235 178616761467168696653832353)
  ·
    refine ⟨133962571100376522490374265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 178616761467168696653832353 133962571100376522490374265)
    ·
      refine ⟨100471928325282391867780699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 133962571100376522490374265 100471928325282391867780699)
      ·
        refine ⟨150707892487923587801671049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100471928325282391867780699 150707892487923587801671049)
        ·
          refine ⟨113030919365942690851253287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 150707892487923587801671049 113030919365942690851253287)
          ·
            refine ⟨169546379048914036276879931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 113030919365942690851253287 169546379048914036276879931)
            ·
              refine ⟨254319568573371054415319897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 169546379048914036276879931 254319568573371054415319897)
              ·
                refine ⟨190739676430028290811489923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 254319568573371054415319897 190739676430028290811489923)
                ·
                  refine ⟨286109514645042436217234885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 190739676430028290811489923 286109514645042436217234885)
                  ·
                    refine ⟨53645533995945456790731541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 286109514645042436217234885 53645533995945456790731541)
                    ·
                      refine ⟨2514634406059943287065541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 53645533995945456790731541 2514634406059943287065541)
                      ·
                        rfl

theorem cell23_4897233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 4, 6].length) (baseStart_4897233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4897233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4897233 prefixEnd_4897233 := by exact prefixLift 4897233
  have htrace : WordTrace (prefixWord ++ tailWord_4897233) baseStart_4897233 baseEnd_4897233 := by
    simpa [prefixWord, tailWord_4897233, baseEnd_4897233] using wordTrace_append hprefix tailTrace_4897233
  have hstable : (prefixWord ++ tailWord_4897233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4897233).length < 2 ^ (prefixWord ++ tailWord_4897233).sum := by decide
  have hdescent : baseEnd_4897233 < baseStart_4897233 := by decide
  rcases family_descends (prefixWord ++ tailWord_4897233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4897240 : List Nat := [2, 1, 2, 2, 2, 1, 1, 3, 3, 3, 3]
def baseStart_4897240 : Nat := 118140960795 + 4897240 * 2 ^ 59
def prefixEnd_4897240 : Nat := 4983230072969 + 3 ^ 40 * 4897240 * 2
def baseEnd_4897240 : Nat := 2514638000424524759678009

theorem tailTrace_4897240 : CollatzResearch.WordTrace tailWord_4897240 prefixEnd_4897240 2514638000424524759678009 := by
  unfold tailWord_4897240
  simp only [CollatzResearch.WordTrace]
  refine ⟨89308508389071668424668587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119078011185428891232891449 89308508389071668424668587)
  ·
    refine ⟨133962762583607502637002881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89308508389071668424668587 133962762583607502637002881)
    ·
      refine ⟨100472071937705626977752161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 133962762583607502637002881 100472071937705626977752161)
      ·
        refine ⟨75354053953279220233314121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 100472071937705626977752161 75354053953279220233314121)
        ·
          refine ⟨56515540464959415174985591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 75354053953279220233314121 56515540464959415174985591)
          ·
            refine ⟨84773310697439122762478387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56515540464959415174985591 84773310697439122762478387)
            ·
              refine ⟨127159966046158684143717581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 84773310697439122762478387 127159966046158684143717581)
              ·
                refine ⟨47684987267309506553894093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 127159966046158684143717581 47684987267309506553894093)
                ·
                  refine ⟨17881870225241064957710285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 47684987267309506553894093 17881870225241064957710285)
                  ·
                    refine ⟨6705701334465399359141357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17881870225241064957710285 6705701334465399359141357)
                    ·
                      refine ⟨2514638000424524759678009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6705701334465399359141357 2514638000424524759678009)
                      ·
                        rfl

theorem cell23_4897240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 3, 3, 3, 3].length) (baseStart_4897240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4897240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4897240 prefixEnd_4897240 := by exact prefixLift 4897240
  have htrace : WordTrace (prefixWord ++ tailWord_4897240) baseStart_4897240 baseEnd_4897240 := by
    simpa [prefixWord, tailWord_4897240, baseEnd_4897240] using wordTrace_append hprefix tailTrace_4897240
  have hstable : (prefixWord ++ tailWord_4897240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4897240).length < 2 ^ (prefixWord ++ tailWord_4897240).sum := by decide
  have hdescent : baseEnd_4897240 < baseStart_4897240 := by decide
  rcases family_descends (prefixWord ++ tailWord_4897240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4897267 : List Nat := [1, 1, 1, 2, 2, 2, 4, 2, 3, 3, 2]
def baseStart_4897267 : Nat := 118140960795 + 4897267 * 2 ^ 59
def prefixEnd_4897267 : Nat := 4983230072969 + 3 ^ 40 * 4897267 * 2
def baseEnd_4897267 : Nat := 2514651864402196154040385

theorem tailTrace_4897267 : CollatzResearch.WordTrace tailWord_4897267 prefixEnd_4897267 2514651864402196154040385 := by
  unfold tailWord_4897267
  simp only [CollatzResearch.WordTrace]
  refine ⟨178618001549045520460570055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119078667699363680307046703 178618001549045520460570055)
  ·
    refine ⟨267927002323568280690855083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 178618001549045520460570055 267927002323568280690855083)
    ·
      refine ⟨401890503485352421036282625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 267927002323568280690855083 401890503485352421036282625)
      ·
        refine ⟨301417877614014315777211969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 401890503485352421036282625 301417877614014315777211969)
        ·
          refine ⟨226063408210510736832908977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 301417877614014315777211969 226063408210510736832908977)
          ·
            refine ⟨169547556157883052624681733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 226063408210510736832908977 169547556157883052624681733)
            ·
              refine ⟨31790166779603072367127825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 169547556157883052624681733 31790166779603072367127825)
              ·
                refine ⟨23842625084702304275345869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31790166779603072367127825 23842625084702304275345869)
                ·
                  refine ⟨8940984406763364103254701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23842625084702304275345869 8940984406763364103254701)
                  ·
                    refine ⟨3352869152536261538720513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8940984406763364103254701 3352869152536261538720513)
                    ·
                      refine ⟨2514651864402196154040385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3352869152536261538720513 2514651864402196154040385)
                      ·
                        rfl

theorem cell23_4897267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 4, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 4, 2, 3, 3, 2].length) (baseStart_4897267 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4897267 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4897267 prefixEnd_4897267 := by exact prefixLift 4897267
  have htrace : WordTrace (prefixWord ++ tailWord_4897267) baseStart_4897267 baseEnd_4897267 := by
    simpa [prefixWord, tailWord_4897267, baseEnd_4897267] using wordTrace_append hprefix tailTrace_4897267
  have hstable : (prefixWord ++ tailWord_4897267).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4897267).length < 2 ^ (prefixWord ++ tailWord_4897267).sum := by decide
  have hdescent : baseEnd_4897267 < baseStart_4897267 := by decide
  rcases family_descends (prefixWord ++ tailWord_4897267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4897301 : List Nat := [1, 3, 2, 1, 3, 1, 5, 1, 1, 3, 2]
def baseStart_4897301 : Nat := 118140960795 + 4897301 * 2 ^ 59
def prefixEnd_4897301 : Nat := 4983230072969 + 3 ^ 40 * 4897301 * 2
def baseEnd_4897301 : Nat := 2514669322744449021015229

theorem tailTrace_4897301 : CollatzResearch.WordTrace tailWord_4897301 prefixEnd_4897301 2514669322744449021015229 := by
  unfold tailWord_4897301
  simp only [CollatzResearch.WordTrace]
  refine ⟨178619241630922344267307757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119079494420614896178205171 178619241630922344267307757)
  ·
    refine ⟨66982215611595879100240409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 178619241630922344267307757 66982215611595879100240409)
    ·
      refine ⟨50236661708696909325180307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66982215611595879100240409 50236661708696909325180307)
      ·
        refine ⟨75354992563045363987770461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50236661708696909325180307 75354992563045363987770461)
        ·
          refine ⟨28258122211142011495413923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 75354992563045363987770461 28258122211142011495413923)
          ·
            refine ⟨42387183316713017243120885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28258122211142011495413923 42387183316713017243120885)
            ·
              refine ⟨3973798435941845366542583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 42387183316713017243120885 3973798435941845366542583)
              ·
                refine ⟨5960697653912768049813875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3973798435941845366542583 5960697653912768049813875)
                ·
                  refine ⟨8941046480869152074720813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5960697653912768049813875 8941046480869152074720813)
                  ·
                    refine ⟨3352892430325932028020305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8941046480869152074720813 3352892430325932028020305)
                    ·
                      refine ⟨2514669322744449021015229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3352892430325932028020305 2514669322744449021015229)
                      ·
                        rfl

theorem cell23_4897301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 5, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 5, 1, 1, 3, 2].length) (baseStart_4897301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4897301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4897301 prefixEnd_4897301 := by exact prefixLift 4897301
  have htrace : WordTrace (prefixWord ++ tailWord_4897301) baseStart_4897301 baseEnd_4897301 := by
    simpa [prefixWord, tailWord_4897301, baseEnd_4897301] using wordTrace_append hprefix tailTrace_4897301
  have hstable : (prefixWord ++ tailWord_4897301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4897301).length < 2 ^ (prefixWord ++ tailWord_4897301).sum := by decide
  have hdescent : baseEnd_4897301 < baseStart_4897301 := by decide
  rcases family_descends (prefixWord ++ tailWord_4897301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4897354 : List Nat := [3, 1, 2, 1, 1, 5, 2, 3, 5]
def baseStart_4897354 : Nat := 118140960795 + 4897354 * 2 ^ 59
def prefixEnd_4897354 : Nat := 4983230072969 + 3 ^ 40 * 4897354 * 2
def baseEnd_4897354 : Nat := 279410726357681923739165

theorem tailTrace_4897354 : CollatzResearch.WordTrace tailWord_4897354 prefixEnd_4897354 279410726357681923739165 := by
  unfold tailWord_4897354
  simp only [CollatzResearch.WordTrace]
  refine ⟨44655293674932583579746779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 119080783133153556212658077 44655293674932583579746779)
  ·
    refine ⟨66982940512398875369620169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44655293674932583579746779 66982940512398875369620169)
    ·
      refine ⟨50237205384299156527215127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66982940512398875369620169 50237205384299156527215127)
      ·
        refine ⟨75355808076448734790822691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50237205384299156527215127 75355808076448734790822691)
        ·
          refine ⟨113033712114673102186234037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75355808076448734790822691 113033712114673102186234037)
          ·
            refine ⟨10596910510750603329959441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 113033712114673102186234037 10596910510750603329959441)
            ·
              refine ⟨7947682883062952497469581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10596910510750603329959441 7947682883062952497469581)
              ·
                refine ⟨2980381081148607186551093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7947682883062952497469581 2980381081148607186551093)
                ·
                  refine ⟨279410726357681923739165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2980381081148607186551093 279410726357681923739165)
                  ·
                    rfl

theorem cell23_4897354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 5, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 5, 2, 3, 5].length) (baseStart_4897354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4897354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4897354 prefixEnd_4897354 := by exact prefixLift 4897354
  have htrace : WordTrace (prefixWord ++ tailWord_4897354) baseStart_4897354 baseEnd_4897354 := by
    simpa [prefixWord, tailWord_4897354, baseEnd_4897354] using wordTrace_append hprefix tailTrace_4897354
  have hstable : (prefixWord ++ tailWord_4897354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4897354).length < 2 ^ (prefixWord ++ tailWord_4897354).sum := by decide
  have hdescent : baseEnd_4897354 < baseStart_4897354 := by decide
  rcases family_descends (prefixWord ++ tailWord_4897354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4897360 : List Nat := [2, 1, 1, 1, 1, 3, 2, 4, 1, 2, 5]
def baseStart_4897360 : Nat := 118140960795 + 4897360 * 2 ^ 59
def prefixEnd_4897360 : Nat := 4983230072969 + 3 ^ 40 * 4897360 * 2
def baseEnd_4897360 : Nat := 2514699618103064290177457

theorem tailTrace_4897360 : CollatzResearch.WordTrace tailWord_4897360 prefixEnd_4897360 2514699618103064290177457 := by
  unfold tailWord_4897360
  simp only [CollatzResearch.WordTrace]
  refine ⟨89310696768854298671852767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119080929025139064895803689 89310696768854298671852767)
  ·
    refine ⟨133966045153281448007779151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89310696768854298671852767 133966045153281448007779151)
    ·
      refine ⟨200949067729922172011668727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 133966045153281448007779151 200949067729922172011668727)
      ·
        refine ⟨301423601594883258017503091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 200949067729922172011668727 301423601594883258017503091)
        ·
          refine ⟨452135402392324887026254637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 301423601594883258017503091 452135402392324887026254637)
          ·
            refine ⟨169550775897121832634845489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 452135402392324887026254637 169550775897121832634845489)
            ·
              refine ⟨127163081922841374476134117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 169550775897121832634845489 127163081922841374476134117)
              ·
                refine ⟨23843077860532757714275147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 127163081922841374476134117 23843077860532757714275147)
                ·
                  refine ⟨35764616790799136571412721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23843077860532757714275147 35764616790799136571412721)
                  ·
                    refine ⟨26823462593099352428559541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 35764616790799136571412721 26823462593099352428559541)
                    ·
                      refine ⟨2514699618103064290177457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26823462593099352428559541 2514699618103064290177457)
                      ·
                        rfl

theorem cell23_4897360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 4, 1, 2, 5].length) (baseStart_4897360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4897360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4897360 prefixEnd_4897360 := by exact prefixLift 4897360
  have htrace : WordTrace (prefixWord ++ tailWord_4897360) baseStart_4897360 baseEnd_4897360 := by
    simpa [prefixWord, tailWord_4897360, baseEnd_4897360] using wordTrace_append hprefix tailTrace_4897360
  have hstable : (prefixWord ++ tailWord_4897360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4897360).length < 2 ^ (prefixWord ++ tailWord_4897360).sum := by decide
  have hdescent : baseEnd_4897360 < baseStart_4897360 := by decide
  rcases family_descends (prefixWord ++ tailWord_4897360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4897387 : List Nat := [1, 1, 1, 1, 2, 2, 1, 5, 1, 6, 2]
def baseStart_4897387 : Nat := 118140960795 + 4897387 * 2 ^ 59
def prefixEnd_4897387 : Nat := 4983230072969 + 3 ^ 40 * 4897387 * 2
def baseEnd_4897387 : Nat := 2514713482080735684539833

theorem tailTrace_4897387 : CollatzResearch.WordTrace tailWord_4897387 prefixEnd_4897387 2514713482080735684539833 := by
  unfold tailWord_4897387
  simp only [CollatzResearch.WordTrace]
  refine ⟨178622378308610780954938415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119081585539073853969958943 178622378308610780954938415)
  ·
    refine ⟨267933567462916171432407623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 178622378308610780954938415 267933567462916171432407623)
    ·
      refine ⟨401900351194374257148611435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 267933567462916171432407623 401900351194374257148611435)
      ·
        refine ⟨602850526791561385722917153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 401900351194374257148611435 602850526791561385722917153)
        ·
          refine ⟨452137895093671039292187865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 602850526791561385722917153 452137895093671039292187865)
          ·
            refine ⟨339103421320253279469140899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 452137895093671039292187865 339103421320253279469140899)
            ·
              refine ⟨508655131980379919203711349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 339103421320253279469140899 508655131980379919203711349)
              ·
                refine ⟨47686418623160617425347939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 508655131980379919203711349 47686418623160617425347939)
                ·
                  refine ⟨71529627934740926138021909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 47686418623160617425347939 71529627934740926138021909)
                  ·
                    refine ⟨3352951309440980912719777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 71529627934740926138021909 3352951309440980912719777)
                    ·
                      refine ⟨2514713482080735684539833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3352951309440980912719777 2514713482080735684539833)
                      ·
                        rfl

theorem cell23_4897387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 5, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 5, 1, 6, 2].length) (baseStart_4897387 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4897387 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4897387 prefixEnd_4897387 := by exact prefixLift 4897387
  have htrace : WordTrace (prefixWord ++ tailWord_4897387) baseStart_4897387 baseEnd_4897387 := by
    simpa [prefixWord, tailWord_4897387, baseEnd_4897387] using wordTrace_append hprefix tailTrace_4897387
  have hstable : (prefixWord ++ tailWord_4897387).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4897387).length < 2 ^ (prefixWord ++ tailWord_4897387).sum := by decide
  have hdescent : baseEnd_4897387 < baseStart_4897387 := by decide
  rcases family_descends (prefixWord ++ tailWord_4897387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4897400 : List Nat := [2, 1, 2, 1, 1, 1, 2, 2, 4, 1, 6]
def baseStart_4897400 : Nat := 118140960795 + 4897400 * 2 ^ 59
def prefixEnd_4897400 : Nat := 4983230072969 + 3 ^ 40 * 4897400 * 2
def baseEnd_4897400 : Nat := 2514720157329244133677273

theorem tailTrace_4897400 : CollatzResearch.WordTrace tailWord_4897400 prefixEnd_4897400 2514720157329244133677273 := by
  unfold tailWord_4897400
  simp only [CollatzResearch.WordTrace]
  refine ⟨89311426228781842087580827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119081901638375789450107769 89311426228781842087580827)
  ·
    refine ⟨133967139343172763131371241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89311426228781842087580827 133967139343172763131371241)
    ·
      refine ⟨100475354507379572348528431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 133967139343172763131371241 100475354507379572348528431)
      ·
        refine ⟨150713031761069358522792647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100475354507379572348528431 150713031761069358522792647)
        ·
          refine ⟨226069547641604037784188971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 150713031761069358522792647 226069547641604037784188971)
          ·
            refine ⟨339104321462406056676283457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 226069547641604037784188971 339104321462406056676283457)
            ·
              refine ⟨254328241096804542507212593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 339104321462406056676283457 254328241096804542507212593)
              ·
                refine ⟨190746180822603406880409445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 254328241096804542507212593 190746180822603406880409445)
                ·
                  refine ⟨35764908904238138790076771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 190746180822603406880409445 35764908904238138790076771)
                  ·
                    refine ⟨53647363356357208185115157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 35764908904238138790076771 53647363356357208185115157)
                    ·
                      refine ⟨2514720157329244133677273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 53647363356357208185115157 2514720157329244133677273)
                      ·
                        rfl

theorem cell23_4897400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 2, 4, 1, 6].length) (baseStart_4897400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4897400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4897400 prefixEnd_4897400 := by exact prefixLift 4897400
  have htrace : WordTrace (prefixWord ++ tailWord_4897400) baseStart_4897400 baseEnd_4897400 := by
    simpa [prefixWord, tailWord_4897400, baseEnd_4897400] using wordTrace_append hprefix tailTrace_4897400
  have hstable : (prefixWord ++ tailWord_4897400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4897400).length < 2 ^ (prefixWord ++ tailWord_4897400).sum := by decide
  have hdescent : baseEnd_4897400 < baseStart_4897400 := by decide
  rcases family_descends (prefixWord ++ tailWord_4897400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4897477 : List Nat := [1, 3, 1, 1, 1, 1, 2, 1, 7, 1, 4]
def baseStart_4897477 : Nat := 118140960795 + 4897477 * 2 ^ 59
def prefixEnd_4897477 : Nat := 4983230072969 + 3 ^ 40 * 4897477 * 2
def baseEnd_4897477 : Nat := 2514759695339640332414419

theorem tailTrace_4897477 : CollatzResearch.WordTrace tailWord_4897477 prefixEnd_4897477 2514759695339640332414419 := by
  unfold tailWord_4897477
  simp only [CollatzResearch.WordTrace]
  refine ⟨178625660878284726325714685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119083773918856484217143123 178625660878284726325714685)
  ·
    refine ⟨66984622829356772372143007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 178625660878284726325714685 66984622829356772372143007)
    ·
      refine ⟨100476934244035158558214511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66984622829356772372143007 100476934244035158558214511)
      ·
        refine ⟨150715401366052737837321767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100476934244035158558214511 150715401366052737837321767)
        ·
          refine ⟨226073102049079106755982651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 150715401366052737837321767 226073102049079106755982651)
          ·
            refine ⟨339109653073618660133973977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 226073102049079106755982651 339109653073618660133973977)
            ·
              refine ⟨254332239805213995100480483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 339109653073618660133973977 254332239805213995100480483)
              ·
                refine ⟨381498359707820992650720725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 254332239805213995100480483 381498359707820992650720725)
                ·
                  refine ⟨8941367805652054515251267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 381498359707820992650720725 8941367805652054515251267)
                  ·
                    refine ⟨13412051708478081772876901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8941367805652054515251267 13412051708478081772876901)
                    ·
                      refine ⟨2514759695339640332414419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13412051708478081772876901 2514759695339640332414419)
                      ·
                        rfl

theorem cell23_4897477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 1, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 1, 7, 1, 4].length) (baseStart_4897477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4897477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4897477 prefixEnd_4897477 := by exact prefixLift 4897477
  have htrace : WordTrace (prefixWord ++ tailWord_4897477) baseStart_4897477 baseEnd_4897477 := by
    simpa [prefixWord, tailWord_4897477, baseEnd_4897477] using wordTrace_append hprefix tailTrace_4897477
  have hstable : (prefixWord ++ tailWord_4897477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4897477).length < 2 ^ (prefixWord ++ tailWord_4897477).sum := by decide
  have hdescent : baseEnd_4897477 < baseStart_4897477 := by decide
  rcases family_descends (prefixWord ++ tailWord_4897477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4897497 : List Nat := [1, 2, 1, 2, 3, 2, 2, 1, 3, 1, 5]
def baseStart_4897497 : Nat := 118140960795 + 4897497 * 2 ^ 59
def prefixEnd_4897497 : Nat := 4983230072969 + 3 ^ 40 * 4897497 * 2
def baseEnd_4897497 : Nat := 2514769964952730254164327

theorem tailTrace_4897497 : CollatzResearch.WordTrace tailWord_4897497 prefixEnd_4897497 2514769964952730254164327 := by
  unfold tailWord_4897497
  simp only [CollatzResearch.WordTrace]
  refine ⟨178626390338212269741442745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119084260225474846494295163 178626390338212269741442745)
  ·
    refine ⟨133969792753659202306082059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 178626390338212269741442745 133969792753659202306082059)
    ·
      refine ⟨200954689130488803459123089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 133969792753659202306082059 200954689130488803459123089)
      ·
        refine ⟨150716016847866602594342317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 200954689130488803459123089 150716016847866602594342317)
        ·
          refine ⟨56518506317949975972878369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 150716016847866602594342317 56518506317949975972878369)
          ·
            refine ⟨42388879738462481979658777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56518506317949975972878369 42388879738462481979658777)
            ·
              refine ⟨31791659803846861484744083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42388879738462481979658777 31791659803846861484744083)
              ·
                refine ⟨47687489705770292227116125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31791659803846861484744083 47687489705770292227116125)
                ·
                  refine ⟨17882808639663859585168547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 47687489705770292227116125 17882808639663859585168547)
                  ·
                    refine ⟨26824212959495789377752821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17882808639663859585168547 26824212959495789377752821)
                    ·
                      refine ⟨2514769964952730254164327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26824212959495789377752821 2514769964952730254164327)
                      ·
                        rfl

theorem cell23_4897497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 2, 1, 3, 1, 5].length) (baseStart_4897497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4897497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4897497 prefixEnd_4897497 := by exact prefixLift 4897497
  have htrace : WordTrace (prefixWord ++ tailWord_4897497) baseStart_4897497 baseEnd_4897497 := by
    simpa [prefixWord, tailWord_4897497, baseEnd_4897497] using wordTrace_append hprefix tailTrace_4897497
  have hstable : (prefixWord ++ tailWord_4897497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4897497).length < 2 ^ (prefixWord ++ tailWord_4897497).sum := by decide
  have hdescent : baseEnd_4897497 < baseStart_4897497 := by decide
  rcases family_descends (prefixWord ++ tailWord_4897497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4897525 : List Nat := [1, 3, 6, 1, 1, 1, 1, 3, 1, 5]
def baseStart_4897525 : Nat := 118140960795 + 4897525 * 2 ^ 59
def prefixEnd_4897525 : Nat := 4983230072969 + 3 ^ 40 * 4897525 * 2
def baseEnd_4897525 : Nat := 838261447470352048204733

theorem tailTrace_4897525 : CollatzResearch.WordTrace tailWord_4897525 prefixEnd_4897525 838261447470352048204733 := by
  unfold tailWord_4897525
  simp only [CollatzResearch.WordTrace]
  refine ⟨178627411582110830523462029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119084941054740553682308019 178627411582110830523462029)
  ·
    refine ⟨66985279343291561446298261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 178627411582110830523462029 66985279343291561446298261)
    ·
      refine ⟨3139934969216791942795231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 66985279343291561446298261 3139934969216791942795231)
      ·
        refine ⟨4709902453825187914192847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3139934969216791942795231 4709902453825187914192847)
        ·
          refine ⟨7064853680737781871289271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4709902453825187914192847 7064853680737781871289271)
          ·
            refine ⟨10597280521106672806933907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7064853680737781871289271 10597280521106672806933907)
            ·
              refine ⟨15895920781660009210400861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10597280521106672806933907 15895920781660009210400861)
              ·
                refine ⟨5960970293122503453900323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15895920781660009210400861 5960970293122503453900323)
                ·
                  refine ⟨8941455439683755180850485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5960970293122503453900323 8941455439683755180850485)
                  ·
                    refine ⟨838261447470352048204733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8941455439683755180850485 838261447470352048204733)
                    ·
                      rfl

theorem cell23_4897525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 1, 1, 3, 1, 5].length) (baseStart_4897525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4897525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4897525 prefixEnd_4897525 := by exact prefixLift 4897525
  have htrace : WordTrace (prefixWord ++ tailWord_4897525) baseStart_4897525 baseEnd_4897525 := by
    simpa [prefixWord, tailWord_4897525, baseEnd_4897525] using wordTrace_append hprefix tailTrace_4897525
  have hstable : (prefixWord ++ tailWord_4897525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4897525).length < 2 ^ (prefixWord ++ tailWord_4897525).sum := by decide
  have hdescent : baseEnd_4897525 < baseStart_4897525 := by decide
  rcases family_descends (prefixWord ++ tailWord_4897525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4897534 : List Nat := [4, 2, 2, 1, 2, 2, 10]
def baseStart_4897534 : Nat := 118140960795 + 4897534 * 2 ^ 59
def prefixEnd_4897534 : Nat := 4983230072969 + 3 ^ 40 * 4897534 * 2
def baseEnd_4897534 : Nat := 31046777330085760609897

theorem tailTrace_4897534 : CollatzResearch.WordTrace tailWord_4897534 prefixEnd_4897534 31046777330085760609897 := by
  unfold tailWord_4897534
  simp only [CollatzResearch.WordTrace]
  refine ⟨22328467479884778132567457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 119085159892718816707026437 22328467479884778132567457)
  ·
    refine ⟨16746350609913583599425593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22328467479884778132567457 16746350609913583599425593)
    ·
      refine ⟨12559762957435187699569195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16746350609913583599425593 12559762957435187699569195)
      ·
        refine ⟨18839644436152781549353793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12559762957435187699569195 18839644436152781549353793)
        ·
          refine ⟨14129733327114586162015345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18839644436152781549353793 14129733327114586162015345)
          ·
            refine ⟨10597299995335939621511509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14129733327114586162015345 10597299995335939621511509)
            ·
              refine ⟨31046777330085760609897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 10597299995335939621511509 31046777330085760609897)
              ·
                rfl

theorem cell23_4897534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 2, 10].length) (baseStart_4897534 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4897534 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4897534 prefixEnd_4897534 := by exact prefixLift 4897534
  have htrace : WordTrace (prefixWord ++ tailWord_4897534) baseStart_4897534 baseEnd_4897534 := by
    simpa [prefixWord, tailWord_4897534, baseEnd_4897534] using wordTrace_append hprefix tailTrace_4897534
  have hstable : (prefixWord ++ tailWord_4897534).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4897534).length < 2 ^ (prefixWord ++ tailWord_4897534).sum := by decide
  have hdescent : baseEnd_4897534 < baseStart_4897534 := by decide
  rcases family_descends (prefixWord ++ tailWord_4897534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4897537 : List Nat := [1, 2, 4, 1, 1, 1, 1, 2, 2, 2, 6]
def baseStart_4897537 : Nat := 118140960795 + 4897537 * 2 ^ 59
def prefixEnd_4897537 : Nat := 4983230072969 + 3 ^ 40 * 4897537 * 2
def baseEnd_4897537 : Nat := 2514790504178910097664143

theorem tailTrace_4897537 : CollatzResearch.WordTrace tailWord_4897537 prefixEnd_4897537 2514790504178910097664143 := by
  unfold tailWord_4897537
  simp only [CollatzResearch.WordTrace]
  refine ⟨178627849258067356572898865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119085232838711571048599243 178627849258067356572898865)
  ·
    refine ⟨133970886943550517429674149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 178627849258067356572898865 133970886943550517429674149)
    ·
      refine ⟨25119541301915722018063903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 133970886943550517429674149 25119541301915722018063903)
      ·
        refine ⟨37679311952873583027095855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25119541301915722018063903 37679311952873583027095855)
        ·
          refine ⟨56518967929310374540643783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37679311952873583027095855 56518967929310374540643783)
          ·
            refine ⟨84778451893965561810965675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56518967929310374540643783 84778451893965561810965675)
            ·
              refine ⟨127167677840948342716448513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 84778451893965561810965675 127167677840948342716448513)
              ·
                refine ⟨95375758380711257037336385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 127167677840948342716448513 95375758380711257037336385)
                ·
                  refine ⟨71531818785533442778002289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 95375758380711257037336385 71531818785533442778002289)
                  ·
                    refine ⟨53648864089150082083501717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 71531818785533442778002289 53648864089150082083501717)
                    ·
                      refine ⟨2514790504178910097664143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 53648864089150082083501717 2514790504178910097664143)
                      ·
                        rfl

theorem cell23_4897537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 2, 2, 2, 6].length) (baseStart_4897537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4897537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4897537 prefixEnd_4897537 := by exact prefixLift 4897537
  have htrace : WordTrace (prefixWord ++ tailWord_4897537) baseStart_4897537 baseEnd_4897537 := by
    simpa [prefixWord, tailWord_4897537, baseEnd_4897537] using wordTrace_append hprefix tailTrace_4897537
  have hstable : (prefixWord ++ tailWord_4897537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4897537).length < 2 ^ (prefixWord ++ tailWord_4897537).sum := by decide
  have hdescent : baseEnd_4897537 < baseStart_4897537 := by decide
  rcases family_descends (prefixWord ++ tailWord_4897537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4897538 : List Nat := [3, 4, 1, 1, 1, 2, 3, 2, 2, 4]
def baseStart_4897538 : Nat := 118140960795 + 4897538 * 2 ^ 59
def prefixEnd_4897538 : Nat := 4983230072969 + 3 ^ 40 * 4897538 * 2
def baseEnd_4897538 : Nat := 838263672553188197917213

theorem tailTrace_4897538 : CollatzResearch.WordTrace tailWord_4897538 prefixEnd_4897538 838263672553188197917213 := by
  unfold tailWord_4897538
  simp only [CollatzResearch.WordTrace]
  refine ⟨44656971432765933435921317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 119085257154042489162456845 44656971432765933435921317)
  ·
    refine ⟨8373182143643612519235247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 44656971432765933435921317 8373182143643612519235247)
    ·
      refine ⟨12559773215465418778852871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8373182143643612519235247 12559773215465418778852871)
      ·
        refine ⟨18839659823198128168279307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12559773215465418778852871 18839659823198128168279307)
        ·
          refine ⟨28259489734797192252418961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18839659823198128168279307 28259489734797192252418961)
          ·
            refine ⟨21194617301097894189314221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28259489734797192252418961 21194617301097894189314221)
            ·
              refine ⟨7947981487911710320992833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21194617301097894189314221 7947981487911710320992833)
              ·
                refine ⟨5960986115933782740744625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7947981487911710320992833 5960986115933782740744625)
                ·
                  refine ⟨4470739586950337055558469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5960986115933782740744625 4470739586950337055558469)
                  ·
                    refine ⟨838263672553188197917213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4470739586950337055558469 838263672553188197917213)
                    ·
                      rfl

theorem cell23_4897538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 3, 2, 2, 4].length) (baseStart_4897538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4897538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4897538 prefixEnd_4897538 := by exact prefixLift 4897538
  have htrace : WordTrace (prefixWord ++ tailWord_4897538) baseStart_4897538 baseEnd_4897538 := by
    simpa [prefixWord, tailWord_4897538, baseEnd_4897538] using wordTrace_append hprefix tailTrace_4897538
  have hstable : (prefixWord ++ tailWord_4897538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4897538).length < 2 ^ (prefixWord ++ tailWord_4897538).sum := by decide
  have hdescent : baseEnd_4897538 < baseStart_4897538 := by decide
  rcases family_descends (prefixWord ++ tailWord_4897538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4897565 : List Nat := [1, 4, 2, 4, 1, 1, 2, 2, 1, 2, 3]
def baseStart_4897565 : Nat := 118140960795 + 4897565 * 2 ^ 59
def prefixEnd_4897565 : Nat := 4983230072969 + 3 ^ 40 * 4897565 * 2
def baseEnd_4897565 : Nat := 2514804881637235988114015

theorem tailTrace_4897565 : CollatzResearch.WordTrace tailWord_4897565 prefixEnd_4897565 2514804881637235988114015 := by
  unfold tailWord_4897565
  simp only [CollatzResearch.WordTrace]
  refine ⟨178628870501965917354918149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119085913667977278236612099 178628870501965917354918149)
  ·
    refine ⟨33492913219118609504047153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 178628870501965917354918149 33492913219118609504047153)
    ·
      refine ⟨25119684914338957128035365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33492913219118609504047153 25119684914338957128035365)
      ·
        refine ⟨4709940921438554461506631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 25119684914338957128035365 4709940921438554461506631)
        ·
          refine ⟨7064911382157831692259947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4709940921438554461506631 7064911382157831692259947)
          ·
            refine ⟨10597367073236747538389921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7064911382157831692259947 10597367073236747538389921)
            ·
              refine ⟨7948025304927560653792441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10597367073236747538389921 7948025304927560653792441)
              ·
                refine ⟨5961018978695670490344331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7948025304927560653792441 5961018978695670490344331)
                ·
                  refine ⟨8941528468043505735516497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5961018978695670490344331 8941528468043505735516497)
                  ·
                    refine ⟨6706146351032629301637373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8941528468043505735516497 6706146351032629301637373)
                    ·
                      refine ⟨2514804881637235988114015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6706146351032629301637373 2514804881637235988114015)
                      ·
                        rfl

theorem cell23_4897565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 1, 2, 2, 1, 2, 3].length) (baseStart_4897565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4897565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4897565 prefixEnd_4897565 := by exact prefixLift 4897565
  have htrace : WordTrace (prefixWord ++ tailWord_4897565) baseStart_4897565 baseEnd_4897565 := by
    simpa [prefixWord, tailWord_4897565, baseEnd_4897565] using wordTrace_append hprefix tailTrace_4897565
  have hstable : (prefixWord ++ tailWord_4897565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4897565).length < 2 ^ (prefixWord ++ tailWord_4897565).sum := by decide
  have hdescent : baseEnd_4897565 < baseStart_4897565 := by decide
  rcases family_descends (prefixWord ++ tailWord_4897565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4897614 : List Nat := [4, 1, 1, 1, 1, 1, 1, 5, 2, 2, 4]
def baseStart_4897614 : Nat := 118140960795 + 4897614 * 2 ^ 59
def prefixEnd_4897614 : Nat := 4983230072969 + 3 ^ 40 * 4897614 * 2
def baseEnd_4897614 : Nat := 2514830042189306296401289

theorem tailTrace_4897614 : CollatzResearch.WordTrace tailWord_4897614 prefixEnd_4897614 2514830042189306296401289 := by
  unfold tailWord_4897614
  simp only [CollatzResearch.WordTrace]
  refine ⟨22328832209848549840431487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 119087105119192265815634597 22328832209848549840431487)
  ·
    refine ⟨33493248314772824760647231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22328832209848549840431487 33493248314772824760647231)
    ·
      refine ⟨50239872472159237140970847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33493248314772824760647231 50239872472159237140970847)
      ·
        refine ⟨75359808708238855711456271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50239872472159237140970847 75359808708238855711456271)
        ·
          refine ⟨113039713062358283567184407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75359808708238855711456271 113039713062358283567184407)
          ·
            refine ⟨169559569593537425350776611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 113039713062358283567184407 169559569593537425350776611)
            ·
              refine ⟨254339354390306138026164917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 169559569593537425350776611 254339354390306138026164917)
              ·
                refine ⟨23844314474091200439952961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 254339354390306138026164917 23844314474091200439952961)
                ·
                  refine ⟨17883235855568400329964721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23844314474091200439952961 17883235855568400329964721)
                  ·
                    refine ⟨13412426891676300247473541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17883235855568400329964721 13412426891676300247473541)
                    ·
                      refine ⟨2514830042189306296401289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13412426891676300247473541 2514830042189306296401289)
                      ·
                        rfl

theorem cell23_4897614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 5, 2, 2, 4].length) (baseStart_4897614 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4897614 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4897614 prefixEnd_4897614 := by exact prefixLift 4897614
  have htrace : WordTrace (prefixWord ++ tailWord_4897614) baseStart_4897614 baseEnd_4897614 := by
    simpa [prefixWord, tailWord_4897614, baseEnd_4897614] using wordTrace_append hprefix tailTrace_4897614
  have hstable : (prefixWord ++ tailWord_4897614).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4897614).length < 2 ^ (prefixWord ++ tailWord_4897614).sum := by decide
  have hdescent : baseEnd_4897614 < baseStart_4897614 := by decide
  rcases family_descends (prefixWord ++ tailWord_4897614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4897661 : List Nat := [1, 4, 1, 1, 2, 1, 3, 1, 2, 5, 2]
def baseStart_4897661 : Nat := 118140960795 + 4897661 * 2 ^ 59
def prefixEnd_4897661 : Nat := 4983230072969 + 3 ^ 40 * 4897661 * 2
def baseEnd_4897661 : Nat := 2514854175780067612513573

theorem tailTrace_4897661 : CollatzResearch.WordTrace tailWord_4897661 prefixEnd_4897661 2514854175780067612513573 := by
  unfold tailWord_4897661
  simp only [CollatzResearch.WordTrace]
  refine ⟨178632371909618125750412837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119088247939745417166941891 178632371909618125750412837)
  ·
    refine ⟨33493569733053398578202407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 178632371909618125750412837 33493569733053398578202407)
    ·
      refine ⟨50240354599580097867303611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33493569733053398578202407 50240354599580097867303611)
      ·
        refine ⟨75360531899370146800955417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50240354599580097867303611 75360531899370146800955417)
        ·
          refine ⟨56520398924527610100716563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 75360531899370146800955417 56520398924527610100716563)
          ·
            refine ⟨84780598386791415151074845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56520398924527610100716563 84780598386791415151074845)
            ·
              refine ⟨31792724395046780681653067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 84780598386791415151074845 31792724395046780681653067)
              ·
                refine ⟨47689086592570171022479601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31792724395046780681653067 47689086592570171022479601)
                ·
                  refine ⟨35766814944427628266859701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 47689086592570171022479601 35766814944427628266859701)
                  ·
                    refine ⟨3353138901040090150018097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 35766814944427628266859701 3353138901040090150018097)
                    ·
                      refine ⟨2514854175780067612513573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3353138901040090150018097 2514854175780067612513573)
                      ·
                        rfl

theorem cell23_4897661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 3, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 3, 1, 2, 5, 2].length) (baseStart_4897661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4897661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4897661 prefixEnd_4897661 := by exact prefixLift 4897661
  have htrace : WordTrace (prefixWord ++ tailWord_4897661) baseStart_4897661 baseEnd_4897661 := by
    simpa [prefixWord, tailWord_4897661, baseEnd_4897661] using wordTrace_append hprefix tailTrace_4897661
  have hstable : (prefixWord ++ tailWord_4897661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4897661).length < 2 ^ (prefixWord ++ tailWord_4897661).sum := by decide
  have hdescent : baseEnd_4897661 < baseStart_4897661 := by decide
  rcases family_descends (prefixWord ++ tailWord_4897661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4897768 : List Nat := [2, 1, 4, 1, 1, 1, 3, 1, 4, 3, 2]
def baseStart_4897768 : Nat := 118140960795 + 4897768 * 2 ^ 59
def prefixEnd_4897768 : Nat := 4983230072969 + 3 ^ 40 * 4897768 * 2
def baseEnd_4897768 : Nat := 2514909118210098693875581

theorem tailTrace_4897768 : CollatzResearch.WordTrace tailWord_4897768 prefixEnd_4897768 2514909118210098693875581 := by
  unfold tailWord_4897768
  simp only [CollatzResearch.WordTrace]
  refine ⟨89318137260115241512278979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119090849680153655349705305 89318137260115241512278979)
  ·
    refine ⟨133977205890172862268418469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89318137260115241512278979 133977205890172862268418469)
    ·
      refine ⟨25120726104407411675328463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 133977205890172862268418469 25120726104407411675328463)
      ·
        refine ⟨37681089156611117512992695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25120726104407411675328463 37681089156611117512992695)
        ·
          refine ⟨56521633734916676269489043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37681089156611117512992695 56521633734916676269489043)
          ·
            refine ⟨84782450602375014404233565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56521633734916676269489043 84782450602375014404233565)
            ·
              refine ⟨31793418975890630401587587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 84782450602375014404233565 31793418975890630401587587)
              ·
                refine ⟨47690128463835945602381381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31793418975890630401587587 47690128463835945602381381)
                ·
                  refine ⟨8941899086969239800446509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 47690128463835945602381381 8941899086969239800446509)
                  ·
                    refine ⟨3353212157613464925167441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8941899086969239800446509 3353212157613464925167441)
                    ·
                      refine ⟨2514909118210098693875581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3353212157613464925167441 2514909118210098693875581)
                      ·
                        rfl

theorem cell23_4897768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 3, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 3, 1, 4, 3, 2].length) (baseStart_4897768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4897768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4897768 prefixEnd_4897768 := by exact prefixLift 4897768
  have htrace : WordTrace (prefixWord ++ tailWord_4897768) baseStart_4897768 baseEnd_4897768 := by
    simpa [prefixWord, tailWord_4897768, baseEnd_4897768] using wordTrace_append hprefix tailTrace_4897768
  have hstable : (prefixWord ++ tailWord_4897768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4897768).length < 2 ^ (prefixWord ++ tailWord_4897768).sum := by decide
  have hdescent : baseEnd_4897768 < baseStart_4897768 := by decide
  rcases family_descends (prefixWord ++ tailWord_4897768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4897775 : List Nat := [1, 1, 2, 1, 4, 5, 1, 1, 3, 1, 3]
def baseStart_4897775 : Nat := 118140960795 + 4897775 * 2 ^ 59
def prefixEnd_4897775 : Nat := 4983230072969 + 3 ^ 40 * 4897775 * 2
def baseEnd_4897775 : Nat := 2514912712574680166488049

theorem tailTrace_4897775 : CollatzResearch.WordTrace tailWord_4897775 prefixEnd_4897775 2514912712574680166488049 := by
  unfold tailWord_4897775
  simp only [CollatzResearch.WordTrace]
  refine ⟨178636529831205123220062779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119091019887470082146708519 178636529831205123220062779)
  ·
    refine ⟨267954794746807684830094169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 178636529831205123220062779 267954794746807684830094169)
    ·
      refine ⟨200966096060105763622570627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 267954794746807684830094169 200966096060105763622570627)
      ·
        refine ⟨301449144090158645433855941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 200966096060105763622570627 301449144090158645433855941)
        ·
          refine ⟨56521714516904746018847989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 301449144090158645433855941 56521714516904746018847989)
          ·
            refine ⟨5298910735959819939266999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 56521714516904746018847989 5298910735959819939266999)
            ·
              refine ⟨7948366103939729908900499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5298910735959819939266999 7948366103939729908900499)
              ·
                refine ⟨11922549155909594863350749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7948366103939729908900499 11922549155909594863350749)
                ·
                  refine ⟨4470955933466098073756531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11922549155909594863350749 4470955933466098073756531)
                  ·
                    refine ⟨6706433900199147110634797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4470955933466098073756531 6706433900199147110634797)
                    ·
                      refine ⟨2514912712574680166488049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6706433900199147110634797 2514912712574680166488049)
                      ·
                        rfl

theorem cell23_4897775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 5, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 5, 1, 1, 3, 1, 3].length) (baseStart_4897775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4897775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4897775 prefixEnd_4897775 := by exact prefixLift 4897775
  have htrace : WordTrace (prefixWord ++ tailWord_4897775) baseStart_4897775 baseEnd_4897775 := by
    simpa [prefixWord, tailWord_4897775, baseEnd_4897775] using wordTrace_append hprefix tailTrace_4897775
  have hstable : (prefixWord ++ tailWord_4897775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4897775).length < 2 ^ (prefixWord ++ tailWord_4897775).sum := by decide
  have hdescent : baseEnd_4897775 < baseStart_4897775 := by decide
  rcases family_descends (prefixWord ++ tailWord_4897775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4897821 : List Nat := [1, 4, 2, 2, 3, 11]
def baseStart_4897821 : Nat := 118140960795 + 4897821 * 2 ^ 59
def prefixEnd_4897821 : Nat := 4983230072969 + 3 ^ 40 * 4897821 * 2
def baseEnd_4897821 : Nat := 10349532233270728339559

theorem tailTrace_4897821 : CollatzResearch.WordTrace tailWord_4897821 prefixEnd_4897821 10349532233270728339559 := by
  unfold tailWord_4897821
  simp only [CollatzResearch.WordTrace]
  refine ⟨178638207589038473076237317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119092138392692315384158211 178638207589038473076237317)
  ·
    refine ⟨33494663922944713701794497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 178638207589038473076237317 33494663922944713701794497)
    ·
      refine ⟨25120997942208535276345873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33494663922944713701794497 25120997942208535276345873)
      ·
        refine ⟨18840748456656401457259405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25120997942208535276345873 18840748456656401457259405)
        ·
          refine ⟨7065280671246150546472277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18840748456656401457259405 7065280671246150546472277)
          ·
            refine ⟨10349532233270728339559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 7065280671246150546472277 10349532233270728339559)
            ·
              rfl

theorem cell23_4897821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 11].length) (baseStart_4897821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4897821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4897821 prefixEnd_4897821 := by exact prefixLift 4897821
  have htrace : WordTrace (prefixWord ++ tailWord_4897821) baseStart_4897821 baseEnd_4897821 := by
    simpa [prefixWord, tailWord_4897821, baseEnd_4897821] using wordTrace_append hprefix tailTrace_4897821
  have hstable : (prefixWord ++ tailWord_4897821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4897821).length < 2 ^ (prefixWord ++ tailWord_4897821).sum := by decide
  have hdescent : baseEnd_4897821 < baseStart_4897821 := by decide
  rcases family_descends (prefixWord ++ tailWord_4897821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4897825 : List Nat := [1, 2, 3, 2, 3, 2, 2, 2, 2, 4]
def baseStart_4897825 : Nat := 118140960795 + 4897825 * 2 ^ 59
def prefixEnd_4897825 : Nat := 4983230072969 + 3 ^ 40 * 4897825 * 2
def baseEnd_4897825 : Nat := 838312795535801656954273

theorem tailTrace_4897825 : CollatzResearch.WordTrace tailWord_4897825 prefixEnd_4897825 838312795535801656954273 := by
  unfold tailWord_4897825
  simp only [CollatzResearch.WordTrace]
  refine ⟨178638353481023981759382929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119092235654015987839588619 178638353481023981759382929)
  ·
    refine ⟨133978765110767986319537197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 178638353481023981759382929 133978765110767986319537197)
    ·
      refine ⟨50242036916537994869826449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 133978765110767986319537197 50242036916537994869826449)
      ·
        refine ⟨37681527687403496152369837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50242036916537994869826449 37681527687403496152369837)
        ·
          refine ⟨14130572882776311057138689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37681527687403496152369837 14130572882776311057138689)
          ·
            refine ⟨10597929662082233292854017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14130572882776311057138689 10597929662082233292854017)
            ·
              refine ⟨7948447246561674969640513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10597929662082233292854017 7948447246561674969640513)
              ·
                refine ⟨5961335434921256227230385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7948447246561674969640513 5961335434921256227230385)
                ·
                  refine ⟨4471001576190942170422789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5961335434921256227230385 4471001576190942170422789)
                  ·
                    refine ⟨838312795535801656954273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4471001576190942170422789 838312795535801656954273)
                    ·
                      rfl

theorem cell23_4897825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 2, 2, 2, 2, 4].length) (baseStart_4897825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4897825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4897825 prefixEnd_4897825 := by exact prefixLift 4897825
  have htrace : WordTrace (prefixWord ++ tailWord_4897825) baseStart_4897825 baseEnd_4897825 := by
    simpa [prefixWord, tailWord_4897825, baseEnd_4897825] using wordTrace_append hprefix tailTrace_4897825
  have hstable : (prefixWord ++ tailWord_4897825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4897825).length < 2 ^ (prefixWord ++ tailWord_4897825).sum := by decide
  have hdescent : baseEnd_4897825 < baseStart_4897825 := by decide
  rcases family_descends (prefixWord ++ tailWord_4897825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4897848 : List Nat := [2, 1, 2, 1, 5, 1, 1, 3, 1, 3, 3]
def baseStart_4897848 : Nat := 118140960795 + 4897848 * 2 ^ 59
def prefixEnd_4897848 : Nat := 4983230072969 + 3 ^ 40 * 4897848 * 2
def baseEnd_4897848 : Nat := 2514950196662458380875213

theorem tailTrace_4897848 : CollatzResearch.WordTrace tailWord_4897848 prefixEnd_4897848 2514950196662458380875213 := by
  unfold tailWord_4897848
  simp only [CollatzResearch.WordTrace]
  refine ⟨89319596179970328343735099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119092794906627104458313465 89319596179970328343735099)
  ·
    refine ⟨133979394269955492515602649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89319596179970328343735099 133979394269955492515602649)
    ·
      refine ⟨100484545702466619386701987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 133979394269955492515602649 100484545702466619386701987)
      ·
        refine ⟨150726818553699929080052981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100484545702466619386701987 150726818553699929080052981)
        ·
          refine ⟨14130639239409368351254967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 150726818553699929080052981 14130639239409368351254967)
          ·
            refine ⟨21195958859114052526882451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14130639239409368351254967 21195958859114052526882451)
            ·
              refine ⟨31793938288671078790323677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21195958859114052526882451 31793938288671078790323677)
              ·
                refine ⟨11922726858251654546371379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31793938288671078790323677 11922726858251654546371379)
                ·
                  refine ⟨17884090287377481819557069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11922726858251654546371379 17884090287377481819557069)
                  ·
                    refine ⟨6706533857766555682333901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17884090287377481819557069 6706533857766555682333901)
                    ·
                      refine ⟨2514950196662458380875213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6706533857766555682333901 2514950196662458380875213)
                      ·
                        rfl

theorem cell23_4897848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 1, 3, 1, 3, 3].length) (baseStart_4897848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4897848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4897848 prefixEnd_4897848 := by exact prefixLift 4897848
  have htrace : WordTrace (prefixWord ++ tailWord_4897848) baseStart_4897848 baseEnd_4897848 := by
    simpa [prefixWord, tailWord_4897848, baseEnd_4897848] using wordTrace_append hprefix tailTrace_4897848
  have hstable : (prefixWord ++ tailWord_4897848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4897848).length < 2 ^ (prefixWord ++ tailWord_4897848).sum := by decide
  have hdescent : baseEnd_4897848 < baseStart_4897848 := by decide
  rcases family_descends (prefixWord ++ tailWord_4897848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4897869 : List Nat := [1, 6, 1, 1, 1, 4, 2, 1, 1, 2, 3]
def baseStart_4897869 : Nat := 118140960795 + 4897869 * 2 ^ 59
def prefixEnd_4897869 : Nat := 4983230072969 + 3 ^ 40 * 4897869 * 2
def baseEnd_4897869 : Nat := 2514960979756202798712617

theorem tailTrace_4897869 : CollatzResearch.WordTrace tailWord_4897869 prefixEnd_4897869 2514960979756202798712617 := by
  unfold tailWord_4897869
  simp only [CollatzResearch.WordTrace]
  refine ⟨178639958292864577273984661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119093305528576384849323107 178639958292864577273984661)
  ·
    refine ⟨8373748044978027059718031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 178639958292864577273984661 8373748044978027059718031)
    ·
      refine ⟨12560622067467040589577047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8373748044978027059718031 12560622067467040589577047)
      ·
        refine ⟨18840933101200560884365571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12560622067467040589577047 18840933101200560884365571)
        ·
          refine ⟨28261399651800841326548357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18840933101200560884365571 28261399651800841326548357)
          ·
            refine ⟨5299012434712657748727817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 28261399651800841326548357 5299012434712657748727817)
            ·
              refine ⟨3974259326034493311545863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5299012434712657748727817 3974259326034493311545863)
              ·
                refine ⟨5961388989051739967318795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3974259326034493311545863 5961388989051739967318795)
                ·
                  refine ⟨8942083483577609950978193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5961388989051739967318795 8942083483577609950978193)
                  ·
                    refine ⟨6706562612683207463233645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8942083483577609950978193 6706562612683207463233645)
                    ·
                      refine ⟨2514960979756202798712617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6706562612683207463233645 2514960979756202798712617)
                      ·
                        rfl

theorem cell23_4897869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 4, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 4, 2, 1, 1, 2, 3].length) (baseStart_4897869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4897869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4897869 prefixEnd_4897869 := by exact prefixLift 4897869
  have htrace : WordTrace (prefixWord ++ tailWord_4897869) baseStart_4897869 baseEnd_4897869 := by
    simpa [prefixWord, tailWord_4897869, baseEnd_4897869] using wordTrace_append hprefix tailTrace_4897869
  have hstable : (prefixWord ++ tailWord_4897869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4897869).length < 2 ^ (prefixWord ++ tailWord_4897869).sum := by decide
  have hdescent : baseEnd_4897869 < baseStart_4897869 := by decide
  rcases family_descends (prefixWord ++ tailWord_4897869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4897891 : List Nat := [1, 1, 1, 5, 1, 1, 1, 2, 4, 1, 5]
def baseStart_4897891 : Nat := 118140960795 + 4897891 * 2 ^ 59
def prefixEnd_4897891 : Nat := 4983230072969 + 3 ^ 40 * 4897891 * 2
def baseEnd_4897891 : Nat := 2514972276330601712637515

theorem tailTrace_4897891 : CollatzResearch.WordTrace tailWord_4897891 prefixEnd_4897891 2514972276330601712637515 := by
  unfold tailWord_4897891
  simp only [CollatzResearch.WordTrace]
  refine ⟨178640760698784875031285527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119093840465856583354190351 178640760698784875031285527)
  ·
    refine ⟨267961141048177312546928291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 178640760698784875031285527 267961141048177312546928291)
    ·
      refine ⟨401941711572265968820392437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 267961141048177312546928291 401941711572265968820392437)
      ·
        refine ⟨37682035459899934576911791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 401941711572265968820392437 37682035459899934576911791)
        ·
          refine ⟨56523053189849901865367687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37682035459899934576911791 56523053189849901865367687)
          ·
            refine ⟨84784579784774852798051531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56523053189849901865367687 84784579784774852798051531)
            ·
              refine ⟨127176869677162279197077297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 84784579784774852798051531 127176869677162279197077297)
              ·
                refine ⟨95382652257871709397807973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 127176869677162279197077297 95382652257871709397807973)
                ·
                  refine ⟨17884247298350945512088995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 95382652257871709397807973 17884247298350945512088995)
                  ·
                    refine ⟨26826370947526418268133493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17884247298350945512088995 26826370947526418268133493)
                    ·
                      refine ⟨2514972276330601712637515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26826370947526418268133493 2514972276330601712637515)
                      ·
                        rfl

theorem cell23_4897891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 2, 4, 1, 5].length) (baseStart_4897891 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4897891 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4897891 prefixEnd_4897891 := by exact prefixLift 4897891
  have htrace : WordTrace (prefixWord ++ tailWord_4897891) baseStart_4897891 baseEnd_4897891 := by
    simpa [prefixWord, tailWord_4897891, baseEnd_4897891] using wordTrace_append hprefix tailTrace_4897891
  have hstable : (prefixWord ++ tailWord_4897891).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4897891).length < 2 ^ (prefixWord ++ tailWord_4897891).sum := by decide
  have hdescent : baseEnd_4897891 < baseStart_4897891 := by decide
  rcases family_descends (prefixWord ++ tailWord_4897891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4897898 : List Nat := [3, 1, 3, 2, 2, 1, 2, 1, 2, 6]
def baseStart_4897898 : Nat := 118140960795 + 4897898 * 2 ^ 59
def prefixEnd_4897898 : Nat := 4983230072969 + 3 ^ 40 * 4897898 * 2
def baseEnd_4897898 : Nat := 838325290231727728416661

theorem tailTrace_4897898 : CollatzResearch.WordTrace tailWord_4897898 prefixEnd_4897898 838325290231727728416661 := by
  unfold tailWord_4897898
  simp only [CollatzResearch.WordTrace]
  refine ⟨44660254002439878806697587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 119094010673173010151193565 44660254002439878806697587)
  ·
    refine ⟨66990381003659818210046381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44660254002439878806697587 66990381003659818210046381)
    ·
      refine ⟨25121392876372431828767393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 66990381003659818210046381 25121392876372431828767393)
      ·
        refine ⟨18841044657279323871575545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25121392876372431828767393 18841044657279323871575545)
        ·
          refine ⟨14130783492959492903681659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18841044657279323871575545 14130783492959492903681659)
          ·
            refine ⟨21196175239439239355522489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14130783492959492903681659 21196175239439239355522489)
            ·
              refine ⟨15897131429579429516641867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21196175239439239355522489 15897131429579429516641867)
              ·
                refine ⟨23845697144369144274962801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15897131429579429516641867 23845697144369144274962801)
                ·
                  refine ⟨17884272858276858206222101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23845697144369144274962801 17884272858276858206222101)
                  ·
                    refine ⟨838325290231727728416661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17884272858276858206222101 838325290231727728416661)
                    ·
                      rfl

theorem cell23_4897898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 2, 1, 2, 6].length) (baseStart_4897898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4897898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4897898 prefixEnd_4897898 := by exact prefixLift 4897898
  have htrace : WordTrace (prefixWord ++ tailWord_4897898) baseStart_4897898 baseEnd_4897898 := by
    simpa [prefixWord, tailWord_4897898, baseEnd_4897898] using wordTrace_append hprefix tailTrace_4897898
  have hstable : (prefixWord ++ tailWord_4897898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4897898).length < 2 ^ (prefixWord ++ tailWord_4897898).sum := by decide
  have hdescent : baseEnd_4897898 < baseStart_4897898 := by decide
  rcases family_descends (prefixWord ++ tailWord_4897898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4897911 : List Nat := [1, 1, 3, 1, 1, 4, 1, 4, 7]
def baseStart_4897911 : Nat := 118140960795 + 4897911 * 2 ^ 59
def prefixEnd_4897911 : Nat := 4983230072969 + 3 ^ 40 * 4897911 * 2
def baseEnd_4897911 : Nat := 279442505104854626043047

theorem tailTrace_4897911 : CollatzResearch.WordTrace tailWord_4897911 prefixEnd_4897911 279442505104854626043047 := by
  unfold tailWord_4897911
  simp only [CollatzResearch.WordTrace]
  refine ⟨178641490158712418447013587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119094326772474945631342391 178641490158712418447013587)
  ·
    refine ⟨267962235238068627670520381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 178641490158712418447013587 267962235238068627670520381)
    ·
      refine ⟨100485838214275735376445143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 267962235238068627670520381 100485838214275735376445143)
      ·
        refine ⟨150728757321413603064667715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100485838214275735376445143 150728757321413603064667715)
        ·
          refine ⟨226093135982120404597001573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 150728757321413603064667715 226093135982120404597001573)
          ·
            refine ⟨42392462996647575861937795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 226093135982120404597001573 42392462996647575861937795)
            ·
              refine ⟨63588694494971363792906693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42392462996647575861937795 63588694494971363792906693)
              ·
                refine ⟨11922880217807130711170005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 63588694494971363792906693 11922880217807130711170005)
                ·
                  refine ⟨279442505104854626043047, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11922880217807130711170005 279442505104854626043047)
                  ·
                    rfl

theorem cell23_4897911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 1, 4, 7].length) (baseStart_4897911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4897911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4897911 prefixEnd_4897911 := by exact prefixLift 4897911
  have htrace : WordTrace (prefixWord ++ tailWord_4897911) baseStart_4897911 baseEnd_4897911 := by
    simpa [prefixWord, tailWord_4897911, baseEnd_4897911] using wordTrace_append hprefix tailTrace_4897911
  have hstable : (prefixWord ++ tailWord_4897911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4897911).length < 2 ^ (prefixWord ++ tailWord_4897911).sum := by decide
  have hdescent : baseEnd_4897911 < baseStart_4897911 := by decide
  rcases family_descends (prefixWord ++ tailWord_4897911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4897941 : List Nat := [1, 3, 2, 1, 1, 1, 2, 2, 3, 7]
def baseStart_4897941 : Nat := 118140960795 + 4897941 * 2 ^ 59
def prefixEnd_4897941 : Nat := 4983230072969 + 3 ^ 40 * 4897941 * 2
def baseEnd_4897941 : Nat := 838332650121108839004095

theorem tailTrace_4897941 : CollatzResearch.WordTrace tailWord_4897941 prefixEnd_4897941 838332650121108839004095 := by
  unfold tailWord_4897941
  simp only [CollatzResearch.WordTrace]
  refine ⟨178642584348603733570605677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119095056232402489047070451 178642584348603733570605677)
  ·
    refine ⟨66990969130726400088977129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 178642584348603733570605677 66990969130726400088977129)
    ·
      refine ⟨50243226848044800066732847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66990969130726400088977129 50243226848044800066732847)
      ·
        refine ⟨75364840272067200100099271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50243226848044800066732847 75364840272067200100099271)
        ·
          refine ⟨113047260408100800150148907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75364840272067200100099271 113047260408100800150148907)
          ·
            refine ⟨169570890612151200225223361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 113047260408100800150148907 169570890612151200225223361)
            ·
              refine ⟨127178167959113400168917521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 169570890612151200225223361 127178167959113400168917521)
              ·
                refine ⟨95383625969335050126688141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 127178167959113400168917521 95383625969335050126688141)
                ·
                  refine ⟨35768859738500643797508053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 95383625969335050126688141 35768859738500643797508053)
                  ·
                    refine ⟨838332650121108839004095, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 35768859738500643797508053 838332650121108839004095)
                    ·
                      rfl

theorem cell23_4897941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 2, 3, 7].length) (baseStart_4897941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4897941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4897941 prefixEnd_4897941 := by exact prefixLift 4897941
  have htrace : WordTrace (prefixWord ++ tailWord_4897941) baseStart_4897941 baseEnd_4897941 := by
    simpa [prefixWord, tailWord_4897941, baseEnd_4897941] using wordTrace_append hprefix tailTrace_4897941
  have hstable : (prefixWord ++ tailWord_4897941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4897941).length < 2 ^ (prefixWord ++ tailWord_4897941).sum := by decide
  have hdescent : baseEnd_4897941 < baseStart_4897941 := by decide
  rcases family_descends (prefixWord ++ tailWord_4897941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4897956 : List Nat := [2, 3, 1, 2, 3, 3, 2, 1, 2, 2, 2]
def baseStart_4897956 : Nat := 118140960795 + 4897956 * 2 ^ 59
def prefixEnd_4897956 : Nat := 4983230072969 + 3 ^ 40 * 4897956 * 2
def baseEnd_4897956 : Nat := 2515005652573143958324717

theorem tailTrace_4897956 : CollatzResearch.WordTrace tailWord_4897956 prefixEnd_4897956 2515005652573143958324717 := by
  unfold tailWord_4897956
  simp only [CollatzResearch.WordTrace]
  refine ⟨89321565721774695566200861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119095420962366260754934481 89321565721774695566200861)
  ·
    refine ⟨33495587145665510837325323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 89321565721774695566200861 33495587145665510837325323)
    ·
      refine ⟨50243380718498266255987985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33495587145665510837325323 50243380718498266255987985)
      ·
        refine ⟨37682535538873699691990989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50243380718498266255987985 37682535538873699691990989)
        ·
          refine ⟨14130950827077637384496621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37682535538873699691990989 14130950827077637384496621)
          ·
            refine ⟨5299106560154114019186233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14130950827077637384496621 5299106560154114019186233)
            ·
              refine ⟨3974329920115585514389675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5299106560154114019186233 3974329920115585514389675)
              ·
                refine ⟨5961494880173378271584513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3974329920115585514389675 5961494880173378271584513)
                ·
                  refine ⟨4471121160130033703688385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5961494880173378271584513 4471121160130033703688385)
                  ·
                    refine ⟨3353340870097525277766289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4471121160130033703688385 3353340870097525277766289)
                    ·
                      refine ⟨2515005652573143958324717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3353340870097525277766289 2515005652573143958324717)
                      ·
                        rfl

theorem cell23_4897956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 3, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 3, 2, 1, 2, 2, 2].length) (baseStart_4897956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4897956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4897956 prefixEnd_4897956 := by exact prefixLift 4897956
  have htrace : WordTrace (prefixWord ++ tailWord_4897956) baseStart_4897956 baseEnd_4897956 := by
    simpa [prefixWord, tailWord_4897956, baseEnd_4897956] using wordTrace_append hprefix tailTrace_4897956
  have hstable : (prefixWord ++ tailWord_4897956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4897956).length < 2 ^ (prefixWord ++ tailWord_4897956).sum := by decide
  have hdescent : baseEnd_4897956 < baseStart_4897956 := by decide
  rcases family_descends (prefixWord ++ tailWord_4897956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4897971 : List Nat := [1, 1, 1, 2, 3, 2, 2, 1, 2, 8]
def baseStart_4897971 : Nat := 118140960795 + 4897971 * 2 ^ 59
def prefixEnd_4897971 : Nat := 4983230072969 + 3 ^ 40 * 4897971 * 2
def baseEnd_4897971 : Nat := 838337784927653799879049

theorem tailTrace_4897971 : CollatzResearch.WordTrace tailWord_4897971 prefixEnd_4897971 838337784927653799879049 := by
  unfold tailWord_4897971
  simp only [CollatzResearch.WordTrace]
  refine ⟨178643678538495048694197767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119095785692330032462798511 178643678538495048694197767)
  ·
    refine ⟨267965517807742573041296651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 178643678538495048694197767 267965517807742573041296651)
    ·
      refine ⟨401948276711613859561944977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 267965517807742573041296651 401948276711613859561944977)
      ·
        refine ⟨301461207533710394671458733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 401948276711613859561944977 301461207533710394671458733)
        ·
          refine ⟨113047952825141398001797025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 301461207533710394671458733 113047952825141398001797025)
          ·
            refine ⟨84785964618856048501347769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 113047952825141398001797025 84785964618856048501347769)
            ·
              refine ⟨63589473464142036376010827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 84785964618856048501347769 63589473464142036376010827)
              ·
                refine ⟨95384210196213054564016241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 63589473464142036376010827 95384210196213054564016241)
                ·
                  refine ⟨71538157647159790923012181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 95384210196213054564016241 71538157647159790923012181)
                  ·
                    refine ⟨838337784927653799879049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 71538157647159790923012181 838337784927653799879049)
                    ·
                      rfl

theorem cell23_4897971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 2, 1, 2, 8].length) (baseStart_4897971 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4897971 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4897971 prefixEnd_4897971 := by exact prefixLift 4897971
  have htrace : WordTrace (prefixWord ++ tailWord_4897971) baseStart_4897971 baseEnd_4897971 := by
    simpa [prefixWord, tailWord_4897971, baseEnd_4897971] using wordTrace_append hprefix tailTrace_4897971
  have hstable : (prefixWord ++ tailWord_4897971).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4897971).length < 2 ^ (prefixWord ++ tailWord_4897971).sum := by decide
  have hdescent : baseEnd_4897971 < baseStart_4897971 := by decide
  rcases family_descends (prefixWord ++ tailWord_4897971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4897985 : List Nat := [1, 2, 6, 1, 1, 1, 1, 2, 1, 2, 5]
def baseStart_4897985 : Nat := 118140960795 + 4897985 * 2 ^ 59
def prefixEnd_4897985 : Nat := 4983230072969 + 3 ^ 40 * 4897985 * 2
def baseEnd_4897985 : Nat := 2515020543512124344862083

theorem tailTrace_4897985 : CollatzResearch.WordTrace tailWord_4897985 prefixEnd_4897985 2515020543512124344862083 := by
  unfold tailWord_4897985
  simp only [CollatzResearch.WordTrace]
  refine ⟨178644189160444329085207409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119096126106962886056804939 178644189160444329085207409)
  ·
    refine ⟨133983141870333246813905557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 178644189160444329085207409 133983141870333246813905557)
    ·
      refine ⟨6280459775171870944401823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 133983141870333246813905557 6280459775171870944401823)
      ·
        refine ⟨9420689662757806416602735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6280459775171870944401823 9420689662757806416602735)
        ·
          refine ⟨14131034494136709624904103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9420689662757806416602735 14131034494136709624904103)
          ·
            refine ⟨21196551741205064437356155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14131034494136709624904103 21196551741205064437356155)
            ·
              refine ⟨31794827611807596656034233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21196551741205064437356155 31794827611807596656034233)
              ·
                refine ⟨23846120708855697492025675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31794827611807596656034233 23846120708855697492025675)
                ·
                  refine ⟨35769181063283546238038513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23846120708855697492025675 35769181063283546238038513)
                  ·
                    refine ⟨26826885797462659678528885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 35769181063283546238038513 26826885797462659678528885)
                    ·
                      refine ⟨2515020543512124344862083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26826885797462659678528885 2515020543512124344862083)
                      ·
                        rfl

theorem cell23_4897985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 1, 2, 1, 2, 5].length) (baseStart_4897985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4897985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4897985 prefixEnd_4897985 := by exact prefixLift 4897985
  have htrace : WordTrace (prefixWord ++ tailWord_4897985) baseStart_4897985 baseEnd_4897985 := by
    simpa [prefixWord, tailWord_4897985, baseEnd_4897985] using wordTrace_append hprefix tailTrace_4897985
  have hstable : (prefixWord ++ tailWord_4897985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4897985).length < 2 ^ (prefixWord ++ tailWord_4897985).sum := by decide
  have hdescent : baseEnd_4897985 < baseStart_4897985 := by decide
  rcases family_descends (prefixWord ++ tailWord_4897985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4897990 : List Nat := [6, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2]
def baseStart_4897990 : Nat := 118140960795 + 4897990 * 2 ^ 59
def prefixEnd_4897990 : Nat := 4983230072969 + 3 ^ 40 * 4897990 * 2
def baseEnd_4897990 : Nat := 2515023110915396825299561

theorem tailTrace_4897990 : CollatzResearch.WordTrace tailWord_4897990 prefixEnd_4897990 2515023110915396825299561 := by
  unfold tailWord_4897990
  simp only [CollatzResearch.WordTrace]
  refine ⟨5582636610169569216848107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 119096247683617476626092949 5582636610169569216848107)
  ·
    refine ⟨8373954915254353825272161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5582636610169569216848107 8373954915254353825272161)
    ·
      refine ⟨6280466186440765368954121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8373954915254353825272161 6280466186440765368954121)
      ·
        refine ⟨4710349639830574026715591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6280466186440765368954121 4710349639830574026715591)
        ·
          refine ⟨7065524459745861040073387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4710349639830574026715591 7065524459745861040073387)
          ·
            refine ⟨10598286689618791560110081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7065524459745861040073387 10598286689618791560110081)
            ·
              refine ⟨7948715017214093670082561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10598286689618791560110081 7948715017214093670082561)
              ·
                refine ⟨5961536262910570252561921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7948715017214093670082561 5961536262910570252561921)
                ·
                  refine ⟨4471152197182927689421441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5961536262910570252561921 4471152197182927689421441)
                  ·
                    refine ⟨3353364147887195767066081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4471152197182927689421441 3353364147887195767066081)
                    ·
                      refine ⟨2515023110915396825299561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3353364147887195767066081 2515023110915396825299561)
                      ·
                        rfl

theorem cell23_4897990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2].length) (baseStart_4897990 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4897990 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4897990 prefixEnd_4897990 := by exact prefixLift 4897990
  have htrace : WordTrace (prefixWord ++ tailWord_4897990) baseStart_4897990 baseEnd_4897990 := by
    simpa [prefixWord, tailWord_4897990, baseEnd_4897990] using wordTrace_append hprefix tailTrace_4897990
  have hstable : (prefixWord ++ tailWord_4897990).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4897990).length < 2 ^ (prefixWord ++ tailWord_4897990).sum := by decide
  have hdescent : baseEnd_4897990 < baseStart_4897990 := by decide
  rcases family_descends (prefixWord ++ tailWord_4897990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4898011 : List Nat := [1, 1, 1, 1, 1, 1, 1, 4, 2, 1, 9]
def baseStart_4898011 : Nat := 118140960795 + 4898011 * 2 ^ 59
def prefixEnd_4898011 : Nat := 4983230072969 + 3 ^ 40 * 4898011 * 2
def baseEnd_4898011 : Nat := 2515033894009141243136963

theorem tailTrace_4898011 : CollatzResearch.WordTrace tailWord_4898011 prefixEnd_4898011 2515033894009141243136963 := by
  unfold tailWord_4898011
  simp only [CollatzResearch.WordTrace]
  refine ⟨178645137458350135525653887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119096758305566757017102591 178645137458350135525653887)
  ·
    refine ⟨267967706187525203288480831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 178645137458350135525653887 267967706187525203288480831)
    ·
      refine ⟨401951559281287804932721247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 267967706187525203288480831 401951559281287804932721247)
      ·
        refine ⟨602927338921931707399081871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 401951559281287804932721247 602927338921931707399081871)
        ·
          refine ⟨904391008382897561098622807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 602927338921931707399081871 904391008382897561098622807)
          ·
            refine ⟨1356586512574346341647934211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 904391008382897561098622807 1356586512574346341647934211)
            ·
              refine ⟨2034879768861519512471901317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1356586512574346341647934211 2034879768861519512471901317)
              ·
                refine ⟨381539956661534908588481497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2034879768861519512471901317 381539956661534908588481497)
                ·
                  refine ⟨286154967496151181441361123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 381539956661534908588481497 286154967496151181441361123)
                  ·
                    refine ⟨429232451244226772162041685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 286154967496151181441361123 429232451244226772162041685)
                    ·
                      refine ⟨2515033894009141243136963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 429232451244226772162041685 2515033894009141243136963)
                      ·
                        rfl

theorem cell23_4898011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 2, 1, 9].length) (baseStart_4898011 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4898011 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4898011 prefixEnd_4898011 := by exact prefixLift 4898011
  have htrace : WordTrace (prefixWord ++ tailWord_4898011) baseStart_4898011 baseEnd_4898011 := by
    simpa [prefixWord, tailWord_4898011, baseEnd_4898011] using wordTrace_append hprefix tailTrace_4898011
  have hstable : (prefixWord ++ tailWord_4898011).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4898011).length < 2 ^ (prefixWord ++ tailWord_4898011).sum := by decide
  have hdescent : baseEnd_4898011 < baseStart_4898011 := by decide
  rcases family_descends (prefixWord ++ tailWord_4898011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4898052 : List Nat := [2, 3, 2, 2, 2, 3, 1, 2, 6]
def baseStart_4898052 : Nat := 118140960795 + 4898052 * 2 ^ 59
def prefixEnd_4898052 : Nat := 4983230072969 + 3 ^ 40 * 4898052 * 2
def baseEnd_4898052 : Nat := 279450549635108398080475

theorem tailTrace_4898052 : CollatzResearch.WordTrace tailWord_4898052 prefixEnd_4898052 279450549635108398080475 := by
  unfold tailWord_4898052
  simp only [CollatzResearch.WordTrace]
  refine ⟨89323316425600799763948205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119097755234134399685264273 89323316425600799763948205)
  ·
    refine ⟨33496243659600299911480577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 89323316425600799763948205 33496243659600299911480577)
    ·
      refine ⟨25122182744700224933610433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33496243659600299911480577 25122182744700224933610433)
      ·
        refine ⟨18841637058525168700207825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25122182744700224933610433 18841637058525168700207825)
        ·
          refine ⟨14131227793893876525155869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18841637058525168700207825 14131227793893876525155869)
          ·
            refine ⟨5299210422710203696933451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14131227793893876525155869 5299210422710203696933451)
            ·
              refine ⟨7948815634065305545400177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5299210422710203696933451 7948815634065305545400177)
              ·
                refine ⟨5961611725548979159050133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7948815634065305545400177 5961611725548979159050133)
                ·
                  refine ⟨279450549635108398080475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5961611725548979159050133 279450549635108398080475)
                  ·
                    rfl

theorem cell23_4898052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 3, 1, 2, 6].length) (baseStart_4898052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4898052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4898052 prefixEnd_4898052 := by exact prefixLift 4898052
  have htrace : WordTrace (prefixWord ++ tailWord_4898052) baseStart_4898052 baseEnd_4898052 := by
    simpa [prefixWord, tailWord_4898052, baseEnd_4898052] using wordTrace_append hprefix tailTrace_4898052
  have hstable : (prefixWord ++ tailWord_4898052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4898052).length < 2 ^ (prefixWord ++ tailWord_4898052).sum := by decide
  have hdescent : baseEnd_4898052 < baseStart_4898052 := by decide
  rcases family_descends (prefixWord ++ tailWord_4898052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4898062 : List Nat := [4, 1, 1, 2, 1, 3, 1, 3, 3, 1, 3]
def baseStart_4898062 : Nat := 118140960795 + 4898062 * 2 ^ 59
def prefixEnd_4898062 : Nat := 4983230072969 + 3 ^ 40 * 4898062 * 2
def baseEnd_4898062 : Nat := 2515060081522520543599229

theorem tailTrace_4898062 : CollatzResearch.WordTrace tailWord_4898062 prefixEnd_4898062 2515060081522520543599229 := by
  unfold tailWord_4898062
  simp only [CollatzResearch.WordTrace]
  refine ⟨22330874697645671404470055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 119097998387443580823840293 22330874697645671404470055)
  ·
    refine ⟨33496312046468507106705083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22330874697645671404470055 33496312046468507106705083)
    ·
      refine ⟨50244468069702760660057625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33496312046468507106705083 50244468069702760660057625)
      ·
        refine ⟨37683351052277070495043219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50244468069702760660057625 37683351052277070495043219)
        ·
          refine ⟨56525026578415605742564829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37683351052277070495043219 56525026578415605742564829)
          ·
            refine ⟨21196884966905852153461811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 56525026578415605742564829 21196884966905852153461811)
            ·
              refine ⟨31795327450358778230192717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21196884966905852153461811 31795327450358778230192717)
              ·
                refine ⟨11923247793884541836322269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31795327450358778230192717 11923247793884541836322269)
                ·
                  refine ⟨4471217922706703188620851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11923247793884541836322269 4471217922706703188620851)
                  ·
                    refine ⟨6706826884060054782931277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4471217922706703188620851 6706826884060054782931277)
                    ·
                      refine ⟨2515060081522520543599229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6706826884060054782931277 2515060081522520543599229)
                      ·
                        rfl

theorem cell23_4898062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 1, 3, 3, 1, 3].length) (baseStart_4898062 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4898062 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4898062 prefixEnd_4898062 := by exact prefixLift 4898062
  have htrace : WordTrace (prefixWord ++ tailWord_4898062) baseStart_4898062 baseEnd_4898062 := by
    simpa [prefixWord, tailWord_4898062, baseEnd_4898062] using wordTrace_append hprefix tailTrace_4898062
  have hstable : (prefixWord ++ tailWord_4898062).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4898062).length < 2 ^ (prefixWord ++ tailWord_4898062).sum := by decide
  have hdescent : baseEnd_4898062 < baseStart_4898062 := by decide
  rcases family_descends (prefixWord ++ tailWord_4898062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4898108 : List Nat := [2, 2, 2, 2, 1, 3, 11]
def baseStart_4898108 : Nat := 118140960795 + 4898108 * 2 ^ 59
def prefixEnd_4898108 : Nat := 4983230072969 + 3 ^ 40 * 4898108 * 2
def baseEnd_4898108 : Nat := 31050416069538609427457

theorem tailTrace_4898108 : CollatzResearch.WordTrace tailWord_4898108 prefixEnd_4898108 31050416069538609427457 := by
  unfold tailWord_4898108
  simp only [CollatzResearch.WordTrace]
  refine ⟨89324337669499360545967489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119099116892665814061289985 89324337669499360545967489)
  ·
    refine ⟨66993253252124520409475617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89324337669499360545967489 66993253252124520409475617)
    ·
      refine ⟨50244939939093390307106713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66993253252124520409475617 50244939939093390307106713)
      ·
        refine ⟨37683704954320042730330035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50244939939093390307106713 37683704954320042730330035)
        ·
          refine ⟨56525557431480064095495053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37683704954320042730330035 56525557431480064095495053)
          ·
            refine ⟨21197084036805024035810645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 56525557431480064095495053 21197084036805024035810645)
            ·
              refine ⟨31050416069538609427457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 21197084036805024035810645 31050416069538609427457)
              ·
                rfl

theorem cell23_4898108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 11].length) (baseStart_4898108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4898108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4898108 prefixEnd_4898108 := by exact prefixLift 4898108
  have htrace : WordTrace (prefixWord ++ tailWord_4898108) baseStart_4898108 baseEnd_4898108 := by
    simpa [prefixWord, tailWord_4898108, baseEnd_4898108] using wordTrace_append hprefix tailTrace_4898108
  have hstable : (prefixWord ++ tailWord_4898108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4898108).length < 2 ^ (prefixWord ++ tailWord_4898108).sum := by decide
  have hdescent : baseEnd_4898108 < baseStart_4898108 := by decide
  rcases family_descends (prefixWord ++ tailWord_4898108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4898113 : List Nat := [1, 2, 5, 2, 1, 2, 3, 2, 1, 1, 3]
def baseStart_4898113 : Nat := 118140960795 + 4898113 * 2 ^ 59
def prefixEnd_4898113 : Nat := 4983230072969 + 3 ^ 40 * 4898113 * 2
def baseEnd_4898113 : Nat := 2515086269035899844061495

theorem tailTrace_4898113 : CollatzResearch.WordTrace tailWord_4898113 prefixEnd_4898113 2515086269035899844061495 := by
  unfold tailWord_4898113
  simp only [CollatzResearch.WordTrace]
  refine ⟨178648857703980606945866993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119099238469320404630577995 178648857703980606945866993)
  ·
    refine ⟨133986643277985455209400245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 178648857703980606945866993 133986643277985455209400245)
    ·
      refine ⟨12561247807311136425881273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 133986643277985455209400245 12561247807311136425881273)
      ·
        refine ⟨9420935855483352319410955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12561247807311136425881273 9420935855483352319410955)
        ·
          refine ⟨14131403783225028479116433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9420935855483352319410955 14131403783225028479116433)
          ·
            refine ⟨10598552837418771359337325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14131403783225028479116433 10598552837418771359337325)
            ·
              refine ⟨3974457314032039259751497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10598552837418771359337325 3974457314032039259751497)
              ·
                refine ⟨2980842985524029444813623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3974457314032039259751497 2980842985524029444813623)
                ·
                  refine ⟨4471264478286044167220435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2980842985524029444813623 4471264478286044167220435)
                  ·
                    refine ⟨6706896717429066250830653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4471264478286044167220435 6706896717429066250830653)
                    ·
                      refine ⟨2515086269035899844061495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6706896717429066250830653 2515086269035899844061495)
                      ·
                        rfl

theorem cell23_4898113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 2, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 2, 3, 2, 1, 1, 3].length) (baseStart_4898113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4898113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4898113 prefixEnd_4898113 := by exact prefixLift 4898113
  have htrace : WordTrace (prefixWord ++ tailWord_4898113) baseStart_4898113 baseEnd_4898113 := by
    simpa [prefixWord, tailWord_4898113, baseEnd_4898113] using wordTrace_append hprefix tailTrace_4898113
  have hstable : (prefixWord ++ tailWord_4898113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4898113).length < 2 ^ (prefixWord ++ tailWord_4898113).sum := by decide
  have hdescent : baseEnd_4898113 < baseStart_4898113 := by decide
  rcases family_descends (prefixWord ++ tailWord_4898113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4898119 : List Nat := [1, 1, 4, 1, 2, 3, 3, 1, 3, 2, 2]
def baseStart_4898119 : Nat := 118140960795 + 4898119 * 2 ^ 59
def prefixEnd_4898119 : Nat := 4983230072969 + 3 ^ 40 * 4898119 * 2
def baseEnd_4898119 : Nat := 2515089349919826820586467

theorem tailTrace_4898119 : CollatzResearch.WordTrace tailWord_4898119 prefixEnd_4898119 2515089349919826820586467 := by
  unfold tailWord_4898119
  simp only [CollatzResearch.WordTrace]
  refine ⟨178649076541958869970585411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119099384361305913313723607 178649076541958869970585411)
  ·
    refine ⟨267973614812938304955878117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 178649076541958869970585411 267973614812938304955878117)
    ·
      refine ⟨50245052777425932179227147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 267973614812938304955878117 50245052777425932179227147)
      ·
        refine ⟨75367579166138898268840721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50245052777425932179227147 75367579166138898268840721)
        ·
          refine ⟨56525684374604173701630541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 75367579166138898268840721 56525684374604173701630541)
          ·
            refine ⟨21197131640476565138111453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 56525684374604173701630541 21197131640476565138111453)
            ·
              refine ⟨7948924365178711926791795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21197131640476565138111453 7948924365178711926791795)
              ·
                refine ⟨11923386547768067890187693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7948924365178711926791795 11923386547768067890187693)
                ·
                  refine ⟨4471269955413025458820385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11923386547768067890187693 4471269955413025458820385)
                  ·
                    refine ⟨3353452466559769094115289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4471269955413025458820385 3353452466559769094115289)
                    ·
                      refine ⟨2515089349919826820586467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3353452466559769094115289 2515089349919826820586467)
                      ·
                        rfl

theorem cell23_4898119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 3, 1, 3, 2, 2].length) (baseStart_4898119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4898119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4898119 prefixEnd_4898119 := by exact prefixLift 4898119
  have htrace : WordTrace (prefixWord ++ tailWord_4898119) baseStart_4898119 baseEnd_4898119 := by
    simpa [prefixWord, tailWord_4898119, baseEnd_4898119] using wordTrace_append hprefix tailTrace_4898119
  have hstable : (prefixWord ++ tailWord_4898119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4898119).length < 2 ^ (prefixWord ++ tailWord_4898119).sum := by decide
  have hdescent : baseEnd_4898119 < baseStart_4898119 := by decide
  rcases family_descends (prefixWord ++ tailWord_4898119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4898128 : List Nat := [2, 1, 1, 1, 1, 5, 1, 1, 2, 2, 6]
def baseStart_4898128 : Nat := 118140960795 + 4898128 * 2 ^ 59
def prefixEnd_4898128 : Nat := 4983230072969 + 3 ^ 40 * 4898128 * 2
def baseEnd_4898128 : Nat := 2515093971245717285373925

theorem tailTrace_4898128 : CollatzResearch.WordTrace tailWord_4898128 prefixEnd_4898128 2515093971245717285373925 := by
  unfold tailWord_4898128
  simp only [CollatzResearch.WordTrace]
  refine ⟨89324702399463132253831519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119099603199284176338442025 89324702399463132253831519)
  ·
    refine ⟨133987053599194698380747279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89324702399463132253831519 133987053599194698380747279)
    ·
      refine ⟨200980580398792047571120919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 133987053599194698380747279 200980580398792047571120919)
      ·
        refine ⟨301470870598188071356681379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 200980580398792047571120919 301470870598188071356681379)
        ·
          refine ⟨452206305897282107035022069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 301470870598188071356681379 452206305897282107035022069)
          ·
            refine ⟨42394341177870197534533319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 452206305897282107035022069 42394341177870197534533319)
            ·
              refine ⟨63591511766805296301799979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42394341177870197534533319 63591511766805296301799979)
              ·
                refine ⟨95387267650207944452699969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 63591511766805296301799979 95387267650207944452699969)
                ·
                  refine ⟨71540450737655958339524977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 95387267650207944452699969 71540450737655958339524977)
                  ·
                    refine ⟨53655338053241968754643733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 71540450737655958339524977 53655338053241968754643733)
                    ·
                      refine ⟨2515093971245717285373925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 53655338053241968754643733 2515093971245717285373925)
                      ·
                        rfl

theorem cell23_4898128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 1, 1, 2, 2, 6].length) (baseStart_4898128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4898128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4898128 prefixEnd_4898128 := by exact prefixLift 4898128
  have htrace : WordTrace (prefixWord ++ tailWord_4898128) baseStart_4898128 baseEnd_4898128 := by
    simpa [prefixWord, tailWord_4898128, baseEnd_4898128] using wordTrace_append hprefix tailTrace_4898128
  have hstable : (prefixWord ++ tailWord_4898128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4898128).length < 2 ^ (prefixWord ++ tailWord_4898128).sum := by decide
  have hdescent : baseEnd_4898128 < baseStart_4898128 := by decide
  rcases family_descends (prefixWord ++ tailWord_4898128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4898168 : List Nat := [2, 1, 2, 1, 1, 1, 1, 1, 5, 8]
def baseStart_4898168 : Nat := 118140960795 + 4898168 * 2 ^ 59
def prefixEnd_4898168 : Nat := 4983230072969 + 3 ^ 40 * 4898168 * 2
def baseEnd_4898168 : Nat := 838371503490632376291247

theorem tailTrace_4898168 : CollatzResearch.WordTrace tailWord_4898168 prefixEnd_4898168 838371503490632376291247 := by
  unfold tailWord_4898168
  simp only [CollatzResearch.WordTrace]
  refine ⟨89325431859390675669559579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119100575812520900892746105 89325431859390675669559579)
  ·
    refine ⟨133988147789086013504339369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89325431859390675669559579 133988147789086013504339369)
    ·
      refine ⟨100491110841814510128254527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 133988147789086013504339369 100491110841814510128254527)
      ·
        refine ⟨150736666262721765192381791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100491110841814510128254527 150736666262721765192381791)
        ·
          refine ⟨226104999394082647788572687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 150736666262721765192381791 226104999394082647788572687)
          ·
            refine ⟨339157499091123971682859031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 226104999394082647788572687 339157499091123971682859031)
            ·
              refine ⟨508736248636685957524288547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 339157499091123971682859031 508736248636685957524288547)
              ·
                refine ⟨763104372955028936286432821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 508736248636685957524288547 763104372955028936286432821)
                ·
                  refine ⟨71541034964533962776853077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 763104372955028936286432821 71541034964533962776853077)
                  ·
                    refine ⟨838371503490632376291247, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 71541034964533962776853077 838371503490632376291247)
                    ·
                      rfl

theorem cell23_4898168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 1, 5, 8].length) (baseStart_4898168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4898168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4898168 prefixEnd_4898168 := by exact prefixLift 4898168
  have htrace : WordTrace (prefixWord ++ tailWord_4898168) baseStart_4898168 baseEnd_4898168 := by
    simpa [prefixWord, tailWord_4898168, baseEnd_4898168] using wordTrace_append hprefix tailTrace_4898168
  have hstable : (prefixWord ++ tailWord_4898168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4898168).length < 2 ^ (prefixWord ++ tailWord_4898168).sum := by decide
  have hdescent : baseEnd_4898168 < baseStart_4898168 := by decide
  rcases family_descends (prefixWord ++ tailWord_4898168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4898215 : List Nat := [1, 1, 6, 1, 1, 1, 1, 2, 9]
def baseStart_4898215 : Nat := 118140960795 + 4898215 * 2 ^ 59
def prefixEnd_4898215 : Nat := 4983230072969 + 3 ^ 40 * 4898215 * 2
def baseEnd_4898215 : Nat := 279459849340295382776225

theorem tailTrace_4898215 : CollatzResearch.WordTrace tailWord_4898215 prefixEnd_4898215 279459849340295382776225 := by
  unfold tailWord_4898215
  simp only [CollatzResearch.WordTrace]
  refine ⟨178652577949611078366080099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119101718633074052244053399 178652577949611078366080099)
  ·
    refine ⟨267978866924416617549120149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 178652577949611078366080099 267978866924416617549120149)
    ·
      refine ⟨12561509387082028947615007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 267978866924416617549120149 12561509387082028947615007)
      ·
        refine ⟨18842264080623043421422511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12561509387082028947615007 18842264080623043421422511)
        ·
          refine ⟨28263396120934565132133767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18842264080623043421422511 28263396120934565132133767)
          ·
            refine ⟨42395094181401847698200651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28263396120934565132133767 42395094181401847698200651)
            ·
              refine ⟨63592641272102771547300977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42395094181401847698200651 63592641272102771547300977)
              ·
                refine ⟨47694480954077078660475733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 63592641272102771547300977 47694480954077078660475733)
                ·
                  refine ⟨279459849340295382776225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 47694480954077078660475733 279459849340295382776225)
                  ·
                    rfl

theorem cell23_4898215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 1, 2, 9].length) (baseStart_4898215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4898215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4898215 prefixEnd_4898215 := by exact prefixLift 4898215
  have htrace : WordTrace (prefixWord ++ tailWord_4898215) baseStart_4898215 baseEnd_4898215 := by
    simpa [prefixWord, tailWord_4898215, baseEnd_4898215] using wordTrace_append hprefix tailTrace_4898215
  have hstable : (prefixWord ++ tailWord_4898215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4898215).length < 2 ^ (prefixWord ++ tailWord_4898215).sum := by decide
  have hdescent : baseEnd_4898215 < baseStart_4898215 := by decide
  rcases family_descends (prefixWord ++ tailWord_4898215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4898232 : List Nat := [2, 1, 2, 1, 2, 2, 4, 4, 5]
def baseStart_4898232 : Nat := 118140960795 + 4898232 * 2 ^ 59
def prefixEnd_4898232 : Nat := 4983230072969 + 3 ^ 40 * 4898232 * 2
def baseEnd_4898232 : Nat := 279460819248198319830383

theorem tailTrace_4898232 : CollatzResearch.WordTrace tailWord_4898232 prefixEnd_4898232 279460819248198319830383 := by
  unfold tailWord_4898232
  simp only [CollatzResearch.WordTrace]
  refine ⟨89326598995274745134724475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119102131993699660179632633 89326598995274745134724475)
  ·
    refine ⟨133989898492912117702086713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89326598995274745134724475 133989898492912117702086713)
    ·
      refine ⟨100492423869684088276565035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 133989898492912117702086713 100492423869684088276565035)
      ·
        refine ⟨150738635804526132414847553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100492423869684088276565035 150738635804526132414847553)
        ·
          refine ⟨113053976853394599311135665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 150738635804526132414847553 113053976853394599311135665)
          ·
            refine ⟨84790482640045949483351749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 113053976853394599311135665 84790482640045949483351749)
            ·
              refine ⟨15898215495008615528128453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 84790482640045949483351749 15898215495008615528128453)
              ·
                refine ⟨2980915405314115411524085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15898215495008615528128453 2980915405314115411524085)
                ·
                  refine ⟨279460819248198319830383, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2980915405314115411524085 279460819248198319830383)
                  ·
                    rfl

theorem cell23_4898232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 4, 4, 5].length) (baseStart_4898232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4898232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4898232 prefixEnd_4898232 := by exact prefixLift 4898232
  have htrace : WordTrace (prefixWord ++ tailWord_4898232) baseStart_4898232 baseEnd_4898232 := by
    simpa [prefixWord, tailWord_4898232, baseEnd_4898232] using wordTrace_append hprefix tailTrace_4898232
  have hstable : (prefixWord ++ tailWord_4898232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4898232).length < 2 ^ (prefixWord ++ tailWord_4898232).sum := by decide
  have hdescent : baseEnd_4898232 < baseStart_4898232 := by decide
  rcases family_descends (prefixWord ++ tailWord_4898232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4898295 : List Nat := [1, 1, 3, 1, 1, 1, 1, 4, 2, 4, 4]
def baseStart_4898295 : Nat := 118140960795 + 4898295 * 2 ^ 59
def prefixEnd_4898295 : Nat := 4983230072969 + 3 ^ 40 * 4898295 * 2
def baseEnd_4898295 : Nat := 2515179722515018131985657

theorem tailTrace_4898295 : CollatzResearch.WordTrace tailWord_4898295 prefixEnd_4898295 2515179722515018131985657 := by
  unfold tailWord_4898295
  simp only [CollatzResearch.WordTrace]
  refine ⟨178655495789321252028992339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119103663859547501352661559 178655495789321252028992339)
  ·
    refine ⟨267983243683981878043488509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 178655495789321252028992339 267983243683981878043488509)
    ·
      refine ⟨100493716381493204266308191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 267983243683981878043488509 100493716381493204266308191)
      ·
        refine ⟨150740574572239806399462287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100493716381493204266308191 150740574572239806399462287)
        ·
          refine ⟨226110861858359709599193431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 150740574572239806399462287 226110861858359709599193431)
          ·
            refine ⟨339166292787539564398790147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 226110861858359709599193431 339166292787539564398790147)
            ·
              refine ⟨508749439181309346598185221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 339166292787539564398790147 508749439181309346598185221)
              ·
                refine ⟨95390519846495502487159729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 508749439181309346598185221 95390519846495502487159729)
                ·
                  refine ⟨71542889884871626865369797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 95390519846495502487159729 71542889884871626865369797)
                  ·
                    refine ⟨13414291853413430037256837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 71542889884871626865369797 13414291853413430037256837)
                    ·
                      refine ⟨2515179722515018131985657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13414291853413430037256837 2515179722515018131985657)
                      ·
                        rfl

theorem cell23_4898295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 4, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 4, 2, 4, 4].length) (baseStart_4898295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4898295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4898295 prefixEnd_4898295 := by exact prefixLift 4898295
  have htrace : WordTrace (prefixWord ++ tailWord_4898295) baseStart_4898295 baseEnd_4898295 := by
    simpa [prefixWord, tailWord_4898295, baseEnd_4898295] using wordTrace_append hprefix tailTrace_4898295
  have hstable : (prefixWord ++ tailWord_4898295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4898295).length < 2 ^ (prefixWord ++ tailWord_4898295).sum := by decide
  have hdescent : baseEnd_4898295 < baseStart_4898295 := by decide
  rcases family_descends (prefixWord ++ tailWord_4898295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4898334 : List Nat := [4, 3, 3, 1, 2, 1, 2, 2, 5]
def baseStart_4898334 : Nat := 118140960795 + 4898334 * 2 ^ 59
def prefixEnd_4898334 : Nat := 4983230072969 + 3 ^ 40 * 4898334 * 2
def baseEnd_4898334 : Nat := 279466638695615942155331

theorem tailTrace_4898334 : CollatzResearch.WordTrace tailWord_4898334 prefixEnd_4898334 279466638695615942155331 := by
  unfold tailWord_4898334
  simp only [CollatzResearch.WordTrace]
  refine ⟨22332114779522495211207757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 119104612157453307793108037 22332114779522495211207757)
  ·
    refine ⟨8374543042320935704202909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22332114779522495211207757 8374543042320935704202909)
    ·
      refine ⟨3140453640870350889076091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8374543042320935704202909 3140453640870350889076091)
      ·
        refine ⟨4710680461305526333614137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3140453640870350889076091 4710680461305526333614137)
        ·
          refine ⟨3533010345979144750210603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4710680461305526333614137 3533010345979144750210603)
          ·
            refine ⟨5299515518968717125315905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3533010345979144750210603 5299515518968717125315905)
            ·
              refine ⟨3974636639226537843986929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5299515518968717125315905 3974636639226537843986929)
              ·
                refine ⟨2980977479419903382990197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3974636639226537843986929 2980977479419903382990197)
                ·
                  refine ⟨279466638695615942155331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2980977479419903382990197 279466638695615942155331)
                  ·
                    rfl

theorem cell23_4898334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 2, 1, 2, 2, 5].length) (baseStart_4898334 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4898334 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4898334 prefixEnd_4898334 := by exact prefixLift 4898334
  have htrace : WordTrace (prefixWord ++ tailWord_4898334) baseStart_4898334 baseEnd_4898334 := by
    simpa [prefixWord, tailWord_4898334, baseEnd_4898334] using wordTrace_append hprefix tailTrace_4898334
  have hstable : (prefixWord ++ tailWord_4898334).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4898334).length < 2 ^ (prefixWord ++ tailWord_4898334).sum := by decide
  have hdescent : baseEnd_4898334 < baseStart_4898334 := by decide
  rcases family_descends (prefixWord ++ tailWord_4898334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4898339 : List Nat := [1, 1, 1, 4, 5, 1, 2, 2, 6]
def baseStart_4898339 : Nat := 118140960795 + 4898339 * 2 ^ 59
def prefixEnd_4898339 : Nat := 4983230072969 + 3 ^ 40 * 4898339 * 2
def baseEnd_4898339 : Nat := 279466923962646217759495

theorem tailTrace_4898339 : CollatzResearch.WordTrace tailWord_4898339 prefixEnd_4898339 279466923962646217759495 := by
  unfold tailWord_4898339
  simp only [CollatzResearch.WordTrace]
  refine ⟨178657100601161847543594071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119104733734107898362396047 178657100601161847543594071)
  ·
    refine ⟨267985650901742771315391107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 178657100601161847543594071 267985650901742771315391107)
    ·
      refine ⟨401978476352614156973086661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 267985650901742771315391107 401978476352614156973086661)
      ·
        refine ⟨75370964316115154432453749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 401978476352614156973086661 75370964316115154432453749)
        ·
          refine ⟨7066027904635795728042539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 75370964316115154432453749 7066027904635795728042539)
          ·
            refine ⟨10599041856953693592063809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7066027904635795728042539 10599041856953693592063809)
            ·
              refine ⟨7949281392715270194047857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10599041856953693592063809 7949281392715270194047857)
              ·
                refine ⟨5961961044536452645535893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7949281392715270194047857 5961961044536452645535893)
                ·
                  refine ⟨279466923962646217759495, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5961961044536452645535893 279466923962646217759495)
                  ·
                    rfl

theorem cell23_4898339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 1, 2, 2, 6].length) (baseStart_4898339 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4898339 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4898339 prefixEnd_4898339 := by exact prefixLift 4898339
  have htrace : WordTrace (prefixWord ++ tailWord_4898339) baseStart_4898339 baseEnd_4898339 := by
    simpa [prefixWord, tailWord_4898339, baseEnd_4898339] using wordTrace_append hprefix tailTrace_4898339
  have hstable : (prefixWord ++ tailWord_4898339).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4898339).length < 2 ^ (prefixWord ++ tailWord_4898339).sum := by decide
  have hdescent : baseEnd_4898339 < baseStart_4898339 := by decide
  rcases family_descends (prefixWord ++ tailWord_4898339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4898369 : List Nat := [1, 2, 5, 1, 1, 1, 2, 4, 1, 5]
def baseStart_4898369 : Nat := 118140960795 + 4898369 * 2 ^ 59
def prefixEnd_4898369 : Nat := 4983230072969 + 3 ^ 40 * 4898369 * 2
def baseEnd_4898369 : Nat := 838405906694483614153439

theorem tailTrace_4898369 : CollatzResearch.WordTrace tailWord_4898369 prefixEnd_4898369 838405906694483614153439 := by
  unfold tailWord_4898369
  simp only [CollatzResearch.WordTrace]
  refine ⟨178658194791053162667186161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119105463194035441778124107 178658194791053162667186161)
  ·
    refine ⟨133993646093289872000389621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 178658194791053162667186161 133993646093289872000389621)
    ·
      refine ⟨12561904321245925500036527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 133993646093289872000389621 12561904321245925500036527)
      ·
        refine ⟨18842856481868888250054791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12561904321245925500036527 18842856481868888250054791)
        ·
          refine ⟨28264284722803332375082187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18842856481868888250054791 28264284722803332375082187)
          ·
            refine ⟨42396427084204998562623281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28264284722803332375082187 42396427084204998562623281)
            ·
              refine ⟨31797320313153748921967461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42396427084204998562623281 31797320313153748921967461)
              ·
                refine ⟨5961997558716327922868899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 31797320313153748921967461 5961997558716327922868899)
                ·
                  refine ⟨8942996338074491884303349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5961997558716327922868899 8942996338074491884303349)
                  ·
                    refine ⟨838405906694483614153439, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8942996338074491884303349 838405906694483614153439)
                    ·
                      rfl

theorem cell23_4898369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 2, 4, 1, 5].length) (baseStart_4898369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4898369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4898369 prefixEnd_4898369 := by exact prefixLift 4898369
  have htrace : WordTrace (prefixWord ++ tailWord_4898369) baseStart_4898369 baseEnd_4898369 := by
    simpa [prefixWord, tailWord_4898369, baseEnd_4898369] using wordTrace_append hprefix tailTrace_4898369
  have hstable : (prefixWord ++ tailWord_4898369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4898369).length < 2 ^ (prefixWord ++ tailWord_4898369).sum := by decide
  have hdescent : baseEnd_4898369 < baseStart_4898369 := by decide
  rcases family_descends (prefixWord ++ tailWord_4898369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
