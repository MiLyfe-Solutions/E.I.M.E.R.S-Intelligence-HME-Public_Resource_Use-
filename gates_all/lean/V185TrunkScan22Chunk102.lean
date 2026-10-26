import V185TrunkScan22Chunk101

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_915953 : List Nat := [1, 2, 2, 2, 3, 1, 1, 1, 1, 8]
def baseStart_915953 : Nat := 118140960795 + 915953 * 2 ^ 59
def prefixEnd_915953 : Nat := 4983230072969 + 3 ^ 40 * 915953 * 2
def baseEnd_915953 : Nat := 313549430618506708916743

theorem tailTrace_915953 : CollatzResearch.WordTrace tailWord_915953 prefixEnd_915953 313549430618506708916743 := by
  unfold tailWord_915953
  simp only [CollatzResearch.WordTrace]
  refine ⟨33407550450666188163296513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22271700300444125442197675 33407550450666188163296513)
  ·
    refine ⟨25055662837999641122472385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33407550450666188163296513 25055662837999641122472385)
    ·
      refine ⟨18791747128499730841854289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25055662837999641122472385 18791747128499730841854289)
      ·
        refine ⟨14093810346374798131390717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18791747128499730841854289 14093810346374798131390717)
        ·
          refine ⟨5285178879890549299271519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14093810346374798131390717 5285178879890549299271519)
          ·
            refine ⟨7927768319835823948907279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5285178879890549299271519 7927768319835823948907279)
            ·
              refine ⟨11891652479753735923360919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7927768319835823948907279 11891652479753735923360919)
              ·
                refine ⟨17837478719630603885041379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11891652479753735923360919 17837478719630603885041379)
                ·
                  refine ⟨26756218079445905827562069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17837478719630603885041379 26756218079445905827562069)
                  ·
                    refine ⟨313549430618506708916743, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 26756218079445905827562069 313549430618506708916743)
                    ·
                      rfl

theorem cell22_915953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 1, 1, 1, 8].length) (baseStart_915953 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_915953 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_915953 prefixEnd_915953 := by exact prefixLift 915953
  have htrace : WordTrace (prefixWord ++ tailWord_915953) baseStart_915953 baseEnd_915953 := by
    simpa [prefixWord, tailWord_915953, baseEnd_915953] using wordTrace_append hprefix tailTrace_915953
  have hstable : (prefixWord ++ tailWord_915953).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_915953).length < 2 ^ (prefixWord ++ tailWord_915953).sum := by decide
  have hdescent : baseEnd_915953 < baseStart_915953 := by decide
  rcases family_descends (prefixWord ++ tailWord_915953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_915955 : List Nat := [1, 1, 1, 2, 2, 2, 4, 3, 3, 3]
def baseStart_915955 : Nat := 118140960795 + 915955 * 2 ^ 59
def prefixEnd_915955 : Nat := 4983230072969 + 3 ^ 40 * 915955 * 2
def baseEnd_915955 : Nat := 313550115259379370366737

theorem tailTrace_915955 : CollatzResearch.WordTrace tailWord_915955 prefixEnd_915955 313550115259379370366737 := by
  unfold tailWord_915955
  simp only [CollatzResearch.WordTrace]
  refine ⟨33407623396658942504869319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22271748931105961669912879 33407623396658942504869319)
  ·
    refine ⟨50111435094988413757303979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33407623396658942504869319 50111435094988413757303979)
    ·
      refine ⟨75167152642482620635955969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50111435094988413757303979 75167152642482620635955969)
      ·
        refine ⟨56375364481861965476966977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75167152642482620635955969 56375364481861965476966977)
        ·
          refine ⟨42281523361396474107725233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56375364481861965476966977 42281523361396474107725233)
          ·
            refine ⟨31711142521047355580793925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42281523361396474107725233 31711142521047355580793925)
            ·
              refine ⟨5945839222696379171398861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31711142521047355580793925 5945839222696379171398861)
              ·
                refine ⟨2229689708511142189274573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5945839222696379171398861 2229689708511142189274573)
                ·
                  refine ⟨836133640691678320977965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2229689708511142189274573 836133640691678320977965)
                  ·
                    refine ⟨313550115259379370366737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 836133640691678320977965 313550115259379370366737)
                    ·
                      rfl

theorem cell22_915955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 4, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 4, 3, 3, 3].length) (baseStart_915955 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_915955 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_915955 prefixEnd_915955 := by exact prefixLift 915955
  have htrace : WordTrace (prefixWord ++ tailWord_915955) baseStart_915955 baseEnd_915955 := by
    simpa [prefixWord, tailWord_915955, baseEnd_915955] using wordTrace_append hprefix tailTrace_915955
  have hstable : (prefixWord ++ tailWord_915955).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_915955).length < 2 ^ (prefixWord ++ tailWord_915955).sum := by decide
  have hdescent : baseEnd_915955 < baseStart_915955 := by decide
  rcases family_descends (prefixWord ++ tailWord_915955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_915972 : List Nat := [2, 3, 2, 3, 1, 1, 1, 1, 5, 3]
def baseStart_915972 : Nat := 118140960795 + 915972 * 2 ^ 59
def prefixEnd_915972 : Nat := 4983230072969 + 3 ^ 40 * 915972 * 2
def baseEnd_915972 : Nat := 313555934706796992691685

theorem tailTrace_915972 : CollatzResearch.WordTrace tailWord_915972 prefixEnd_915972 313555934706796992691685 := by
  unfold tailWord_915972
  simp only [CollatzResearch.WordTrace]
  refine ⟨16704121718798677204119085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22272162291731569605492113 16704121718798677204119085)
  ·
    refine ⟨6264045644549503951544657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16704121718798677204119085 6264045644549503951544657)
    ·
      refine ⟨4698034233412127963658493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6264045644549503951544657 4698034233412127963658493)
      ·
        refine ⟨1761762837529547986371935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4698034233412127963658493 1761762837529547986371935)
        ·
          refine ⟨2642644256294321979557903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1761762837529547986371935 2642644256294321979557903)
          ·
            refine ⟨3963966384441482969336855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2642644256294321979557903 3963966384441482969336855)
            ·
              refine ⟨5945949576662224454005283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3963966384441482969336855 5945949576662224454005283)
              ·
                refine ⟨8918924364993336681007925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5945949576662224454005283 8918924364993336681007925)
                ·
                  refine ⟨836149159218125313844493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 8918924364993336681007925 836149159218125313844493)
                  ·
                    refine ⟨313555934706796992691685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 836149159218125313844493 313555934706796992691685)
                    ·
                      rfl

theorem cell22_915972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 1, 1, 5, 3].length) (baseStart_915972 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_915972 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_915972 prefixEnd_915972 := by exact prefixLift 915972
  have htrace : WordTrace (prefixWord ++ tailWord_915972) baseStart_915972 baseEnd_915972 := by
    simpa [prefixWord, tailWord_915972, baseEnd_915972] using wordTrace_append hprefix tailTrace_915972
  have hstable : (prefixWord ++ tailWord_915972).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_915972).length < 2 ^ (prefixWord ++ tailWord_915972).sum := by decide
  have hdescent : baseEnd_915972 < baseStart_915972 := by decide
  rcases family_descends (prefixWord ++ tailWord_915972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_915983 : List Nat := [1, 1, 2, 1, 1, 1, 2, 4, 4, 5]
def baseStart_915983 : Nat := 118140960795 + 915983 * 2 ^ 59
def prefixEnd_915983 : Nat := 4983230072969 + 3 ^ 40 * 915983 * 2
def baseEnd_915983 : Nat := 313559700231596630666651

theorem tailTrace_915983 : CollatzResearch.WordTrace tailWord_915983 prefixEnd_915983 313559700231596630666651 := by
  unfold tailWord_915983
  simp only [CollatzResearch.WordTrace]
  refine ⟨33408644640557503286888603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22272429760371668857925735 33408644640557503286888603)
  ·
    refine ⟨50112966960836254930332905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33408644640557503286888603 50112966960836254930332905)
    ·
      refine ⟨37584725220627191197749679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50112966960836254930332905 37584725220627191197749679)
      ·
        refine ⟨56377087830940786796624519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37584725220627191197749679 56377087830940786796624519)
        ·
          refine ⟨84565631746411180194936779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56377087830940786796624519 84565631746411180194936779)
          ·
            refine ⟨126848447619616770292405169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84565631746411180194936779 126848447619616770292405169)
            ·
              refine ⟨95136335714712577719303877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 126848447619616770292405169 95136335714712577719303877)
              ·
                refine ⟨17838062946508608322369477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 95136335714712577719303877 17838062946508608322369477)
                ·
                  refine ⟨3344636802470364060444277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17838062946508608322369477 3344636802470364060444277)
                  ·
                    refine ⟨313559700231596630666651, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3344636802470364060444277 313559700231596630666651)
                    ·
                      rfl

theorem cell22_915983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 4, 4, 5].length) (baseStart_915983 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_915983 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_915983 prefixEnd_915983 := by exact prefixLift 915983
  have htrace : WordTrace (prefixWord ++ tailWord_915983) baseStart_915983 baseEnd_915983 := by
    simpa [prefixWord, tailWord_915983, baseEnd_915983] using wordTrace_append hprefix tailTrace_915983
  have hstable : (prefixWord ++ tailWord_915983).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_915983).length < 2 ^ (prefixWord ++ tailWord_915983).sum := by decide
  have hdescent : baseEnd_915983 < baseStart_915983 := by decide
  rcases family_descends (prefixWord ++ tailWord_915983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_915989 : List Nat := [1, 3, 2, 1, 3, 1, 4, 3, 1, 3]
def baseStart_915989 : Nat := 118140960795 + 915989 * 2 ^ 59
def prefixEnd_915989 : Nat := 4983230072969 + 3 ^ 40 * 915989 * 2
def baseEnd_915989 : Nat := 313561754154214615016633

theorem tailTrace_915989 : CollatzResearch.WordTrace tailWord_915989 prefixEnd_915989 313561754154214615016633 := by
  unfold tailWord_915989
  simp only [CollatzResearch.WordTrace]
  refine ⟨33408863478535766311607021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22272575652357177541071347 33408863478535766311607021)
  ·
    refine ⟨12528323804450912366852633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33408863478535766311607021 12528323804450912366852633)
    ·
      refine ⟨9396242853338184275139475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12528323804450912366852633 9396242853338184275139475)
      ·
        refine ⟨14094364280007276412709213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9396242853338184275139475 14094364280007276412709213)
        ·
          refine ⟨5285386605002728654765955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14094364280007276412709213 5285386605002728654765955)
          ·
            refine ⟨7928079907504092982148933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5285386605002728654765955 7928079907504092982148933)
            ·
              refine ⟨1486514982657017434152925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7928079907504092982148933 1486514982657017434152925)
              ·
                refine ⟨557443118496381537807347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1486514982657017434152925 557443118496381537807347)
                ·
                  refine ⟨836164677744572306711021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 557443118496381537807347 836164677744572306711021)
                  ·
                    refine ⟨313561754154214615016633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 836164677744572306711021 313561754154214615016633)
                    ·
                      rfl

theorem cell22_915989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 4, 3, 1, 3].length) (baseStart_915989 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_915989 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_915989 prefixEnd_915989 := by exact prefixLift 915989
  have htrace : WordTrace (prefixWord ++ tailWord_915989) baseStart_915989 baseEnd_915989 := by
    simpa [prefixWord, tailWord_915989, baseEnd_915989] using wordTrace_append hprefix tailTrace_915989
  have hstable : (prefixWord ++ tailWord_915989).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_915989).length < 2 ^ (prefixWord ++ tailWord_915989).sum := by decide
  have hdescent : baseEnd_915989 < baseStart_915989 := by decide
  rcases family_descends (prefixWord ++ tailWord_915989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_916047 : List Nat := [1, 1, 2, 1, 1, 2, 7, 3, 4]
def baseStart_916047 : Nat := 118140960795 + 916047 * 2 ^ 59
def prefixEnd_916047 : Nat := 4983230072969 + 3 ^ 40 * 916047 * 2
def baseEnd_916047 : Nat := 104527202913173932355485

theorem tailTrace_916047 : CollatzResearch.WordTrace tailWord_916047 prefixEnd_916047 104527202913173932355485 := by
  unfold tailWord_916047
  simp only [CollatzResearch.WordTrace]
  refine ⟨33410978912325642217218395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22273985941550428144812263 33410978912325642217218395)
  ·
    refine ⟨50116468368488463325827593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33410978912325642217218395 50116468368488463325827593)
    ·
      refine ⟨37587351276366347494370695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50116468368488463325827593 37587351276366347494370695)
      ·
        refine ⟨56381026914549521241556043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37587351276366347494370695 56381026914549521241556043)
        ·
          refine ⟨84571540371824281862334065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56381026914549521241556043 84571540371824281862334065)
          ·
            refine ⟨63428655278868211396750549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84571540371824281862334065 63428655278868211396750549)
            ·
              refine ⟨1486609108098473704611341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 63428655278868211396750549 1486609108098473704611341)
              ·
                refine ⟨557478415536927639229253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1486609108098473704611341 557478415536927639229253)
                ·
                  refine ⟨104527202913173932355485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 557478415536927639229253 104527202913173932355485)
                  ·
                    rfl

theorem cell22_916047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 7, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 7, 3, 4].length) (baseStart_916047 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_916047 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_916047 prefixEnd_916047 := by exact prefixLift 916047
  have htrace : WordTrace (prefixWord ++ tailWord_916047) baseStart_916047 baseEnd_916047 := by
    simpa [prefixWord, tailWord_916047, baseEnd_916047] using wordTrace_append hprefix tailTrace_916047
  have hstable : (prefixWord ++ tailWord_916047).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_916047).length < 2 ^ (prefixWord ++ tailWord_916047).sum := by decide
  have hdescent : baseEnd_916047 < baseStart_916047 := by decide
  rcases family_descends (prefixWord ++ tailWord_916047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_916079 : List Nat := [1, 1, 2, 1, 3, 2, 6, 1, 2, 3]
def baseStart_916079 : Nat := 118140960795 + 916079 * 2 ^ 59
def prefixEnd_916079 : Nat := 4983230072969 + 3 ^ 40 * 916079 * 2
def baseEnd_916079 : Nat := 313592562993484380266357

theorem tailTrace_916079 : CollatzResearch.WordTrace tailWord_916079 prefixEnd_916079 313592562993484380266357 := by
  unfold tailWord_916079
  simp only [CollatzResearch.WordTrace]
  refine ⟨33412146048209711682383291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22274764032139807788255527 33412146048209711682383291)
  ·
    refine ⟨50118219072314567523574937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33412146048209711682383291 50118219072314567523574937)
    ·
      refine ⟨37588664304235925642681203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50118219072314567523574937 37588664304235925642681203)
      ·
        refine ⟨56382996456353888464021805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37588664304235925642681203 56382996456353888464021805)
        ·
          refine ⟨21143623671132708174008177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56382996456353888464021805 21143623671132708174008177)
          ·
            refine ⟨15857717753349531130506133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21143623671132708174008177 15857717753349531130506133)
            ·
              refine ⟨743330519688259271742475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 15857717753349531130506133 743330519688259271742475)
              ·
                refine ⟨1114995779532388907613713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 743330519688259271742475 1114995779532388907613713)
                ·
                  refine ⟨836246834649291680710285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1114995779532388907613713 836246834649291680710285)
                  ·
                    refine ⟨313592562993484380266357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 836246834649291680710285 313592562993484380266357)
                    ·
                      rfl

theorem cell22_916079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 6, 1, 2, 3].length) (baseStart_916079 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_916079 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_916079 prefixEnd_916079 := by exact prefixLift 916079
  have htrace : WordTrace (prefixWord ++ tailWord_916079) baseStart_916079 baseEnd_916079 := by
    simpa [prefixWord, tailWord_916079, baseEnd_916079] using wordTrace_append hprefix tailTrace_916079
  have hstable : (prefixWord ++ tailWord_916079).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_916079).length < 2 ^ (prefixWord ++ tailWord_916079).sum := by decide
  have hdescent : baseEnd_916079 < baseStart_916079 := by decide
  rcases family_descends (prefixWord ++ tailWord_916079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_916214 : List Nat := [5, 1, 1, 1, 1, 2, 1, 1, 6, 3]
def baseStart_916214 : Nat := 118140960795 + 916214 * 2 ^ 59
def prefixEnd_916214 : Nat := 4983230072969 + 3 ^ 40 * 916214 * 2
def baseEnd_916214 : Nat := 313638776252389028140943

theorem tailTrace_916214 : CollatzResearch.WordTrace tailWord_916214 prefixEnd_916214 313638776252389028140943 := by
  unfold tailWord_916214
  simp only [CollatzResearch.WordTrace]
  refine ⟨2088566868920039358659231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 22278046601813753159031797 2088566868920039358659231)
  ·
    refine ⟨3132850303380059037988847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2088566868920039358659231 3132850303380059037988847)
    ·
      refine ⟨4699275455070088556983271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3132850303380059037988847 4699275455070088556983271)
      ·
        refine ⟨7048913182605132835474907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4699275455070088556983271 7048913182605132835474907)
        ·
          refine ⟨10573369773907699253212361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7048913182605132835474907 10573369773907699253212361)
          ·
            refine ⟨7930027330430774439909271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10573369773907699253212361 7930027330430774439909271)
            ·
              refine ⟨11895040995646161659863907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7930027330430774439909271 11895040995646161659863907)
              ·
                refine ⟨17842561493469242489795861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11895040995646161659863907 17842561493469242489795861)
                ·
                  refine ⟨836370070006370741709181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 17842561493469242489795861 836370070006370741709181)
                  ·
                    refine ⟨313638776252389028140943, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 836370070006370741709181 313638776252389028140943)
                    ·
                      rfl

theorem cell22_916214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 1, 1, 6, 3].length) (baseStart_916214 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_916214 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_916214 prefixEnd_916214 := by exact prefixLift 916214
  have htrace : WordTrace (prefixWord ++ tailWord_916214) baseStart_916214 baseEnd_916214 := by
    simpa [prefixWord, tailWord_916214, baseEnd_916214] using wordTrace_append hprefix tailTrace_916214
  have hstable : (prefixWord ++ tailWord_916214).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_916214).length < 2 ^ (prefixWord ++ tailWord_916214).sum := by decide
  have hdescent : baseEnd_916214 < baseStart_916214 := by decide
  rcases family_descends (prefixWord ++ tailWord_916214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_916319 : List Nat := [1, 1, 2, 3, 1, 3, 2, 4, 1, 4]
def baseStart_916319 : Nat := 118140960795 + 916319 * 2 ^ 59
def prefixEnd_916319 : Nat := 4983230072969 + 3 ^ 40 * 916319 * 2
def baseEnd_916319 : Nat := 313674719898203754265621

theorem tailTrace_916319 : CollatzResearch.WordTrace tailWord_916319 prefixEnd_916319 313674719898203754265621 := by
  unfold tailWord_916319
  simp only [CollatzResearch.WordTrace]
  refine ⟨33420899567340232671120011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22280599711560155114080007 33420899567340232671120011)
  ·
    refine ⟨50131349351010349006680017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33420899567340232671120011 50131349351010349006680017)
    ·
      refine ⟨37598512013257761755010013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50131349351010349006680017 37598512013257761755010013)
      ·
        refine ⟨14099442004971660658128755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37598512013257761755010013 14099442004971660658128755)
        ·
          refine ⟨21149163007457490987193133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14099442004971660658128755 21149163007457490987193133)
          ·
            refine ⟨7930936127796559120197425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21149163007457490987193133 7930936127796559120197425)
            ·
              refine ⟨5948202095847419340148069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7930936127796559120197425 5948202095847419340148069)
              ·
                refine ⟨1115287892971391126277763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5948202095847419340148069 1115287892971391126277763)
                ·
                  refine ⟨1672931839457086689416645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1115287892971391126277763 1672931839457086689416645)
                  ·
                    refine ⟨313674719898203754265621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1672931839457086689416645 313674719898203754265621)
                    ·
                      rfl

theorem cell22_916319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 2, 4, 1, 4].length) (baseStart_916319 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_916319 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_916319 prefixEnd_916319 := by exact prefixLift 916319
  have htrace : WordTrace (prefixWord ++ tailWord_916319) baseStart_916319 baseEnd_916319 := by
    simpa [prefixWord, tailWord_916319, baseEnd_916319] using wordTrace_append hprefix tailTrace_916319
  have hstable : (prefixWord ++ tailWord_916319).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_916319).length < 2 ^ (prefixWord ++ tailWord_916319).sum := by decide
  have hdescent : baseEnd_916319 < baseStart_916319 := by decide
  rcases family_descends (prefixWord ++ tailWord_916319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_916336 : List Nat := [2, 1, 1, 1, 4, 1, 6, 1, 1, 4]
def baseStart_916336 : Nat := 118140960795 + 916336 * 2 ^ 59
def prefixEnd_916336 : Nat := 4983230072969 + 3 ^ 40 * 916336 * 2
def baseEnd_916336 : Nat := 313680539345621376590569

theorem tailTrace_916336 : CollatzResearch.WordTrace tailWord_916336 prefixEnd_916336 313680539345621376590569 := by
  unfold tailWord_916336
  simp only [CollatzResearch.WordTrace]
  refine ⟨16710759804139322287244431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22281013072185763049659241 16710759804139322287244431)
  ·
    refine ⟨25066139706208983430866647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16710759804139322287244431 25066139706208983430866647)
    ·
      refine ⟨37599209559313475146299971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25066139706208983430866647 37599209559313475146299971)
      ·
        refine ⟨56398814338970212719449957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37599209559313475146299971 56398814338970212719449957)
        ·
          refine ⟨10574777688556914884896867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 56398814338970212719449957 10574777688556914884896867)
          ·
            refine ⟨15862166532835372327345301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10574777688556914884896867 15862166532835372327345301)
            ·
              refine ⟨743539056226658077844311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 15862166532835372327345301 743539056226658077844311)
              ·
                refine ⟨1115308584339987116766467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 743539056226658077844311 1115308584339987116766467)
                ·
                  refine ⟨1672962876509980675149701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1115308584339987116766467 1672962876509980675149701)
                  ·
                    refine ⟨313680539345621376590569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1672962876509980675149701 313680539345621376590569)
                    ·
                      rfl

theorem cell22_916336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 6, 1, 1, 4].length) (baseStart_916336 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_916336 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_916336 prefixEnd_916336 := by exact prefixLift 916336
  have htrace : WordTrace (prefixWord ++ tailWord_916336) baseStart_916336 baseEnd_916336 := by
    simpa [prefixWord, tailWord_916336, baseEnd_916336] using wordTrace_append hprefix tailTrace_916336
  have hstable : (prefixWord ++ tailWord_916336).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_916336).length < 2 ^ (prefixWord ++ tailWord_916336).sum := by decide
  have hdescent : baseEnd_916336 < baseStart_916336 := by decide
  rcases family_descends (prefixWord ++ tailWord_916336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_916377 : List Nat := [1, 2, 1, 2, 1, 3, 1, 1, 1, 9]
def baseStart_916377 : Nat := 118140960795 + 916377 * 2 ^ 59
def prefixEnd_916377 : Nat := 4983230072969 + 3 ^ 40 * 916377 * 2
def baseEnd_916377 : Nat := 313694574483510936315443

theorem tailTrace_916377 : CollatzResearch.WordTrace tailWord_916377 prefixEnd_916377 313694574483510936315443 := by
  unfold tailWord_916377
  simp only [CollatzResearch.WordTrace]
  refine ⟨33423015001130108576731385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22282010000753405717820923 33423015001130108576731385)
  ·
    refine ⟨25067261250847581432548539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33423015001130108576731385 25067261250847581432548539)
    ·
      refine ⟨37600891876271372148822809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25067261250847581432548539 37600891876271372148822809)
      ·
        refine ⟨28200668907203529111617107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37600891876271372148822809 28200668907203529111617107)
        ·
          refine ⟨42301003360805293667425661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28200668907203529111617107 42301003360805293667425661)
          ·
            refine ⟨15862876260301985125284623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42301003360805293667425661 15862876260301985125284623)
            ·
              refine ⟨23794314390452977687926935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15862876260301985125284623 23794314390452977687926935)
              ·
                refine ⟨35691471585679466531890403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23794314390452977687926935 35691471585679466531890403)
                ·
                  refine ⟨53537207378519199797835605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35691471585679466531890403 53537207378519199797835605)
                  ·
                    refine ⟨313694574483510936315443, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 53537207378519199797835605 313694574483510936315443)
                    ·
                      rfl

theorem cell22_916377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 1, 1, 9].length) (baseStart_916377 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_916377 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_916377 prefixEnd_916377 := by exact prefixLift 916377
  have htrace : WordTrace (prefixWord ++ tailWord_916377) baseStart_916377 baseEnd_916377 := by
    simpa [prefixWord, tailWord_916377, baseEnd_916377] using wordTrace_append hprefix tailTrace_916377
  have hstable : (prefixWord ++ tailWord_916377).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_916377).length < 2 ^ (prefixWord ++ tailWord_916377).sum := by decide
  have hdescent : baseEnd_916377 < baseStart_916377 := by decide
  rcases family_descends (prefixWord ++ tailWord_916377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_916501 : List Nat := [1, 3, 2, 1, 4, 1, 2, 2, 1, 5]
def baseStart_916501 : Nat := 118140960795 + 916501 * 2 ^ 59
def prefixEnd_916501 : Nat := 4983230072969 + 3 ^ 40 * 916501 * 2
def baseEnd_916501 : Nat := 313737022217615946215063

theorem tailTrace_916501 : CollatzResearch.WordTrace tailWord_916501 prefixEnd_916501 313737022217615946215063 := by
  unfold tailWord_916501
  simp only [CollatzResearch.WordTrace]
  refine ⟨33427537652680877754245357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22285025101787251836163571 33427537652680877754245357)
  ·
    refine ⟨12535326619755329157842009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33427537652680877754245357 12535326619755329157842009)
    ·
      refine ⟨9401494964816496868381507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12535326619755329157842009 9401494964816496868381507)
      ·
        refine ⟨14102242447224745302572261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9401494964816496868381507 14102242447224745302572261)
        ·
          refine ⟨2644170458854639744232299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14102242447224745302572261 2644170458854639744232299)
          ·
            refine ⟨3966255688281959616348449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2644170458854639744232299 3966255688281959616348449)
            ·
              refine ⟨2974691766211469712261337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3966255688281959616348449 2974691766211469712261337)
              ·
                refine ⟨2231018824658602284196003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2974691766211469712261337 2231018824658602284196003)
                ·
                  refine ⟨3346528236987903426294005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2231018824658602284196003 3346528236987903426294005)
                  ·
                    refine ⟨313737022217615946215063, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3346528236987903426294005 313737022217615946215063)
                    ·
                      rfl

theorem cell22_916501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 2, 2, 1, 5].length) (baseStart_916501 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_916501 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_916501 prefixEnd_916501 := by exact prefixLift 916501
  have htrace : WordTrace (prefixWord ++ tailWord_916501) baseStart_916501 baseEnd_916501 := by
    simpa [prefixWord, tailWord_916501, baseEnd_916501] using wordTrace_append hprefix tailTrace_916501
  have hstable : (prefixWord ++ tailWord_916501).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_916501).length < 2 ^ (prefixWord ++ tailWord_916501).sum := by decide
  have hdescent : baseEnd_916501 < baseStart_916501 := by decide
  rcases family_descends (prefixWord ++ tailWord_916501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_916503 : List Nat := [1, 1, 3, 5, 1, 1, 1, 5, 4]
def baseStart_916503 : Nat := 118140960795 + 916503 * 2 ^ 59
def prefixEnd_916503 : Nat := 4983230072969 + 3 ^ 40 * 916503 * 2
def baseEnd_916503 : Nat := 104579235619496202555019

theorem tailTrace_916503 : CollatzResearch.WordTrace tailWord_916503 prefixEnd_916503 104579235619496202555019 := by
  unfold tailWord_916503
  simp only [CollatzResearch.WordTrace]
  refine ⟨33427610598673632095818163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22285073732449088063878775 33427610598673632095818163)
  ·
    refine ⟨50141415898010448143727245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33427610598673632095818163 50141415898010448143727245)
    ·
      refine ⟨18803030961753918053897717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50141415898010448143727245 18803030961753918053897717)
      ·
        refine ⟨1762784152664429817552911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 18803030961753918053897717 1762784152664429817552911)
        ·
          refine ⟨2644176228996644726329367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1762784152664429817552911 2644176228996644726329367)
          ·
            refine ⟨3966264343494967089494051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2644176228996644726329367 3966264343494967089494051)
            ·
              refine ⟨5949396515242450634241077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3966264343494967089494051 5949396515242450634241077)
              ·
                refine ⟨557755923303979746960101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5949396515242450634241077 557755923303979746960101)
                ·
                  refine ⟨104579235619496202555019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 557755923303979746960101 104579235619496202555019)
                  ·
                    rfl

theorem cell22_916503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 1, 5, 4].length) (baseStart_916503 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_916503 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_916503 prefixEnd_916503 := by exact prefixLift 916503
  have htrace : WordTrace (prefixWord ++ tailWord_916503) baseStart_916503 baseEnd_916503 := by
    simpa [prefixWord, tailWord_916503, baseEnd_916503] using wordTrace_append hprefix tailTrace_916503
  have hstable : (prefixWord ++ tailWord_916503).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_916503).length < 2 ^ (prefixWord ++ tailWord_916503).sum := by decide
  have hdescent : baseEnd_916503 < baseStart_916503 := by decide
  rcases family_descends (prefixWord ++ tailWord_916503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_916576 : List Nat := [2, 1, 1, 3, 2, 2, 2, 4, 5]
def baseStart_916576 : Nat := 118140960795 + 916576 * 2 ^ 59
def prefixEnd_916576 : Nat := 4983230072969 + 3 ^ 40 * 916576 * 2
def baseEnd_916576 : Nat := 104587565416780250196611

theorem tailTrace_916576 : CollatzResearch.WordTrace tailWord_916576 prefixEnd_916576 104587565416780250196611 := by
  unfold tailWord_916576
  simp only [CollatzResearch.WordTrace]
  refine ⟨16715136563704582781612791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22286848751606110375483721 16715136563704582781612791)
  ·
    refine ⟨25072704845556874172419187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16715136563704582781612791 25072704845556874172419187)
    ·
      refine ⟨37609057268335311258628781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25072704845556874172419187 37609057268335311258628781)
      ·
        refine ⟨14103396475625741721985793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37609057268335311258628781 14103396475625741721985793)
        ·
          refine ⟨10577547356719306291489345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14103396475625741721985793 10577547356719306291489345)
          ·
            refine ⟨7933160517539479718617009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10577547356719306291489345 7933160517539479718617009)
            ·
              refine ⟨5949870388154609788962757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7933160517539479718617009 5949870388154609788962757)
              ·
                refine ⟨1115600697778989335430517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5949870388154609788962757 1115600697778989335430517)
                ·
                  refine ⟨104587565416780250196611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1115600697778989335430517 104587565416780250196611)
                  ·
                    rfl

theorem cell22_916576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 2, 4, 5].length) (baseStart_916576 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_916576 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_916576 prefixEnd_916576 := by exact prefixLift 916576
  have htrace : WordTrace (prefixWord ++ tailWord_916576) baseStart_916576 baseEnd_916576 := by
    simpa [prefixWord, tailWord_916576, baseEnd_916576] using wordTrace_append hprefix tailTrace_916576
  have hstable : (prefixWord ++ tailWord_916576).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_916576).length < 2 ^ (prefixWord ++ tailWord_916576).sum := by decide
  have hdescent : baseEnd_916576 < baseStart_916576 := by decide
  rcases family_descends (prefixWord ++ tailWord_916576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_916668 : List Nat := [2, 2, 2, 3, 2, 2, 1, 1, 1, 6]
def baseStart_916668 : Nat := 118140960795 + 916668 * 2 ^ 59
def prefixEnd_916668 : Nat := 4983230072969 + 3 ^ 40 * 916668 * 2
def baseEnd_916668 : Nat := 313794189730483177289551

theorem tailTrace_916668 : CollatzResearch.WordTrace tailWord_916668 prefixEnd_916668 313794189730483177289551 := by
  unfold tailWord_916668
  simp only [CollatzResearch.WordTrace]
  refine ⟨16716814321537932637787329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22289085762050576850383105 16716814321537932637787329)
  ·
    refine ⟨12537610741153449478340497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16716814321537932637787329 12537610741153449478340497)
    ·
      refine ⟨9403208055865087108755373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12537610741153449478340497 9403208055865087108755373)
      ·
        refine ⟨3526203020949407665783265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9403208055865087108755373 3526203020949407665783265)
        ·
          refine ⟨2644652265712055749337449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3526203020949407665783265 2644652265712055749337449)
          ·
            refine ⟨1983489199284041812003087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2644652265712055749337449 1983489199284041812003087)
            ·
              refine ⟨2975233798926062718004631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1983489199284041812003087 2975233798926062718004631)
              ·
                refine ⟨4462850698389094077006947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2975233798926062718004631 4462850698389094077006947)
                ·
                  refine ⟨6694276047583641115510421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4462850698389094077006947 6694276047583641115510421)
                  ·
                    refine ⟨313794189730483177289551, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6694276047583641115510421 313794189730483177289551)
                    ·
                      rfl

theorem cell22_916668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 2, 1, 1, 1, 6].length) (baseStart_916668 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_916668 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_916668 prefixEnd_916668 := by exact prefixLift 916668
  have htrace : WordTrace (prefixWord ++ tailWord_916668) baseStart_916668 baseEnd_916668 := by
    simpa [prefixWord, tailWord_916668, baseEnd_916668] using wordTrace_append hprefix tailTrace_916668
  have hstable : (prefixWord ++ tailWord_916668).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_916668).length < 2 ^ (prefixWord ++ tailWord_916668).sum := by decide
  have hdescent : baseEnd_916668 < baseStart_916668 := by decide
  rcases family_descends (prefixWord ++ tailWord_916668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_916674 : List Nat := [3, 5, 1, 1, 2, 1, 1, 3, 1, 4]
def baseStart_916674 : Nat := 118140960795 + 916674 * 2 ^ 59
def prefixEnd_916674 : Nat := 4983230072969 + 3 ^ 40 * 916674 * 2
def baseEnd_916674 : Nat := 313796243653101161639533

theorem tailTrace_916674 : CollatzResearch.WordTrace tailWord_916674 prefixEnd_916674 313796243653101161639533 := by
  unfold tailWord_916674
  simp only [CollatzResearch.WordTrace]
  refine ⟨8358461870263532075073269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22289231654036085533528717 8358461870263532075073269)
  ·
    refine ⟨783605800337206132038119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 8358461870263532075073269 783605800337206132038119)
    ·
      refine ⟨1175408700505809198057179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 783605800337206132038119 1175408700505809198057179)
      ·
        refine ⟨1763113050758713797085769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1175408700505809198057179 1763113050758713797085769)
        ·
          refine ⟨1322334788069035347814327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1763113050758713797085769 1322334788069035347814327)
          ·
            refine ⟨1983502182103553021721491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1322334788069035347814327 1983502182103553021721491)
            ·
              refine ⟨2975253273155329532582237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1983502182103553021721491 2975253273155329532582237)
              ·
                refine ⟨1115719977433248574718339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2975253273155329532582237 1115719977433248574718339)
                ·
                  refine ⟨1673579966149872862077509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1115719977433248574718339 1673579966149872862077509)
                  ·
                    refine ⟨313796243653101161639533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1673579966149872862077509 313796243653101161639533)
                    ·
                      rfl

theorem cell22_916674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 1, 1, 3, 1, 4].length) (baseStart_916674 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_916674 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_916674 prefixEnd_916674 := by exact prefixLift 916674
  have htrace : WordTrace (prefixWord ++ tailWord_916674) baseStart_916674 baseEnd_916674 := by
    simpa [prefixWord, tailWord_916674, baseEnd_916674] using wordTrace_append hprefix tailTrace_916674
  have hstable : (prefixWord ++ tailWord_916674).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_916674).length < 2 ^ (prefixWord ++ tailWord_916674).sum := by decide
  have hdescent : baseEnd_916674 < baseStart_916674 := by decide
  rcases family_descends (prefixWord ++ tailWord_916674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_916762 : List Nat := [3, 1, 1, 3, 3, 3, 2, 1, 5]
def baseStart_916762 : Nat := 118140960795 + 916762 * 2 ^ 59
def prefixEnd_916762 : Nat := 4983230072969 + 3 ^ 40 * 916762 * 2
def baseEnd_916762 : Nat := 104608789283832755146421

theorem tailTrace_916762 : CollatzResearch.WordTrace tailWord_916762 prefixEnd_916762 104608789283832755146421 := by
  unfold tailWord_916762
  simp only [CollatzResearch.WordTrace]
  refine ⟨8359264276183829832374135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22291371403156879552997693 8359264276183829832374135)
  ·
    refine ⟨12538896414275744748561203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8359264276183829832374135 12538896414275744748561203)
    ·
      refine ⟨18808344621413617122841805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12538896414275744748561203 18808344621413617122841805)
      ·
        refine ⟨7053129233030106421065677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18808344621413617122841805 7053129233030106421065677)
        ·
          refine ⟨2644923462386289907899629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7053129233030106421065677 2644923462386289907899629)
          ·
            refine ⟨991846298394858715462361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2644923462386289907899629 991846298394858715462361)
            ·
              refine ⟨743884723796144036596771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 991846298394858715462361 743884723796144036596771)
              ·
                refine ⟨1115827085694216054895157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 743884723796144036596771 1115827085694216054895157)
                ·
                  refine ⟨104608789283832755146421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1115827085694216054895157 104608789283832755146421)
                  ·
                    rfl

theorem cell22_916762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 3, 2, 1, 5].length) (baseStart_916762 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_916762 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_916762 prefixEnd_916762 := by exact prefixLift 916762
  have htrace : WordTrace (prefixWord ++ tailWord_916762) baseStart_916762 baseEnd_916762 := by
    simpa [prefixWord, tailWord_916762, baseEnd_916762] using wordTrace_append hprefix tailTrace_916762
  have hstable : (prefixWord ++ tailWord_916762).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_916762).length < 2 ^ (prefixWord ++ tailWord_916762).sum := by decide
  have hdescent : baseEnd_916762 < baseStart_916762 := by decide
  rcases family_descends (prefixWord ++ tailWord_916762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_916807 : List Nat := [1, 1, 4, 1, 2, 3, 4, 2, 4]
def baseStart_916807 : Nat := 118140960795 + 916807 * 2 ^ 59
def prefixEnd_916807 : Nat := 4983230072969 + 3 ^ 40 * 916807 * 2
def baseEnd_916807 : Nat := 104613924090377716021375

theorem tailTrace_916807 : CollatzResearch.WordTrace tailWord_916807 prefixEnd_916807 104613924090377716021375 := by
  unfold tailWord_916807
  simp only [CollatzResearch.WordTrace]
  refine ⟨33438698389572292014884675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22292465593048194676589783 33438698389572292014884675)
  ·
    refine ⟨50158047584358438022327013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33438698389572292014884675 50158047584358438022327013)
    ·
      refine ⟨9404633922067207129186315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 50158047584358438022327013 9404633922067207129186315)
      ·
        refine ⟨14106950883100810693779473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9404633922067207129186315 14106950883100810693779473)
        ·
          refine ⟨10580213162325608020334605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14106950883100810693779473 10580213162325608020334605)
          ·
            refine ⟨3967579935872103007625477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10580213162325608020334605 3967579935872103007625477)
            ·
              refine ⟨743921237976019313929777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3967579935872103007625477 743921237976019313929777)
              ·
                refine ⟨557940928482014485447333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 743921237976019313929777 557940928482014485447333)
                ·
                  refine ⟨104613924090377716021375, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 557940928482014485447333 104613924090377716021375)
                  ·
                    rfl

theorem cell22_916807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 4, 2, 4].length) (baseStart_916807 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_916807 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_916807 prefixEnd_916807 := by exact prefixLift 916807
  have htrace : WordTrace (prefixWord ++ tailWord_916807) baseStart_916807 baseEnd_916807 := by
    simpa [prefixWord, tailWord_916807, baseEnd_916807] using wordTrace_append hprefix tailTrace_916807
  have hstable : (prefixWord ++ tailWord_916807).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_916807).length < 2 ^ (prefixWord ++ tailWord_916807).sum := by decide
  have hdescent : baseEnd_916807 < baseStart_916807 := by decide
  rcases family_descends (prefixWord ++ tailWord_916807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_916835 : List Nat := [1, 1, 1, 5, 2, 3, 3, 6]
def baseStart_916835 : Nat := 118140960795 + 916835 * 2 ^ 59
def prefixEnd_916835 : Nat := 4983230072969 + 3 ^ 40 * 916835 * 2
def baseEnd_916835 : Nat := 34872373027038934262671

theorem tailTrace_916835 : CollatzResearch.WordTrace tailWord_916835 prefixEnd_916835 34872373027038934262671 := by
  unfold tailWord_916835
  simp only [CollatzResearch.WordTrace]
  refine ⟨33439719633470852796903959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22293146422313901864602639 33439719633470852796903959)
  ·
    refine ⟨50159579450206279195355939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33439719633470852796903959 50159579450206279195355939)
    ·
      refine ⟨75239369175309418793033909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50159579450206279195355939 75239369175309418793033909)
      ·
        refine ⟨7053690860185258011846929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 75239369175309418793033909 7053690860185258011846929)
        ·
          refine ⟨5290268145138943508885197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7053690860185258011846929 5290268145138943508885197)
          ·
            refine ⟨1983850554427103815831949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5290268145138943508885197 1983850554427103815831949)
            ·
              refine ⟨743943957910163930936981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1983850554427103815831949 743943957910163930936981)
              ·
                refine ⟨34872373027038934262671, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 743943957910163930936981 34872373027038934262671)
                ·
                  rfl

theorem cell22_916835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 3, 3, 6].length) (baseStart_916835 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_916835 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_916835 prefixEnd_916835 := by exact prefixLift 916835
  have htrace : WordTrace (prefixWord ++ tailWord_916835) baseStart_916835 baseEnd_916835 := by
    simpa [prefixWord, tailWord_916835, baseEnd_916835] using wordTrace_append hprefix tailTrace_916835
  have hstable : (prefixWord ++ tailWord_916835).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_916835).length < 2 ^ (prefixWord ++ tailWord_916835).sum := by decide
  have hdescent : baseEnd_916835 < baseStart_916835 := by decide
  rcases family_descends (prefixWord ++ tailWord_916835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_916850 : List Nat := [3, 2, 1, 2, 1, 2, 1, 2, 5, 3]
def baseStart_916850 : Nat := 118140960795 + 916850 * 2 ^ 59
def prefixEnd_916850 : Nat := 4983230072969 + 3 ^ 40 * 916850 * 2
def baseEnd_916850 : Nat := 313856492049895369238993

theorem tailTrace_916850 : CollatzResearch.WordTrace tailWord_916850 prefixEnd_916850 313856492049895369238993 := by
  unfold tailWord_916850
  simp only [CollatzResearch.WordTrace]
  refine ⟨8360066682104127589675001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22293511152277673572466669 8360066682104127589675001)
  ·
    refine ⟨6270050011578095692256251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8360066682104127589675001 6270050011578095692256251)
    ·
      refine ⟨9405075017367143538384377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6270050011578095692256251 9405075017367143538384377)
      ·
        refine ⟨7053806263025357653788283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9405075017367143538384377 7053806263025357653788283)
        ·
          refine ⟨10580709394538036480682425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7053806263025357653788283 10580709394538036480682425)
          ·
            refine ⟨7935532045903527360511819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10580709394538036480682425 7935532045903527360511819)
            ·
              refine ⟨11903298068855291040767729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7935532045903527360511819 11903298068855291040767729)
              ·
                refine ⟨8927473551641468280575797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11903298068855291040767729 8927473551641468280575797)
                ·
                  refine ⟨836950645466387651303981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 8927473551641468280575797 836950645466387651303981)
                  ·
                    refine ⟨313856492049895369238993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 836950645466387651303981 313856492049895369238993)
                    ·
                      rfl

theorem cell22_916850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 1, 2, 5, 3].length) (baseStart_916850 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_916850 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_916850 prefixEnd_916850 := by exact prefixLift 916850
  have htrace : WordTrace (prefixWord ++ tailWord_916850) baseStart_916850 baseEnd_916850 := by
    simpa [prefixWord, tailWord_916850, baseEnd_916850] using wordTrace_append hprefix tailTrace_916850
  have hstable : (prefixWord ++ tailWord_916850).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_916850).length < 2 ^ (prefixWord ++ tailWord_916850).sum := by decide
  have hdescent : baseEnd_916850 < baseStart_916850 := by decide
  rcases family_descends (prefixWord ++ tailWord_916850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_916867 : List Nat := [1, 1, 1, 3, 5, 2, 2, 1, 3, 3]
def baseStart_916867 : Nat := 118140960795 + 916867 * 2 ^ 59
def prefixEnd_916867 : Nat := 4983230072969 + 3 ^ 40 * 916867 * 2
def baseEnd_916867 : Nat := 313862311497312991563941

theorem tailTrace_916867 : CollatzResearch.WordTrace tailWord_916867 prefixEnd_916867 313862311497312991563941 := by
  unfold tailWord_916867
  simp only [CollatzResearch.WordTrace]
  refine ⟨33440886769354922262068855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22293924512903281508045903 33440886769354922262068855)
  ·
    refine ⟨50161330154032383393103283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33440886769354922262068855 50161330154032383393103283)
    ·
      refine ⟨75241995231048575089654925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50161330154032383393103283 75241995231048575089654925)
      ·
        refine ⟨28215748211643215658620597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 75241995231048575089654925 28215748211643215658620597)
        ·
          refine ⟨2645226394841551467995681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 28215748211643215658620597 2645226394841551467995681)
          ·
            refine ⟨1983919796131163600996761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2645226394841551467995681 1983919796131163600996761)
            ·
              refine ⟨1487939847098372700747571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1983919796131163600996761 1487939847098372700747571)
              ·
                refine ⟨2231909770647559051121357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1487939847098372700747571 2231909770647559051121357)
                ·
                  refine ⟨836966163992834644170509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2231909770647559051121357 836966163992834644170509)
                  ·
                    refine ⟨313862311497312991563941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 836966163992834644170509 313862311497312991563941)
                    ·
                      rfl

theorem cell22_916867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 2, 2, 1, 3, 3].length) (baseStart_916867 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_916867 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_916867 prefixEnd_916867 := by exact prefixLift 916867
  have htrace : WordTrace (prefixWord ++ tailWord_916867) baseStart_916867 baseEnd_916867 := by
    simpa [prefixWord, tailWord_916867, baseEnd_916867] using wordTrace_append hprefix tailTrace_916867
  have hstable : (prefixWord ++ tailWord_916867).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_916867).length < 2 ^ (prefixWord ++ tailWord_916867).sum := by decide
  have hdescent : baseEnd_916867 < baseStart_916867 := by decide
  rcases family_descends (prefixWord ++ tailWord_916867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_916908 : List Nat := [2, 2, 1, 1, 1, 1, 4, 2, 8]
def baseStart_916908 : Nat := 118140960795 + 916908 * 2 ^ 59
def prefixEnd_916908 : Nat := 4983230072969 + 3 ^ 40 * 916908 * 2
def baseEnd_916908 : Nat := 104625448878400850429605

theorem tailTrace_916908 : CollatzResearch.WordTrace tailWord_916908 prefixEnd_916908 104625448878400850429605 := by
  unfold tailWord_916908
  simp only [CollatzResearch.WordTrace]
  refine ⟨16721191081103193132155689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22294921441470924176207585 16721191081103193132155689)
  ·
    refine ⟨12540893310827394849116767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16721191081103193132155689 12540893310827394849116767)
    ·
      refine ⟨18811339966241092273675151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12540893310827394849116767 18811339966241092273675151)
      ·
        refine ⟨28217009949361638410512727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18811339966241092273675151 28217009949361638410512727)
        ·
          refine ⟨42325514924042457615769091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28217009949361638410512727 42325514924042457615769091)
          ·
            refine ⟨63488272386063686423653637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42325514924042457615769091 63488272386063686423653637)
            ·
              refine ⟨11904051072386941204435057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 63488272386063686423653637 11904051072386941204435057)
              ·
                refine ⟨8928038304290205903326293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11904051072386941204435057 8928038304290205903326293)
                ·
                  refine ⟨104625448878400850429605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 8928038304290205903326293 104625448878400850429605)
                  ·
                    rfl

theorem cell22_916908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 8].length) (baseStart_916908 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_916908 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_916908 prefixEnd_916908 := by exact prefixLift 916908
  have htrace : WordTrace (prefixWord ++ tailWord_916908) baseStart_916908 baseEnd_916908 := by
    simpa [prefixWord, tailWord_916908, baseEnd_916908] using wordTrace_append hprefix tailTrace_916908
  have hstable : (prefixWord ++ tailWord_916908).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_916908).length < 2 ^ (prefixWord ++ tailWord_916908).sum := by decide
  have hdescent : baseEnd_916908 < baseStart_916908 := by decide
  rcases family_descends (prefixWord ++ tailWord_916908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_916957 : List Nat := [1, 4, 3, 1, 1, 3, 1, 2, 1, 5]
def baseStart_916957 : Nat := 118140960795 + 916957 * 2 ^ 59
def prefixEnd_916957 : Nat := 4983230072969 + 3 ^ 40 * 916957 * 2
def baseEnd_916957 : Nat := 313893120336582756813665

theorem tailTrace_916957 : CollatzResearch.WordTrace tailWord_916957 prefixEnd_916957 313893120336582756813665 := by
  unfold tailWord_916957
  simp only [CollatzResearch.WordTrace]
  refine ⟨33444169339028867632845125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22296112892685911755230083 33444169339028867632845125)
  ·
    refine ⟨6270781751067912681158461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 33444169339028867632845125 6270781751067912681158461)
    ·
      refine ⟨2351543156650467255434423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6270781751067912681158461 2351543156650467255434423)
      ·
        refine ⟨3527314734975700883151635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2351543156650467255434423 3527314734975700883151635)
        ·
          refine ⟨5290972102463551324727453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3527314734975700883151635 5290972102463551324727453)
          ·
            refine ⟨1984114538423831746772795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5290972102463551324727453 1984114538423831746772795)
            ·
              refine ⟨2976171807635747620159193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1984114538423831746772795 2976171807635747620159193)
              ·
                refine ⟨2232128855726810715119395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2976171807635747620159193 2232128855726810715119395)
                ·
                  refine ⟨3348193283590216072679093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2232128855726810715119395 3348193283590216072679093)
                  ·
                    refine ⟨313893120336582756813665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3348193283590216072679093 313893120336582756813665)
                    ·
                      rfl

theorem cell22_916957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 3, 1, 2, 1, 5].length) (baseStart_916957 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_916957 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_916957 prefixEnd_916957 := by exact prefixLift 916957
  have htrace : WordTrace (prefixWord ++ tailWord_916957) baseStart_916957 baseEnd_916957 := by
    simpa [prefixWord, tailWord_916957, baseEnd_916957] using wordTrace_append hprefix tailTrace_916957
  have hstable : (prefixWord ++ tailWord_916957).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_916957).length < 2 ^ (prefixWord ++ tailWord_916957).sum := by decide
  have hdescent : baseEnd_916957 < baseStart_916957 := by decide
  rcases family_descends (prefixWord ++ tailWord_916957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_916970 : List Nat := [3, 1, 3, 1, 4, 10]
def baseStart_916970 : Nat := 118140960795 + 916970 * 2 ^ 59
def prefixEnd_916970 : Nat := 4983230072969 + 3 ^ 40 * 916970 * 2
def baseEnd_916970 : Nat := 3875278648175988348625

theorem tailTrace_916970 : CollatzResearch.WordTrace tailWord_916970 prefixEnd_916970 3875278648175988348625 := by
  unfold tailWord_916970
  simp only [CollatzResearch.WordTrace]
  refine ⟨8361160871995442713267091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22296428991987847235378909 8361160871995442713267091)
  ·
    refine ⟨12541741307993164069900637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8361160871995442713267091 12541741307993164069900637)
    ·
      refine ⟨4703152990497436526212739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12541741307993164069900637 4703152990497436526212739)
      ·
        refine ⟨7054729485746154789319109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4703152990497436526212739 7054729485746154789319109)
        ·
          refine ⟨1322761778577404022997333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7054729485746154789319109 1322761778577404022997333)
          ·
            refine ⟨3875278648175988348625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 1322761778577404022997333 3875278648175988348625)
            ·
              rfl

theorem cell22_916970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 10].length) (baseStart_916970 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_916970 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_916970 prefixEnd_916970 := by exact prefixLift 916970
  have htrace : WordTrace (prefixWord ++ tailWord_916970) baseStart_916970 baseEnd_916970 := by
    simpa [prefixWord, tailWord_916970, baseEnd_916970] using wordTrace_append hprefix tailTrace_916970
  have hstable : (prefixWord ++ tailWord_916970).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_916970).length < 2 ^ (prefixWord ++ tailWord_916970).sum := by decide
  have hdescent : baseEnd_916970 < baseStart_916970 := by decide
  rcases family_descends (prefixWord ++ tailWord_916970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_916974 : List Nat := [4, 1, 2, 1, 2, 1, 4, 2, 2, 3]
def baseStart_916974 : Nat := 118140960795 + 916974 * 2 ^ 59
def prefixEnd_916974 : Nat := 4983230072969 + 3 ^ 40 * 916974 * 2
def baseEnd_916974 : Nat := 313898939784000379138613

theorem tailTrace_916974 : CollatzResearch.WordTrace tailWord_916974 prefixEnd_916974 313898939784000379138613 := by
  unfold tailWord_916974
  simp only [CollatzResearch.WordTrace]
  refine ⟨4180598672495909942026747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22296526253311519690809317 4180598672495909942026747)
  ·
    refine ⟨6270898008743864913040121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4180598672495909942026747 6270898008743864913040121)
    ·
      refine ⟨4703173506557898684780091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6270898008743864913040121 4703173506557898684780091)
      ·
        refine ⟨7054760259836848027170137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4703173506557898684780091 7054760259836848027170137)
        ·
          refine ⟨5291070194877636020377603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7054760259836848027170137 5291070194877636020377603)
          ·
            refine ⟨7936605292316454030566405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5291070194877636020377603 7936605292316454030566405)
            ·
              refine ⟨1488113492309335130731201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7936605292316454030566405 1488113492309335130731201)
              ·
                refine ⟨1116085119232001348048401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1488113492309335130731201 1116085119232001348048401)
                ·
                  refine ⟨837063839424001011036301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1116085119232001348048401 837063839424001011036301)
                  ·
                    refine ⟨313898939784000379138613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 837063839424001011036301 313898939784000379138613)
                    ·
                      rfl

theorem cell22_916974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 4, 2, 2, 3].length) (baseStart_916974 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_916974 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_916974 prefixEnd_916974 := by exact prefixLift 916974
  have htrace : WordTrace (prefixWord ++ tailWord_916974) baseStart_916974 baseEnd_916974 := by
    simpa [prefixWord, tailWord_916974, baseEnd_916974] using wordTrace_append hprefix tailTrace_916974
  have hstable : (prefixWord ++ tailWord_916974).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_916974).length < 2 ^ (prefixWord ++ tailWord_916974).sum := by decide
  have hdescent : baseEnd_916974 < baseStart_916974 := by decide
  rcases family_descends (prefixWord ++ tailWord_916974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_917002 : List Nat := [3, 1, 2, 2, 2, 2, 1, 1, 5, 3]
def baseStart_917002 : Nat := 118140960795 + 917002 * 2 ^ 59
def prefixEnd_917002 : Nat := 4983230072969 + 3 ^ 40 * 917002 * 2
def baseEnd_917002 : Nat := 313908524756217639438527

theorem tailTrace_917002 : CollatzResearch.WordTrace tailWord_917002 prefixEnd_917002 313908524756217639438527 := by
  unfold tailWord_917002
  simp only [CollatzResearch.WordTrace]
  refine ⟨8361452655966460079558315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22297207082577226878822173 8361452655966460079558315)
  ·
    refine ⟨12542178983949690119337473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8361452655966460079558315 12542178983949690119337473)
    ·
      refine ⟨9406634237962267589503105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12542178983949690119337473 9406634237962267589503105)
      ·
        refine ⟨7054975678471700692127329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9406634237962267589503105 7054975678471700692127329)
        ·
          refine ⟨5291231758853775519095497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7054975678471700692127329 5291231758853775519095497)
          ·
            refine ⟨3968423819140331639321623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5291231758853775519095497 3968423819140331639321623)
            ·
              refine ⟨5952635728710497458982435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3968423819140331639321623 5952635728710497458982435)
              ·
                refine ⟨8928953593065746188473653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5952635728710497458982435 8928953593065746188473653)
                ·
                  refine ⟨837089399349913705169405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 8928953593065746188473653 837089399349913705169405)
                  ·
                    refine ⟨313908524756217639438527, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 837089399349913705169405 313908524756217639438527)
                    ·
                      rfl

theorem cell22_917002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 1, 1, 5, 3].length) (baseStart_917002 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_917002 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_917002 prefixEnd_917002 := by exact prefixLift 917002
  have htrace : WordTrace (prefixWord ++ tailWord_917002) baseStart_917002 baseEnd_917002 := by
    simpa [prefixWord, tailWord_917002, baseEnd_917002] using wordTrace_append hprefix tailTrace_917002
  have hstable : (prefixWord ++ tailWord_917002).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_917002).length < 2 ^ (prefixWord ++ tailWord_917002).sum := by decide
  have hdescent : baseEnd_917002 < baseStart_917002 := by decide
  rcases family_descends (prefixWord ++ tailWord_917002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_917006 : List Nat := [4, 1, 1, 2, 5, 1, 1, 1, 2, 4]
def baseStart_917006 : Nat := 118140960795 + 917006 * 2 ^ 59
def prefixEnd_917006 : Nat := 4983230072969 + 3 ^ 40 * 917006 * 2
def baseEnd_917006 : Nat := 313909894037962962338515

theorem tailTrace_917006 : CollatzResearch.WordTrace tailWord_917006 prefixEnd_917006 313909894037962962338515 := by
  unfold tailWord_917006
  simp only [CollatzResearch.WordTrace]
  refine ⟨4180744564481418625172359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22297304343900899334252581 4180744564481418625172359)
  ·
    refine ⟨6271116846722127937758539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4180744564481418625172359 6271116846722127937758539)
    ·
      refine ⟨9406675270083191906637809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6271116846722127937758539 9406675270083191906637809)
      ·
        refine ⟨7055006452562393929978357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9406675270083191906637809 7055006452562393929978357)
        ·
          refine ⟨661406854927724430935471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 7055006452562393929978357 661406854927724430935471)
          ·
            refine ⟨992110282391586646403207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 661406854927724430935471 992110282391586646403207)
            ·
              refine ⟨1488165423587379969604811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 992110282391586646403207 1488165423587379969604811)
              ·
                refine ⟨2232248135381069954407217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1488165423587379969604811 2232248135381069954407217)
                ·
                  refine ⟨1674186101535802465805413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2232248135381069954407217 1674186101535802465805413)
                  ·
                    refine ⟨313909894037962962338515, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1674186101535802465805413 313909894037962962338515)
                    ·
                      rfl

theorem cell22_917006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 5, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 5, 1, 1, 1, 2, 4].length) (baseStart_917006 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_917006 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_917006 prefixEnd_917006 := by exact prefixLift 917006
  have htrace : WordTrace (prefixWord ++ tailWord_917006) baseStart_917006 baseEnd_917006 := by
    simpa [prefixWord, tailWord_917006, baseEnd_917006] using wordTrace_append hprefix tailTrace_917006
  have hstable : (prefixWord ++ tailWord_917006).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_917006).length < 2 ^ (prefixWord ++ tailWord_917006).sum := by decide
  have hdescent : baseEnd_917006 < baseStart_917006 := by decide
  rcases family_descends (prefixWord ++ tailWord_917006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_917049 : List Nat := [1, 2, 1, 5, 1, 3, 3, 1, 5]
def baseStart_917049 : Nat := 118140960795 + 917049 * 2 ^ 59
def prefixEnd_917049 : Nat := 4983230072969 + 3 ^ 40 * 917049 * 2
def baseEnd_917049 : Nat := 104641537938908394504461

theorem tailTrace_917049 : CollatzResearch.WordTrace tailWord_917049 prefixEnd_917049 104641537938908394504461 := by
  unfold tailWord_917049
  simp only [CollatzResearch.WordTrace]
  refine ⟨33447524854695567345194201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22298349903130378230129467 33447524854695567345194201)
  ·
    refine ⟨25085643641021675508895651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33447524854695567345194201 25085643641021675508895651)
    ·
      refine ⟨37628465461532513263343477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25085643641021675508895651 37628465461532513263343477)
      ·
        refine ⟨3527668637018673118438451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 37628465461532513263343477 3527668637018673118438451)
        ·
          refine ⟨5291502955528009677657677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3527668637018673118438451 5291502955528009677657677)
          ·
            refine ⟨1984313608323003629121629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5291502955528009677657677 1984313608323003629121629)
            ·
              refine ⟨744117603121126360920611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1984313608323003629121629 744117603121126360920611)
              ·
                refine ⟨1116176404681689541380917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 744117603121126360920611 1116176404681689541380917)
                ·
                  refine ⟨104641537938908394504461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1116176404681689541380917 104641537938908394504461)
                  ·
                    rfl

theorem cell22_917049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 3, 3, 1, 5].length) (baseStart_917049 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_917049 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_917049 prefixEnd_917049 := by exact prefixLift 917049
  have htrace : WordTrace (prefixWord ++ tailWord_917049) baseStart_917049 baseEnd_917049 := by
    simpa [prefixWord, tailWord_917049, baseEnd_917049] using wordTrace_append hprefix tailTrace_917049
  have hstable : (prefixWord ++ tailWord_917049).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_917049).length < 2 ^ (prefixWord ++ tailWord_917049).sum := by decide
  have hdescent : baseEnd_917049 < baseStart_917049 := by decide
  rcases family_descends (prefixWord ++ tailWord_917049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_917135 : List Nat := [1, 1, 2, 1, 1, 1, 1, 3, 3, 8]
def baseStart_917135 : Nat := 118140960795 + 917135 * 2 ^ 59
def prefixEnd_917135 : Nat := 4983230072969 + 3 ^ 40 * 917135 * 2
def baseEnd_917135 : Nat := 313954053374249625863119

theorem tailTrace_917135 : CollatzResearch.WordTrace tailWord_917135 prefixEnd_917135 313954053374249625863119 := by
  unfold tailWord_917135
  simp only [CollatzResearch.WordTrace]
  refine ⟨33450661532384004032824859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22300441021589336021883239 33450661532384004032824859)
  ·
    refine ⟨50175992298576006049237289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33450661532384004032824859 50175992298576006049237289)
    ·
      refine ⟨37631994223932004536927967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50175992298576006049237289 37631994223932004536927967)
      ·
        refine ⟨56447991335898006805391951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37631994223932004536927967 56447991335898006805391951)
        ·
          refine ⟨84671987003847010208087927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56447991335898006805391951 84671987003847010208087927)
          ·
            refine ⟨127007980505770515312131891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84671987003847010208087927 127007980505770515312131891)
            ·
              refine ⟨190511970758655772968197837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 127007980505770515312131891 190511970758655772968197837)
              ·
                refine ⟨71441989034495914863074189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 190511970758655772968197837 71441989034495914863074189)
                ·
                  refine ⟨26790745887935968073652821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 71441989034495914863074189 26790745887935968073652821)
                  ·
                    refine ⟨313954053374249625863119, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 26790745887935968073652821 313954053374249625863119)
                    ·
                      rfl

theorem cell22_917135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 3, 3, 8].length) (baseStart_917135 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_917135 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_917135 prefixEnd_917135 := by exact prefixLift 917135
  have htrace : WordTrace (prefixWord ++ tailWord_917135) baseStart_917135 baseEnd_917135 := by
    simpa [prefixWord, tailWord_917135, baseEnd_917135] using wordTrace_append hprefix tailTrace_917135
  have hstable : (prefixWord ++ tailWord_917135).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_917135).length < 2 ^ (prefixWord ++ tailWord_917135).sum := by decide
  have hdescent : baseEnd_917135 < baseStart_917135 := by decide
  rcases family_descends (prefixWord ++ tailWord_917135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_917137 : List Nat := [1, 2, 2, 1, 1, 1, 1, 3, 7, 3]
def baseStart_917137 : Nat := 118140960795 + 917137 * 2 ^ 59
def prefixEnd_917137 : Nat := 4983230072969 + 3 ^ 40 * 917137 * 2
def baseEnd_917137 : Nat := 313954738015122287313113

theorem tailTrace_917137 : CollatzResearch.WordTrace tailWord_917137 prefixEnd_917137 313954738015122287313113 := by
  unfold tailWord_917137
  simp only [CollatzResearch.WordTrace]
  refine ⟨33450734478376758374397665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22300489652251172249598443 33450734478376758374397665)
  ·
    refine ⟨25088050858782568780798249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33450734478376758374397665 25088050858782568780798249)
    ·
      refine ⟨18816038144086926585598687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25088050858782568780798249 18816038144086926585598687)
      ·
        refine ⟨28224057216130389878398031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18816038144086926585598687 28224057216130389878398031)
        ·
          refine ⟨42336085824195584817597047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28224057216130389878398031 42336085824195584817597047)
          ·
            refine ⟨63504128736293377226395571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42336085824195584817597047 63504128736293377226395571)
            ·
              refine ⟨95256193104440065839593357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63504128736293377226395571 95256193104440065839593357)
              ·
                refine ⟨35721072414165024689847509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 95256193104440065839593357 35721072414165024689847509)
                ·
                  refine ⟨837212634706992766168301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 35721072414165024689847509 837212634706992766168301)
                  ·
                    refine ⟨313954738015122287313113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 837212634706992766168301 313954738015122287313113)
                    ·
                      rfl

theorem cell22_917137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 3, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 3, 7, 3].length) (baseStart_917137 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_917137 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_917137 prefixEnd_917137 := by exact prefixLift 917137
  have htrace : WordTrace (prefixWord ++ tailWord_917137) baseStart_917137 baseEnd_917137 := by
    simpa [prefixWord, tailWord_917137, baseEnd_917137] using wordTrace_append hprefix tailTrace_917137
  have hstable : (prefixWord ++ tailWord_917137).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_917137).length < 2 ^ (prefixWord ++ tailWord_917137).sum := by decide
  have hdescent : baseEnd_917137 < baseStart_917137 := by decide
  rcases family_descends (prefixWord ++ tailWord_917137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_917152 : List Nat := [2, 1, 1, 4, 3, 1, 1, 1, 2, 6]
def baseStart_917152 : Nat := 118140960795 + 917152 * 2 ^ 59
def prefixEnd_917152 : Nat := 4983230072969 + 3 ^ 40 * 917152 * 2
def baseEnd_917152 : Nat := 313959872821667248188067

theorem tailTrace_917152 : CollatzResearch.WordTrace tailWord_917152 prefixEnd_917152 313959872821667248188067 := by
  unfold tailWord_917152
  simp only [CollatzResearch.WordTrace]
  refine ⟨16725640786661207968096855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22300854382214943957462473 16725640786661207968096855)
  ·
    refine ⟨25088461179991811952145283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16725640786661207968096855 25088461179991811952145283)
    ·
      refine ⟨37632691769987717928217925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25088461179991811952145283 37632691769987717928217925)
      ·
        refine ⟨7056129706872697111540861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 37632691769987717928217925 7056129706872697111540861)
        ·
          refine ⟨2646048640077261416827823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7056129706872697111540861 2646048640077261416827823)
          ·
            refine ⟨3969072960115892125241735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2646048640077261416827823 3969072960115892125241735)
            ·
              refine ⟨5953609440173838187862603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3969072960115892125241735 5953609440173838187862603)
              ·
                refine ⟨8930414160260757281793905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5953609440173838187862603 8930414160260757281793905)
                ·
                  refine ⟨6697810620195567961345429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8930414160260757281793905 6697810620195567961345429)
                  ·
                    refine ⟨313959872821667248188067, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6697810620195567961345429 313959872821667248188067)
                    ·
                      rfl

theorem cell22_917152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 1, 1, 2, 6].length) (baseStart_917152 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_917152 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_917152 prefixEnd_917152 := by exact prefixLift 917152
  have htrace : WordTrace (prefixWord ++ tailWord_917152) baseStart_917152 baseEnd_917152 := by
    simpa [prefixWord, tailWord_917152, baseEnd_917152] using wordTrace_append hprefix tailTrace_917152
  have hstable : (prefixWord ++ tailWord_917152).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_917152).length < 2 ^ (prefixWord ++ tailWord_917152).sum := by decide
  have hdescent : baseEnd_917152 < baseStart_917152 := by decide
  rcases family_descends (prefixWord ++ tailWord_917152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_917167 : List Nat := [1, 1, 2, 1, 2, 4, 1, 5, 5]
def baseStart_917167 : Nat := 118140960795 + 917167 * 2 ^ 59
def prefixEnd_917167 : Nat := 4983230072969 + 3 ^ 40 * 917167 * 2
def baseEnd_917167 : Nat := 104655002542737403021007

theorem tailTrace_917167 : CollatzResearch.WordTrace tailWord_917167 prefixEnd_917167 104655002542737403021007 := by
  unfold tailWord_917167
  simp only [CollatzResearch.WordTrace]
  refine ⟨33451828668268073497989755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22301219112178715665326503 33451828668268073497989755)
  ·
    refine ⟨50177743002402110246984633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33451828668268073497989755 50177743002402110246984633)
    ·
      refine ⟨37633307251801582685238475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50177743002402110246984633 37633307251801582685238475)
      ·
        refine ⟨56449960877702374027857713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37633307251801582685238475 56449960877702374027857713)
        ·
          refine ⟨42337470658276780520893285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56449960877702374027857713 42337470658276780520893285)
          ·
            refine ⟨7938275748426896347667491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 42337470658276780520893285 7938275748426896347667491)
            ·
              refine ⟨11907413622640344521501237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7938275748426896347667491 11907413622640344521501237)
              ·
                refine ⟨1116320027122532298890741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11907413622640344521501237 1116320027122532298890741)
                ·
                  refine ⟨104655002542737403021007, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1116320027122532298890741 104655002542737403021007)
                  ·
                    rfl

theorem cell22_917167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 1, 5, 5].length) (baseStart_917167 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_917167 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_917167 prefixEnd_917167 := by exact prefixLift 917167
  have htrace : WordTrace (prefixWord ++ tailWord_917167) baseStart_917167 baseEnd_917167 := by
    simpa [prefixWord, tailWord_917167, baseEnd_917167] using wordTrace_append hprefix tailTrace_917167
  have hstable : (prefixWord ++ tailWord_917167).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_917167).length < 2 ^ (prefixWord ++ tailWord_917167).sum := by decide
  have hdescent : baseEnd_917167 < baseStart_917167 := by decide
  rcases family_descends (prefixWord ++ tailWord_917167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_917188 : List Nat := [2, 3, 3, 1, 1, 1, 4, 3, 1, 3]
def baseStart_917188 : Nat := 118140960795 + 917188 * 2 ^ 59
def prefixEnd_917188 : Nat := 4983230072969 + 3 ^ 40 * 917188 * 2
def baseEnd_917188 : Nat := 313972196357375154287957

theorem tailTrace_917188 : CollatzResearch.WordTrace tailWord_917188 prefixEnd_917188 313972196357375154287957 := by
  unfold tailWord_917188
  simp only [CollatzResearch.WordTrace]
  refine ⟨16726297300595997042252109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22301729734127996056336145 16726297300595997042252109)
  ·
    refine ⟨6272361487723498890844541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16726297300595997042252109 6272361487723498890844541)
    ·
      refine ⟨2352135557896312084066703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6272361487723498890844541 2352135557896312084066703)
      ·
        refine ⟨3528203336844468126100055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2352135557896312084066703 3528203336844468126100055)
        ·
          refine ⟨5292305005266702189150083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3528203336844468126100055 5292305005266702189150083)
          ·
            refine ⟨7938457507900053283725125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5292305005266702189150083 7938457507900053283725125)
            ·
              refine ⟨1488460782731259990698461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7938457507900053283725125 1488460782731259990698461)
              ·
                refine ⟨558172793524222496511923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1488460782731259990698461 558172793524222496511923)
                ·
                  refine ⟨837259190286333744767885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 558172793524222496511923 837259190286333744767885)
                  ·
                    refine ⟨313972196357375154287957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 837259190286333744767885 313972196357375154287957)
                    ·
                      rfl

theorem cell22_917188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 4, 3, 1, 3].length) (baseStart_917188 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_917188 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_917188 prefixEnd_917188 := by exact prefixLift 917188
  have htrace : WordTrace (prefixWord ++ tailWord_917188) baseStart_917188 baseEnd_917188 := by
    simpa [prefixWord, tailWord_917188, baseEnd_917188] using wordTrace_append hprefix tailTrace_917188
  have hstable : (prefixWord ++ tailWord_917188).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_917188).length < 2 ^ (prefixWord ++ tailWord_917188).sum := by decide
  have hdescent : baseEnd_917188 < baseStart_917188 := by decide
  rcases family_descends (prefixWord ++ tailWord_917188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_917229 : List Nat := [1, 5, 1, 2, 1, 2, 2, 2, 6]
def baseStart_917229 : Nat := 118140960795 + 917229 * 2 ^ 59
def prefixEnd_917229 : Nat := 4983230072969 + 3 ^ 40 * 917229 * 2
def baseEnd_917229 : Nat := 104662077165088238004277

theorem tailTrace_917229 : CollatzResearch.WordTrace tailWord_917229 prefixEnd_917229 104662077165088238004277 := by
  unfold tailWord_917229
  simp only [CollatzResearch.WordTrace]
  refine ⟨33454089994043458086746741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22302726662695638724497827 33454089994043458086746741)
  ·
    refine ⟨3136320936941574195632507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 33454089994043458086746741 3136320936941574195632507)
    ·
      refine ⟨4704481405412361293448761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3136320936941574195632507 4704481405412361293448761)
      ·
        refine ⟨3528361054059270970086571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4704481405412361293448761 3528361054059270970086571)
        ·
          refine ⟨5292541581088906455129857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3528361054059270970086571 5292541581088906455129857)
          ·
            refine ⟨3969406185816679841347393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5292541581088906455129857 3969406185816679841347393)
            ·
              refine ⟨2977054639362509881010545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3969406185816679841347393 2977054639362509881010545)
              ·
                refine ⟨2232790979521882410757909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2977054639362509881010545 2232790979521882410757909)
                ·
                  refine ⟨104662077165088238004277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2232790979521882410757909 104662077165088238004277)
                  ·
                    rfl

theorem cell22_917229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 2, 2, 6].length) (baseStart_917229 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_917229 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_917229 prefixEnd_917229 := by exact prefixLift 917229
  have htrace : WordTrace (prefixWord ++ tailWord_917229) baseStart_917229 baseEnd_917229 := by
    simpa [prefixWord, tailWord_917229, baseEnd_917229] using wordTrace_append hprefix tailTrace_917229
  have hstable : (prefixWord ++ tailWord_917229).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_917229).length < 2 ^ (prefixWord ++ tailWord_917229).sum := by decide
  have hdescent : baseEnd_917229 < baseStart_917229 := by decide
  rcases family_descends (prefixWord ++ tailWord_917229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_917244 : List Nat := [2, 2, 2, 1, 3, 1, 1, 1, 6, 3]
def baseStart_917244 : Nat := 118140960795 + 917244 * 2 ^ 59
def prefixEnd_917244 : Nat := 4983230072969 + 3 ^ 40 * 917244 * 2
def baseEnd_917244 : Nat := 313991366301809674887785

theorem tailTrace_917244 : CollatzResearch.WordTrace tailWord_917244 prefixEnd_917244 313991366301809674887785 := by
  unfold tailWord_917244
  simp only [CollatzResearch.WordTrace]
  refine ⟨16727318544494557824271393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22303091392659410432361857 16727318544494557824271393)
  ·
    refine ⟨12545488908370918368203545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16727318544494557824271393 12545488908370918368203545)
    ·
      refine ⟨9409116681278188776152659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12545488908370918368203545 9409116681278188776152659)
      ·
        refine ⟨14113675021917283164228989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9409116681278188776152659 14113675021917283164228989)
        ·
          refine ⟨5292628133218981186585871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14113675021917283164228989 5292628133218981186585871)
          ·
            refine ⟨7938942199828471779878807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5292628133218981186585871 7938942199828471779878807)
            ·
              refine ⟨11908413299742707669818211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7938942199828471779878807 11908413299742707669818211)
              ·
                refine ⟨17862619949614061504727317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11908413299742707669818211 17862619949614061504727317)
                ·
                  refine ⟨837310310138159133034093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 17862619949614061504727317 837310310138159133034093)
                  ·
                    refine ⟨313991366301809674887785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 837310310138159133034093 313991366301809674887785)
                    ·
                      rfl

theorem cell22_917244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 1, 1, 6, 3].length) (baseStart_917244 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_917244 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_917244 prefixEnd_917244 := by exact prefixLift 917244
  have htrace : WordTrace (prefixWord ++ tailWord_917244) baseStart_917244 baseEnd_917244 := by
    simpa [prefixWord, tailWord_917244, baseEnd_917244] using wordTrace_append hprefix tailTrace_917244
  have hstable : (prefixWord ++ tailWord_917244).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_917244).length < 2 ^ (prefixWord ++ tailWord_917244).sum := by decide
  have hdescent : baseEnd_917244 < baseStart_917244 := by decide
  rcases family_descends (prefixWord ++ tailWord_917244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_917274 : List Nat := [3, 1, 1, 3, 2, 3, 2, 7]
def baseStart_917274 : Nat := 118140960795 + 917274 * 2 ^ 59
def prefixEnd_917274 : Nat := 4983230072969 + 3 ^ 40 * 917274 * 2
def baseEnd_917274 : Nat := 34889070657211066293077

theorem tailTrace_917274 : CollatzResearch.WordTrace tailWord_917274 prefixEnd_917274 34889070657211066293077 := by
  unfold tailWord_917274
  simp only [CollatzResearch.WordTrace]
  refine ⟨8363932819720107693033719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22303820852586953848089917 8363932819720107693033719)
  ·
    refine ⟨12545899229580161539550579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8363932819720107693033719 12545899229580161539550579)
    ·
      refine ⟨18818848844370242309325869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12545899229580161539550579 18818848844370242309325869)
      ·
        refine ⟨7057068316638840865997201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18818848844370242309325869 7057068316638840865997201)
        ·
          refine ⟨5292801237479130649497901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7057068316638840865997201 5292801237479130649497901)
          ·
            refine ⟨1984800464054673993561713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5292801237479130649497901 1984800464054673993561713)
            ·
              refine ⟨1488600348041005495171285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1984800464054673993561713 1488600348041005495171285)
              ·
                refine ⟨34889070657211066293077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1488600348041005495171285 34889070657211066293077)
                ·
                  rfl

theorem cell22_917274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 3, 2, 7].length) (baseStart_917274 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_917274 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_917274 prefixEnd_917274 := by exact prefixLift 917274
  have htrace : WordTrace (prefixWord ++ tailWord_917274) baseStart_917274 baseEnd_917274 := by
    simpa [prefixWord, tailWord_917274, baseEnd_917274] using wordTrace_append hprefix tailTrace_917274
  have hstable : (prefixWord ++ tailWord_917274).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_917274).length < 2 ^ (prefixWord ++ tailWord_917274).sum := by decide
  have hdescent : baseEnd_917274 < baseStart_917274 := by decide
  rcases family_descends (prefixWord ++ tailWord_917274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_917319 : List Nat := [1, 1, 4, 1, 2, 1, 3, 4, 5]
def baseStart_917319 : Nat := 118140960795 + 917319 * 2 ^ 59
def prefixEnd_917319 : Nat := 4983230072969 + 3 ^ 40 * 917319 * 2
def baseEnd_917319 : Nat := 104672346778178159754185

theorem tailTrace_917319 : CollatzResearch.WordTrace tailWord_917319 prefixEnd_917319 104672346778178159754185 := by
  unfold tailWord_917319
  simp only [CollatzResearch.WordTrace]
  refine ⟨33457372563717403457523011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22304915042478268971682007 33457372563717403457523011)
  ·
    refine ⟨50186058845576105186284517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33457372563717403457523011 50186058845576105186284517)
    ·
      refine ⟨9409886033545519722428347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 50186058845576105186284517 9409886033545519722428347)
      ·
        refine ⟨14114829050318279583642521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9409886033545519722428347 14114829050318279583642521)
        ·
          refine ⟨10586121787738709687731891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14114829050318279583642521 10586121787738709687731891)
          ·
            refine ⟨15879182681608064531597837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10586121787738709687731891 15879182681608064531597837)
            ·
              refine ⟨5954693505603024199349189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15879182681608064531597837 5954693505603024199349189)
              ·
                refine ⟨1116505032300567037377973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5954693505603024199349189 1116505032300567037377973)
                ·
                  refine ⟨104672346778178159754185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1116505032300567037377973 104672346778178159754185)
                  ·
                    rfl

theorem cell22_917319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 3, 4, 5].length) (baseStart_917319 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_917319 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_917319 prefixEnd_917319 := by exact prefixLift 917319
  have htrace : WordTrace (prefixWord ++ tailWord_917319) baseStart_917319 baseEnd_917319 := by
    simpa [prefixWord, tailWord_917319, baseEnd_917319] using wordTrace_append hprefix tailTrace_917319
  have hstable : (prefixWord ++ tailWord_917319).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_917319).length < 2 ^ (prefixWord ++ tailWord_917319).sum := by decide
  have hdescent : baseEnd_917319 < baseStart_917319 := by decide
  rcases family_descends (prefixWord ++ tailWord_917319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_917381 : List Nat := [1, 3, 1, 1, 3, 2, 1, 6, 4]
def baseStart_917381 : Nat := 118140960795 + 917381 * 2 ^ 59
def prefixEnd_917381 : Nat := 4983230072969 + 3 ^ 40 * 917381 * 2
def baseEnd_917381 : Nat := 104679421400528994737455

theorem tailTrace_917381 : CollatzResearch.WordTrace tailWord_917381 prefixEnd_917381 104679421400528994737455 := by
  unfold tailWord_917381
  simp only [CollatzResearch.WordTrace]
  refine ⟨33459633889492788046279997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22306422592995192030853331 33459633889492788046279997)
  ·
    refine ⟨12547362708559795517354999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33459633889492788046279997 12547362708559795517354999)
    ·
      refine ⟨18821044062839693276032499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12547362708559795517354999 18821044062839693276032499)
      ·
        refine ⟨28231566094259539914048749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18821044062839693276032499 28231566094259539914048749)
        ·
          refine ⟨10586837285347327467768281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28231566094259539914048749 10586837285347327467768281)
          ·
            refine ⟨7940127964010495600826211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10586837285347327467768281 7940127964010495600826211)
            ·
              refine ⟨11910191946015743401239317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7940127964010495600826211 11910191946015743401239317)
              ·
                refine ⟨558290247469487971933093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 11910191946015743401239317 558290247469487971933093)
                ·
                  refine ⟨104679421400528994737455, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 558290247469487971933093 104679421400528994737455)
                  ·
                    rfl

theorem cell22_917381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 1, 6, 4].length) (baseStart_917381 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_917381 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_917381 prefixEnd_917381 := by exact prefixLift 917381
  have htrace : WordTrace (prefixWord ++ tailWord_917381) baseStart_917381 baseEnd_917381 := by
    simpa [prefixWord, tailWord_917381, baseEnd_917381] using wordTrace_append hprefix tailTrace_917381
  have hstable : (prefixWord ++ tailWord_917381).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_917381).length < 2 ^ (prefixWord ++ tailWord_917381).sum := by decide
  have hdescent : baseEnd_917381 < baseStart_917381 := by decide
  rcases family_descends (prefixWord ++ tailWord_917381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_917400 : List Nat := [2, 1, 2, 6, 1, 1, 2, 2, 1, 4]
def baseStart_917400 : Nat := 118140960795 + 917400 * 2 ^ 59
def prefixEnd_917400 : Nat := 4983230072969 + 3 ^ 40 * 917400 * 2
def baseEnd_917400 : Nat := 314044768289877267987307

theorem tailTrace_917400 : CollatzResearch.WordTrace tailWord_917400 prefixEnd_917400 314044768289877267987307 := by
  unfold tailWord_917400
  simp only [CollatzResearch.WordTrace]
  refine ⟨16730163438211977145610827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22306884584282636194147769 16730163438211977145610827)
  ·
    refine ⟨25095245157317965718416241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16730163438211977145610827 25095245157317965718416241)
    ·
      refine ⟨18821433867988474288812181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25095245157317965718416241 18821433867988474288812181)
      ·
        refine ⟨882254712561959732288071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 18821433867988474288812181 882254712561959732288071)
        ·
          refine ⟨1323382068842939598432107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 882254712561959732288071 1323382068842939598432107)
          ·
            refine ⟨1985073103264409397648161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1323382068842939598432107 1985073103264409397648161)
            ·
              refine ⟨1488804827448307048236121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1985073103264409397648161 1488804827448307048236121)
              ·
                refine ⟨1116603620586230286177091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1488804827448307048236121 1116603620586230286177091)
                ·
                  refine ⟨1674905430879345429265637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1116603620586230286177091 1674905430879345429265637)
                  ·
                    refine ⟨314044768289877267987307, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1674905430879345429265637 314044768289877267987307)
                    ·
                      rfl

theorem cell22_917400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 1, 2, 2, 1, 4].length) (baseStart_917400 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_917400 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_917400 prefixEnd_917400 := by exact prefixLift 917400
  have htrace : WordTrace (prefixWord ++ tailWord_917400) baseStart_917400 baseEnd_917400 := by
    simpa [prefixWord, tailWord_917400, baseEnd_917400] using wordTrace_append hprefix tailTrace_917400
  have hstable : (prefixWord ++ tailWord_917400).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_917400).length < 2 ^ (prefixWord ++ tailWord_917400).sum := by decide
  have hdescent : baseEnd_917400 < baseStart_917400 := by decide
  rcases family_descends (prefixWord ++ tailWord_917400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_917415 : List Nat := [1, 1, 6, 1, 2, 3, 1, 3, 4]
def baseStart_917415 : Nat := 118140960795 + 917415 * 2 ^ 59
def prefixEnd_917415 : Nat := 4983230072969 + 3 ^ 40 * 917415 * 2
def baseEnd_917415 : Nat := 104683301032140742954087

theorem tailTrace_917415 : CollatzResearch.WordTrace tailWord_917415 prefixEnd_917415 104683301032140742954087 := by
  unfold tailWord_917415
  simp only [CollatzResearch.WordTrace]
  refine ⟨33460873971369611853017699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22307249314246407902011799 33460873971369611853017699)
  ·
    refine ⟨50191310957054417779526549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33460873971369611853017699 50191310957054417779526549)
    ·
      refine ⟨2352717701111925833415307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 50191310957054417779526549 2352717701111925833415307)
      ·
        refine ⟨3529076551667888750122961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2352717701111925833415307 3529076551667888750122961)
        ·
          refine ⟨2646807413750916562592221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3529076551667888750122961 2646807413750916562592221)
          ·
            refine ⟨992552780156593710972083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2646807413750916562592221 992552780156593710972083)
            ·
              refine ⟨1488829170234890566458125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 992552780156593710972083 1488829170234890566458125)
              ·
                refine ⟨558310938838083962421797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1488829170234890566458125 558310938838083962421797)
                ·
                  refine ⟨104683301032140742954087, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 558310938838083962421797 104683301032140742954087)
                  ·
                    rfl

theorem cell22_917415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 3, 1, 3, 4].length) (baseStart_917415 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_917415 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_917415 prefixEnd_917415 := by exact prefixLift 917415
  have htrace : WordTrace (prefixWord ++ tailWord_917415) baseStart_917415 baseEnd_917415 := by
    simpa [prefixWord, tailWord_917415, baseEnd_917415] using wordTrace_append hprefix tailTrace_917415
  have hstable : (prefixWord ++ tailWord_917415).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_917415).length < 2 ^ (prefixWord ++ tailWord_917415).sum := by decide
  have hdescent : baseEnd_917415 < baseStart_917415 := by decide
  rcases family_descends (prefixWord ++ tailWord_917415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_917439 : List Nat := [1, 1, 2, 2, 2, 1, 4, 1, 2, 6]
def baseStart_917439 : Nat := 118140960795 + 917439 * 2 ^ 59
def prefixEnd_917439 : Nat := 4983230072969 + 3 ^ 40 * 917439 * 2
def baseEnd_917439 : Nat := 314058118786894166262187

theorem tailTrace_917439 : CollatzResearch.WordTrace tailWord_917439 prefixEnd_917439 314058118786894166262187 := by
  unfold tailWord_917439
  simp only [CollatzResearch.WordTrace]
  refine ⟨33461749323282663951891371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22307832882188442634594247 33461749323282663951891371)
  ·
    refine ⟨50192623984923995927837057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33461749323282663951891371 50192623984923995927837057)
    ·
      refine ⟨37644467988692996945877793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50192623984923995927837057 37644467988692996945877793)
      ·
        refine ⟨28233350991519747709408345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37644467988692996945877793 28233350991519747709408345)
        ·
          refine ⟨21175013243639810782056259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28233350991519747709408345 21175013243639810782056259)
          ·
            refine ⟨31762519865459716173084389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21175013243639810782056259 31762519865459716173084389)
            ·
              refine ⟨5955472474773696782453323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31762519865459716173084389 5955472474773696782453323)
              ·
                refine ⟨8933208712160545173679985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5955472474773696782453323 8933208712160545173679985)
                ·
                  refine ⟨6699906534120408880259989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8933208712160545173679985 6699906534120408880259989)
                  ·
                    refine ⟨314058118786894166262187, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6699906534120408880259989 314058118786894166262187)
                    ·
                      rfl

theorem cell22_917439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 4, 1, 2, 6].length) (baseStart_917439 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_917439 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_917439 prefixEnd_917439 := by exact prefixLift 917439
  have htrace : WordTrace (prefixWord ++ tailWord_917439) baseStart_917439 baseEnd_917439 := by
    simpa [prefixWord, tailWord_917439, baseEnd_917439] using wordTrace_append hprefix tailTrace_917439
  have hstable : (prefixWord ++ tailWord_917439).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_917439).length < 2 ^ (prefixWord ++ tailWord_917439).sum := by decide
  have hdescent : baseEnd_917439 < baseStart_917439 := by decide
  rcases family_descends (prefixWord ++ tailWord_917439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_917501 : List Nat := [1, 4, 1, 1, 1, 2, 3, 2, 3, 4]
def baseStart_917501 : Nat := 118140960795 + 917501 * 2 ^ 59
def prefixEnd_917501 : Nat := 4983230072969 + 3 ^ 40 * 917501 * 2
def baseEnd_917501 : Nat := 314079342653946671211997

theorem tailTrace_917501 : CollatzResearch.WordTrace tailWord_917501 prefixEnd_917501 314079342653946671211997 := by
  unfold tailWord_917501
  simp only [CollatzResearch.WordTrace]
  refine ⟨33464010649058048540648357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22309340432705365693765571 33464010649058048540648357)
  ·
    refine ⟨6274501996698384101371567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 33464010649058048540648357 6274501996698384101371567)
    ·
      refine ⟨9411752995047576152057351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6274501996698384101371567 9411752995047576152057351)
      ·
        refine ⟨14117629492571364228086027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9411752995047576152057351 14117629492571364228086027)
        ·
          refine ⟨21176444238857046342129041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14117629492571364228086027 21176444238857046342129041)
          ·
            refine ⟨15882333179142784756596781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21176444238857046342129041 15882333179142784756596781)
            ·
              refine ⟨5955874942178544283723793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15882333179142784756596781 5955874942178544283723793)
              ·
                refine ⟨4466906206633908212792845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5955874942178544283723793 4466906206633908212792845)
                ·
                  refine ⟨1675089827487715579797317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4466906206633908212792845 1675089827487715579797317)
                  ·
                    refine ⟨314079342653946671211997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1675089827487715579797317 314079342653946671211997)
                    ·
                      rfl

theorem cell22_917501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 3, 2, 3, 4].length) (baseStart_917501 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_917501 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_917501 prefixEnd_917501 := by exact prefixLift 917501
  have htrace : WordTrace (prefixWord ++ tailWord_917501) baseStart_917501 baseEnd_917501 := by
    simpa [prefixWord, tailWord_917501, baseEnd_917501] using wordTrace_append hprefix tailTrace_917501
  have hstable : (prefixWord ++ tailWord_917501).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_917501).length < 2 ^ (prefixWord ++ tailWord_917501).sum := by decide
  have hdescent : baseEnd_917501 < baseStart_917501 := by decide
  rcases family_descends (prefixWord ++ tailWord_917501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_917516 : List Nat := [2, 2, 1, 2, 3, 1, 3, 2, 6]
def baseStart_917516 : Nat := 118140960795 + 917516 * 2 ^ 59
def prefixEnd_917516 : Nat := 4983230072969 + 3 ^ 40 * 917516 * 2
def baseEnd_917516 : Nat := 104694825820163877362317

theorem tailTrace_917516 : CollatzResearch.WordTrace tailWord_917516 prefixEnd_917516 104694825820163877362317 := by
  unfold tailWord_917516
  simp only [CollatzResearch.WordTrace]
  refine ⟨16732278872001853051222201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22309705162669137401629601 16732278872001853051222201)
  ·
    refine ⟨12549209154001389788416651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16732278872001853051222201 12549209154001389788416651)
    ·
      refine ⟨18823813731002084682624977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12549209154001389788416651 18823813731002084682624977)
      ·
        refine ⟨14117860298251563511968733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18823813731002084682624977 14117860298251563511968733)
        ·
          refine ⟨5294197611844336316988275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14117860298251563511968733 5294197611844336316988275)
          ·
            refine ⟨7941296417766504475482413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5294197611844336316988275 7941296417766504475482413)
            ·
              refine ⟨2977986156662439178305905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7941296417766504475482413 2977986156662439178305905)
              ·
                refine ⟨2233489617496829383729429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2977986156662439178305905 2233489617496829383729429)
                ·
                  refine ⟨104694825820163877362317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2233489617496829383729429 104694825820163877362317)
                  ·
                    rfl

theorem cell22_917516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 3, 2, 6].length) (baseStart_917516 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_917516 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_917516 prefixEnd_917516 := by exact prefixLift 917516
  have htrace : WordTrace (prefixWord ++ tailWord_917516) baseStart_917516 baseEnd_917516 := by
    simpa [prefixWord, tailWord_917516, baseEnd_917516] using wordTrace_append hprefix tailTrace_917516
  have hstable : (prefixWord ++ tailWord_917516).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_917516).length < 2 ^ (prefixWord ++ tailWord_917516).sum := by decide
  have hdescent : baseEnd_917516 < baseStart_917516 := by decide
  rcases family_descends (prefixWord ++ tailWord_917516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_917518 : List Nat := [4, 1, 1, 2, 2, 1, 2, 4, 1, 4]
def baseStart_917518 : Nat := 118140960795 + 917518 * 2 ^ 59
def prefixEnd_917518 : Nat := 4983230072969 + 3 ^ 40 * 917518 * 2
def baseEnd_917518 : Nat := 314085162101364293536945

theorem tailTrace_917518 : CollatzResearch.WordTrace tailWord_917518 prefixEnd_917518 314085162101364293536945 := by
  unfold tailWord_917518
  simp only [CollatzResearch.WordTrace]
  refine ⟨4183078836249557555502151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22309753793330973629344805 4183078836249557555502151)
  ·
    refine ⟨6274618254374336333253227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4183078836249557555502151 6274618254374336333253227)
    ·
      refine ⟨9411927381561504499879841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6274618254374336333253227 9411927381561504499879841)
      ·
        refine ⟨7058945536171128374909881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9411927381561504499879841 7058945536171128374909881)
        ·
          refine ⟨5294209152128346281182411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7058945536171128374909881 5294209152128346281182411)
          ·
            refine ⟨7941313728192519421773617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5294209152128346281182411 7941313728192519421773617)
            ·
              refine ⟨5955985296144389566330213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7941313728192519421773617 5955985296144389566330213)
              ·
                refine ⟨1116747243027073043686915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5955985296144389566330213 1116747243027073043686915)
                ·
                  refine ⟨1675120864540609565530373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1116747243027073043686915 1675120864540609565530373)
                  ·
                    refine ⟨314085162101364293536945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1675120864540609565530373 314085162101364293536945)
                    ·
                      rfl

theorem cell22_917518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 2, 4, 1, 4].length) (baseStart_917518 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_917518 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_917518 prefixEnd_917518 := by exact prefixLift 917518
  have htrace : WordTrace (prefixWord ++ tailWord_917518) baseStart_917518 baseEnd_917518 := by
    simpa [prefixWord, tailWord_917518, baseEnd_917518] using wordTrace_append hprefix tailTrace_917518
  have hstable : (prefixWord ++ tailWord_917518).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_917518).length < 2 ^ (prefixWord ++ tailWord_917518).sum := by decide
  have hdescent : baseEnd_917518 < baseStart_917518 := by decide
  rcases family_descends (prefixWord ++ tailWord_917518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_917548 : List Nat := [2, 2, 1, 1, 1, 2, 2, 6, 2, 3]
def baseStart_917548 : Nat := 118140960795 + 917548 * 2 ^ 59
def prefixEnd_917548 : Nat := 4983230072969 + 3 ^ 40 * 917548 * 2
def baseEnd_917548 : Nat := 314095431714454215286853

theorem tailTrace_917548 : CollatzResearch.WordTrace tailWord_917548 prefixEnd_917548 314095431714454215286853 := by
  unfold tailWord_917548
  simp only [CollatzResearch.WordTrace]
  refine ⟨16732862439943887783804649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22310483253258517045072865 16732862439943887783804649)
  ·
    refine ⟨12549646829957915837853487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16732862439943887783804649 12549646829957915837853487)
    ·
      refine ⟨18824470244936873756780231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12549646829957915837853487 18824470244936873756780231)
      ·
        refine ⟨28236705367405310635170347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18824470244936873756780231 28236705367405310635170347)
        ·
          refine ⟨42355058051107965952755521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28236705367405310635170347 42355058051107965952755521)
          ·
            refine ⟨31766293538330974464566641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42355058051107965952755521 31766293538330974464566641)
            ·
              refine ⟨23824720153748230848424981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31766293538330974464566641 23824720153748230848424981)
              ·
                refine ⟨1116783757206948321019921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 23824720153748230848424981 1116783757206948321019921)
                ·
                  refine ⟨837587817905211240764941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1116783757206948321019921 837587817905211240764941)
                  ·
                    refine ⟨314095431714454215286853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 837587817905211240764941 314095431714454215286853)
                    ·
                      rfl

theorem cell22_917548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 2, 3].length) (baseStart_917548 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_917548 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_917548 prefixEnd_917548 := by exact prefixLift 917548
  have htrace : WordTrace (prefixWord ++ tailWord_917548) baseStart_917548 baseEnd_917548 := by
    simpa [prefixWord, tailWord_917548, baseEnd_917548] using wordTrace_append hprefix tailTrace_917548
  have hstable : (prefixWord ++ tailWord_917548).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_917548).length < 2 ^ (prefixWord ++ tailWord_917548).sum := by decide
  have hdescent : baseEnd_917548 < baseStart_917548 := by decide
  rcases family_descends (prefixWord ++ tailWord_917548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_917550 : List Nat := [4, 1, 3, 1, 1, 2, 2, 4, 4]
def baseStart_917550 : Nat := 118140960795 + 917550 * 2 ^ 59
def prefixEnd_917550 : Nat := 4983230072969 + 3 ^ 40 * 917550 * 2
def baseEnd_917550 : Nat := 104698705451775625578949

theorem tailTrace_917550 : CollatzResearch.WordTrace tailWord_917550 prefixEnd_917550 104698705451775625578949 := by
  unfold tailWord_917550
  simp only [CollatzResearch.WordTrace]
  refine ⟨4183224728235066238647763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22310531883920353272788069 4183224728235066238647763)
  ·
    refine ⟨6274837092352599357971645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4183224728235066238647763 6274837092352599357971645)
    ·
      refine ⟨2353063909632224759239367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6274837092352599357971645 2353063909632224759239367)
      ·
        refine ⟨3529595864448337138859051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2353063909632224759239367 3529595864448337138859051)
        ·
          refine ⟨5294393796672505708288577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3529595864448337138859051 5294393796672505708288577)
          ·
            refine ⟨3970795347504379281216433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5294393796672505708288577 3970795347504379281216433)
            ·
              refine ⟨2978096510628284460912325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3970795347504379281216433 2978096510628284460912325)
              ·
                refine ⟨558393095742803336421061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2978096510628284460912325 558393095742803336421061)
                ·
                  refine ⟨104698705451775625578949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 558393095742803336421061 104698705451775625578949)
                  ·
                    rfl

theorem cell22_917550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 2, 4, 4].length) (baseStart_917550 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_917550 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_917550 prefixEnd_917550 := by exact prefixLift 917550
  have htrace : WordTrace (prefixWord ++ tailWord_917550) baseStart_917550 baseEnd_917550 := by
    simpa [prefixWord, tailWord_917550, baseEnd_917550] using wordTrace_append hprefix tailTrace_917550
  have hstable : (prefixWord ++ tailWord_917550).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_917550).length < 2 ^ (prefixWord ++ tailWord_917550).sum := by decide
  have hdescent : baseEnd_917550 < baseStart_917550 := by decide
  rcases family_descends (prefixWord ++ tailWord_917550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_917623 : List Nat := [1, 1, 3, 1, 1, 6, 1, 3, 5]
def baseStart_917623 : Nat := 118140960795 + 917623 * 2 ^ 59
def prefixEnd_917623 : Nat := 4983230072969 + 3 ^ 40 * 917623 * 2
def baseEnd_917623 : Nat := 104707035249059673220541

theorem tailTrace_917623 : CollatzResearch.WordTrace tailWord_917623 prefixEnd_917623 104707035249059673220541 := by
  unfold tailWord_917623
  simp only [CollatzResearch.WordTrace]
  refine ⟨33468460354616063376589523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22312306903077375584393015 33468460354616063376589523)
  ·
    refine ⟨50202690531924095064884285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33468460354616063376589523 50202690531924095064884285)
    ·
      refine ⟨18826008949471535649331607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50202690531924095064884285 18826008949471535649331607)
      ·
        refine ⟨28239013424207303473997411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18826008949471535649331607 28239013424207303473997411)
        ·
          refine ⟨42358520136310955210996117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28239013424207303473997411 42358520136310955210996117)
          ·
            refine ⟨1985555631389576025515443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 42358520136310955210996117 1985555631389576025515443)
            ·
              refine ⟨2978333447084364038273165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1985555631389576025515443 2978333447084364038273165)
              ·
                refine ⟨1116875042656636514352437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2978333447084364038273165 1116875042656636514352437)
                ·
                  refine ⟨104707035249059673220541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1116875042656636514352437 104707035249059673220541)
                  ·
                    rfl

theorem cell22_917623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 6, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 6, 1, 3, 5].length) (baseStart_917623 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_917623 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_917623 prefixEnd_917623 := by exact prefixLift 917623
  have htrace : WordTrace (prefixWord ++ tailWord_917623) baseStart_917623 baseEnd_917623 := by
    simpa [prefixWord, tailWord_917623, baseEnd_917623] using wordTrace_append hprefix tailTrace_917623
  have hstable : (prefixWord ++ tailWord_917623).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_917623).length < 2 ^ (prefixWord ++ tailWord_917623).sum := by decide
  have hdescent : baseEnd_917623 < baseStart_917623 := by decide
  rcases family_descends (prefixWord ++ tailWord_917623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_917683 : List Nat := [1, 1, 1, 2, 3, 2, 1, 2, 6, 3]
def baseStart_917683 : Nat := 118140960795 + 917683 * 2 ^ 59
def prefixEnd_917683 : Nat := 4983230072969 + 3 ^ 40 * 917683 * 2
def baseEnd_917683 : Nat := 314141644973358863161439

theorem tailTrace_917683 : CollatzResearch.WordTrace tailWord_917683 prefixEnd_917683 314141644973358863161439 := by
  unfold tailWord_917683
  simp only [CollatzResearch.WordTrace]
  refine ⟨33470648734398693623773703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22313765822932462415849135 33470648734398693623773703)
  ·
    refine ⟨50205973101598040435660555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33470648734398693623773703 50205973101598040435660555)
    ·
      refine ⟨75308959652397060653490833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50205973101598040435660555 75308959652397060653490833)
      ·
        refine ⟨56481719739297795490118125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75308959652397060653490833 56481719739297795490118125)
        ·
          refine ⟨21180644902236673308794297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56481719739297795490118125 21180644902236673308794297)
          ·
            refine ⟨15885483676677504981595723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21180644902236673308794297 15885483676677504981595723)
            ·
              refine ⟨23828225515016257472393585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15885483676677504981595723 23828225515016257472393585)
              ·
                refine ⟨17871169136262193104295189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23828225515016257472393585 17871169136262193104295189)
                ·
                  refine ⟨837711053262290301763837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 17871169136262193104295189 837711053262290301763837)
                  ·
                    refine ⟨314141644973358863161439, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 837711053262290301763837 314141644973358863161439)
                    ·
                      rfl

theorem cell22_917683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 2, 6, 3].length) (baseStart_917683 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_917683 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_917683 prefixEnd_917683 := by exact prefixLift 917683
  have htrace : WordTrace (prefixWord ++ tailWord_917683) baseStart_917683 baseEnd_917683 := by
    simpa [prefixWord, tailWord_917683, baseEnd_917683] using wordTrace_append hprefix tailTrace_917683
  have hstable : (prefixWord ++ tailWord_917683).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_917683).length < 2 ^ (prefixWord ++ tailWord_917683).sum := by decide
  have hdescent : baseEnd_917683 < baseStart_917683 := by decide
  rcases family_descends (prefixWord ++ tailWord_917683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_917700 : List Nat := [2, 3, 3, 1, 2, 1, 2, 2, 1, 5]
def baseStart_917700 : Nat := 118140960795 + 917700 * 2 ^ 59
def prefixEnd_917700 : Nat := 4983230072969 + 3 ^ 40 * 917700 * 2
def baseEnd_917700 : Nat := 314147464420776485486387

theorem tailTrace_917700 : CollatzResearch.WordTrace tailWord_917700 prefixEnd_917700 314147464420776485486387 := by
  unfold tailWord_917700
  simp only [CollatzResearch.WordTrace]
  refine ⟨16735634387668552763571277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22314179183558070351428369 16735634387668552763571277)
  ·
    refine ⟨6275862895375707286339229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16735634387668552763571277 6275862895375707286339229)
    ·
      refine ⟨2353448585765890232377211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6275862895375707286339229 2353448585765890232377211)
      ·
        refine ⟨3530172878648835348565817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2353448585765890232377211 3530172878648835348565817)
        ·
          refine ⟨2647629658986626511424363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3530172878648835348565817 2647629658986626511424363)
          ·
            refine ⟨3971444488479939767136545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2647629658986626511424363 3971444488479939767136545)
            ·
              refine ⟨2978583366359954825352409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3971444488479939767136545 2978583366359954825352409)
              ·
                refine ⟨2233937524769966119014307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2978583366359954825352409 2233937524769966119014307)
                ·
                  refine ⟨3350906287154949178521461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2233937524769966119014307 3350906287154949178521461)
                  ·
                    refine ⟨314147464420776485486387, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3350906287154949178521461 314147464420776485486387)
                    ·
                      rfl

theorem cell22_917700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 2, 2, 1, 5].length) (baseStart_917700 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_917700 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_917700 prefixEnd_917700 := by exact prefixLift 917700
  have htrace : WordTrace (prefixWord ++ tailWord_917700) baseStart_917700 baseEnd_917700 := by
    simpa [prefixWord, tailWord_917700, baseEnd_917700] using wordTrace_append hprefix tailTrace_917700
  have hstable : (prefixWord ++ tailWord_917700).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_917700).length < 2 ^ (prefixWord ++ tailWord_917700).sum := by decide
  have hdescent : baseEnd_917700 < baseStart_917700 := by decide
  rcases family_descends (prefixWord ++ tailWord_917700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_917717 : List Nat := [1, 3, 2, 4, 2, 1, 1, 1, 4, 3]
def baseStart_917717 : Nat := 118140960795 + 917717 * 2 ^ 59
def prefixEnd_917717 : Nat := 4983230072969 + 3 ^ 40 * 917717 * 2
def baseEnd_917717 : Nat := 314153283868194107811335

theorem tailTrace_917717 : CollatzResearch.WordTrace tailWord_917717 prefixEnd_917717 314153283868194107811335 := by
  unfold tailWord_917717
  simp only [CollatzResearch.WordTrace]
  refine ⟨33471888816275517430511405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22314592544183678287007603 33471888816275517430511405)
  ·
    refine ⟨12551958306103319036441777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33471888816275517430511405 12551958306103319036441777)
    ·
      refine ⟨9413968729577489277331333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12551958306103319036441777 9413968729577489277331333)
      ·
        refine ⟨1765119136795779239499625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9413968729577489277331333 1765119136795779239499625)
        ·
          refine ⟨1323839352596834429624719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1765119136795779239499625 1323839352596834429624719)
          ·
            refine ⟨1985759028895251644437079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1323839352596834429624719 1985759028895251644437079)
            ·
              refine ⟨2978638543342877466655619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1985759028895251644437079 2978638543342877466655619)
              ·
                refine ⟨4467957815014316199983429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2978638543342877466655619 4467957815014316199983429)
                ·
                  refine ⟨837742090315184287496893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4467957815014316199983429 837742090315184287496893)
                  ·
                    refine ⟨314153283868194107811335, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 837742090315184287496893 314153283868194107811335)
                    ·
                      rfl

theorem cell22_917717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 1, 1, 1, 4, 3].length) (baseStart_917717 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_917717 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_917717 prefixEnd_917717 := by exact prefixLift 917717
  have htrace : WordTrace (prefixWord ++ tailWord_917717) baseStart_917717 baseEnd_917717 := by
    simpa [prefixWord, tailWord_917717, baseEnd_917717] using wordTrace_append hprefix tailTrace_917717
  have hstable : (prefixWord ++ tailWord_917717).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_917717).length < 2 ^ (prefixWord ++ tailWord_917717).sum := by decide
  have hdescent : baseEnd_917717 < baseStart_917717 := by decide
  rcases family_descends (prefixWord ++ tailWord_917717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_917745 : List Nat := [1, 2, 2, 2, 2, 1, 4, 2, 3, 3]
def baseStart_917745 : Nat := 118140960795 + 917745 * 2 ^ 59
def prefixEnd_917745 : Nat := 4983230072969 + 3 ^ 40 * 917745 * 2
def baseEnd_917745 : Nat := 314162868840411368111249

theorem tailTrace_917745 : CollatzResearch.WordTrace tailWord_917745 prefixEnd_917745 314162868840411368111249 := by
  unfold tailWord_917745
  simp only [CollatzResearch.WordTrace]
  refine ⟨33472910060174078212530689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22315273373449385475020459 33472910060174078212530689)
  ·
    refine ⟨25104682545130558659398017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33472910060174078212530689 25104682545130558659398017)
    ·
      refine ⟨18828511908847918994548513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25104682545130558659398017 18828511908847918994548513)
      ·
        refine ⟨14121383931635939245911385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18828511908847918994548513 14121383931635939245911385)
        ·
          refine ⟨10591037948726954434433539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14121383931635939245911385 10591037948726954434433539)
          ·
            refine ⟨15886556923090431651650309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10591037948726954434433539 15886556923090431651650309)
            ·
              refine ⟨2978729423079455934684433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15886556923090431651650309 2978729423079455934684433)
              ·
                refine ⟨2234047067309591951013325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2978729423079455934684433 2234047067309591951013325)
                ·
                  refine ⟨837767650241096981629997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2234047067309591951013325 837767650241096981629997)
                  ·
                    refine ⟨314162868840411368111249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 837767650241096981629997 314162868840411368111249)
                    ·
                      rfl

theorem cell22_917745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 4, 2, 3, 3].length) (baseStart_917745 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_917745 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_917745 prefixEnd_917745 := by exact prefixLift 917745
  have htrace : WordTrace (prefixWord ++ tailWord_917745) baseStart_917745 baseEnd_917745 := by
    simpa [prefixWord, tailWord_917745, baseEnd_917745] using wordTrace_append hprefix tailTrace_917745
  have hstable : (prefixWord ++ tailWord_917745).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_917745).length < 2 ^ (prefixWord ++ tailWord_917745).sum := by decide
  have hdescent : baseEnd_917745 < baseStart_917745 := by decide
  rcases family_descends (prefixWord ++ tailWord_917745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_917788 : List Nat := [2, 2, 3, 1, 1, 1, 1, 1, 2, 8]
def baseStart_917788 : Nat := 118140960795 + 917788 * 2 ^ 59
def prefixEnd_917788 : Nat := 4983230072969 + 3 ^ 40 * 917788 * 2
def baseEnd_917788 : Nat := 314177588619173589286117

theorem tailTrace_917788 : CollatzResearch.WordTrace tailWord_917788 prefixEnd_917788 314177588619173589286117 := by
  unfold tailWord_917788
  simp only [CollatzResearch.WordTrace]
  refine ⟨16737239199509148278173009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22316318932678864370897345 16737239199509148278173009)
  ·
    refine ⟨12552929399631861208629757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16737239199509148278173009 12552929399631861208629757)
    ·
      refine ⟨4707348524861947953236159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12552929399631861208629757 4707348524861947953236159)
      ·
        refine ⟨7061022787292921929854239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4707348524861947953236159 7061022787292921929854239)
        ·
          refine ⟨10591534180939382894781359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7061022787292921929854239 10591534180939382894781359)
          ·
            refine ⟨15887301271409074342172039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10591534180939382894781359 15887301271409074342172039)
            ·
              refine ⟨23830951907113611513258059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15887301271409074342172039 23830951907113611513258059)
              ·
                refine ⟨35746427860670417269887089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23830951907113611513258059 35746427860670417269887089)
                ·
                  refine ⟨26809820895502812952415317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35746427860670417269887089 26809820895502812952415317)
                  ·
                    refine ⟨314177588619173589286117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 26809820895502812952415317 314177588619173589286117)
                    ·
                      rfl

theorem cell22_917788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 1, 2, 8].length) (baseStart_917788 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_917788 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_917788 prefixEnd_917788 := by exact prefixLift 917788
  have htrace : WordTrace (prefixWord ++ tailWord_917788) baseStart_917788 baseEnd_917788 := by
    simpa [prefixWord, tailWord_917788, baseEnd_917788] using wordTrace_append hprefix tailTrace_917788
  have hstable : (prefixWord ++ tailWord_917788).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_917788).length < 2 ^ (prefixWord ++ tailWord_917788).sum := by decide
  have hdescent : baseEnd_917788 < baseStart_917788 := by decide
  rcases family_descends (prefixWord ++ tailWord_917788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_917792 : List Nat := [2, 1, 1, 5, 2, 1, 4, 1, 5]
def baseStart_917792 : Nat := 118140960795 + 917792 * 2 ^ 59
def prefixEnd_917792 : Nat := 4983230072969 + 3 ^ 40 * 917792 * 2
def baseEnd_917792 : Nat := 104726319300306304062035

theorem tailTrace_917792 : CollatzResearch.WordTrace tailWord_917792 prefixEnd_917792 104726319300306304062035 := by
  unfold tailWord_917792
  simp only [CollatzResearch.WordTrace]
  refine ⟨16737312145501902619745815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22316416194002536826327753 16737312145501902619745815)
  ·
    refine ⟨25105968218252853929618723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16737312145501902619745815 25105968218252853929618723)
    ·
      refine ⟨37658952327379280894428085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25105968218252853929618723 37658952327379280894428085)
      ·
        refine ⟨3530526780691807583852633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 37658952327379280894428085 3530526780691807583852633)
        ·
          refine ⟨2647895085518855687889475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3530526780691807583852633 2647895085518855687889475)
          ·
            refine ⟨3971842628278283531834213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2647895085518855687889475 3971842628278283531834213)
            ·
              refine ⟨744720492802178162218915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3971842628278283531834213 744720492802178162218915)
              ·
                refine ⟨1117080739203267243328373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 744720492802178162218915 1117080739203267243328373)
                ·
                  refine ⟨104726319300306304062035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1117080739203267243328373 104726319300306304062035)
                  ·
                    rfl

theorem cell22_917792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 4, 1, 5].length) (baseStart_917792 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_917792 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_917792 prefixEnd_917792 := by exact prefixLift 917792
  have htrace : WordTrace (prefixWord ++ tailWord_917792) baseStart_917792 baseEnd_917792 := by
    simpa [prefixWord, tailWord_917792, baseEnd_917792] using wordTrace_append hprefix tailTrace_917792
  have hstable : (prefixWord ++ tailWord_917792).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_917792).length < 2 ^ (prefixWord ++ tailWord_917792).sum := by decide
  have hdescent : baseEnd_917792 < baseStart_917792 := by decide
  rcases family_descends (prefixWord ++ tailWord_917792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_917833 : List Nat := [1, 2, 1, 1, 2, 3, 1, 2, 3, 6]
def baseStart_917833 : Nat := 118140960795 + 917833 * 2 ^ 59
def prefixEnd_917833 : Nat := 4983230072969 + 3 ^ 40 * 917833 * 2
def baseEnd_917833 : Nat := 314192993038808471910979

theorem tailTrace_917833 : CollatzResearch.WordTrace tailWord_917833 prefixEnd_917833 314192993038808471910979 := by
  unfold tailWord_917833
  simp only [CollatzResearch.WordTrace]
  refine ⟨33476119683855269241734153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22317413122570179494489435 33476119683855269241734153)
  ·
    refine ⟨25107089762891451931300615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33476119683855269241734153 25107089762891451931300615)
    ·
      refine ⟨37660634644337177896950923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25107089762891451931300615 37660634644337177896950923)
      ·
        refine ⟨56490951966505766845426385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37660634644337177896950923 56490951966505766845426385)
        ·
          refine ⟨42368213974879325134069789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56490951966505766845426385 42368213974879325134069789)
          ·
            refine ⟨15888080240579746925276171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42368213974879325134069789 15888080240579746925276171)
            ·
              refine ⟨23832120360869620387914257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15888080240579746925276171 23832120360869620387914257)
              ·
                refine ⟨17874090270652215290935693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23832120360869620387914257 17874090270652215290935693)
                ·
                  refine ⟨6702783851494580734100885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17874090270652215290935693 6702783851494580734100885)
                  ·
                    refine ⟨314192993038808471910979, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6702783851494580734100885 314192993038808471910979)
                    ·
                      rfl

theorem cell22_917833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 2, 3, 6].length) (baseStart_917833 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_917833 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_917833 prefixEnd_917833 := by exact prefixLift 917833
  have htrace : WordTrace (prefixWord ++ tailWord_917833) baseStart_917833 baseEnd_917833 := by
    simpa [prefixWord, tailWord_917833, baseEnd_917833] using wordTrace_append hprefix tailTrace_917833
  have hstable : (prefixWord ++ tailWord_917833).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_917833).length < 2 ^ (prefixWord ++ tailWord_917833).sum := by decide
  have hdescent : baseEnd_917833 < baseStart_917833 := by decide
  rcases family_descends (prefixWord ++ tailWord_917833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_917848 : List Nat := [2, 1, 2, 2, 1, 1, 2, 11]
def baseStart_917848 : Nat := 118140960795 + 917848 * 2 ^ 59
def prefixEnd_917848 : Nat := 4983230072969 + 3 ^ 40 * 917848 * 2
def baseEnd_917848 : Nat := 34910903093928159198437

theorem tailTrace_917848 : CollatzResearch.WordTrace tailWord_917848 prefixEnd_917848 34910903093928159198437 := by
  unfold tailWord_917848
  simp only [CollatzResearch.WordTrace]
  refine ⟨16738333389400463401765099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22317777852533951202353465 16738333389400463401765099)
  ·
    refine ⟨25107500084100695102647649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16738333389400463401765099 25107500084100695102647649)
    ·
      refine ⟨18830625063075521326985737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25107500084100695102647649 18830625063075521326985737)
      ·
        refine ⟨14122968797306640995239303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18830625063075521326985737 14122968797306640995239303)
        ·
          refine ⟨21184453195959961492858955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14122968797306640995239303 21184453195959961492858955)
          ·
            refine ⟨31776679793939942239288433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21184453195959961492858955 31776679793939942239288433)
            ·
              refine ⟨23832509845454956679466325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31776679793939942239288433 23832509845454956679466325)
              ·
                refine ⟨34910903093928159198437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 23832509845454956679466325 34910903093928159198437)
                ·
                  rfl

theorem cell22_917848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 11].length) (baseStart_917848 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_917848 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_917848 prefixEnd_917848 := by exact prefixLift 917848
  have htrace : WordTrace (prefixWord ++ tailWord_917848) baseStart_917848 baseEnd_917848 := by
    simpa [prefixWord, tailWord_917848, baseEnd_917848] using wordTrace_append hprefix tailTrace_917848
  have hstable : (prefixWord ++ tailWord_917848).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_917848).length < 2 ^ (prefixWord ++ tailWord_917848).sum := by decide
  have hdescent : baseEnd_917848 < baseStart_917848 := by decide
  rcases family_descends (prefixWord ++ tailWord_917848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_917865 : List Nat := [1, 2, 1, 1, 1, 3, 7, 6]
def baseStart_917865 : Nat := 118140960795 + 917865 * 2 ^ 59
def prefixEnd_917865 : Nat := 4983230072969 + 3 ^ 40 * 917865 * 2
def baseEnd_917865 : Nat := 34911549699196783901209

theorem tailTrace_917865 : CollatzResearch.WordTrace tailWord_917865 prefixEnd_917865 34911549699196783901209 := by
  unfold tailWord_917865
  simp only [CollatzResearch.WordTrace]
  refine ⟨33477286819739338706899049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22318191213159559137932699 33477286819739338706899049)
  ·
    refine ⟨25107965114804504030174287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33477286819739338706899049 25107965114804504030174287)
    ·
      refine ⟨37661947672206756045261431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25107965114804504030174287 37661947672206756045261431)
      ·
        refine ⟨56492921508310134067892147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37661947672206756045261431 56492921508310134067892147)
        ·
          refine ⟨84739382262465201101838221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56492921508310134067892147 84739382262465201101838221)
          ·
            refine ⟨31777268348424450413189333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 84739382262465201101838221 31777268348424450413189333)
            ·
              refine ⟨744779726916198056559125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 31777268348424450413189333 744779726916198056559125)
              ·
                refine ⟨34911549699196783901209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 744779726916198056559125 34911549699196783901209)
                ·
                  rfl

theorem cell22_917865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 7, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 7, 6].length) (baseStart_917865 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_917865 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_917865 prefixEnd_917865 := by exact prefixLift 917865
  have htrace : WordTrace (prefixWord ++ tailWord_917865) baseStart_917865 baseEnd_917865 := by
    simpa [prefixWord, tailWord_917865, baseEnd_917865] using wordTrace_append hprefix tailTrace_917865
  have hstable : (prefixWord ++ tailWord_917865).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_917865).length < 2 ^ (prefixWord ++ tailWord_917865).sum := by decide
  have hdescent : baseEnd_917865 < baseStart_917865 := by decide
  rcases family_descends (prefixWord ++ tailWord_917865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_917897 : List Nat := [1, 2, 1, 1, 6, 1, 1, 3, 3, 3]
def baseStart_917897 : Nat := 118140960795 + 917897 * 2 ^ 59
def prefixEnd_917897 : Nat := 4983230072969 + 3 ^ 40 * 917897 * 2
def baseEnd_917897 : Nat := 314214901546733638310783

theorem tailTrace_917897 : CollatzResearch.WordTrace tailWord_917897 prefixEnd_917897 314214901546733638310783 := by
  unfold tailWord_917897
  simp only [CollatzResearch.WordTrace]
  refine ⟨33478453955623408172063945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22318969303748938781375963 33478453955623408172063945)
  ·
    refine ⟨25108840466717556129047959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33478453955623408172063945 25108840466717556129047959)
    ·
      refine ⟨37663260700076334193571939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25108840466717556129047959 37663260700076334193571939)
      ·
        refine ⟨56494891050114501290357909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37663260700076334193571939 56494891050114501290357909)
        ·
          refine ⟨2648198017974117247985527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 56494891050114501290357909 2648198017974117247985527)
          ·
            refine ⟨3972297026961175871978291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2648198017974117247985527 3972297026961175871978291)
            ·
              refine ⟨5958445540441763807967437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3972297026961175871978291 5958445540441763807967437)
              ·
                refine ⟨2234417077665661427987789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5958445540441763807967437 2234417077665661427987789)
                ·
                  refine ⟨837906404124623035495421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2234417077665661427987789 837906404124623035495421)
                  ·
                    refine ⟨314214901546733638310783, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 837906404124623035495421 314214901546733638310783)
                    ·
                      rfl

theorem cell22_917897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 1, 3, 3, 3].length) (baseStart_917897 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_917897 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_917897 prefixEnd_917897 := by exact prefixLift 917897
  have htrace : WordTrace (prefixWord ++ tailWord_917897) baseStart_917897 baseEnd_917897 := by
    simpa [prefixWord, tailWord_917897, baseEnd_917897] using wordTrace_append hprefix tailTrace_917897
  have hstable : (prefixWord ++ tailWord_917897).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_917897).length < 2 ^ (prefixWord ++ tailWord_917897).sum := by decide
  have hdescent : baseEnd_917897 < baseStart_917897 := by decide
  rcases family_descends (prefixWord ++ tailWord_917897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_917948 : List Nat := [2, 2, 2, 4, 1, 2, 3, 2, 1, 3]
def baseStart_917948 : Nat := 118140960795 + 917948 * 2 ^ 59
def prefixEnd_917948 : Nat := 4983230072969 + 3 ^ 40 * 917948 * 2
def baseEnd_917948 : Nat := 314232359888986505285627

theorem tailTrace_917948 : CollatzResearch.WordTrace tailWord_917948 prefixEnd_917948 314232359888986505285627 := by
  unfold tailWord_917948
  simp only [CollatzResearch.WordTrace]
  refine ⟨16740157039219321941085249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22320209385625762588113665 16740157039219321941085249)
  ·
    refine ⟨12555117779414491455813937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16740157039219321941085249 12555117779414491455813937)
    ·
      refine ⟨9416338334560868591860453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12555117779414491455813937 9416338334560868591860453)
      ·
        refine ⟨1765563437730162860973835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9416338334560868591860453 1765563437730162860973835)
        ·
          refine ⟨2648345156595244291460753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1765563437730162860973835 2648345156595244291460753)
          ·
            refine ⟨1986258867446433218595565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2648345156595244291460753 1986258867446433218595565)
            ·
              refine ⟨744847075292412456973337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1986258867446433218595565 744847075292412456973337)
              ·
                refine ⟨558635306469309342730003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 744847075292412456973337 558635306469309342730003)
                ·
                  refine ⟨837952959703964014095005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 558635306469309342730003 837952959703964014095005)
                  ·
                    refine ⟨314232359888986505285627, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 837952959703964014095005 314232359888986505285627)
                    ·
                      rfl

theorem cell22_917948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 2, 3, 2, 1, 3].length) (baseStart_917948 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_917948 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_917948 prefixEnd_917948 := by exact prefixLift 917948
  have htrace : WordTrace (prefixWord ++ tailWord_917948) baseStart_917948 baseEnd_917948 := by
    simpa [prefixWord, tailWord_917948, baseEnd_917948] using wordTrace_append hprefix tailTrace_917948
  have hstable : (prefixWord ++ tailWord_917948).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_917948).length < 2 ^ (prefixWord ++ tailWord_917948).sum := by decide
  have hdescent : baseEnd_917948 < baseStart_917948 := by decide
  rcases family_descends (prefixWord ++ tailWord_917948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_917974 : List Nat := [5, 2, 1, 1, 1, 1, 3, 1, 3, 4]
def baseStart_917974 : Nat := 118140960795 + 917974 * 2 ^ 59
def prefixEnd_917974 : Nat := 4983230072969 + 3 ^ 40 * 917974 * 2
def baseEnd_917974 : Nat := 314241260220331104135547

theorem tailTrace_917974 : CollatzResearch.WordTrace tailWord_917974 prefixEnd_917974 314241260220331104135547 := by
  unfold tailWord_917974
  simp only [CollatzResearch.WordTrace]
  refine ⟨2092578898521528145163561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 22320841584229633548411317 2092578898521528145163561)
  ·
    refine ⟨1569434173891146108872671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2092578898521528145163561 1569434173891146108872671)
    ·
      refine ⟨2354151260836719163309007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1569434173891146108872671 2354151260836719163309007)
      ·
        refine ⟨3531226891255078744963511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2354151260836719163309007 3531226891255078744963511)
        ·
          refine ⟨5296840336882618117445267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3531226891255078744963511 5296840336882618117445267)
          ·
            refine ⟨7945260505323927176167901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5296840336882618117445267 7945260505323927176167901)
            ·
              refine ⟨2979472689496472691062963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7945260505323927176167901 2979472689496472691062963)
              ·
                refine ⟨4469209034244709036594445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2979472689496472691062963 4469209034244709036594445)
                ·
                  refine ⟨1675953387841765888722917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4469209034244709036594445 1675953387841765888722917)
                  ·
                    refine ⟨314241260220331104135547, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1675953387841765888722917 314241260220331104135547)
                    ·
                      rfl

theorem cell22_917974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 3, 1, 3, 4].length) (baseStart_917974 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_917974 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_917974 prefixEnd_917974 := by exact prefixLift 917974
  have htrace : WordTrace (prefixWord ++ tailWord_917974) baseStart_917974 baseEnd_917974 := by
    simpa [prefixWord, tailWord_917974, baseEnd_917974] using wordTrace_append hprefix tailTrace_917974
  have hstable : (prefixWord ++ tailWord_917974).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_917974).length < 2 ^ (prefixWord ++ tailWord_917974).sum := by decide
  have hdescent : baseEnd_917974 < baseStart_917974 := by decide
  rcases family_descends (prefixWord ++ tailWord_917974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_918017 : List Nat := [1, 2, 4, 1, 3, 1, 3, 7]
def baseStart_918017 : Nat := 118140960795 + 918017 * 2 ^ 59
def prefixEnd_918017 : Nat := 4983230072969 + 3 ^ 40 * 918017 * 2
def baseEnd_918017 : Nat := 34917331111010369478935

theorem tailTrace_918017 : CollatzResearch.WordTrace tailWord_918017 prefixEnd_918017 34917331111010369478935 := by
  unfold tailWord_918017
  simp only [CollatzResearch.WordTrace]
  refine ⟨33482830715188668666432305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22321887143459112444288203 33482830715188668666432305)
  ·
    refine ⟨25112123036391501499824229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33482830715188668666432305 25112123036391501499824229)
    ·
      refine ⟨4708523069323406531217043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25112123036391501499824229 4708523069323406531217043)
      ·
        refine ⟨7062784603985109796825565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4708523069323406531217043 7062784603985109796825565)
        ·
          refine ⟨2648544226494416173809587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7062784603985109796825565 2648544226494416173809587)
          ·
            refine ⟨3972816339741624260714381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2648544226494416173809587 3972816339741624260714381)
            ·
              refine ⟨1489806127403109097767893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3972816339741624260714381 1489806127403109097767893)
              ·
                refine ⟨34917331111010369478935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1489806127403109097767893 34917331111010369478935)
                ·
                  rfl

theorem cell22_918017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 3, 7].length) (baseStart_918017 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_918017 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_918017 prefixEnd_918017 := by exact prefixLift 918017
  have htrace : WordTrace (prefixWord ++ tailWord_918017) baseStart_918017 baseEnd_918017 := by
    simpa [prefixWord, tailWord_918017, baseEnd_918017] using wordTrace_append hprefix tailTrace_918017
  have hstable : (prefixWord ++ tailWord_918017).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_918017).length < 2 ^ (prefixWord ++ tailWord_918017).sum := by decide
  have hdescent : baseEnd_918017 < baseStart_918017 := by decide
  rcases family_descends (prefixWord ++ tailWord_918017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_918036 : List Nat := [2, 4, 3, 1, 1, 1, 3, 1, 2, 4]
def baseStart_918036 : Nat := 118140960795 + 918036 * 2 ^ 59
def prefixEnd_918036 : Nat := 4983230072969 + 3 ^ 40 * 918036 * 2
def baseEnd_918036 : Nat := 314262484087383609085357

theorem tailTrace_918036 : CollatzResearch.WordTrace tailWord_918036 prefixEnd_918036 314262484087383609085357 := by
  unfold tailWord_918036
  simp only [CollatzResearch.WordTrace]
  refine ⟨16741761851059917455686981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22322349134746556607582641 16741761851059917455686981)
  ·
    refine ⟨3139080347073734522941309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16741761851059917455686981 3139080347073734522941309)
    ·
      refine ⟨1177155130152650446102991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3139080347073734522941309 1177155130152650446102991)
      ·
        refine ⟨1765732695228975669154487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1177155130152650446102991 1765732695228975669154487)
        ·
          refine ⟨2648599042843463503731731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1765732695228975669154487 2648599042843463503731731)
          ·
            refine ⟨3972898564265195255597597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2648599042843463503731731 3972898564265195255597597)
            ·
              refine ⟨1489836961599448220849099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3972898564265195255597597 1489836961599448220849099)
              ·
                refine ⟨2234755442399172331273649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1489836961599448220849099 2234755442399172331273649)
                ·
                  refine ⟨1676066581799379248455237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2234755442399172331273649 1676066581799379248455237)
                  ·
                    refine ⟨314262484087383609085357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1676066581799379248455237 314262484087383609085357)
                    ·
                      rfl

theorem cell22_918036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 3, 1, 2, 4].length) (baseStart_918036 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_918036 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_918036 prefixEnd_918036 := by exact prefixLift 918036
  have htrace : WordTrace (prefixWord ++ tailWord_918036) baseStart_918036 baseEnd_918036 := by
    simpa [prefixWord, tailWord_918036, baseEnd_918036] using wordTrace_append hprefix tailTrace_918036
  have hstable : (prefixWord ++ tailWord_918036).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_918036).length < 2 ^ (prefixWord ++ tailWord_918036).sum := by decide
  have hdescent : baseEnd_918036 < baseStart_918036 := by decide
  rcases family_descends (prefixWord ++ tailWord_918036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_918055 : List Nat := [1, 1, 7, 2, 1, 2, 1, 2, 2, 3]
def baseStart_918055 : Nat := 118140960795 + 918055 * 2 ^ 59
def prefixEnd_918055 : Nat := 4983230072969 + 3 ^ 40 * 918055 * 2
def baseEnd_918055 : Nat := 314268988175673892860299

theorem tailTrace_918055 : CollatzResearch.WordTrace tailWord_918055 prefixEnd_918055 314268988175673892860299 := by
  unfold tailWord_918055
  simp only [CollatzResearch.WordTrace]
  refine ⟨33484216689051001156315619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22322811126034000770877079 33484216689051001156315619)
  ·
    refine ⟨50226325033576501734473429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33484216689051001156315619 50226325033576501734473429)
    ·
      refine ⟨1177179492974449259401721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 50226325033576501734473429 1177179492974449259401721)
      ·
        refine ⟨882884619730836944551291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1177179492974449259401721 882884619730836944551291)
        ·
          refine ⟨1324326929596255416826937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 882884619730836944551291 1324326929596255416826937)
          ·
            refine ⟨993245197197191562620203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1324326929596255416826937 993245197197191562620203)
            ·
              refine ⟨1489867795795787343930305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 993245197197191562620203 1489867795795787343930305)
              ·
                refine ⟨1117400846846840507947729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1489867795795787343930305 1117400846846840507947729)
                ·
                  refine ⟨838050635135130380960797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1117400846846840507947729 838050635135130380960797)
                  ·
                    refine ⟨314268988175673892860299, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 838050635135130380960797 314268988175673892860299)
                    ·
                      rfl

theorem cell22_918055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 2, 1, 2, 2, 3].length) (baseStart_918055 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_918055 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_918055 prefixEnd_918055 := by exact prefixLift 918055
  have htrace : WordTrace (prefixWord ++ tailWord_918055) baseStart_918055 baseEnd_918055 := by
    simpa [prefixWord, tailWord_918055, baseEnd_918055] using wordTrace_append hprefix tailTrace_918055
  have hstable : (prefixWord ++ tailWord_918055).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_918055).length < 2 ^ (prefixWord ++ tailWord_918055).sum := by decide
  have hdescent : baseEnd_918055 < baseStart_918055 := by decide
  rcases family_descends (prefixWord ++ tailWord_918055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_918066 : List Nat := [3, 2, 1, 1, 2, 1, 4, 4, 1, 3]
def baseStart_918066 : Nat := 118140960795 + 918066 * 2 ^ 59
def prefixEnd_918066 : Nat := 4983230072969 + 3 ^ 40 * 918066 * 2
def baseEnd_918066 : Nat := 314272753700473530835265

theorem tailTrace_918066 : CollatzResearch.WordTrace tailWord_918066 prefixEnd_918066 314272753700473530835265 := by
  unfold tailWord_918066
  simp only [CollatzResearch.WordTrace]
  refine ⟨8371154473002787508741513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22323078594674100023310701 8371154473002787508741513)
  ·
    refine ⟨6278365854752090631556135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8371154473002787508741513 6278365854752090631556135)
    ·
      refine ⟨9417548782128135947334203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6278365854752090631556135 9417548782128135947334203)
      ·
        refine ⟨14126323173192203921001305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9417548782128135947334203 14126323173192203921001305)
        ·
          refine ⟨10594742379894152940750979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14126323173192203921001305 10594742379894152940750979)
          ·
            refine ⟨15892113569841229411126469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10594742379894152940750979 15892113569841229411126469)
            ·
              refine ⟨2979771294345230514586213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15892113569841229411126469 2979771294345230514586213)
              ·
                refine ⟨558707117689730721484915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2979771294345230514586213 558707117689730721484915)
                ·
                  refine ⟨838060676534596082227373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 558707117689730721484915 838060676534596082227373)
                  ·
                    refine ⟨314272753700473530835265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 838060676534596082227373 314272753700473530835265)
                    ·
                      rfl

theorem cell22_918066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 4, 4, 1, 3].length) (baseStart_918066 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_918066 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_918066 prefixEnd_918066 := by exact prefixLift 918066
  have htrace : WordTrace (prefixWord ++ tailWord_918066) baseStart_918066 baseEnd_918066 := by
    simpa [prefixWord, tailWord_918066, baseEnd_918066] using wordTrace_append hprefix tailTrace_918066
  have hstable : (prefixWord ++ tailWord_918066).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_918066).length < 2 ^ (prefixWord ++ tailWord_918066).sum := by decide
  have hdescent : baseEnd_918066 < baseStart_918066 := by decide
  rcases family_descends (prefixWord ++ tailWord_918066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_918079 : List Nat := [1, 1, 2, 2, 3, 2, 5, 1, 5]
def baseStart_918079 : Nat := 118140960795 + 918079 * 2 ^ 59
def prefixEnd_918079 : Nat := 4983230072969 + 3 ^ 40 * 918079 * 2
def baseEnd_918079 : Nat := 104759067955381943420075

theorem tailTrace_918079 : CollatzResearch.WordTrace tailWord_918079 prefixEnd_918079 104759067955381943420075 := by
  unfold tailWord_918079
  simp only [CollatzResearch.WordTrace]
  refine ⟨33485092040964053255189291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22323394693976035503459527 33485092040964053255189291)
  ·
    refine ⟨50227638061446079882783937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33485092040964053255189291 50227638061446079882783937)
    ·
      refine ⟨37670728546084559912087953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50227638061446079882783937 37670728546084559912087953)
      ·
        refine ⟨28253046409563419934065965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37670728546084559912087953 28253046409563419934065965)
        ·
          refine ⟨10594892403586282475274737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28253046409563419934065965 10594892403586282475274737)
          ·
            refine ⟨7946169302689711856456053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10594892403586282475274737 7946169302689711856456053)
            ·
              refine ⟨744953372127160486542755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 7946169302689711856456053 744953372127160486542755)
              ·
                refine ⟨1117430058190740729814133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 744953372127160486542755 1117430058190740729814133)
                ·
                  refine ⟨104759067955381943420075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1117430058190740729814133 104759067955381943420075)
                  ·
                    rfl

theorem cell22_918079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 5, 1, 5].length) (baseStart_918079 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_918079 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_918079 prefixEnd_918079 := by exact prefixLift 918079
  have htrace : WordTrace (prefixWord ++ tailWord_918079) baseStart_918079 baseEnd_918079 := by
    simpa [prefixWord, tailWord_918079, baseEnd_918079] using wordTrace_append hprefix tailTrace_918079
  have hstable : (prefixWord ++ tailWord_918079).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_918079).length < 2 ^ (prefixWord ++ tailWord_918079).sum := by decide
  have hdescent : baseEnd_918079 < baseStart_918079 := by decide
  rcases family_descends (prefixWord ++ tailWord_918079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_918124 : List Nat := [2, 2, 1, 1, 3, 1, 2, 6, 4]
def baseStart_918124 : Nat := 118140960795 + 918124 * 2 ^ 59
def prefixEnd_918124 : Nat := 4983230072969 + 3 ^ 40 * 918124 * 2
def baseEnd_918124 : Nat := 104764202761926904295029

theorem tailTrace_918124 : CollatzResearch.WordTrace tailWord_918124 prefixEnd_918124 104764202761926904295029 := by
  unfold tailWord_918124
  simp only [CollatzResearch.WordTrace]
  refine ⟨16743366662900512970288713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22324488883867350627051617 16743366662900512970288713)
  ·
    refine ⟨12557524997175384727716535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16743366662900512970288713 12557524997175384727716535)
    ·
      refine ⟨18836287495763077091574803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12557524997175384727716535 18836287495763077091574803)
      ·
        refine ⟨28254431243644615637362205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18836287495763077091574803 28254431243644615637362205)
        ·
          refine ⟨10595411716366730864010827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28254431243644615637362205 10595411716366730864010827)
          ·
            refine ⟨15893117574550096296016241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10595411716366730864010827 15893117574550096296016241)
            ·
              refine ⟨11919838180912572222012181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15893117574550096296016241 11919838180912572222012181)
              ·
                refine ⟨558742414730276822906821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 11919838180912572222012181 558742414730276822906821)
                ·
                  refine ⟨104764202761926904295029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 558742414730276822906821 104764202761926904295029)
                  ·
                    rfl

theorem cell22_918124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 2, 6, 4].length) (baseStart_918124 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_918124 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_918124 prefixEnd_918124 := by exact prefixLift 918124
  have htrace : WordTrace (prefixWord ++ tailWord_918124) baseStart_918124 baseEnd_918124 := by
    simpa [prefixWord, tailWord_918124, baseEnd_918124] using wordTrace_append hprefix tailTrace_918124
  have hstable : (prefixWord ++ tailWord_918124).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_918124).length < 2 ^ (prefixWord ++ tailWord_918124).sum := by decide
  have hdescent : baseEnd_918124 < baseStart_918124 := by decide
  rcases family_descends (prefixWord ++ tailWord_918124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_918218 : List Nat := [3, 1, 2, 1, 4, 1, 1, 5, 1, 3]
def baseStart_918218 : Nat := 118140960795 + 918218 * 2 ^ 59
def prefixEnd_918218 : Nat := 4983230072969 + 3 ^ 40 * 918218 * 2
def baseEnd_918218 : Nat := 314324786406795801034799

theorem tailTrace_918218 : CollatzResearch.WordTrace tailWord_918218 prefixEnd_918218 314324786406795801034799 := by
  unfold tailWord_918218
  simp only [CollatzResearch.WordTrace]
  refine ⟨8372540446865119998624827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22326774524973653329666205 8372540446865119998624827)
  ·
    refine ⟨12558810670297679997937241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8372540446865119998624827 12558810670297679997937241)
    ·
      refine ⟨9419108002723259998452931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12558810670297679997937241 9419108002723259998452931)
      ·
        refine ⟨14128662004084889997679397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9419108002723259998452931 14128662004084889997679397)
        ·
          refine ⟨2649124125765916874564887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14128662004084889997679397 2649124125765916874564887)
          ·
            refine ⟨3973686188648875311847331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2649124125765916874564887 3973686188648875311847331)
            ·
              refine ⟨5960529282973312967770997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3973686188648875311847331 5960529282973312967770997)
              ·
                refine ⟨558799620278748090728531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5960529282973312967770997 558799620278748090728531)
                ·
                  refine ⟨838199430418122136092797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 558799620278748090728531 838199430418122136092797)
                  ·
                    refine ⟨314324786406795801034799, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 838199430418122136092797 314324786406795801034799)
                    ·
                      rfl

theorem cell22_918218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 1, 5, 1, 3].length) (baseStart_918218 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_918218 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_918218 prefixEnd_918218 := by exact prefixLift 918218
  have htrace : WordTrace (prefixWord ++ tailWord_918218) baseStart_918218 baseEnd_918218 := by
    simpa [prefixWord, tailWord_918218, baseEnd_918218] using wordTrace_append hprefix tailTrace_918218
  have hstable : (prefixWord ++ tailWord_918218).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_918218).length < 2 ^ (prefixWord ++ tailWord_918218).sum := by decide
  have hdescent : baseEnd_918218 < baseStart_918218 := by decide
  rcases family_descends (prefixWord ++ tailWord_918218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_918231 : List Nat := [1, 1, 3, 2, 1, 6, 1, 2, 5]
def baseStart_918231 : Nat := 118140960795 + 918231 * 2 ^ 59
def prefixEnd_918231 : Nat := 4983230072969 + 3 ^ 40 * 918231 * 2
def baseEnd_918231 : Nat := 104776412190822700153253

theorem tailTrace_918231 : CollatzResearch.WordTrace tailWord_918231 prefixEnd_918231 104776412190822700153253 := by
  unfold tailWord_918231
  simp only [CollatzResearch.WordTrace]
  refine ⟨33490635936413383214722547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22327090624275588809815031 33490635936413383214722547)
  ·
    refine ⟨50235953904620074822083821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33490635936413383214722547 50235953904620074822083821)
    ·
      refine ⟨18838482714232528058281433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50235953904620074822083821 18838482714232528058281433)
      ·
        refine ⟨14128862035674396043711075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18838482714232528058281433 14128862035674396043711075)
        ·
          refine ⟨21193293053511594065566613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14128862035674396043711075 21193293053511594065566613)
          ·
            refine ⟨993435611883355971823435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 21193293053511594065566613 993435611883355971823435)
            ·
              refine ⟨1490153417825033957735153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 993435611883355971823435 1490153417825033957735153)
              ·
                refine ⟨1117615063368775468301365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1490153417825033957735153 1117615063368775468301365)
                ·
                  refine ⟨104776412190822700153253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1117615063368775468301365 104776412190822700153253)
                  ·
                    rfl

theorem cell22_918231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 6, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 6, 1, 2, 5].length) (baseStart_918231 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_918231 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_918231 prefixEnd_918231 := by exact prefixLift 918231
  have htrace : WordTrace (prefixWord ++ tailWord_918231) baseStart_918231 baseEnd_918231 := by
    simpa [prefixWord, tailWord_918231, baseEnd_918231] using wordTrace_append hprefix tailTrace_918231
  have hstable : (prefixWord ++ tailWord_918231).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_918231).length < 2 ^ (prefixWord ++ tailWord_918231).sum := by decide
  have hdescent : baseEnd_918231 < baseStart_918231 := by decide
  rcases family_descends (prefixWord ++ tailWord_918231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_918248 : List Nat := [2, 1, 4, 1, 4, 1, 3, 1, 5]
def baseStart_918248 : Nat := 118140960795 + 918248 * 2 ^ 59
def prefixEnd_918248 : Nat := 4983230072969 + 3 ^ 40 * 918248 * 2
def baseEnd_918248 : Nat := 104778352006628574261569

theorem tailTrace_918248 : CollatzResearch.WordTrace tailWord_918248 prefixEnd_918248 104778352006628574261569 := by
  unfold tailWord_918248
  simp only [CollatzResearch.WordTrace]
  refine ⟨16745627988675897559045699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22327503984901196745394265 16745627988675897559045699)
  ·
    refine ⟨25118441983013846338568549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16745627988675897559045699 25118441983013846338568549)
    ·
      refine ⟨4709707871815096188481603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25118441983013846338568549 4709707871815096188481603)
      ·
        refine ⟨7064561807722644282722405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4709707871815096188481603 7064561807722644282722405)
        ·
          refine ⟨1324605338947995803010451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7064561807722644282722405 1324605338947995803010451)
          ·
            refine ⟨1986908008421993704515677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1324605338947995803010451 1986908008421993704515677)
            ·
              refine ⟨745090503158247639193379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1986908008421993704515677 745090503158247639193379)
              ·
                refine ⟨1117635754737371458790069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 745090503158247639193379 1117635754737371458790069)
                ·
                  refine ⟨104778352006628574261569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1117635754737371458790069 104778352006628574261569)
                  ·
                    rfl

theorem cell22_918248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 1, 3, 1, 5].length) (baseStart_918248 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_918248 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_918248 prefixEnd_918248 := by exact prefixLift 918248
  have htrace : WordTrace (prefixWord ++ tailWord_918248) baseStart_918248 baseEnd_918248 := by
    simpa [prefixWord, tailWord_918248, baseEnd_918248] using wordTrace_append hprefix tailTrace_918248
  have hstable : (prefixWord ++ tailWord_918248).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_918248).length < 2 ^ (prefixWord ++ tailWord_918248).sum := by decide
  have hdescent : baseEnd_918248 < baseStart_918248 := by decide
  rcases family_descends (prefixWord ++ tailWord_918248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_918289 : List Nat := [1, 2, 2, 1, 1, 3, 3, 1, 4, 4]
def baseStart_918289 : Nat := 118140960795 + 918289 * 2 ^ 59
def prefixEnd_918289 : Nat := 4983230072969 + 3 ^ 40 * 918289 * 2
def baseEnd_918289 : Nat := 314349091157775282509581

theorem tailTrace_918289 : CollatzResearch.WordTrace tailWord_918289 prefixEnd_918289 314349091157775282509581 := by
  unfold tailWord_918289
  simp only [CollatzResearch.WordTrace]
  refine ⟨33492751370203259120333921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22328500913468839413555947 33492751370203259120333921)
  ·
    refine ⟨25119563527652444340250441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33492751370203259120333921 25119563527652444340250441)
    ·
      refine ⟨18839672645739333255187831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25119563527652444340250441 18839672645739333255187831)
      ·
        refine ⟨28259508968608999882781747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18839672645739333255187831 28259508968608999882781747)
        ·
          refine ⟨42389263452913499824172621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28259508968608999882781747 42389263452913499824172621)
          ·
            refine ⟨15895973794842562434064733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42389263452913499824172621 15895973794842562434064733)
            ·
              refine ⟨5960990173065960912774275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15895973794842562434064733 5960990173065960912774275)
              ·
                refine ⟨8941485259598941369161413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5960990173065960912774275 8941485259598941369161413)
                ·
                  refine ⟨1676528486174801506717765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8941485259598941369161413 1676528486174801506717765)
                  ·
                    refine ⟨314349091157775282509581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1676528486174801506717765 314349091157775282509581)
                    ·
                      rfl

theorem cell22_918289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 4].length) (baseStart_918289 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_918289 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_918289 prefixEnd_918289 := by exact prefixLift 918289
  have htrace : WordTrace (prefixWord ++ tailWord_918289) baseStart_918289 baseEnd_918289 := by
    simpa [prefixWord, tailWord_918289, baseEnd_918289] using wordTrace_append hprefix tailTrace_918289
  have hstable : (prefixWord ++ tailWord_918289).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_918289).length < 2 ^ (prefixWord ++ tailWord_918289).sum := by decide
  have hdescent : baseEnd_918289 < baseStart_918289 := by decide
  rcases family_descends (prefixWord ++ tailWord_918289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_918291 : List Nat := [1, 1, 1, 2, 1, 3, 4, 4, 2, 3]
def baseStart_918291 : Nat := 118140960795 + 918291 * 2 ^ 59
def prefixEnd_918291 : Nat := 4983230072969 + 3 ^ 40 * 918291 * 2
def baseEnd_918291 : Nat := 314349775798647943959575

theorem tailTrace_918291 : CollatzResearch.WordTrace tailWord_918291 prefixEnd_918291 314349775798647943959575 := by
  unfold tailWord_918291
  simp only [CollatzResearch.WordTrace]
  refine ⟨33492824316196013461906727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22328549544130675641271151 33492824316196013461906727)
  ·
    refine ⟨50239236474294020192860091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33492824316196013461906727 50239236474294020192860091)
    ·
      refine ⟨75358854711441030289290137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50239236474294020192860091 75358854711441030289290137)
      ·
        refine ⟨56519141033580772716967603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75358854711441030289290137 56519141033580772716967603)
        ·
          refine ⟨84778711550371159075451405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56519141033580772716967603 84778711550371159075451405)
          ·
            refine ⟨31792016831389184653294277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 84778711550371159075451405 31792016831389184653294277)
            ·
              refine ⟨5961003155885472122492677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31792016831389184653294277 5961003155885472122492677)
              ·
                refine ⟨1117688091728526022967377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5961003155885472122492677 1117688091728526022967377)
                ·
                  refine ⟨838266068796394517225533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1117688091728526022967377 838266068796394517225533)
                  ·
                    refine ⟨314349775798647943959575, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 838266068796394517225533 314349775798647943959575)
                    ·
                      rfl

theorem cell22_918291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 4, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 4, 4, 2, 3].length) (baseStart_918291 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_918291 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_918291 prefixEnd_918291 := by exact prefixLift 918291
  have htrace : WordTrace (prefixWord ++ tailWord_918291) baseStart_918291 baseEnd_918291 := by
    simpa [prefixWord, tailWord_918291, baseEnd_918291] using wordTrace_append hprefix tailTrace_918291
  have hstable : (prefixWord ++ tailWord_918291).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_918291).length < 2 ^ (prefixWord ++ tailWord_918291).sum := by decide
  have hdescent : baseEnd_918291 < baseStart_918291 := by decide
  rcases family_descends (prefixWord ++ tailWord_918291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_918293 : List Nat := [1, 3, 2, 1, 2, 2, 5, 2, 4]
def baseStart_918293 : Nat := 118140960795 + 918293 * 2 ^ 59
def prefixEnd_918293 : Nat := 4983230072969 + 3 ^ 40 * 918293 * 2
def baseEnd_918293 : Nat := 104783486813173535136523

theorem tailTrace_918293 : CollatzResearch.WordTrace tailWord_918293 prefixEnd_918293 104783486813173535136523 := by
  unfold tailWord_918293
  simp only [CollatzResearch.WordTrace]
  refine ⟨33492897262188767803479533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22328598174792511868986355 33492897262188767803479533)
  ·
    refine ⟨12559836473320787926304825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33492897262188767803479533 12559836473320787926304825)
    ·
      refine ⟨9419877354990590944728619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12559836473320787926304825 9419877354990590944728619)
      ·
        refine ⟨14129816032485886417092929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9419877354990590944728619 14129816032485886417092929)
        ·
          refine ⟨10597362024364414812819697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14129816032485886417092929 10597362024364414812819697)
          ·
            refine ⟨7948021518273311109614773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10597362024364414812819697 7948021518273311109614773)
            ·
              refine ⟨745127017338122916526385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 7948021518273311109614773 745127017338122916526385)
              ·
                refine ⟨558845263003592187394789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 745127017338122916526385 558845263003592187394789)
                ·
                  refine ⟨104783486813173535136523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 558845263003592187394789 104783486813173535136523)
                  ·
                    rfl

theorem cell22_918293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 5, 2, 4].length) (baseStart_918293 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_918293 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_918293 prefixEnd_918293 := by exact prefixLift 918293
  have htrace : WordTrace (prefixWord ++ tailWord_918293) baseStart_918293 baseEnd_918293 := by
    simpa [prefixWord, tailWord_918293, baseEnd_918293] using wordTrace_append hprefix tailTrace_918293
  have hstable : (prefixWord ++ tailWord_918293).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_918293).length < 2 ^ (prefixWord ++ tailWord_918293).sum := by decide
  have hdescent : baseEnd_918293 < baseStart_918293 := by decide
  rcases family_descends (prefixWord ++ tailWord_918293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_918304 : List Nat := [2, 1, 1, 5, 1, 2, 1, 9]
def baseStart_918304 : Nat := 118140960795 + 918304 * 2 ^ 59
def prefixEnd_918304 : Nat := 4983230072969 + 3 ^ 40 * 918304 * 2
def baseEnd_918304 : Nat := 34928247329368915931615

theorem tailTrace_918304 : CollatzResearch.WordTrace tailWord_918304 prefixEnd_918304 34928247329368915931615 := by
  unfold tailWord_918304
  simp only [CollatzResearch.WordTrace]
  refine ⟨16746649232574458341064983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22328865643432611121419977 16746649232574458341064983)
  ·
    refine ⟨25119973848861687511597475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16746649232574458341064983 25119973848861687511597475)
    ·
      refine ⟨37679960773292531267396213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25119973848861687511597475 37679960773292531267396213)
      ·
        refine ⟨3532496322496174806318395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 37679960773292531267396213 3532496322496174806318395)
        ·
          refine ⟨5298744483744262209477593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3532496322496174806318395 5298744483744262209477593)
          ·
            refine ⟨3974058362808196657108195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5298744483744262209477593 3974058362808196657108195)
            ·
              refine ⟨5961087544212294985662293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3974058362808196657108195 5961087544212294985662293)
              ·
                refine ⟨34928247329368915931615, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 5961087544212294985662293 34928247329368915931615)
                ·
                  rfl

theorem cell22_918304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 1, 9].length) (baseStart_918304 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_918304 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_918304 prefixEnd_918304 := by exact prefixLift 918304
  have htrace : WordTrace (prefixWord ++ tailWord_918304) baseStart_918304 baseEnd_918304 := by
    simpa [prefixWord, tailWord_918304, baseEnd_918304] using wordTrace_append hprefix tailTrace_918304
  have hstable : (prefixWord ++ tailWord_918304).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_918304).length < 2 ^ (prefixWord ++ tailWord_918304).sum := by decide
  have hdescent : baseEnd_918304 < baseStart_918304 := by decide
  rcases family_descends (prefixWord ++ tailWord_918304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_918370 : List Nat := [3, 3, 2, 1, 3, 1, 1, 2, 3, 3]
def baseStart_918370 : Nat := 118140960795 + 918370 * 2 ^ 59
def prefixEnd_918370 : Nat := 4983230072969 + 3 ^ 40 * 918370 * 2
def baseEnd_918370 : Nat := 314376819113118071234333

theorem tailTrace_918370 : CollatzResearch.WordTrace tailWord_918370 prefixEnd_918370 314376819113118071234333 := by
  unfold tailWord_918370
  simp only [CollatzResearch.WordTrace]
  refine ⟨8373926420727452488508141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22330470455273206636021709 8373926420727452488508141)
  ·
    refine ⟨3140222407772794683190553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8373926420727452488508141 3140222407772794683190553)
    ·
      refine ⟨2355166805829596012392915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3140222407772794683190553 2355166805829596012392915)
      ·
        refine ⟨3532750208744394018589373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2355166805829596012392915 3532750208744394018589373)
        ·
          refine ⟨1324781328279147756971015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3532750208744394018589373 1324781328279147756971015)
          ·
            refine ⟨1987171992418721635456523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1324781328279147756971015 1987171992418721635456523)
            ·
              refine ⟨2980757988628082453184785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1987171992418721635456523 2980757988628082453184785)
              ·
                refine ⟨2235568491471061839888589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2980757988628082453184785 2235568491471061839888589)
                ·
                  refine ⟨838338184301648189958221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2235568491471061839888589 838338184301648189958221)
                  ·
                    refine ⟨314376819113118071234333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 838338184301648189958221 314376819113118071234333)
                    ·
                      rfl

theorem cell22_918370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 1, 1, 2, 3, 3].length) (baseStart_918370 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_918370 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_918370 prefixEnd_918370 := by exact prefixLift 918370
  have htrace : WordTrace (prefixWord ++ tailWord_918370) baseStart_918370 baseEnd_918370 := by
    simpa [prefixWord, tailWord_918370, baseEnd_918370] using wordTrace_append hprefix tailTrace_918370
  have hstable : (prefixWord ++ tailWord_918370).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_918370).length < 2 ^ (prefixWord ++ tailWord_918370).sum := by decide
  have hdescent : baseEnd_918370 < baseStart_918370 := by decide
  rcases family_descends (prefixWord ++ tailWord_918370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_918394 : List Nat := [3, 1, 1, 1, 1, 1, 3, 1, 10]
def baseStart_918394 : Nat := 118140960795 + 918394 * 2 ^ 59
def prefixEnd_918394 : Nat := 4983230072969 + 3 ^ 40 * 918394 * 2
def baseEnd_918394 : Nat := 104795011601196669544753

theorem tailTrace_918394 : CollatzResearch.WordTrace tailWord_918394 prefixEnd_918394 104795011601196669544753 := by
  unfold tailWord_918394
  simp only [CollatzResearch.WordTrace]
  refine ⟨8374145258705715513226559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22331054023215241368604157 8374145258705715513226559)
  ·
    refine ⟨12561217888058573269839839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8374145258705715513226559 12561217888058573269839839)
    ·
      refine ⟨18841826832087859904759759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12561217888058573269839839 18841826832087859904759759)
      ·
        refine ⟨28262740248131789857139639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18841826832087859904759759 28262740248131789857139639)
        ·
          refine ⟨42394110372197684785709459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28262740248131789857139639 42394110372197684785709459)
          ·
            refine ⟨63591165558296527178564189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42394110372197684785709459 63591165558296527178564189)
            ·
              refine ⟨23846687084361197691961571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 63591165558296527178564189 23846687084361197691961571)
              ·
                refine ⟨35770030626541796537942357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23846687084361197691961571 35770030626541796537942357)
                ·
                  refine ⟨104795011601196669544753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 35770030626541796537942357 104795011601196669544753)
                  ·
                    rfl

theorem cell22_918394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 1, 10].length) (baseStart_918394 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_918394 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_918394 prefixEnd_918394 := by exact prefixLift 918394
  have htrace : WordTrace (prefixWord ++ tailWord_918394) baseStart_918394 baseEnd_918394 := by
    simpa [prefixWord, tailWord_918394, baseEnd_918394] using wordTrace_append hprefix tailTrace_918394
  have hstable : (prefixWord ++ tailWord_918394).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_918394).length < 2 ^ (prefixWord ++ tailWord_918394).sum := by decide
  have hdescent : baseEnd_918394 < baseStart_918394 := by decide
  rcases family_descends (prefixWord ++ tailWord_918394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_918441 : List Nat := [1, 2, 1, 1, 1, 1, 6, 3, 2, 4]
def baseStart_918441 : Nat := 118140960795 + 918441 * 2 ^ 59
def prefixEnd_918441 : Nat := 4983230072969 + 3 ^ 40 * 918441 * 2
def baseEnd_918441 : Nat := 314401123864097552709115

theorem tailTrace_918441 : CollatzResearch.WordTrace tailWord_918441 prefixEnd_918441 314401123864097552709115 := by
  unfold tailWord_918441
  simp only [CollatzResearch.WordTrace]
  refine ⟨33498295265652589079867177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22332196843768392719911451 33498295265652589079867177)
  ·
    refine ⟨25123721449239441809900383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33498295265652589079867177 25123721449239441809900383)
    ·
      refine ⟨37685582173859162714850575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25123721449239441809900383 37685582173859162714850575)
      ·
        refine ⟨56528373260788744072275863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37685582173859162714850575 56528373260788744072275863)
        ·
          refine ⟨84792559891183116108413795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56528373260788744072275863 84792559891183116108413795)
          ·
            refine ⟨127188839836774674162620693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84792559891183116108413795 127188839836774674162620693)
            ·
              refine ⟨5961976867348812851372845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 127188839836774674162620693 5961976867348812851372845)
              ·
                refine ⟨2235741325255804819264817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5961976867348812851372845 2235741325255804819264817)
                ·
                  refine ⟨1676805993941853614448613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2235741325255804819264817 1676805993941853614448613)
                  ·
                    refine ⟨314401123864097552709115, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1676805993941853614448613 314401123864097552709115)
                    ·
                      rfl

theorem cell22_918441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 6, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 6, 3, 2, 4].length) (baseStart_918441 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_918441 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_918441 prefixEnd_918441 := by exact prefixLift 918441
  have htrace : WordTrace (prefixWord ++ tailWord_918441) baseStart_918441 baseEnd_918441 := by
    simpa [prefixWord, tailWord_918441, baseEnd_918441] using wordTrace_append hprefix tailTrace_918441
  have hstable : (prefixWord ++ tailWord_918441).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_918441).length < 2 ^ (prefixWord ++ tailWord_918441).sum := by decide
  have hdescent : baseEnd_918441 < baseStart_918441 := by decide
  rcases family_descends (prefixWord ++ tailWord_918441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_918456 : List Nat := [2, 1, 2, 1, 2, 6, 8]
def baseStart_918456 : Nat := 118140960795 + 918456 * 2 ^ 59
def prefixEnd_918456 : Nat := 4983230072969 + 3 ^ 40 * 918456 * 2
def baseEnd_918456 : Nat := 11644676247060833836447

theorem tailTrace_918456 : CollatzResearch.WordTrace tailWord_918456 prefixEnd_918456 11644676247060833836447 := by
  unfold tailWord_918456
  simp only [CollatzResearch.WordTrace]
  refine ⟨16749421180299123320831611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22332561573732164427775481 16749421180299123320831611)
  ·
    refine ⟨25124131770448684981247417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16749421180299123320831611 25124131770448684981247417)
    ·
      refine ⟨18843098827836513735935563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25124131770448684981247417 18843098827836513735935563)
      ·
        refine ⟨28264648241754770603903345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18843098827836513735935563 28264648241754770603903345)
        ·
          refine ⟨21198486181316077952927509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28264648241754770603903345 21198486181316077952927509)
          ·
            refine ⟨993679039749191154043477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 21198486181316077952927509 993679039749191154043477)
            ·
              refine ⟨11644676247060833836447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 993679039749191154043477 11644676247060833836447)
              ·
                rfl

theorem cell22_918456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 6, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 6, 8].length) (baseStart_918456 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_918456 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_918456 prefixEnd_918456 := by exact prefixLift 918456
  have htrace : WordTrace (prefixWord ++ tailWord_918456) baseStart_918456 baseEnd_918456 := by
    simpa [prefixWord, tailWord_918456, baseEnd_918456] using wordTrace_append hprefix tailTrace_918456
  have hstable : (prefixWord ++ tailWord_918456).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_918456).length < 2 ^ (prefixWord ++ tailWord_918456).sum := by decide
  have hdescent : baseEnd_918456 < baseStart_918456 := by decide
  rcases family_descends (prefixWord ++ tailWord_918456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_918580 : List Nat := [2, 5, 1, 2, 1, 1, 1, 3, 6]
def baseStart_918580 : Nat := 118140960795 + 918580 * 2 ^ 59
def prefixEnd_918580 : Nat := 4983230072969 + 3 ^ 40 * 918580 * 2
def baseEnd_918580 : Nat := 104816235468249174494563

theorem tailTrace_918580 : CollatzResearch.WordTrace tailWord_918580 prefixEnd_918580 104816235468249174494563 := by
  unfold tailWord_918580
  simp only [CollatzResearch.WordTrace]
  refine ⟨16751682506074507909588597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22335576674766010546118129 16751682506074507909588597)
  ·
    refine ⟨1570470234944485116523931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 16751682506074507909588597 1570470234944485116523931)
    ·
      refine ⟨2355705352416727674785897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1570470234944485116523931 2355705352416727674785897)
      ·
        refine ⟨1766779014312545756089423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2355705352416727674785897 1766779014312545756089423)
        ·
          refine ⟨2650168521468818634134135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1766779014312545756089423 2650168521468818634134135)
          ·
            refine ⟨3975252782203227951201203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2650168521468818634134135 3975252782203227951201203)
            ·
              refine ⟨5962879173304841926801805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3975252782203227951201203 5962879173304841926801805)
              ·
                refine ⟨2236079689989315722550677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5962879173304841926801805 2236079689989315722550677)
                ·
                  refine ⟨104816235468249174494563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2236079689989315722550677 104816235468249174494563)
                  ·
                    rfl

theorem cell22_918580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 1, 3, 6].length) (baseStart_918580 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_918580 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_918580 prefixEnd_918580 := by exact prefixLift 918580
  have htrace : WordTrace (prefixWord ++ tailWord_918580) baseStart_918580 baseEnd_918580 := by
    simpa [prefixWord, tailWord_918580, baseEnd_918580] using wordTrace_append hprefix tailTrace_918580
  have hstable : (prefixWord ++ tailWord_918580).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_918580).length < 2 ^ (prefixWord ++ tailWord_918580).sum := by decide
  have hdescent : baseEnd_918580 < baseStart_918580 := by decide
  rcases family_descends (prefixWord ++ tailWord_918580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_918591 : List Nat := [1, 1, 2, 2, 3, 1, 1, 11]
def baseStart_918591 : Nat := 118140960795 + 918591 * 2 ^ 59
def prefixEnd_918591 : Nat := 4983230072969 + 3 ^ 40 * 918591 * 2
def baseEnd_918591 : Nat := 34939163547727462384295

theorem tailTrace_918591 : CollatzResearch.WordTrace tailWord_918591 prefixEnd_918591 34939163547727462384295 := by
  unfold tailWord_918591
  simp only [CollatzResearch.WordTrace]
  refine ⟨33503766215109164697827627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22335844143406109798551751 33503766215109164697827627)
  ·
    refine ⟨50255649322663747046741441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33503766215109164697827627 50255649322663747046741441)
    ·
      refine ⟨37691736991997810285056081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50255649322663747046741441 37691736991997810285056081)
      ·
        refine ⟨28268802743998357713792061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37691736991997810285056081 28268802743998357713792061)
        ·
          refine ⟨10600801028999384142672023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28268802743998357713792061 10600801028999384142672023)
          ·
            refine ⟨15901201543499076214008035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10600801028999384142672023 15901201543499076214008035)
            ·
              refine ⟨23851802315248614321012053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15901201543499076214008035 23851802315248614321012053)
              ·
                refine ⟨34939163547727462384295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 23851802315248614321012053 34939163547727462384295)
                ·
                  rfl

theorem cell22_918591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 11].length) (baseStart_918591 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_918591 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_918591 prefixEnd_918591 := by exact prefixLift 918591
  have htrace : WordTrace (prefixWord ++ tailWord_918591) baseStart_918591 baseEnd_918591 := by
    simpa [prefixWord, tailWord_918591, baseEnd_918591] using wordTrace_append hprefix tailTrace_918591
  have hstable : (prefixWord ++ tailWord_918591).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_918591).length < 2 ^ (prefixWord ++ tailWord_918591).sum := by decide
  have hdescent : baseEnd_918591 < baseStart_918591 := by decide
  rcases family_descends (prefixWord ++ tailWord_918591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_918687 : List Nat := [1, 1, 2, 6, 2, 1, 2, 2, 5]
def baseStart_918687 : Nat := 118140960795 + 918687 * 2 ^ 59
def prefixEnd_918687 : Nat := 4983230072969 + 3 ^ 40 * 918687 * 2
def baseEnd_918687 : Nat := 104828444897144970352787

theorem tailTrace_918687 : CollatzResearch.WordTrace tailWord_918687 prefixEnd_918687 104828444897144970352787 := by
  unfold tailWord_918687
  simp only [CollatzResearch.WordTrace]
  refine ⟨33507267622761373093322315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22338178415174248728881543 33507267622761373093322315)
  ·
    refine ⟨50260901434142059639983473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33507267622761373093322315 50260901434142059639983473)
    ·
      refine ⟨37695676075606544729987605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50260901434142059639983473 37695676075606544729987605)
      ·
        refine ⟨1766984816044056784218169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 37695676075606544729987605 1766984816044056784218169)
        ·
          refine ⟨1325238612033042588163627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1766984816044056784218169 1325238612033042588163627)
          ·
            refine ⟨1987857918049563882245441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1325238612033042588163627 1987857918049563882245441)
            ·
              refine ⟨1490893438537172911684081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1987857918049563882245441 1490893438537172911684081)
              ·
                refine ⟨1118170078902879683763061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1490893438537172911684081 1118170078902879683763061)
                ·
                  refine ⟨104828444897144970352787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1118170078902879683763061 104828444897144970352787)
                  ·
                    rfl

theorem cell22_918687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 1, 2, 2, 5].length) (baseStart_918687 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_918687 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_918687 prefixEnd_918687 := by exact prefixLift 918687
  have htrace : WordTrace (prefixWord ++ tailWord_918687) baseStart_918687 baseEnd_918687 := by
    simpa [prefixWord, tailWord_918687, baseEnd_918687] using wordTrace_append hprefix tailTrace_918687
  have hstable : (prefixWord ++ tailWord_918687).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_918687).length < 2 ^ (prefixWord ++ tailWord_918687).sum := by decide
  have hdescent : baseEnd_918687 < baseStart_918687 := by decide
  rcases family_descends (prefixWord ++ tailWord_918687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_918730 : List Nat := [3, 1, 2, 1, 3, 2, 2, 2, 1, 5]
def baseStart_918730 : Nat := 118140960795 + 918730 * 2 ^ 59
def prefixEnd_918730 : Nat := 4983230072969 + 3 ^ 40 * 918730 * 2
def baseEnd_918730 : Nat := 314500054470197132233229

theorem tailTrace_918730 : CollatzResearch.WordTrace tailWord_918730 prefixEnd_918730 314500054470197132233229 := by
  unfold tailWord_918730
  simp only [CollatzResearch.WordTrace]
  refine ⟨8377208990401397859284411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22339223974403727624758429 8377208990401397859284411)
  ·
    refine ⟨12565813485602096788926617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8377208990401397859284411 12565813485602096788926617)
    ·
      refine ⟨9424360114201572591694963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12565813485602096788926617 9424360114201572591694963)
      ·
        refine ⟨14136540171302358887542445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9424360114201572591694963 14136540171302358887542445)
        ·
          refine ⟨5301202564238384582828417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14136540171302358887542445 5301202564238384582828417)
          ·
            refine ⟨3975901923178788437121313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5301202564238384582828417 3975901923178788437121313)
            ·
              refine ⟨2981926442384091327840985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3975901923178788437121313 2981926442384091327840985)
              ·
                refine ⟨2236444831788068495880739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2981926442384091327840985 2236444831788068495880739)
                ·
                  refine ⟨3354667247682102743821109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2236444831788068495880739 3354667247682102743821109)
                  ·
                    refine ⟨314500054470197132233229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3354667247682102743821109 314500054470197132233229)
                    ·
                      rfl

theorem cell22_918730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 2, 2, 1, 5].length) (baseStart_918730 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_918730 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_918730 prefixEnd_918730 := by exact prefixLift 918730
  have htrace : WordTrace (prefixWord ++ tailWord_918730) baseStart_918730 baseEnd_918730 := by
    simpa [prefixWord, tailWord_918730, baseEnd_918730] using wordTrace_append hprefix tailTrace_918730
  have hstable : (prefixWord ++ tailWord_918730).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_918730).length < 2 ^ (prefixWord ++ tailWord_918730).sum := by decide
  have hdescent : baseEnd_918730 < baseStart_918730 := by decide
  rcases family_descends (prefixWord ++ tailWord_918730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_918764 : List Nat := [2, 2, 1, 1, 2, 5, 3, 1, 2, 3]
def baseStart_918764 : Nat := 118140960795 + 918764 * 2 ^ 59
def prefixEnd_918764 : Nat := 4983230072969 + 3 ^ 40 * 918764 * 2
def baseEnd_918764 : Nat := 314511693365032376883125

theorem tailTrace_918764 : CollatzResearch.WordTrace tailWord_918764 prefixEnd_918764 314511693365032376883125 := by
  unfold tailWord_918764
  simp only [CollatzResearch.WordTrace]
  refine ⟨16755038021741207621937673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22340050695654943495916897 16755038021741207621937673)
  ·
    refine ⟨12566278516305905716453255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16755038021741207621937673 12566278516305905716453255)
    ·
      refine ⟨18849417774458858574679883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12566278516305905716453255 18849417774458858574679883)
      ·
        refine ⟨28274126661688287862019825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18849417774458858574679883 28274126661688287862019825)
        ·
          refine ⟨21205594996266215896514869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28274126661688287862019825 21205594996266215896514869)
          ·
            refine ⟨1988024530899957740298269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 21205594996266215896514869 1988024530899957740298269)
            ·
              refine ⟨745509199087484152611851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1988024530899957740298269 745509199087484152611851)
              ·
                refine ⟨1118263798631226228917777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 745509199087484152611851 1118263798631226228917777)
                ·
                  refine ⟨838697848973419671688333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1118263798631226228917777 838697848973419671688333)
                  ·
                    refine ⟨314511693365032376883125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 838697848973419671688333 314511693365032376883125)
                    ·
                      rfl

theorem cell22_918764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 2, 3].length) (baseStart_918764 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_918764 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_918764 prefixEnd_918764 := by exact prefixLift 918764
  have htrace : WordTrace (prefixWord ++ tailWord_918764) baseStart_918764 baseEnd_918764 := by
    simpa [prefixWord, tailWord_918764, baseEnd_918764] using wordTrace_append hprefix tailTrace_918764
  have hstable : (prefixWord ++ tailWord_918764).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_918764).length < 2 ^ (prefixWord ++ tailWord_918764).sum := by decide
  have hdescent : baseEnd_918764 < baseStart_918764 := by decide
  rcases family_descends (prefixWord ++ tailWord_918764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_918805 : List Nat := [1, 3, 2, 1, 2, 1, 1, 6, 5]
def baseStart_918805 : Nat := 118140960795 + 918805 * 2 ^ 59
def prefixEnd_918805 : Nat := 4983230072969 + 3 ^ 40 * 918805 * 2
def baseEnd_918805 : Nat := 104841909500973978869333

theorem tailTrace_918805 : CollatzResearch.WordTrace tailWord_918805 prefixEnd_918805 104841909500973978869333 := by
  unfold tailWord_918805
  simp only [CollatzResearch.WordTrace]
  refine ⟨33511571436333879246117869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22341047624222586164078579 33511571436333879246117869)
  ·
    refine ⟨12566839288625204717294201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33511571436333879246117869 12566839288625204717294201)
    ·
      refine ⟨9425129466468903537970651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12566839288625204717294201 9425129466468903537970651)
      ·
        refine ⟨14137694199703355306955977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9425129466468903537970651 14137694199703355306955977)
        ·
          refine ⟨10603270649777516480216983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14137694199703355306955977 10603270649777516480216983)
          ·
            refine ⟨15904905974666274720325475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10603270649777516480216983 15904905974666274720325475)
            ·
              refine ⟨23857358961999412080488213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15904905974666274720325475 23857358961999412080488213)
              ·
                refine ⟨1118313701343722441272885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 23857358961999412080488213 1118313701343722441272885)
                ·
                  refine ⟨104841909500973978869333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1118313701343722441272885 104841909500973978869333)
                  ·
                    rfl

theorem cell22_918805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 6, 5].length) (baseStart_918805 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_918805 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_918805 prefixEnd_918805 := by exact prefixLift 918805
  have htrace : WordTrace (prefixWord ++ tailWord_918805) baseStart_918805 baseEnd_918805 := by
    simpa [prefixWord, tailWord_918805, baseEnd_918805] using wordTrace_append hprefix tailTrace_918805
  have hstable : (prefixWord ++ tailWord_918805).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_918805).length < 2 ^ (prefixWord ++ tailWord_918805).sum := by decide
  have hdescent : baseEnd_918805 < baseStart_918805 := by decide
  rcases family_descends (prefixWord ++ tailWord_918805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_918820 : List Nat := [2, 3, 1, 3, 1, 1, 2, 1, 1, 7]
def baseStart_918820 : Nat := 118140960795 + 918820 * 2 ^ 59
def prefixEnd_918820 : Nat := 4983230072969 + 3 ^ 40 * 918820 * 2
def baseEnd_918820 : Nat := 314530863309466897482953

theorem tailTrace_918820 : CollatzResearch.WordTrace tailWord_918820 prefixEnd_918820 314530863309466897482953 := by
  unfold tailWord_918820
  simp only [CollatzResearch.WordTrace]
  refine ⟨16756059265639768403956957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22341412354186357871942609 16756059265639768403956957)
  ·
    refine ⟨6283522224614913151483859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16756059265639768403956957 6283522224614913151483859)
    ·
      refine ⟨9425283336922369727225789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6283522224614913151483859 9425283336922369727225789)
      ·
        refine ⟨3534481251345888647709671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9425283336922369727225789 3534481251345888647709671)
        ·
          refine ⟨5301721877018832971564507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3534481251345888647709671 5301721877018832971564507)
          ·
            refine ⟨7952582815528249457346761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5301721877018832971564507 7952582815528249457346761)
            ·
              refine ⟨5964437111646187093010071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7952582815528249457346761 5964437111646187093010071)
              ·
                refine ⟨8946655667469280639515107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5964437111646187093010071 8946655667469280639515107)
                ·
                  refine ⟨13419983501203920959272661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8946655667469280639515107 13419983501203920959272661)
                  ·
                    refine ⟨314530863309466897482953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 13419983501203920959272661 314530863309466897482953)
                    ·
                      rfl

theorem cell22_918820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 2, 1, 1, 7].length) (baseStart_918820 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_918820 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_918820 prefixEnd_918820 := by exact prefixLift 918820
  have htrace : WordTrace (prefixWord ++ tailWord_918820) baseStart_918820 baseEnd_918820 := by
    simpa [prefixWord, tailWord_918820, baseEnd_918820] using wordTrace_append hprefix tailTrace_918820
  have hstable : (prefixWord ++ tailWord_918820).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_918820).length < 2 ^ (prefixWord ++ tailWord_918820).sum := by decide
  have hdescent : baseEnd_918820 < baseStart_918820 := by decide
  rcases family_descends (prefixWord ++ tailWord_918820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_918865 : List Nat := [1, 2, 2, 1, 4, 1, 1, 2, 3, 5]
def baseStart_918865 : Nat := 118140960795 + 918865 * 2 ^ 59
def prefixEnd_918865 : Nat := 4983230072969 + 3 ^ 40 * 918865 * 2
def baseEnd_918865 : Nat := 314546267729101780107815

theorem tailTrace_918865 : CollatzResearch.WordTrace tailWord_918865 prefixEnd_918865 314546267729101780107815 := by
  unfold tailWord_918865
  simp only [CollatzResearch.WordTrace]
  refine ⟨33513759816116509493302049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22342506544077672995534699 33513759816116509493302049)
  ·
    refine ⟨25135319862087382119976537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33513759816116509493302049 25135319862087382119976537)
    ·
      refine ⟨18851489896565536589982403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25135319862087382119976537 18851489896565536589982403)
      ·
        refine ⟨28277234844848304884973605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18851489896565536589982403 28277234844848304884973605)
        ·
          refine ⟨5301981533409057165932551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28277234844848304884973605 5301981533409057165932551)
          ·
            refine ⟨7952972300113585748898827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5301981533409057165932551 7952972300113585748898827)
            ·
              refine ⟨11929458450170378623348241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7952972300113585748898827 11929458450170378623348241)
              ·
                refine ⟨8947093837627783967511181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11929458450170378623348241 8947093837627783967511181)
                ·
                  refine ⟨3355160189110418987816693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8947093837627783967511181 3355160189110418987816693)
                  ·
                    refine ⟨314546267729101780107815, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3355160189110418987816693 314546267729101780107815)
                    ·
                      rfl

theorem cell22_918865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 1, 2, 3, 5].length) (baseStart_918865 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_918865 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_918865 prefixEnd_918865 := by exact prefixLift 918865
  have htrace : WordTrace (prefixWord ++ tailWord_918865) baseStart_918865 baseEnd_918865 := by
    simpa [prefixWord, tailWord_918865, baseEnd_918865] using wordTrace_append hprefix tailTrace_918865
  have hstable : (prefixWord ++ tailWord_918865).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_918865).length < 2 ^ (prefixWord ++ tailWord_918865).sum := by decide
  have hdescent : baseEnd_918865 < baseStart_918865 := by decide
  rcases family_descends (prefixWord ++ tailWord_918865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_918867 : List Nat := [1, 1, 1, 2, 1, 1, 7, 4, 4]
def baseStart_918867 : Nat := 118140960795 + 918867 * 2 ^ 59
def prefixEnd_918867 : Nat := 4983230072969 + 3 ^ 40 * 918867 * 2
def baseEnd_918867 : Nat := 104848984123324813852603

theorem tailTrace_918867 : CollatzResearch.WordTrace tailWord_918867 prefixEnd_918867 104848984123324813852603 := by
  unfold tailWord_918867
  simp only [CollatzResearch.WordTrace]
  refine ⟨33513832762109263834874855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22342555174739509223249903 33513832762109263834874855)
  ·
    refine ⟨50270749143163895752312283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33513832762109263834874855 50270749143163895752312283)
    ·
      refine ⟨75406123714745843628468425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50270749143163895752312283 75406123714745843628468425)
      ·
        refine ⟨56554592786059382721351319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75406123714745843628468425 56554592786059382721351319)
        ·
          refine ⟨84831889179089074082026979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56554592786059382721351319 84831889179089074082026979)
          ·
            refine ⟨127247833768633611123040469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84831889179089074082026979 127247833768633611123040469)
            ·
              refine ⟨2982371103952350260696261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 127247833768633611123040469 2982371103952350260696261)
              ·
                refine ⟨559194581991065673880549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2982371103952350260696261 559194581991065673880549)
                ·
                  refine ⟨104848984123324813852603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 559194581991065673880549 104848984123324813852603)
                  ·
                    rfl

theorem cell22_918867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 7, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 7, 4, 4].length) (baseStart_918867 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_918867 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_918867 prefixEnd_918867 := by exact prefixLift 918867
  have htrace : WordTrace (prefixWord ++ tailWord_918867) baseStart_918867 baseEnd_918867 := by
    simpa [prefixWord, tailWord_918867, baseEnd_918867] using wordTrace_append hprefix tailTrace_918867
  have hstable : (prefixWord ++ tailWord_918867).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_918867).length < 2 ^ (prefixWord ++ tailWord_918867).sum := by decide
  have hdescent : baseEnd_918867 < baseStart_918867 := by decide
  rcases family_descends (prefixWord ++ tailWord_918867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_918897 : List Nat := [1, 2, 2, 2, 1, 2, 5, 1, 2, 4]
def baseStart_918897 : Nat := 118140960795 + 918897 * 2 ^ 59
def prefixEnd_918897 : Nat := 4983230072969 + 3 ^ 40 * 918897 * 2
def baseEnd_918897 : Nat := 314557221983064363307717

theorem tailTrace_918897 : CollatzResearch.WordTrace tailWord_918897 prefixEnd_918897 314557221983064363307717 := by
  unfold tailWord_918897
  simp only [CollatzResearch.WordTrace]
  refine ⟨33514926952000578958466945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22343284634667052638977963 33514926952000578958466945)
  ·
    refine ⟨25136195214000434218850209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33514926952000578958466945 25136195214000434218850209)
    ·
      refine ⟨18852146410500325664137657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25136195214000434218850209 18852146410500325664137657)
      ·
        refine ⟨14139109807875244248103243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18852146410500325664137657 14139109807875244248103243)
        ·
          refine ⟨21208664711812866372154865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14139109807875244248103243 21208664711812866372154865)
          ·
            refine ⟨15906498533859649779116149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21208664711812866372154865 15906498533859649779116149)
            ·
              refine ⟨1491234237549342166792139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 15906498533859649779116149 1491234237549342166792139)
              ·
                refine ⟨2236851356324013250188209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1491234237549342166792139 2236851356324013250188209)
                ·
                  refine ⟨1677638517243009937641157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2236851356324013250188209 1677638517243009937641157)
                  ·
                    refine ⟨314557221983064363307717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1677638517243009937641157 314557221983064363307717)
                    ·
                      rfl

theorem cell22_918897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 5, 1, 2, 4].length) (baseStart_918897 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_918897 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_918897 prefixEnd_918897 := by exact prefixLift 918897
  have htrace : WordTrace (prefixWord ++ tailWord_918897) baseStart_918897 baseEnd_918897 := by
    simpa [prefixWord, tailWord_918897, baseEnd_918897] using wordTrace_append hprefix tailTrace_918897
  have hstable : (prefixWord ++ tailWord_918897).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_918897).length < 2 ^ (prefixWord ++ tailWord_918897).sum := by decide
  have hdescent : baseEnd_918897 < baseStart_918897 := by decide
  rcases family_descends (prefixWord ++ tailWord_918897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_918901 : List Nat := [1, 3, 4, 1, 3, 1, 2, 3, 4]
def baseStart_918901 : Nat := 118140960795 + 918901 * 2 ^ 59
def prefixEnd_918901 : Nat := 4983230072969 + 3 ^ 40 * 918901 * 2
def baseEnd_918901 : Nat := 104852863754936562069235

theorem tailTrace_918901 : CollatzResearch.WordTrace tailWord_918901 prefixEnd_918901 104852863754936562069235 := by
  unfold tailWord_918901
  simp only [CollatzResearch.WordTrace]
  refine ⟨33515072843986087641612557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22343381895990725094408371 33515072843986087641612557)
  ·
    refine ⟨12568152316494782865604709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33515072843986087641612557 12568152316494782865604709)
    ·
      refine ⟨2356528559342771787300883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12568152316494782865604709 2356528559342771787300883)
      ·
        refine ⟨3534792839014157680951325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2356528559342771787300883 3534792839014157680951325)
        ·
          refine ⟨1325547314630309130356747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3534792839014157680951325 1325547314630309130356747)
          ·
            refine ⟨1988320971945463695535121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1325547314630309130356747 1988320971945463695535121)
            ·
              refine ⟨1491240728959097771651341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1988320971945463695535121 1491240728959097771651341)
              ·
                refine ⟨559215273359661664369253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1491240728959097771651341 559215273359661664369253)
                ·
                  refine ⟨104852863754936562069235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 559215273359661664369253 104852863754936562069235)
                  ·
                    rfl

theorem cell22_918901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 1, 2, 3, 4].length) (baseStart_918901 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_918901 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_918901 prefixEnd_918901 := by exact prefixLift 918901
  have htrace : WordTrace (prefixWord ++ tailWord_918901) baseStart_918901 baseEnd_918901 := by
    simpa [prefixWord, tailWord_918901, baseEnd_918901] using wordTrace_append hprefix tailTrace_918901
  have hstable : (prefixWord ++ tailWord_918901).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_918901).length < 2 ^ (prefixWord ++ tailWord_918901).sum := by decide
  have hdescent : baseEnd_918901 < baseStart_918901 := by decide
  rcases family_descends (prefixWord ++ tailWord_918901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_918916 : List Nat := [2, 3, 2, 1, 1, 5, 1, 2, 2, 3]
def baseStart_918916 : Nat := 118140960795 + 918916 * 2 ^ 59
def prefixEnd_918916 : Nat := 4983230072969 + 3 ^ 40 * 918916 * 2
def baseEnd_918916 : Nat := 314563726071354647082659

theorem tailTrace_918916 : CollatzResearch.WordTrace tailWord_918916 prefixEnd_918916 314563726071354647082659 := by
  unfold tailWord_918916
  simp only [CollatzResearch.WordTrace]
  refine ⟨16757809969465872601704301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22343746625954496802272401 16757809969465872601704301)
  ·
    refine ⟨6284178738549702225639113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16757809969465872601704301 6284178738549702225639113)
    ·
      refine ⟨4713134053912276669229335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6284178738549702225639113 4713134053912276669229335)
      ·
        refine ⟨7069701080868415003844003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4713134053912276669229335 7069701080868415003844003)
        ·
          refine ⟨10604551621302622505766005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7069701080868415003844003 10604551621302622505766005)
          ·
            refine ⟨994176714497120859915563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 10604551621302622505766005 994176714497120859915563)
            ·
              refine ⟨1491265071745681289873345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 994176714497120859915563 1491265071745681289873345)
              ·
                refine ⟨1118448803809260967405009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1491265071745681289873345 1118448803809260967405009)
                ·
                  refine ⟨838836602856945725553757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1118448803809260967405009 838836602856945725553757)
                  ·
                    refine ⟨314563726071354647082659, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 838836602856945725553757 314563726071354647082659)
                    ·
                      rfl

theorem cell22_918916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 5, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 5, 1, 2, 2, 3].length) (baseStart_918916 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_918916 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_918916 prefixEnd_918916 := by exact prefixLift 918916
  have htrace : WordTrace (prefixWord ++ tailWord_918916) baseStart_918916 baseEnd_918916 := by
    simpa [prefixWord, tailWord_918916, baseEnd_918916] using wordTrace_append hprefix tailTrace_918916
  have hstable : (prefixWord ++ tailWord_918916).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_918916).length < 2 ^ (prefixWord ++ tailWord_918916).sum := by decide
  have hdescent : baseEnd_918916 < baseStart_918916 := by decide
  rcases family_descends (prefixWord ++ tailWord_918916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_919036 : List Nat := [2, 2, 2, 1, 2, 1, 6, 2, 4]
def baseStart_919036 : Nat := 118140960795 + 919036 * 2 ^ 59
def prefixEnd_919036 : Nat := 4983230072969 + 3 ^ 40 * 919036 * 2
def baseEnd_919036 : Nat := 104868268174571444694097

theorem tailTrace_919036 : CollatzResearch.WordTrace tailWord_919036 prefixEnd_919036 104868268174571444694097 := by
  unfold tailWord_919036
  simp only [CollatzResearch.WordTrace]
  refine ⟨16759998349248502848888481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22346664465664670465184641 16759998349248502848888481)
  ·
    refine ⟨12569998761936377136666361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16759998349248502848888481 12569998761936377136666361)
    ·
      refine ⟨9427499071452282852499771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12569998761936377136666361 9427499071452282852499771)
      ·
        refine ⟨14141248607178424278749657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9427499071452282852499771 14141248607178424278749657)
        ·
          refine ⟨10605936455383818209062243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14141248607178424278749657 10605936455383818209062243)
          ·
            refine ⟨15908904683075727313593365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10605936455383818209062243 15908904683075727313593365)
            ·
              refine ⟨745729907019174717824689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 15908904683075727313593365 745729907019174717824689)
              ·
                refine ⟨559297430264381038368517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 745729907019174717824689 559297430264381038368517)
                ·
                  refine ⟨104868268174571444694097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 559297430264381038368517 104868268174571444694097)
                  ·
                    rfl

theorem cell22_919036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 6, 2, 4].length) (baseStart_919036 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_919036 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_919036 prefixEnd_919036 := by exact prefixLift 919036
  have htrace : WordTrace (prefixWord ++ tailWord_919036) baseStart_919036 baseEnd_919036 := by
    simpa [prefixWord, tailWord_919036, baseEnd_919036] using wordTrace_append hprefix tailTrace_919036
  have hstable : (prefixWord ++ tailWord_919036).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_919036).length < 2 ^ (prefixWord ++ tailWord_919036).sum := by decide
  have hdescent : baseEnd_919036 < baseStart_919036 := by decide
  rcases family_descends (prefixWord ++ tailWord_919036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_919053 : List Nat := [1, 7, 1, 1, 2, 1, 1, 2, 6]
def baseStart_919053 : Nat := 118140960795 + 919053 * 2 ^ 59
def prefixEnd_919053 : Nat := 4983230072969 + 3 ^ 40 * 919053 * 2
def baseEnd_919053 : Nat := 104870207990377318802413

theorem tailTrace_919053 : CollatzResearch.WordTrace tailWord_919053 prefixEnd_919053 104870207990377318802413 := by
  unfold tailWord_919053
  simp only [CollatzResearch.WordTrace]
  refine ⟨33520616739435417601145813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22347077826290278400763875 33520616739435417601145813)
  ·
    refine ⟨785639454830517600026855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 33520616739435417601145813 785639454830517600026855)
    ·
      refine ⟨1178459182245776400040283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 785639454830517600026855 1178459182245776400040283)
      ·
        refine ⟨1767688773368664600060425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1178459182245776400040283 1767688773368664600060425)
        ·
          refine ⟨1325766580026498450045319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1767688773368664600060425 1325766580026498450045319)
          ·
            refine ⟨1988649870039747675067979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1325766580026498450045319 1988649870039747675067979)
            ·
              refine ⟨2982974805059621512601969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1988649870039747675067979 2982974805059621512601969)
              ·
                refine ⟨2237231103794716134451477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2982974805059621512601969 2237231103794716134451477)
                ·
                  refine ⟨104870207990377318802413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2237231103794716134451477 104870207990377318802413)
                  ·
                    rfl

theorem cell22_919053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 1, 1, 2, 6].length) (baseStart_919053 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_919053 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_919053 prefixEnd_919053 := by exact prefixLift 919053
  have htrace : WordTrace (prefixWord ++ tailWord_919053) baseStart_919053 baseEnd_919053 := by
    simpa [prefixWord, tailWord_919053, baseEnd_919053] using wordTrace_append hprefix tailTrace_919053
  have hstable : (prefixWord ++ tailWord_919053).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_919053).length < 2 ^ (prefixWord ++ tailWord_919053).sum := by decide
  have hdescent : baseEnd_919053 < baseStart_919053 := by decide
  rcases family_descends (prefixWord ++ tailWord_919053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_919096 : List Nat := [2, 1, 2, 1, 4, 3, 2, 1, 3, 3]
def baseStart_919096 : Nat := 118140960795 + 919096 * 2 ^ 59
def prefixEnd_919096 : Nat := 4983230072969 + 3 ^ 40 * 919096 * 2
def baseEnd_919096 : Nat := 314625343749894177582107

theorem tailTrace_919096 : CollatzResearch.WordTrace tailWord_919096 prefixEnd_919096 314625343749894177582107 := by
  unfold tailWord_919096
  simp only [CollatzResearch.WordTrace]
  refine ⟨16761092539139817972480571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22348123385519757296640761 16761092539139817972480571)
  ·
    refine ⟨25141638808709726958720857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16761092539139817972480571 25141638808709726958720857)
    ·
      refine ⟨18856229106532295219040643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25141638808709726958720857 18856229106532295219040643)
      ·
        refine ⟨28284343659798442828560965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18856229106532295219040643 28284343659798442828560965)
        ·
          refine ⟨5303314436212208030355181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28284343659798442828560965 5303314436212208030355181)
          ·
            refine ⟨1988742913579578011383193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5303314436212208030355181 1988742913579578011383193)
            ·
              refine ⟨1491557185184683508537395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1988742913579578011383193 1491557185184683508537395)
              ·
                refine ⟨2237335777777025262806093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1491557185184683508537395 2237335777777025262806093)
                ·
                  refine ⟨839000916666384473552285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2237335777777025262806093 839000916666384473552285)
                  ·
                    refine ⟨314625343749894177582107, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 839000916666384473552285 314625343749894177582107)
                    ·
                      rfl

theorem cell22_919096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 3, 2, 1, 3, 3].length) (baseStart_919096 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_919096 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_919096 prefixEnd_919096 := by exact prefixLift 919096
  have htrace : WordTrace (prefixWord ++ tailWord_919096) baseStart_919096 baseEnd_919096 := by
    simpa [prefixWord, tailWord_919096, baseEnd_919096] using wordTrace_append hprefix tailTrace_919096
  have hstable : (prefixWord ++ tailWord_919096).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_919096).length < 2 ^ (prefixWord ++ tailWord_919096).sum := by decide
  have hdescent : baseEnd_919096 < baseStart_919096 := by decide
  rcases family_descends (prefixWord ++ tailWord_919096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_919199 : List Nat := [1, 1, 2, 7, 11]
def baseStart_919199 : Nat := 118140960795 + 919199 * 2 ^ 59
def prefixEnd_919199 : Nat := 4983230072969 + 3 ^ 40 * 919199 * 2
def baseEnd_919199 : Nat := 1294899599814140914637

theorem tailTrace_919199 : CollatzResearch.WordTrace tailWord_919199 prefixEnd_919199 1294899599814140914637 := by
  unfold tailWord_919199
  simp only [CollatzResearch.WordTrace]
  refine ⟨33525941796906484535960651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22350627864604323023973767 33525941796906484535960651)
  ·
    refine ⟨50288912695359726803940977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33525941796906484535960651 50288912695359726803940977)
    ·
      refine ⟨37716684521519795102955733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50288912695359726803940977 37716684521519795102955733)
      ·
        refine ⟨883984793473120197725525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 37716684521519795102955733 883984793473120197725525)
        ·
          refine ⟨1294899599814140914637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 11 883984793473120197725525 1294899599814140914637)
          ·
            rfl

theorem cell22_919199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 11].length) (baseStart_919199 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_919199 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_919199 prefixEnd_919199 := by exact prefixLift 919199
  have htrace : WordTrace (prefixWord ++ tailWord_919199) baseStart_919199 baseEnd_919199 := by
    simpa [prefixWord, tailWord_919199, baseEnd_919199] using wordTrace_append hprefix tailTrace_919199
  have hstable : (prefixWord ++ tailWord_919199).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_919199).length < 2 ^ (prefixWord ++ tailWord_919199).sum := by decide
  have hdescent : baseEnd_919199 < baseStart_919199 := by decide
  rcases family_descends (prefixWord ++ tailWord_919199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_919201 : List Nat := [1, 2, 3, 3, 2, 1, 2, 2, 2, 4]
def baseStart_919201 : Nat := 118140960795 + 919201 * 2 ^ 59
def prefixEnd_919201 : Nat := 4983230072969 + 3 ^ 40 * 919201 * 2
def baseEnd_919201 : Nat := 314661287395708903706785

theorem tailTrace_919201 : CollatzResearch.WordTrace tailWord_919201 prefixEnd_919201 314661287395708903706785 := by
  unfold tailWord_919201
  simp only [CollatzResearch.WordTrace]
  refine ⟨33526014742899238877533457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22350676495266159251688971 33526014742899238877533457)
  ·
    refine ⟨25144511057174429158150093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33526014742899238877533457 25144511057174429158150093)
    ·
      refine ⟨9429191646440410934306285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25144511057174429158150093 9429191646440410934306285)
      ·
        refine ⟨3535946867415154100364857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9429191646440410934306285 3535946867415154100364857)
        ·
          refine ⟨2651960150561365575273643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3535946867415154100364857 2651960150561365575273643)
          ·
            refine ⟨3977940225842048362910465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2651960150561365575273643 3977940225842048362910465)
            ·
              refine ⟨2983455169381536272182849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3977940225842048362910465 2983455169381536272182849)
              ·
                refine ⟨2237591377036152204137137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2983455169381536272182849 2237591377036152204137137)
                ·
                  refine ⟨1678193532777114153102853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2237591377036152204137137 1678193532777114153102853)
                  ·
                    refine ⟨314661287395708903706785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1678193532777114153102853 314661287395708903706785)
                    ·
                      rfl

theorem cell22_919201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 2, 2, 2, 4].length) (baseStart_919201 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_919201 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_919201 prefixEnd_919201 := by exact prefixLift 919201
  have htrace : WordTrace (prefixWord ++ tailWord_919201) baseStart_919201 baseEnd_919201 := by
    simpa [prefixWord, tailWord_919201, baseEnd_919201] using wordTrace_append hprefix tailTrace_919201
  have hstable : (prefixWord ++ tailWord_919201).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_919201).length < 2 ^ (prefixWord ++ tailWord_919201).sum := by decide
  have hdescent : baseEnd_919201 < baseStart_919201 := by decide
  rcases family_descends (prefixWord ++ tailWord_919201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_919229 : List Nat := [1, 4, 1, 2, 1, 2, 1, 2, 2, 6]
def baseStart_919229 : Nat := 118140960795 + 919229 * 2 ^ 59
def prefixEnd_919229 : Nat := 4983230072969 + 3 ^ 40 * 919229 * 2
def baseEnd_919229 : Nat := 314670872367926164006699

theorem tailTrace_919229 : CollatzResearch.WordTrace tailWord_919229 prefixEnd_919229 314670872367926164006699 := by
  unfold tailWord_919229
  simp only [CollatzResearch.WordTrace]
  refine ⟨33527035986797799659552741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22351357324531866439701827 33527035986797799659552741)
  ·
    refine ⟨6286319247524587436166139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 33527035986797799659552741 6286319247524587436166139)
    ·
      refine ⟨9429478871286881154249209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6286319247524587436166139 9429478871286881154249209)
      ·
        refine ⟨7072109153465160865686907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9429478871286881154249209 7072109153465160865686907)
        ·
          refine ⟨10608163730197741298530361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7072109153465160865686907 10608163730197741298530361)
          ·
            refine ⟨7956122797648305973897771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10608163730197741298530361 7956122797648305973897771)
            ·
              refine ⟨11934184196472458960846657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7956122797648305973897771 11934184196472458960846657)
              ·
                refine ⟨8950638147354344220634993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11934184196472458960846657 8950638147354344220634993)
                ·
                  refine ⟨6712978610515758165476245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8950638147354344220634993 6712978610515758165476245)
                  ·
                    refine ⟨314670872367926164006699, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6712978610515758165476245 314670872367926164006699)
                    ·
                      rfl

theorem cell22_919229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 1, 2, 2, 6].length) (baseStart_919229 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_919229 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_919229 prefixEnd_919229 := by exact prefixLift 919229
  have htrace : WordTrace (prefixWord ++ tailWord_919229) baseStart_919229 baseEnd_919229 := by
    simpa [prefixWord, tailWord_919229, baseEnd_919229] using wordTrace_append hprefix tailTrace_919229
  have hstable : (prefixWord ++ tailWord_919229).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_919229).length < 2 ^ (prefixWord ++ tailWord_919229).sum := by decide
  have hdescent : baseEnd_919229 < baseStart_919229 := by decide
  rcases family_descends (prefixWord ++ tailWord_919229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_919231 : List Nat := [1, 1, 2, 2, 2, 3, 3, 2, 3, 3]
def baseStart_919231 : Nat := 118140960795 + 919231 * 2 ^ 59
def prefixEnd_919231 : Nat := 4983230072969 + 3 ^ 40 * 919231 * 2
def baseEnd_919231 : Nat := 314671557008798825456693

theorem tailTrace_919231 : CollatzResearch.WordTrace tailWord_919231 prefixEnd_919231 314671557008798825456693 := by
  unfold tailWord_919231
  simp only [CollatzResearch.WordTrace]
  refine ⟨33527108932790554001125547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22351405955193702667417031 33527108932790554001125547)
  ·
    refine ⟨50290663399185831001688321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33527108932790554001125547 50290663399185831001688321)
    ·
      refine ⟨37717997549389373251266241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50290663399185831001688321 37717997549389373251266241)
      ·
        refine ⟨28288498162042029938449681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37717997549389373251266241 28288498162042029938449681)
        ·
          refine ⟨21216373621531522453837261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28288498162042029938449681 21216373621531522453837261)
          ·
            refine ⟨7956140108074320920188973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21216373621531522453837261 7956140108074320920188973)
            ·
              refine ⟨2983552540527870345070865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7956140108074320920188973 2983552540527870345070865)
              ·
                refine ⟨2237664405395902758803149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2983552540527870345070865 2237664405395902758803149)
                ·
                  refine ⟨839124152023463534551181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2237664405395902758803149 839124152023463534551181)
                  ·
                    refine ⟨314671557008798825456693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 839124152023463534551181 314671557008798825456693)
                    ·
                      rfl

theorem cell22_919231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 3, 2, 3, 3].length) (baseStart_919231 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_919231 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_919231 prefixEnd_919231 := by exact prefixLift 919231
  have htrace : WordTrace (prefixWord ++ tailWord_919231) baseStart_919231 baseEnd_919231 := by
    simpa [prefixWord, tailWord_919231, baseEnd_919231] using wordTrace_append hprefix tailTrace_919231
  have hstable : (prefixWord ++ tailWord_919231).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_919231).length < 2 ^ (prefixWord ++ tailWord_919231).sum := by decide
  have hdescent : baseEnd_919231 < baseStart_919231 := by decide
  rcases family_descends (prefixWord ++ tailWord_919231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_919254 : List Nat := [5, 2, 1, 3, 1, 2, 1, 2, 2, 3]
def baseStart_919254 : Nat := 118140960795 + 919254 * 2 ^ 59
def prefixEnd_919254 : Nat := 4983230072969 + 3 ^ 40 * 919254 * 2
def baseEnd_919254 : Nat := 314679430378834432131623

theorem tailTrace_919254 : CollatzResearch.WordTrace tailWord_919254 prefixEnd_919254 314679430378834432131623 := by
  unfold tailWord_919254
  simp only [CollatzResearch.WordTrace]
  refine ⟨2095496738231701808075801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 22351965207804819286141877 2095496738231701808075801)
  ·
    refine ⟨1571622553673776356056851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2095496738231701808075801 1571622553673776356056851)
    ·
      refine ⟨2357433830510664534085277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1571622553673776356056851 2357433830510664534085277)
      ·
        refine ⟨884037686441499200281979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2357433830510664534085277 884037686441499200281979)
        ·
          refine ⟨1326056529662248800422969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 884037686441499200281979 1326056529662248800422969)
          ·
            refine ⟨994542397246686600317227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1326056529662248800422969 994542397246686600317227)
            ·
              refine ⟨1491813595870029900475841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 994542397246686600317227 1491813595870029900475841)
              ·
                refine ⟨1118860196902522425356881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1491813595870029900475841 1118860196902522425356881)
                ·
                  refine ⟨839145147676891819017661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1118860196902522425356881 839145147676891819017661)
                  ·
                    refine ⟨314679430378834432131623, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 839145147676891819017661 314679430378834432131623)
                    ·
                      rfl

theorem cell22_919254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 2, 1, 2, 2, 3].length) (baseStart_919254 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_919254 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_919254 prefixEnd_919254 := by exact prefixLift 919254
  have htrace : WordTrace (prefixWord ++ tailWord_919254) baseStart_919254 baseEnd_919254 := by
    simpa [prefixWord, tailWord_919254, baseEnd_919254] using wordTrace_append hprefix tailTrace_919254
  have hstable : (prefixWord ++ tailWord_919254).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_919254).length < 2 ^ (prefixWord ++ tailWord_919254).sum := by decide
  have hdescent : baseEnd_919254 < baseStart_919254 := by decide
  rcases family_descends (prefixWord ++ tailWord_919254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_919278 : List Nat := [4, 1, 2, 1, 1, 2, 5, 1, 5]
def baseStart_919278 : Nat := 118140960795 + 919278 * 2 ^ 59
def prefixEnd_919278 : Nat := 4983230072969 + 3 ^ 40 * 919278 * 2
def baseEnd_919278 : Nat := 104895882023102123177183

theorem tailTrace_919278 : CollatzResearch.WordTrace tailWord_919278 prefixEnd_919278 104895882023102123177183 := by
  unfold tailWord_919278
  simp only [CollatzResearch.WordTrace]
  refine ⟨4191102895452535128510811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22352548775746854018724325 4191102895452535128510811)
  ·
    refine ⟨6286654343178802692766217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4191102895452535128510811 6286654343178802692766217)
    ·
      refine ⟨4714990757384102019574663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6286654343178802692766217 4714990757384102019574663)
      ·
        refine ⟨7072486136076153029361995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4714990757384102019574663 7072486136076153029361995)
        ·
          refine ⟨10608729204114229544042993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7072486136076153029361995 10608729204114229544042993)
          ·
            refine ⟨7956546903085672158032245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10608729204114229544042993 7956546903085672158032245)
            ·
              refine ⟨745926272164281764815523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 7956546903085672158032245 745926272164281764815523)
              ·
                refine ⟨1118889408246422647223285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 745926272164281764815523 1118889408246422647223285)
                ·
                  refine ⟨104895882023102123177183, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1118889408246422647223285 104895882023102123177183)
                  ·
                    rfl

theorem cell22_919278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 5, 1, 5].length) (baseStart_919278 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_919278 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_919278 prefixEnd_919278 := by exact prefixLift 919278
  have htrace : WordTrace (prefixWord ++ tailWord_919278) baseStart_919278 baseEnd_919278 := by
    simpa [prefixWord, tailWord_919278, baseEnd_919278] using wordTrace_append hprefix tailTrace_919278
  have hstable : (prefixWord ++ tailWord_919278).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_919278).length < 2 ^ (prefixWord ++ tailWord_919278).sum := by decide
  have hdescent : baseEnd_919278 < baseStart_919278 := by decide
  rcases family_descends (prefixWord ++ tailWord_919278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_919316 : List Nat := [2, 4, 4, 1, 2, 1, 1, 1, 3, 3]
def baseStart_919316 : Nat := 118140960795 + 919316 * 2 ^ 59
def prefixEnd_919316 : Nat := 4983230072969 + 3 ^ 40 * 919316 * 2
def baseEnd_919316 : Nat := 314700654245886937081433

theorem tailTrace_919316 : CollatzResearch.WordTrace tailWord_919316 prefixEnd_919316 314700654245886937081433 := by
  unfold tailWord_919316
  simp only [CollatzResearch.WordTrace]
  refine ⟨16765104568741306758984901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22353472758321742345313201 16765104568741306758984901)
  ·
    refine ⟨3143457106638995017309669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16765104568741306758984901 3143457106638995017309669)
    ·
      refine ⟨589398207494811565745563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3143457106638995017309669 589398207494811565745563)
      ·
        refine ⟨884097311242217348618345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 589398207494811565745563 884097311242217348618345)
        ·
          refine ⟨663072983431663011463759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 884097311242217348618345 663072983431663011463759)
          ·
            refine ⟨994609475147494517195639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 663072983431663011463759 994609475147494517195639)
            ·
              refine ⟨1491914212721241775793459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 994609475147494517195639 1491914212721241775793459)
              ·
                refine ⟨2237871319081862663690189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1491914212721241775793459 2237871319081862663690189)
                ·
                  refine ⟨839201744655698498883821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2237871319081862663690189 839201744655698498883821)
                  ·
                    refine ⟨314700654245886937081433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 839201744655698498883821 314700654245886937081433)
                    ·
                      rfl

theorem cell22_919316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 2, 1, 1, 1, 3, 3].length) (baseStart_919316 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_919316 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_919316 prefixEnd_919316 := by exact prefixLift 919316
  have htrace : WordTrace (prefixWord ++ tailWord_919316) baseStart_919316 baseEnd_919316 := by
    simpa [prefixWord, tailWord_919316, baseEnd_919316] using wordTrace_append hprefix tailTrace_919316
  have hstable : (prefixWord ++ tailWord_919316).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_919316).length < 2 ^ (prefixWord ++ tailWord_919316).sum := by decide
  have hdescent : baseEnd_919316 < baseStart_919316 := by decide
  rcases family_descends (prefixWord ++ tailWord_919316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_919342 : List Nat := [4, 1, 3, 2, 2, 2, 1, 2, 1, 4]
def baseStart_919342 : Nat := 118140960795 + 919342 * 2 ^ 59
def prefixEnd_919342 : Nat := 4983230072969 + 3 ^ 40 * 919342 * 2
def baseEnd_919342 : Nat := 314709554577231535931353

theorem tailTrace_919342 : CollatzResearch.WordTrace tailWord_919342 prefixEnd_919342 314709554577231535931353 := by
  unfold tailWord_919342
  simp only [CollatzResearch.WordTrace]
  refine ⟨4191394679423552494802035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22354104956925613305610853 4191394679423552494802035)
  ·
    refine ⟨6287092019135328742203053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4191394679423552494802035 6287092019135328742203053)
    ·
      refine ⟨2357659507175748278326145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6287092019135328742203053 2357659507175748278326145)
      ·
        refine ⟨1768244630381811208744609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2357659507175748278326145 1768244630381811208744609)
        ·
          refine ⟨1326183472786358406558457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1768244630381811208744609 1326183472786358406558457)
          ·
            refine ⟨994637604589768804918843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1326183472786358406558457 994637604589768804918843)
            ·
              refine ⟨1491956406884653207378265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 994637604589768804918843 1491956406884653207378265)
              ·
                refine ⟨1118967305163489905533699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1491956406884653207378265 1118967305163489905533699)
                ·
                  refine ⟨1678450957745234858300549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1118967305163489905533699 1678450957745234858300549)
                  ·
                    refine ⟨314709554577231535931353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1678450957745234858300549 314709554577231535931353)
                    ·
                      rfl

theorem cell22_919342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 2, 1, 2, 1, 4].length) (baseStart_919342 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_919342 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_919342 prefixEnd_919342 := by exact prefixLift 919342
  have htrace : WordTrace (prefixWord ++ tailWord_919342) baseStart_919342 baseEnd_919342 := by
    simpa [prefixWord, tailWord_919342, baseEnd_919342] using wordTrace_append hprefix tailTrace_919342
  have hstable : (prefixWord ++ tailWord_919342).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_919342).length < 2 ^ (prefixWord ++ tailWord_919342).sum := by decide
  have hdescent : baseEnd_919342 < baseStart_919342 := by decide
  rcases family_descends (prefixWord ++ tailWord_919342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_919381 : List Nat := [1, 3, 2, 2, 2, 2, 1, 1, 2, 6]
def baseStart_919381 : Nat := 118140960795 + 919381 * 2 ^ 59
def prefixEnd_919381 : Nat := 4983230072969 + 3 ^ 40 * 919381 * 2
def baseEnd_919381 : Nat := 314722905074248434206233

theorem tailTrace_919381 : CollatzResearch.WordTrace tailWord_919381 prefixEnd_919381 314722905074248434206233 := by
  unfold tailWord_919381
  simp only [CollatzResearch.WordTrace]
  refine ⟨33532579882247129619085997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22355053254831419746057331 33532579882247129619085997)
  ·
    refine ⟨12574717455842673607157249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33532579882247129619085997 12574717455842673607157249)
    ·
      refine ⟨9431038091882005205367937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12574717455842673607157249 9431038091882005205367937)
      ·
        refine ⟨7073278568911503904025953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9431038091882005205367937 7073278568911503904025953)
        ·
          refine ⟨5304958926683627928019465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7073278568911503904025953 5304958926683627928019465)
          ·
            refine ⟨3978719195012720946014599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5304958926683627928019465 3978719195012720946014599)
            ·
              refine ⟨5968078792519081419021899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3978719195012720946014599 5968078792519081419021899)
              ·
                refine ⟨8952118188778622128532849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5968078792519081419021899 8952118188778622128532849)
                ·
                  refine ⟨6714088641583966596399637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8952118188778622128532849 6714088641583966596399637)
                  ·
                    refine ⟨314722905074248434206233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6714088641583966596399637 314722905074248434206233)
                    ·
                      rfl

theorem cell22_919381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 1, 1, 2, 6].length) (baseStart_919381 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_919381 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_919381 prefixEnd_919381 := by exact prefixLift 919381
  have htrace : WordTrace (prefixWord ++ tailWord_919381) baseStart_919381 baseEnd_919381 := by
    simpa [prefixWord, tailWord_919381, baseEnd_919381] using wordTrace_append hprefix tailTrace_919381
  have hstable : (prefixWord ++ tailWord_919381).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_919381).length < 2 ^ (prefixWord ++ tailWord_919381).sum := by decide
  have hdescent : baseEnd_919381 < baseStart_919381 := by decide
  rcases family_descends (prefixWord ++ tailWord_919381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_919441 : List Nat := [1, 2, 2, 1, 1, 1, 5, 3, 6]
def baseStart_919441 : Nat := 118140960795 + 919441 * 2 ^ 59
def prefixEnd_919441 : Nat := 4983230072969 + 3 ^ 40 * 919441 * 2
def baseEnd_919441 : Nat := 104914481433476092568683

theorem tailTrace_919441 : CollatzResearch.WordTrace tailWord_919441 prefixEnd_919441 104914481433476092568683 := by
  unfold tailWord_919441
  simp only [CollatzResearch.WordTrace]
  refine ⟨33534768262029759866270177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22356512174686506577513451 33534768262029759866270177)
  ·
    refine ⟨25151076196522319899702633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33534768262029759866270177 25151076196522319899702633)
    ·
      refine ⟨18863307147391739924776975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25151076196522319899702633 18863307147391739924776975)
      ·
        refine ⟨28294960721087609887165463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18863307147391739924776975 28294960721087609887165463)
        ·
          refine ⟨42442441081631414830748195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28294960721087609887165463 42442441081631414830748195)
          ·
            refine ⟨63663661622447122246122293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42442441081631414830748195 63663661622447122246122293)
            ·
              refine ⟨5968468277104417710573965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 63663661622447122246122293 5968468277104417710573965)
              ·
                refine ⟨2238175603914156641465237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5968468277104417710573965 2238175603914156641465237)
                ·
                  refine ⟨104914481433476092568683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2238175603914156641465237 104914481433476092568683)
                  ·
                    rfl

theorem cell22_919441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 5, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 5, 3, 6].length) (baseStart_919441 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_919441 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_919441 prefixEnd_919441 := by exact prefixLift 919441
  have htrace : WordTrace (prefixWord ++ tailWord_919441) baseStart_919441 baseEnd_919441 := by
    simpa [prefixWord, tailWord_919441, baseEnd_919441] using wordTrace_append hprefix tailTrace_919441
  have hstable : (prefixWord ++ tailWord_919441).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_919441).length < 2 ^ (prefixWord ++ tailWord_919441).sum := by decide
  have hdescent : baseEnd_919441 < baseStart_919441 := by decide
  rcases family_descends (prefixWord ++ tailWord_919441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_919460 : List Nat := [2, 3, 1, 2, 1, 4, 2, 2, 1, 4]
def baseStart_919460 : Nat := 118140960795 + 919460 * 2 ^ 59
def prefixEnd_919460 : Nat := 4983230072969 + 3 ^ 40 * 919460 * 2
def baseEnd_919460 : Nat := 314749948388718561480991

theorem tailTrace_919460 : CollatzResearch.WordTrace tailWord_919460 prefixEnd_919460 314749948388718561480991 := by
  unfold tailWord_919460
  simp only [CollatzResearch.WordTrace]
  refine ⟨16767730624480463055605917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22356974165973950740807889 16767730624480463055605917)
  ·
    refine ⟨6287898984180173645852219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16767730624480463055605917 6287898984180173645852219)
    ·
      refine ⟨9431848476270260468778329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6287898984180173645852219 9431848476270260468778329)
      ·
        refine ⟨7073886357202695351583747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9431848476270260468778329 7073886357202695351583747)
        ·
          refine ⟨10610829535804043027375621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7073886357202695351583747 10610829535804043027375621)
          ·
            refine ⟨1989530537963258067632929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10610829535804043027375621 1989530537963258067632929)
            ·
              refine ⟨1492147903472443550724697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1989530537963258067632929 1492147903472443550724697)
              ·
                refine ⟨1119110927604332663043523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1492147903472443550724697 1119110927604332663043523)
                ·
                  refine ⟨1678666391406498994565285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1119110927604332663043523 1678666391406498994565285)
                  ·
                    refine ⟨314749948388718561480991, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1678666391406498994565285 314749948388718561480991)
                    ·
                      rfl

theorem cell22_919460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 4, 2, 2, 1, 4].length) (baseStart_919460 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_919460 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_919460 prefixEnd_919460 := by exact prefixLift 919460
  have htrace : WordTrace (prefixWord ++ tailWord_919460) baseStart_919460 baseEnd_919460 := by
    simpa [prefixWord, tailWord_919460, baseEnd_919460] using wordTrace_append hprefix tailTrace_919460
  have hstable : (prefixWord ++ tailWord_919460).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_919460).length < 2 ^ (prefixWord ++ tailWord_919460).sum := by decide
  have hdescent : baseEnd_919460 < baseStart_919460 := by decide
  rcases family_descends (prefixWord ++ tailWord_919460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_919471 : List Nat := [1, 1, 2, 1, 2, 2, 3, 3, 1, 6]
def baseStart_919471 : Nat := 118140960795 + 919471 * 2 ^ 59
def prefixEnd_919471 : Nat := 4983230072969 + 3 ^ 40 * 919471 * 2
def baseEnd_919471 : Nat := 314753713913518199455957

theorem tailTrace_919471 : CollatzResearch.WordTrace tailWord_919471 prefixEnd_919471 314753713913518199455957 := by
  unfold tailWord_919471
  simp only [CollatzResearch.WordTrace]
  refine ⟨33535862451921074989862267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22357241634614049993241511 33535862451921074989862267)
  ·
    refine ⟨50303793677881612484793401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33535862451921074989862267 50303793677881612484793401)
    ·
      refine ⟨37727845258411209363595051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50303793677881612484793401 37727845258411209363595051)
      ·
        refine ⟨56591767887616814045392577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37727845258411209363595051 56591767887616814045392577)
        ·
          refine ⟨42443825915712610534044433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56591767887616814045392577 42443825915712610534044433)
          ·
            refine ⟨31832869436784457900533325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42443825915712610534044433 31832869436784457900533325)
            ·
              refine ⟨11937326038794171712699997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31832869436784457900533325 11937326038794171712699997)
              ·
                refine ⟨4476497264547814392262499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11937326038794171712699997 4476497264547814392262499)
                ·
                  refine ⟨6714745896821721588393749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4476497264547814392262499 6714745896821721588393749)
                  ·
                    refine ⟨314753713913518199455957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6714745896821721588393749 314753713913518199455957)
                    ·
                      rfl

theorem cell22_919471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 3, 3, 1, 6].length) (baseStart_919471 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_919471 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_919471 prefixEnd_919471 := by exact prefixLift 919471
  have htrace : WordTrace (prefixWord ++ tailWord_919471) baseStart_919471 baseEnd_919471 := by
    simpa [prefixWord, tailWord_919471, baseEnd_919471] using wordTrace_append hprefix tailTrace_919471
  have hstable : (prefixWord ++ tailWord_919471).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_919471).length < 2 ^ (prefixWord ++ tailWord_919471).sum := by decide
  have hdescent : baseEnd_919471 < baseStart_919471 := by decide
  rcases family_descends (prefixWord ++ tailWord_919471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_919488 : List Nat := [2, 1, 1, 2, 3, 2, 3, 2, 2, 4]
def baseStart_919488 : Nat := 118140960795 + 919488 * 2 ^ 59
def prefixEnd_919488 : Nat := 4983230072969 + 3 ^ 40 * 919488 * 2
def baseEnd_919488 : Nat := 314759533360935821780905

theorem tailTrace_919488 : CollatzResearch.WordTrace tailWord_919488 prefixEnd_919488 314759533360935821780905 := by
  unfold tailWord_919488
  simp only [CollatzResearch.WordTrace]
  refine ⟨16768241246429743446615559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22357654995239657928820745 16768241246429743446615559)
  ·
    refine ⟨25152361869644615169923339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16768241246429743446615559 25152361869644615169923339)
    ·
      refine ⟨37728542804466922754885009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25152361869644615169923339 37728542804466922754885009)
      ·
        refine ⟨28296407103350192066163757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37728542804466922754885009 28296407103350192066163757)
        ·
          refine ⟨10611152663756322024811409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28296407103350192066163757 10611152663756322024811409)
          ·
            refine ⟨7958364497817241518608557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10611152663756322024811409 7958364497817241518608557)
            ·
              refine ⟨2984386686681465569478209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7958364497817241518608557 2984386686681465569478209)
              ·
                refine ⟨2238290015011099177108657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2984386686681465569478209 2238290015011099177108657)
                ·
                  refine ⟨1678717511258324382831493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2238290015011099177108657 1678717511258324382831493)
                  ·
                    refine ⟨314759533360935821780905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1678717511258324382831493 314759533360935821780905)
                    ·
                      rfl

theorem cell22_919488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 3, 2, 2, 4].length) (baseStart_919488 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_919488 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_919488 prefixEnd_919488 := by exact prefixLift 919488
  have htrace : WordTrace (prefixWord ++ tailWord_919488) baseStart_919488 baseEnd_919488 := by
    simpa [prefixWord, tailWord_919488, baseEnd_919488] using wordTrace_append hprefix tailTrace_919488
  have hstable : (prefixWord ++ tailWord_919488).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_919488).length < 2 ^ (prefixWord ++ tailWord_919488).sum := by decide
  have hdescent : baseEnd_919488 < baseStart_919488 := by decide
  rcases family_descends (prefixWord ++ tailWord_919488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_919531 : List Nat := [1, 1, 1, 1, 2, 3, 1, 3, 9]
def baseStart_919531 : Nat := 118140960795 + 919531 * 2 ^ 59
def prefixEnd_919531 : Nat := 4983230072969 + 3 ^ 40 * 919531 * 2
def baseEnd_919531 : Nat := 104924751046566014318591

theorem tailTrace_919531 : CollatzResearch.WordTrace tailWord_919531 prefixEnd_919531 104924751046566014318591 := by
  unfold tailWord_919531
  simp only [CollatzResearch.WordTrace]
  refine ⟨33538050831703705237046447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22358700554469136824697631 33538050831703705237046447)
  ·
    refine ⟨50307076247555557855569671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33538050831703705237046447 50307076247555557855569671)
    ·
      refine ⟨75460614371333336783354507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50307076247555557855569671 75460614371333336783354507)
      ·
        refine ⟨113190921557000005175031761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75460614371333336783354507 113190921557000005175031761)
        ·
          refine ⟨84893191167750003881273821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 113190921557000005175031761 84893191167750003881273821)
          ·
            refine ⟨31834946687906251455477683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 84893191167750003881273821 31834946687906251455477683)
            ·
              refine ⟨47752420031859377183216525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31834946687906251455477683 47752420031859377183216525)
              ·
                refine ⟨17907157511947266443706197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47752420031859377183216525 17907157511947266443706197)
                ·
                  refine ⟨104924751046566014318591, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 17907157511947266443706197 104924751046566014318591)
                  ·
                    rfl

theorem cell22_919531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 3, 9].length) (baseStart_919531 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_919531 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_919531 prefixEnd_919531 := by exact prefixLift 919531
  have htrace : WordTrace (prefixWord ++ tailWord_919531) baseStart_919531 baseEnd_919531 := by
    simpa [prefixWord, tailWord_919531, baseEnd_919531] using wordTrace_append hprefix tailTrace_919531
  have hstable : (prefixWord ++ tailWord_919531).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_919531).length < 2 ^ (prefixWord ++ tailWord_919531).sum := by decide
  have hdescent : baseEnd_919531 < baseStart_919531 := by decide
  rcases family_descends (prefixWord ++ tailWord_919531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_919550 : List Nat := [4, 2, 2, 2, 1, 1, 1, 1, 2, 6]
def baseStart_919550 : Nat := 118140960795 + 919550 * 2 ^ 59
def prefixEnd_919550 : Nat := 4983230072969 + 3 ^ 40 * 919550 * 2
def baseEnd_919550 : Nat := 314780757227988326730715

theorem tailTrace_919550 : CollatzResearch.WordTrace tailWord_919550 prefixEnd_919550 314780757227988326730715 := by
  unfold tailWord_919550
  simp only [CollatzResearch.WordTrace]
  refine ⟨4192342977329358935248513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22359162545756580987992069 4192342977329358935248513)
  ·
    refine ⟨3144257232997019201436385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4192342977329358935248513 3144257232997019201436385)
    ·
      refine ⟨2358192924747764401077289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3144257232997019201436385 2358192924747764401077289)
      ·
        refine ⟨1768644693560823300807967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2358192924747764401077289 1768644693560823300807967)
        ·
          refine ⟨2652967040341234951211951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1768644693560823300807967 2652967040341234951211951)
          ·
            refine ⟨3979450560511852426817927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2652967040341234951211951 3979450560511852426817927)
            ·
              refine ⟨5969175840767778640226891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3979450560511852426817927 5969175840767778640226891)
              ·
                refine ⟨8953763761151667960340337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5969175840767778640226891 8953763761151667960340337)
                ·
                  refine ⟨6715322820863750970255253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8953763761151667960340337 6715322820863750970255253)
                  ·
                    refine ⟨314780757227988326730715, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6715322820863750970255253 314780757227988326730715)
                    ·
                      rfl

theorem cell22_919550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 1, 1, 2, 6].length) (baseStart_919550 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_919550 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_919550 prefixEnd_919550 := by exact prefixLift 919550
  have htrace : WordTrace (prefixWord ++ tailWord_919550) baseStart_919550 baseEnd_919550 := by
    simpa [prefixWord, tailWord_919550, baseEnd_919550] using wordTrace_append hprefix tailTrace_919550
  have hstable : (prefixWord ++ tailWord_919550).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_919550).length < 2 ^ (prefixWord ++ tailWord_919550).sum := by decide
  have hdescent : baseEnd_919550 < baseStart_919550 := by decide
  rcases family_descends (prefixWord ++ tailWord_919550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_919563 : List Nat := [1, 1, 1, 1, 6, 1, 3, 1, 2, 5]
def baseStart_919563 : Nat := 118140960795 + 919563 * 2 ^ 59
def prefixEnd_919563 : Nat := 4983230072969 + 3 ^ 40 * 919563 * 2
def baseEnd_919563 : Nat := 314785207393660626155675

theorem tailTrace_919563 : CollatzResearch.WordTrace tailWord_919563 prefixEnd_919563 314785207393660626155675 := by
  unfold tailWord_919563
  simp only [CollatzResearch.WordTrace]
  refine ⟨33539217967587774702211343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22359478645058516468140895 33539217967587774702211343)
  ·
    refine ⟨50308826951381662053317015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33539217967587774702211343 50308826951381662053317015)
    ·
      refine ⟨75463240427072493079975523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50308826951381662053317015 75463240427072493079975523)
      ·
        refine ⟨113194860640608739619963285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75463240427072493079975523 113194860640608739619963285)
        ·
          refine ⟨5306009092528534669685779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 113194860640608739619963285 5306009092528534669685779)
          ·
            refine ⟨7959013638792802004528669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5306009092528534669685779 7959013638792802004528669)
            ·
              refine ⟨2984630114547300751698251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7959013638792802004528669 2984630114547300751698251)
              ·
                refine ⟨4476945171820951127547377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2984630114547300751698251 4476945171820951127547377)
                ·
                  refine ⟨3357708878865713345660533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4476945171820951127547377 3357708878865713345660533)
                  ·
                    refine ⟨314785207393660626155675, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3357708878865713345660533 314785207393660626155675)
                    ·
                      rfl

theorem cell22_919563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 3, 1, 2, 5].length) (baseStart_919563 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_919563 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_919563 prefixEnd_919563 := by exact prefixLift 919563
  have htrace : WordTrace (prefixWord ++ tailWord_919563) baseStart_919563 baseEnd_919563 := by
    simpa [prefixWord, tailWord_919563, baseEnd_919563] using wordTrace_append hprefix tailTrace_919563
  have hstable : (prefixWord ++ tailWord_919563).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_919563).length < 2 ^ (prefixWord ++ tailWord_919563).sum := by decide
  have hdescent : baseEnd_919563 < baseStart_919563 := by decide
  rcases family_descends (prefixWord ++ tailWord_919563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_919623 : List Nat := [1, 1, 4, 1, 3, 1, 1, 1, 3, 6]
def baseStart_919623 : Nat := 118140960795 + 919623 * 2 ^ 59
def prefixEnd_919623 : Nat := 4983230072969 + 3 ^ 40 * 919623 * 2
def baseEnd_919623 : Nat := 314805746619840469655491

theorem tailTrace_919623 : CollatzResearch.WordTrace tailWord_919623 prefixEnd_919623 314805746619840469655491 := by
  unfold tailWord_919623
  simp only [CollatzResearch.WordTrace]
  refine ⟨33541406347370404949395523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22360937564913603299597015 33541406347370404949395523)
  ·
    refine ⟨50312109521055607424093285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33541406347370404949395523 50312109521055607424093285)
    ·
      refine ⟨9433520535197926392017491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 50312109521055607424093285 9433520535197926392017491)
      ·
        refine ⟨14150280802796889588026237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9433520535197926392017491 14150280802796889588026237)
        ·
          refine ⟨5306355301048833595509839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14150280802796889588026237 5306355301048833595509839)
          ·
            refine ⟨7959532951573250393264759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5306355301048833595509839 7959532951573250393264759)
            ·
              refine ⟨11939299427359875589897139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7959532951573250393264759 11939299427359875589897139)
              ·
                refine ⟨17908949141039813384845709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11939299427359875589897139 17908949141039813384845709)
                ·
                  refine ⟨6715855927889930019317141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17908949141039813384845709 6715855927889930019317141)
                  ·
                    refine ⟨314805746619840469655491, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6715855927889930019317141 314805746619840469655491)
                    ·
                      rfl

theorem cell22_919623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 1, 1, 3, 6].length) (baseStart_919623 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_919623 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_919623 prefixEnd_919623 := by exact prefixLift 919623
  have htrace : WordTrace (prefixWord ++ tailWord_919623) baseStart_919623 baseEnd_919623 := by
    simpa [prefixWord, tailWord_919623, baseEnd_919623] using wordTrace_append hprefix tailTrace_919623
  have hstable : (prefixWord ++ tailWord_919623).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_919623).length < 2 ^ (prefixWord ++ tailWord_919623).sum := by decide
  have hdescent : baseEnd_919623 < baseStart_919623 := by decide
  rcases family_descends (prefixWord ++ tailWord_919623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_919644 : List Nat := [2, 2, 4, 1, 1, 4, 1, 3, 4]
def baseStart_919644 : Nat := 118140960795 + 919644 * 2 ^ 59
def prefixEnd_919644 : Nat := 4983230072969 + 3 ^ 40 * 919644 * 2
def baseEnd_919644 : Nat := 104937645116334471626809

theorem tailTrace_919644 : CollatzResearch.WordTrace tailWord_919644 prefixEnd_919644 104937645116334471626809 := by
  unfold tailWord_919644
  simp only [CollatzResearch.WordTrace]
  refine ⟨16771086140147162767954993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22361448186862883690606657 16771086140147162767954993)
  ·
    refine ⟨12578314605110372075966245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16771086140147162767954993 12578314605110372075966245)
    ·
      refine ⟨2358433988458194764243671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12578314605110372075966245 2358433988458194764243671)
      ·
        refine ⟨3537650982687292146365507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2358433988458194764243671 3537650982687292146365507)
        ·
          refine ⟨5306476474030938219548261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3537650982687292146365507 5306476474030938219548261)
          ·
            refine ⟨994964338880800916165299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5306476474030938219548261 994964338880800916165299)
            ·
              refine ⟨1492446508321201374247949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 994964338880800916165299 1492446508321201374247949)
              ·
                refine ⟨559667440620450515342981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1492446508321201374247949 559667440620450515342981)
                ·
                  refine ⟨104937645116334471626809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 559667440620450515342981 104937645116334471626809)
                  ·
                    rfl

theorem cell22_919644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 4, 1, 3, 4].length) (baseStart_919644 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_919644 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_919644 prefixEnd_919644 := by exact prefixLift 919644
  have htrace : WordTrace (prefixWord ++ tailWord_919644) baseStart_919644 baseEnd_919644 := by
    simpa [prefixWord, tailWord_919644, baseEnd_919644] using wordTrace_append hprefix tailTrace_919644
  have hstable : (prefixWord ++ tailWord_919644).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_919644).length < 2 ^ (prefixWord ++ tailWord_919644).sum := by decide
  have hdescent : baseEnd_919644 < baseStart_919644 := by decide
  rcases family_descends (prefixWord ++ tailWord_919644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_919730 : List Nat := [3, 2, 1, 1, 1, 3, 1, 1, 5, 4]
def baseStart_919730 : Nat := 118140960795 + 919730 * 2 ^ 59
def prefixEnd_919730 : Nat := 4983230072969 + 3 ^ 40 * 919730 * 2
def baseEnd_919730 : Nat := 314842374906527857230163

theorem tailTrace_919730 : CollatzResearch.WordTrace tailWord_919730 prefixEnd_919730 314842374906527857230163 := by
  unfold tailWord_919730
  simp only [CollatzResearch.WordTrace]
  refine ⟨8386327239495690555885161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22363539305321841482360429 8386327239495690555885161)
  ·
    refine ⟨6289745429621767916913871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8386327239495690555885161 6289745429621767916913871)
    ·
      refine ⟨9434618144432651875370807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6289745429621767916913871 9434618144432651875370807)
      ·
        refine ⟨14151927216648977813056211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9434618144432651875370807 14151927216648977813056211)
        ·
          refine ⟨21227890824973466719584317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14151927216648977813056211 21227890824973466719584317)
          ·
            refine ⟨7960459059365050019844119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21227890824973466719584317 7960459059365050019844119)
            ·
              refine ⟨11940688589047575029766179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7960459059365050019844119 11940688589047575029766179)
              ·
                refine ⟨17911032883571362544649269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11940688589047575029766179 17911032883571362544649269)
                ·
                  refine ⟨1679159332834815238560869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 17911032883571362544649269 1679159332834815238560869)
                  ·
                    refine ⟨314842374906527857230163, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1679159332834815238560869 314842374906527857230163)
                    ·
                      rfl

theorem cell22_919730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 1, 1, 5, 4].length) (baseStart_919730 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_919730 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_919730 prefixEnd_919730 := by exact prefixLift 919730
  have htrace : WordTrace (prefixWord ++ tailWord_919730) baseStart_919730 baseEnd_919730 := by
    simpa [prefixWord, tailWord_919730, baseEnd_919730] using wordTrace_append hprefix tailTrace_919730
  have hstable : (prefixWord ++ tailWord_919730).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_919730).length < 2 ^ (prefixWord ++ tailWord_919730).sum := by decide
  have hdescent : baseEnd_919730 < baseStart_919730 := by decide
  rcases family_descends (prefixWord ++ tailWord_919730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_919775 : List Nat := [1, 1, 2, 3, 2, 1, 1, 3, 4, 4]
def baseStart_919775 : Nat := 118140960795 + 919775 * 2 ^ 59
def prefixEnd_919775 : Nat := 4983230072969 + 3 ^ 40 * 919775 * 2
def baseEnd_919775 : Nat := 314857779326162739855025

theorem tailTrace_919775 : CollatzResearch.WordTrace tailWord_919775 prefixEnd_919775 314857779326162739855025 := by
  unfold tailWord_919775
  simp only [CollatzResearch.WordTrace]
  refine ⟨33546950242819734908928779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22364633495213156605952519 33546950242819734908928779)
  ·
    refine ⟨50320425364229602363393169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33546950242819734908928779 50320425364229602363393169)
    ·
      refine ⟨37740319023172201772544877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50320425364229602363393169 37740319023172201772544877)
      ·
        refine ⟨14152619633689575664704329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37740319023172201772544877 14152619633689575664704329)
        ·
          refine ⟨10614464725267181748528247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14152619633689575664704329 10614464725267181748528247)
          ·
            refine ⟨15921697087900772622792371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10614464725267181748528247 15921697087900772622792371)
            ·
              refine ⟨23882545631851158934188557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15921697087900772622792371 23882545631851158934188557)
              ·
                refine ⟨8955954611944184600320709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23882545631851158934188557 8955954611944184600320709)
                ·
                  refine ⟨1679241489739534612560133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8955954611944184600320709 1679241489739534612560133)
                  ·
                    refine ⟨314857779326162739855025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1679241489739534612560133 314857779326162739855025)
                    ·
                      rfl

theorem cell22_919775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 3, 4, 4].length) (baseStart_919775 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_919775 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_919775 prefixEnd_919775 := by exact prefixLift 919775
  have htrace : WordTrace (prefixWord ++ tailWord_919775) baseStart_919775 baseEnd_919775 := by
    simpa [prefixWord, tailWord_919775, baseEnd_919775] using wordTrace_append hprefix tailTrace_919775
  have hstable : (prefixWord ++ tailWord_919775).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_919775).length < 2 ^ (prefixWord ++ tailWord_919775).sum := by decide
  have hdescent : baseEnd_919775 < baseStart_919775 := by decide
  rcases family_descends (prefixWord ++ tailWord_919775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_919777 : List Nat := [1, 2, 3, 1, 3, 1, 3, 1, 4, 3]
def baseStart_919777 : Nat := 118140960795 + 919777 * 2 ^ 59
def prefixEnd_919777 : Nat := 4983230072969 + 3 ^ 40 * 919777 * 2
def baseEnd_919777 : Nat := 314858463967035401305019

theorem tailTrace_919777 : CollatzResearch.WordTrace tailWord_919777 prefixEnd_919777 314858463967035401305019 := by
  unfold tailWord_919777
  simp only [CollatzResearch.WordTrace]
  refine ⟨33547023188812489250501585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22364682125874992833667723 33547023188812489250501585)
  ·
    refine ⟨25160267391609366937876189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33547023188812489250501585 25160267391609366937876189)
    ·
      refine ⟨9435100271853512601703571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25160267391609366937876189 9435100271853512601703571)
      ·
        refine ⟨14152650407780268902555357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9435100271853512601703571 14152650407780268902555357)
        ·
          refine ⟨5307243902917600838458259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14152650407780268902555357 5307243902917600838458259)
          ·
            refine ⟨7960865854376401257687389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5307243902917600838458259 7960865854376401257687389)
            ·
              refine ⟨2985324695391150471632771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7960865854376401257687389 2985324695391150471632771)
              ·
                refine ⟨4477987043086725707449157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2985324695391150471632771 4477987043086725707449157)
                ·
                  refine ⟨839622570578761070146717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4477987043086725707449157 839622570578761070146717)
                  ·
                    refine ⟨314858463967035401305019, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 839622570578761070146717 314858463967035401305019)
                    ·
                      rfl

theorem cell22_919777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 3, 1, 4, 3].length) (baseStart_919777 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_919777 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_919777 prefixEnd_919777 := by exact prefixLift 919777
  have htrace : WordTrace (prefixWord ++ tailWord_919777) baseStart_919777 baseEnd_919777 := by
    simpa [prefixWord, tailWord_919777, baseEnd_919777] using wordTrace_append hprefix tailTrace_919777
  have hstable : (prefixWord ++ tailWord_919777).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_919777).length < 2 ^ (prefixWord ++ tailWord_919777).sum := by decide
  have hdescent : baseEnd_919777 < baseStart_919777 := by decide
  rcases family_descends (prefixWord ++ tailWord_919777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_919779 : List Nat := [1, 1, 1, 8, 1, 1, 2, 1, 6]
def baseStart_919779 : Nat := 118140960795 + 919779 * 2 ^ 59
def prefixEnd_919779 : Nat := 4983230072969 + 3 ^ 40 * 919779 * 2
def baseEnd_919779 : Nat := 104953049535969354251671

theorem tailTrace_919779 : CollatzResearch.WordTrace tailWord_919779 prefixEnd_919779 104953049535969354251671 := by
  unfold tailWord_919779
  simp only [CollatzResearch.WordTrace]
  refine ⟨33547096134805243592074391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22364730756536829061382927 33547096134805243592074391)
  ·
    refine ⟨50320644202207865388111587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33547096134805243592074391 50320644202207865388111587)
    ·
      refine ⟨75480966303311798082167381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50320644202207865388111587 75480966303311798082167381)
      ·
        refine ⟨884542573866935133775399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 8 75480966303311798082167381 884542573866935133775399)
        ·
          refine ⟨1326813860800402700663099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 884542573866935133775399 1326813860800402700663099)
          ·
            refine ⟨1990220791200604050994649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1326813860800402700663099 1990220791200604050994649)
            ·
              refine ⟨1492665593400453038245987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1990220791200604050994649 1492665593400453038245987)
              ·
                refine ⟨2238998390100679557368981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1492665593400453038245987 2238998390100679557368981)
                ·
                  refine ⟨104953049535969354251671, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2238998390100679557368981 104953049535969354251671)
                  ·
                    rfl

theorem cell22_919779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 1, 2, 1, 6].length) (baseStart_919779 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_919779 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_919779 prefixEnd_919779 := by exact prefixLift 919779
  have htrace : WordTrace (prefixWord ++ tailWord_919779) baseStart_919779 baseEnd_919779 := by
    simpa [prefixWord, tailWord_919779, baseEnd_919779] using wordTrace_append hprefix tailTrace_919779
  have hstable : (prefixWord ++ tailWord_919779).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_919779).length < 2 ^ (prefixWord ++ tailWord_919779).sum := by decide
  have hdescent : baseEnd_919779 < baseStart_919779 := by decide
  rcases family_descends (prefixWord ++ tailWord_919779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_919790 : List Nat := [4, 1, 2, 1, 1, 1, 1, 11]
def baseStart_919790 : Nat := 118140960795 + 919790 * 2 ^ 59
def prefixEnd_919790 : Nat := 4983230072969 + 3 ^ 40 * 919790 * 2
def baseEnd_919790 : Nat := 34984768236967522303331

theorem tailTrace_919790 : CollatzResearch.WordTrace tailWord_919790 prefixEnd_919790 34984768236967522303331 := by
  unfold tailWord_919790
  simp only [CollatzResearch.WordTrace]
  refine ⟨4193437167220674058840603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22364998225176928313816549 4193437167220674058840603)
  ·
    refine ⟨6290155750831011088260905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4193437167220674058840603 6290155750831011088260905)
    ·
      refine ⟨4717616813123258316195679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6290155750831011088260905 4717616813123258316195679)
      ·
        refine ⟨7076425219684887474293519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4717616813123258316195679 7076425219684887474293519)
        ·
          refine ⟨10614637829527331211440279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7076425219684887474293519 10614637829527331211440279)
          ·
            refine ⟨15921956744290996817160419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10614637829527331211440279 15921956744290996817160419)
            ·
              refine ⟨23882935116436495225740629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15921956744290996817160419 23882935116436495225740629)
              ·
                refine ⟨34984768236967522303331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 23882935116436495225740629 34984768236967522303331)
                ·
                  rfl

theorem cell22_919790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 11].length) (baseStart_919790 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_919790 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_919790 prefixEnd_919790 := by exact prefixLift 919790
  have htrace : WordTrace (prefixWord ++ tailWord_919790) baseStart_919790 baseEnd_919790 := by
    simpa [prefixWord, tailWord_919790, baseEnd_919790] using wordTrace_append hprefix tailTrace_919790
  have hstable : (prefixWord ++ tailWord_919790).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_919790).length < 2 ^ (prefixWord ++ tailWord_919790).sum := by decide
  have hdescent : baseEnd_919790 < baseStart_919790 := by decide
  rcases family_descends (prefixWord ++ tailWord_919790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_919794 : List Nat := [3, 2, 1, 3, 2, 3, 1, 1, 1, 5]
def baseStart_919794 : Nat := 118140960795 + 919794 * 2 ^ 59
def prefixEnd_919794 : Nat := 4983230072969 + 3 ^ 40 * 919794 * 2
def baseEnd_919794 : Nat := 314864283414453023629967

theorem tailTrace_919794 : CollatzResearch.WordTrace tailWord_919794 prefixEnd_919794 314864283414453023629967 := by
  unfold tailWord_919794
  simp only [CollatzResearch.WordTrace]
  refine ⟨8386910807437725288467609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22365095486500600769246957 8386910807437725288467609)
  ·
    refine ⟨6290183105578293966350707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8386910807437725288467609 6290183105578293966350707)
    ·
      refine ⟨9435274658367440949526061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6290183105578293966350707 9435274658367440949526061)
      ·
        refine ⟨3538227996887790356072273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9435274658367440949526061 3538227996887790356072273)
        ·
          refine ⟨2653670997665842767054205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3538227996887790356072273 2653670997665842767054205)
          ·
            refine ⟨995126624124691037645327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2653670997665842767054205 995126624124691037645327)
            ·
              refine ⟨1492689936187036556467991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 995126624124691037645327 1492689936187036556467991)
              ·
                refine ⟨2239034904280554834701987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1492689936187036556467991 2239034904280554834701987)
                ·
                  refine ⟨3358552356420832252052981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2239034904280554834701987 3358552356420832252052981)
                  ·
                    refine ⟨314864283414453023629967, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3358552356420832252052981 314864283414453023629967)
                    ·
                      rfl

theorem cell22_919794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 3, 1, 1, 1, 5].length) (baseStart_919794 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_919794 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_919794 prefixEnd_919794 := by exact prefixLift 919794
  have htrace : WordTrace (prefixWord ++ tailWord_919794) baseStart_919794 baseEnd_919794 := by
    simpa [prefixWord, tailWord_919794, baseEnd_919794] using wordTrace_append hprefix tailTrace_919794
  have hstable : (prefixWord ++ tailWord_919794).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_919794).length < 2 ^ (prefixWord ++ tailWord_919794).sum := by decide
  have hdescent : baseEnd_919794 < baseStart_919794 := by decide
  rcases family_descends (prefixWord ++ tailWord_919794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_919835 : List Nat := [1, 1, 1, 1, 1, 1, 8, 1, 7]
def baseStart_919835 : Nat := 118140960795 + 919835 * 2 ^ 59
def prefixEnd_919835 : Nat := 4983230072969 + 3 ^ 40 * 919835 * 2
def baseEnd_919835 : Nat := 104959439517447527784947

theorem tailTrace_919835 : CollatzResearch.WordTrace tailWord_919835 prefixEnd_919835 104959439517447527784947 := by
  unfold tailWord_919835
  simp only [CollatzResearch.WordTrace]
  refine ⟨33549138622602365156112959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22366092415068243437408639 33549138622602365156112959)
  ·
    refine ⟨50323707933903547734169439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33549138622602365156112959 50323707933903547734169439)
    ·
      refine ⟨75485561900855321601254159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50323707933903547734169439 75485561900855321601254159)
      ·
        refine ⟨113228342851282982401881239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75485561900855321601254159 113228342851282982401881239)
        ·
          refine ⟨169842514276924473602821859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113228342851282982401881239 169842514276924473602821859)
          ·
            refine ⟨254763771415386710404232789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 169842514276924473602821859 254763771415386710404232789)
            ·
              refine ⟨2985512946274063012549603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 254763771415386710404232789 2985512946274063012549603)
              ·
                refine ⟨4478269419411094518824405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2985512946274063012549603 4478269419411094518824405)
                ·
                  refine ⟨104959439517447527784947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4478269419411094518824405 104959439517447527784947)
                  ·
                    rfl

theorem cell22_919835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 8, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 8, 1, 7].length) (baseStart_919835 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_919835 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_919835 prefixEnd_919835 := by exact prefixLift 919835
  have htrace : WordTrace (prefixWord ++ tailWord_919835) baseStart_919835 baseEnd_919835 := by
    simpa [prefixWord, tailWord_919835, baseEnd_919835] using wordTrace_append hprefix tailTrace_919835
  have hstable : (prefixWord ++ tailWord_919835).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_919835).length < 2 ^ (prefixWord ++ tailWord_919835).sum := by decide
  have hdescent : baseEnd_919835 < baseStart_919835 := by decide
  rcases family_descends (prefixWord ++ tailWord_919835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_919839 : List Nat := [1, 1, 2, 4, 3, 1, 3, 1, 3, 3]
def baseStart_919839 : Nat := 118140960795 + 919839 * 2 ^ 59
def prefixEnd_919839 : Nat := 4983230072969 + 3 ^ 40 * 919839 * 2
def baseEnd_919839 : Nat := 314879687834087906254829

theorem tailTrace_919839 : CollatzResearch.WordTrace tailWord_919839 prefixEnd_919839 314879687834087906254829 := by
  unfold tailWord_919839
  simp only [CollatzResearch.WordTrace]
  refine ⟨33549284514587873839258571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22366189676391915892839047 33549284514587873839258571)
  ·
    refine ⟨50323926771881810758887857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33549284514587873839258571 50323926771881810758887857)
    ·
      refine ⟨37742945078911358069165893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50323926771881810758887857 37742945078911358069165893)
      ·
        refine ⟨7076802202295879637968605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 37742945078911358069165893 7076802202295879637968605)
        ·
          refine ⟨2653800825860954864238227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7076802202295879637968605 2653800825860954864238227)
          ·
            refine ⟨3980701238791432296357341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2653800825860954864238227 3980701238791432296357341)
            ·
              refine ⟨1492762964546787111134003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3980701238791432296357341 1492762964546787111134003)
              ·
                refine ⟨2239144446820180666701005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1492762964546787111134003 2239144446820180666701005)
                ·
                  refine ⟨839679167557567750012877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2239144446820180666701005 839679167557567750012877)
                  ·
                    refine ⟨314879687834087906254829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 839679167557567750012877 314879687834087906254829)
                    ·
                      rfl

theorem cell22_919839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 3, 1, 3, 3].length) (baseStart_919839 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_919839 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_919839 prefixEnd_919839 := by exact prefixLift 919839
  have htrace : WordTrace (prefixWord ++ tailWord_919839) baseStart_919839 baseEnd_919839 := by
    simpa [prefixWord, tailWord_919839, baseEnd_919839] using wordTrace_append hprefix tailTrace_919839
  have hstable : (prefixWord ++ tailWord_919839).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_919839).length < 2 ^ (prefixWord ++ tailWord_919839).sum := by decide
  have hdescent : baseEnd_919839 < baseStart_919839 := by decide
  rcases family_descends (prefixWord ++ tailWord_919839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_919914 : List Nat := [3, 1, 3, 3, 1, 2, 1, 2, 6]
def baseStart_919914 : Nat := 118140960795 + 919914 * 2 ^ 59
def prefixEnd_919914 : Nat := 4983230072969 + 3 ^ 40 * 919914 * 2
def baseEnd_919914 : Nat := 104968453955604236876533

theorem tailTrace_919914 : CollatzResearch.WordTrace tailWord_919914 prefixEnd_919914 104968453955604236876533 := by
  unfold tailWord_919914
  simp only [CollatzResearch.WordTrace]
  refine ⟨8388004997329040412059699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22368013326210774432159197 8388004997329040412059699)
  ·
    refine ⟨12582007495993560618089549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8388004997329040412059699 12582007495993560618089549)
    ·
      refine ⟨4718252810997585231783581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12582007495993560618089549 4718252810997585231783581)
      ·
        refine ⟨1769344804124094461918843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4718252810997585231783581 1769344804124094461918843)
        ·
          refine ⟨2654017206186141692878265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1769344804124094461918843 2654017206186141692878265)
          ·
            refine ⟨1990512904639606269658699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2654017206186141692878265 1990512904639606269658699)
            ·
              refine ⟨2985769356959409404488049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1990512904639606269658699 2985769356959409404488049)
              ·
                refine ⟨2239327017719557053366037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2985769356959409404488049 2239327017719557053366037)
                ·
                  refine ⟨104968453955604236876533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2239327017719557053366037 104968453955604236876533)
                  ·
                    rfl

theorem cell22_919914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 2, 1, 2, 6].length) (baseStart_919914 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_919914 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_919914 prefixEnd_919914 := by exact prefixLift 919914
  have htrace : WordTrace (prefixWord ++ tailWord_919914) baseStart_919914 baseEnd_919914 := by
    simpa [prefixWord, tailWord_919914, baseEnd_919914] using wordTrace_append hprefix tailTrace_919914
  have hstable : (prefixWord ++ tailWord_919914).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_919914).length < 2 ^ (prefixWord ++ tailWord_919914).sum := by decide
  have hdescent : baseEnd_919914 < baseStart_919914 := by decide
  rcases family_descends (prefixWord ++ tailWord_919914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_919927 : List Nat := [1, 1, 3, 1, 1, 2, 2, 5, 2, 4]
def baseStart_919927 : Nat := 118140960795 + 919927 * 2 ^ 59
def prefixEnd_919927 : Nat := 4983230072969 + 3 ^ 40 * 919927 * 2
def baseEnd_919927 : Nat := 314909812032485010054559

theorem tailTrace_919927 : CollatzResearch.WordTrace tailWord_919927 prefixEnd_919927 314909812032485010054559 := by
  unfold tailWord_919927
  simp only [CollatzResearch.WordTrace]
  refine ⟨33552494138269064868462035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22368329425512709912308023 33552494138269064868462035)
  ·
    refine ⟨50328741207403597302693053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33552494138269064868462035 50328741207403597302693053)
    ·
      refine ⟨18873277952776348988509895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50328741207403597302693053 18873277952776348988509895)
      ·
        refine ⟨28309916929164523482764843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18873277952776348988509895 28309916929164523482764843)
        ·
          refine ⟨42464875393746785224147265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28309916929164523482764843 42464875393746785224147265)
          ·
            refine ⟨31848656545310088918110449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42464875393746785224147265 31848656545310088918110449)
            ·
              refine ⟨23886492408982566688582837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31848656545310088918110449 23886492408982566688582837)
              ·
                refine ⟨2239358663342115627054641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 23886492408982566688582837 2239358663342115627054641)
                ·
                  refine ⟨1679518997506586720290981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2239358663342115627054641 1679518997506586720290981)
                  ·
                    refine ⟨314909812032485010054559, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1679518997506586720290981 314909812032485010054559)
                    ·
                      rfl

theorem cell22_919927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 5, 2, 4].length) (baseStart_919927 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_919927 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_919927 prefixEnd_919927 := by exact prefixLift 919927
  have htrace : WordTrace (prefixWord ++ tailWord_919927) baseStart_919927 baseEnd_919927 := by
    simpa [prefixWord, tailWord_919927, baseEnd_919927] using wordTrace_append hprefix tailTrace_919927
  have hstable : (prefixWord ++ tailWord_919927).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_919927).length < 2 ^ (prefixWord ++ tailWord_919927).sum := by decide
  have hdescent : baseEnd_919927 < baseStart_919927 := by decide
  rcases family_descends (prefixWord ++ tailWord_919927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_919972 : List Nat := [2, 3, 1, 2, 1, 1, 2, 2, 2, 6]
def baseStart_919972 : Nat := 118140960795 + 919972 * 2 ^ 59
def prefixEnd_919972 : Nat := 4983230072969 + 3 ^ 40 * 919972 * 2
def baseEnd_919972 : Nat := 314925216452119892679421

theorem tailTrace_919972 : CollatzResearch.WordTrace tailWord_919972 prefixEnd_919972 314925216452119892679421 := by
  unfold tailWord_919972
  simp only [CollatzResearch.WordTrace]
  refine ⟨16777067711553018776925085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22369423615404025035900113 16777067711553018776925085)
  ·
    refine ⟨6291400391832382041346907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16777067711553018776925085 6291400391832382041346907)
    ·
      refine ⟨9437100587748573062020361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6291400391832382041346907 9437100587748573062020361)
      ·
        refine ⟨7077825440811429796515271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9437100587748573062020361 7077825440811429796515271)
        ·
          refine ⟨10616738161217144694772907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7077825440811429796515271 10616738161217144694772907)
          ·
            refine ⟨15925107241825717042159361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10616738161217144694772907 15925107241825717042159361)
            ·
              refine ⟨11943830431369287781619521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15925107241825717042159361 11943830431369287781619521)
              ·
                refine ⟨8957872823526965836214641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11943830431369287781619521 8957872823526965836214641)
                ·
                  refine ⟨6718404617645224377160981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8957872823526965836214641 6718404617645224377160981)
                  ·
                    refine ⟨314925216452119892679421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6718404617645224377160981 314925216452119892679421)
                    ·
                      rfl

theorem cell22_919972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 2, 2, 2, 6].length) (baseStart_919972 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_919972 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_919972 prefixEnd_919972 := by exact prefixLift 919972
  have htrace : WordTrace (prefixWord ++ tailWord_919972) baseStart_919972 baseEnd_919972 := by
    simpa [prefixWord, tailWord_919972, baseEnd_919972] using wordTrace_append hprefix tailTrace_919972
  have hstable : (prefixWord ++ tailWord_919972).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_919972).length < 2 ^ (prefixWord ++ tailWord_919972).sum := by decide
  have hdescent : baseEnd_919972 < baseStart_919972 := by decide
  rcases family_descends (prefixWord ++ tailWord_919972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_919976 : List Nat := [2, 1, 6, 1, 1, 1, 4, 6]
def baseStart_919976 : Nat := 118140960795 + 919976 * 2 ^ 59
def prefixEnd_919976 : Nat := 4983230072969 + 3 ^ 40 * 919976 * 2
def baseEnd_919976 : Nat := 34991842859318357286601

theorem tailTrace_919976 : CollatzResearch.WordTrace tailWord_919976 prefixEnd_919976 34991842859318357286601 := by
  unfold tailWord_919976
  simp only [CollatzResearch.WordTrace]
  refine ⟨16777140657545773118497891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22369520876727697491330521 16777140657545773118497891)
  ·
    refine ⟨25165710986318659677746837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16777140657545773118497891 25165710986318659677746837)
    ·
      refine ⟨1179642702483687172394383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 25165710986318659677746837 1179642702483687172394383)
      ·
        refine ⟨1769464053725530758591575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1179642702483687172394383 1769464053725530758591575)
        ·
          refine ⟨2654196080588296137887363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1769464053725530758591575 2654196080588296137887363)
          ·
            refine ⟨3981294120882444206831045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2654196080588296137887363 3981294120882444206831045)
            ·
              refine ⟨746492647665458288780821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3981294120882444206831045 746492647665458288780821)
              ·
                refine ⟨34991842859318357286601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 746492647665458288780821 34991842859318357286601)
                ·
                  rfl

theorem cell22_919976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 4, 6].length) (baseStart_919976 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_919976 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_919976 prefixEnd_919976 := by exact prefixLift 919976
  have htrace : WordTrace (prefixWord ++ tailWord_919976) baseStart_919976 baseEnd_919976 := by
    simpa [prefixWord, tailWord_919976, baseEnd_919976] using wordTrace_append hprefix tailTrace_919976
  have hstable : (prefixWord ++ tailWord_919976).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_919976).length < 2 ^ (prefixWord ++ tailWord_919976).sum := by decide
  have hdescent : baseEnd_919976 < baseStart_919976 := by decide
  rcases family_descends (prefixWord ++ tailWord_919976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_920021 : List Nat := [1, 3, 2, 3, 1, 2, 4, 1, 5]
def baseStart_920021 : Nat := 118140960795 + 920021 * 2 ^ 59
def prefixEnd_920021 : Nat := 4983230072969 + 3 ^ 40 * 920021 * 2
def baseEnd_920021 : Nat := 104980663384500032734757

theorem tailTrace_920021 : CollatzResearch.WordTrace tailWord_920021 prefixEnd_920021 104980663384500032734757 := by
  unfold tailWord_920021
  simp only [CollatzResearch.WordTrace]
  refine ⟨33555922599928518922383917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22370615066619012614922611 33555922599928518922383917)
  ·
    refine ⟨12583470974973194595893969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33555922599928518922383917 12583470974973194595893969)
    ·
      refine ⟨9437603231229895946920477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12583470974973194595893969 9437603231229895946920477)
      ·
        refine ⟨3539101211711210980095179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9437603231229895946920477 3539101211711210980095179)
        ·
          refine ⟨5308651817566816470142769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3539101211711210980095179 5308651817566816470142769)
          ·
            refine ⟨3981488863175112352607077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5308651817566816470142769 3981488863175112352607077)
            ·
              refine ⟨746529161845333566113827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3981488863175112352607077 746529161845333566113827)
              ·
                refine ⟨1119793742768000349170741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 746529161845333566113827 1119793742768000349170741)
                ·
                  refine ⟨104980663384500032734757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1119793742768000349170741 104980663384500032734757)
                  ·
                    rfl

theorem cell22_920021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 4, 1, 5].length) (baseStart_920021 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_920021 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_920021 prefixEnd_920021 := by exact prefixLift 920021
  have htrace : WordTrace (prefixWord ++ tailWord_920021) baseStart_920021 baseEnd_920021 := by
    simpa [prefixWord, tailWord_920021, baseEnd_920021] using wordTrace_append hprefix tailTrace_920021
  have hstable : (prefixWord ++ tailWord_920021).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_920021).length < 2 ^ (prefixWord ++ tailWord_920021).sum := by decide
  have hdescent : baseEnd_920021 < baseStart_920021 := by decide
  rcases family_descends (prefixWord ++ tailWord_920021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_920032 : List Nat := [2, 1, 1, 3, 1, 1, 4, 1, 8]
def baseStart_920032 : Nat := 118140960795 + 920032 * 2 ^ 59
def prefixEnd_920032 : Nat := 4983230072969 + 3 ^ 40 * 920032 * 2
def baseEnd_920032 : Nat := 104981918559433245393079

theorem tailTrace_920032 : CollatzResearch.WordTrace tailWord_920032 prefixEnd_920032 104981918559433245393079 := by
  unfold tailWord_920032
  simp only [CollatzResearch.WordTrace]
  refine ⟨16778161901444333900517175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22370882535259111867356233 16778161901444333900517175)
  ·
    refine ⟨25167242852166500850775763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16778161901444333900517175 25167242852166500850775763)
    ·
      refine ⟨37750864278249751276163645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25167242852166500850775763 37750864278249751276163645)
      ·
        refine ⟨14156574104343656728561367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37750864278249751276163645 14156574104343656728561367)
        ·
          refine ⟨21234861156515485092842051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14156574104343656728561367 21234861156515485092842051)
          ·
            refine ⟨31852291734773227639263077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21234861156515485092842051 31852291734773227639263077)
            ·
              refine ⟨5972304700269980182361827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31852291734773227639263077 5972304700269980182361827)
              ·
                refine ⟨8958457050404970273542741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5972304700269980182361827 8958457050404970273542741)
                ·
                  refine ⟨104981918559433245393079, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 8958457050404970273542741 104981918559433245393079)
                  ·
                    rfl

theorem cell22_920032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 4, 1, 8].length) (baseStart_920032 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_920032 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_920032 prefixEnd_920032 := by exact prefixLift 920032
  have htrace : WordTrace (prefixWord ++ tailWord_920032) baseStart_920032 baseEnd_920032 := by
    simpa [prefixWord, tailWord_920032, baseEnd_920032] using wordTrace_append hprefix tailTrace_920032
  have hstable : (prefixWord ++ tailWord_920032).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_920032).length < 2 ^ (prefixWord ++ tailWord_920032).sum := by decide
  have hdescent : baseEnd_920032 < baseStart_920032 := by decide
  rcases family_descends (prefixWord ++ tailWord_920032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_920051 : List Nat := [1, 1, 1, 2, 2, 2, 7, 1, 1, 4]
def baseStart_920051 : Nat := 118140960795 + 920051 * 2 ^ 59
def prefixEnd_920051 : Nat := 4983230072969 + 3 ^ 40 * 920051 * 2
def baseEnd_920051 : Nat := 314952259766590019954179

theorem tailTrace_920051 : CollatzResearch.WordTrace tailWord_920051 prefixEnd_920051 314952259766590019954179 := by
  unfold tailWord_920051
  simp only [CollatzResearch.WordTrace]
  refine ⟨33557016789819834045976007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22371344526546556030650671 33557016789819834045976007)
  ·
    refine ⟨50335525184729751068964011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33557016789819834045976007 50335525184729751068964011)
    ·
      refine ⟨75503287777094626603446017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50335525184729751068964011 75503287777094626603446017)
      ·
        refine ⟨56627465832820969952584513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75503287777094626603446017 56627465832820969952584513)
        ·
          refine ⟨42470599374615727464438385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56627465832820969952584513 42470599374615727464438385)
          ·
            refine ⟨31852949530961795598328789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42470599374615727464438385 31852949530961795598328789)
            ·
              refine ⟨746553504631917084335831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 31852949530961795598328789 746553504631917084335831)
              ·
                refine ⟨1119830256947875626503747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 746553504631917084335831 1119830256947875626503747)
                ·
                  refine ⟨1679745385421813439755621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1119830256947875626503747 1679745385421813439755621)
                  ·
                    refine ⟨314952259766590019954179, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1679745385421813439755621 314952259766590019954179)
                    ·
                      rfl

theorem cell22_920051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 7, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 7, 1, 1, 4].length) (baseStart_920051 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_920051 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_920051 prefixEnd_920051 := by exact prefixLift 920051
  have htrace : WordTrace (prefixWord ++ tailWord_920051) baseStart_920051 baseEnd_920051 := by
    simpa [prefixWord, tailWord_920051, baseEnd_920051] using wordTrace_append hprefix tailTrace_920051
  have hstable : (prefixWord ++ tailWord_920051).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_920051).length < 2 ^ (prefixWord ++ tailWord_920051).sum := by decide
  have hdescent : baseEnd_920051 < baseStart_920051 := by decide
  rcases family_descends (prefixWord ++ tailWord_920051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_920070 : List Nat := [6, 2, 1, 1, 1, 2, 1, 1, 2, 5]
def baseStart_920070 : Nat := 118140960795 + 920070 * 2 ^ 59
def prefixEnd_920070 : Nat := 4983230072969 + 3 ^ 40 * 920070 * 2
def baseEnd_920070 : Nat := 314958763854880303729121

theorem tailTrace_920070 : CollatzResearch.WordTrace tailWord_920070 prefixEnd_920070 314958763854880303729121 := by
  unfold tailWord_920070
  simp only [CollatzResearch.WordTrace]
  refine ⟨1048678430523468759091177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 22371806517834000193945109 1048678430523468759091177)
  ·
    refine ⟨786508822892601569318383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1048678430523468759091177 786508822892601569318383)
    ·
      refine ⟨1179763234338902353977575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 786508822892601569318383 1179763234338902353977575)
      ·
        refine ⟨1769644851508353530966363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1179763234338902353977575 1769644851508353530966363)
        ·
          refine ⟨2654467277262530296449545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1769644851508353530966363 2654467277262530296449545)
          ·
            refine ⟨1990850457946897722337159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2654467277262530296449545 1990850457946897722337159)
            ·
              refine ⟨2986275686920346583505739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1990850457946897722337159 2986275686920346583505739)
              ·
                refine ⟨4479413530380519875258609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2986275686920346583505739 4479413530380519875258609)
                ·
                  refine ⟨3359560147785389906443957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4479413530380519875258609 3359560147785389906443957)
                  ·
                    refine ⟨314958763854880303729121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3359560147785389906443957 314958763854880303729121)
                    ·
                      rfl

theorem cell22_920070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 2, 1, 1, 2, 5].length) (baseStart_920070 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_920070 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_920070 prefixEnd_920070 := by exact prefixLift 920070
  have htrace : WordTrace (prefixWord ++ tailWord_920070) baseStart_920070 baseEnd_920070 := by
    simpa [prefixWord, tailWord_920070, baseEnd_920070] using wordTrace_append hprefix tailTrace_920070
  have hstable : (prefixWord ++ tailWord_920070).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_920070).length < 2 ^ (prefixWord ++ tailWord_920070).sum := by decide
  have hdescent : baseEnd_920070 < baseStart_920070 := by decide
  rcases family_descends (prefixWord ++ tailWord_920070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_920096 : List Nat := [2, 1, 1, 6, 2, 1, 1, 1, 1, 6]
def baseStart_920096 : Nat := 118140960795 + 920096 * 2 ^ 59
def prefixEnd_920096 : Nat := 4983230072969 + 3 ^ 40 * 920096 * 2
def baseEnd_920096 : Nat := 314967664186224902579041

theorem tailTrace_920096 : CollatzResearch.WordTrace tailWord_920096 prefixEnd_920096 314967664186224902579041 := by
  unfold tailWord_920096
  simp only [CollatzResearch.WordTrace]
  refine ⟨16779329037328403365682071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22372438716437871154242761 16779329037328403365682071)
  ·
    refine ⟨25168993555992605048523107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16779329037328403365682071 25168993555992605048523107)
    ·
      refine ⟨37753490333988907572784661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25168993555992605048523107 37753490333988907572784661)
      ·
        refine ⟨1769694859405730042474281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 37753490333988907572784661 1769694859405730042474281)
        ·
          refine ⟨1327271144554297531855711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1769694859405730042474281 1327271144554297531855711)
          ·
            refine ⟨1990906716831446297783567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1327271144554297531855711 1990906716831446297783567)
            ·
              refine ⟨2986360075247169446675351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1990906716831446297783567 2986360075247169446675351)
              ·
                refine ⟨4479540112870754170013027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2986360075247169446675351 4479540112870754170013027)
                ·
                  refine ⟨6719310169306131255019541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4479540112870754170013027 6719310169306131255019541)
                  ·
                    refine ⟨314967664186224902579041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6719310169306131255019541 314967664186224902579041)
                    ·
                      rfl

theorem cell22_920096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 1, 1, 1, 1, 6].length) (baseStart_920096 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_920096 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_920096 prefixEnd_920096 := by exact prefixLift 920096
  have htrace : WordTrace (prefixWord ++ tailWord_920096) baseStart_920096 baseEnd_920096 := by
    simpa [prefixWord, tailWord_920096, baseEnd_920096] using wordTrace_append hprefix tailTrace_920096
  have hstable : (prefixWord ++ tailWord_920096).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_920096).length < 2 ^ (prefixWord ++ tailWord_920096).sum := by decide
  have hdescent : baseEnd_920096 < baseStart_920096 := by decide
  rcases family_descends (prefixWord ++ tailWord_920096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_920100 : List Nat := [2, 3, 1, 5, 1, 1, 2, 3, 4]
def baseStart_920100 : Nat := 118140960795 + 920100 * 2 ^ 59
def prefixEnd_920100 : Nat := 4983230072969 + 3 ^ 40 * 920100 * 2
def baseEnd_920100 : Nat := 104989677822656741826343

theorem tailTrace_920100 : CollatzResearch.WordTrace tailWord_920100 prefixEnd_920100 104989677822656741826343 := by
  unfold tailWord_920100
  simp only [CollatzResearch.WordTrace]
  refine ⟨16779401983321157707254877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22372535977761543609673169 16779401983321157707254877)
  ·
    refine ⟨6292275743745434140220579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16779401983321157707254877 6292275743745434140220579)
    ·
      refine ⟨9438413615618151210330869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6292275743745434140220579 9438413615618151210330869)
      ·
        refine ⟨884851276464201675968519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 9438413615618151210330869 884851276464201675968519)
        ·
          refine ⟨1327276914696302513952779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 884851276464201675968519 1327276914696302513952779)
          ·
            refine ⟨1990915372044453770929169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1327276914696302513952779 1990915372044453770929169)
            ·
              refine ⟨1493186529033340328196877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1990915372044453770929169 1493186529033340328196877)
              ·
                refine ⟨559944948387502623073829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1493186529033340328196877 559944948387502623073829)
                ·
                  refine ⟨104989677822656741826343, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 559944948387502623073829 104989677822656741826343)
                  ·
                    rfl

theorem cell22_920100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 1, 2, 3, 4].length) (baseStart_920100 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_920100 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_920100 prefixEnd_920100 := by exact prefixLift 920100
  have htrace : WordTrace (prefixWord ++ tailWord_920100) baseStart_920100 baseEnd_920100 := by
    simpa [prefixWord, tailWord_920100, baseEnd_920100] using wordTrace_append hprefix tailTrace_920100
  have hstable : (prefixWord ++ tailWord_920100).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_920100).length < 2 ^ (prefixWord ++ tailWord_920100).sum := by decide
  have hdescent : baseEnd_920100 < baseStart_920100 := by decide
  rcases family_descends (prefixWord ++ tailWord_920100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_920132 : List Nat := [2, 3, 5, 1, 1, 2, 1, 1, 1, 5]
def baseStart_920132 : Nat := 118140960795 + 920132 * 2 ^ 59
def prefixEnd_920132 : Nat := 4983230072969 + 3 ^ 40 * 920132 * 2
def baseEnd_920132 : Nat := 314979987721932808678931

theorem tailTrace_920132 : CollatzResearch.WordTrace tailWord_920132 prefixEnd_920132 314979987721932808678931 := by
  unfold tailWord_920132
  simp only [CollatzResearch.WordTrace]
  refine ⟨16779985551263192439837325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22373314068350923253116433 16779985551263192439837325)
  ·
    refine ⟨6292494581723697164938997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16779985551263192439837325 6292494581723697164938997)
    ·
      refine ⟨589921367036596609213031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 6292494581723697164938997 589921367036596609213031)
      ·
        refine ⟨884882050554894913819547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 589921367036596609213031 884882050554894913819547)
        ·
          refine ⟨1327323075832342370729321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 884882050554894913819547 1327323075832342370729321)
          ·
            refine ⟨995492306874256778046991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1327323075832342370729321 995492306874256778046991)
            ·
              refine ⟨1493238460311385167070487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 995492306874256778046991 1493238460311385167070487)
              ·
                refine ⟨2239857690467077750605731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1493238460311385167070487 2239857690467077750605731)
                ·
                  refine ⟨3359786535700616625908597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2239857690467077750605731 3359786535700616625908597)
                  ·
                    refine ⟨314979987721932808678931, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3359786535700616625908597 314979987721932808678931)
                    ·
                      rfl

theorem cell22_920132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 2, 1, 1, 1, 5].length) (baseStart_920132 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_920132 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_920132 prefixEnd_920132 := by exact prefixLift 920132
  have htrace : WordTrace (prefixWord ++ tailWord_920132) baseStart_920132 baseEnd_920132 := by
    simpa [prefixWord, tailWord_920132, baseEnd_920132] using wordTrace_append hprefix tailTrace_920132
  have hstable : (prefixWord ++ tailWord_920132).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_920132).length < 2 ^ (prefixWord ++ tailWord_920132).sum := by decide
  have hdescent : baseEnd_920132 < baseStart_920132 := by decide
  rcases family_descends (prefixWord ++ tailWord_920132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_920139 : List Nat := [1, 1, 1, 1, 3, 1, 4, 5, 5]
def baseStart_920139 : Nat := 118140960795 + 920139 * 2 ^ 59
def prefixEnd_920139 : Nat := 4983230072969 + 3 ^ 40 * 920139 * 2
def baseEnd_920139 : Nat := 104994127988329041251303

theorem tailTrace_920139 : CollatzResearch.WordTrace tailWord_920139 prefixEnd_920139 104994127988329041251303 := by
  unfold tailWord_920139
  simp only [CollatzResearch.WordTrace]
  refine ⟨33560226413501025075179471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22373484275667350050119647 33560226413501025075179471)
  ·
    refine ⟨50340339620251537612769207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33560226413501025075179471 50340339620251537612769207)
    ·
      refine ⟨75510509430377306419153811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50340339620251537612769207 75510509430377306419153811)
      ·
        refine ⟨113265764145565959628730717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75510509430377306419153811 113265764145565959628730717)
        ·
          refine ⟨42474661554587234860774019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 113265764145565959628730717 42474661554587234860774019)
          ·
            refine ⟨63711992331880852291161029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42474661554587234860774019 63711992331880852291161029)
            ·
              refine ⟨11945998562227659804592693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 63711992331880852291161029 11945998562227659804592693)
              ·
                refine ⟨1119937365208843106680565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11945998562227659804592693 1119937365208843106680565)
                ·
                  refine ⟨104994127988329041251303, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1119937365208843106680565 104994127988329041251303)
                  ·
                    rfl

theorem cell22_920139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 4, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 4, 5, 5].length) (baseStart_920139 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_920139 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_920139 prefixEnd_920139 := by exact prefixLift 920139
  have htrace : WordTrace (prefixWord ++ tailWord_920139) baseStart_920139 baseEnd_920139 := by
    simpa [prefixWord, tailWord_920139, baseEnd_920139] using wordTrace_append hprefix tailTrace_920139
  have hstable : (prefixWord ++ tailWord_920139).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_920139).length < 2 ^ (prefixWord ++ tailWord_920139).sum := by decide
  have hdescent : baseEnd_920139 < baseStart_920139 := by decide
  rcases family_descends (prefixWord ++ tailWord_920139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_920169 : List Nat := [1, 2, 1, 1, 1, 4, 1, 2, 5, 4]
def baseStart_920169 : Nat := 118140960795 + 920169 * 2 ^ 59
def prefixEnd_920169 : Nat := 4983230072969 + 3 ^ 40 * 920169 * 2
def baseEnd_920169 : Nat := 314992653578077045503817

theorem tailTrace_920169 : CollatzResearch.WordTrace tailWord_920169 prefixEnd_920169 314992653578077045503817 := by
  unfold tailWord_920169
  simp only [CollatzResearch.WordTrace]
  refine ⟨33561320603392340198771561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22374213735594893465847707 33561320603392340198771561)
  ·
    refine ⟨25170990452544255149078671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33561320603392340198771561 25170990452544255149078671)
    ·
      refine ⟨37756485678816382723618007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25170990452544255149078671 37756485678816382723618007)
      ·
        refine ⟨56634728518224574085427011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37756485678816382723618007 56634728518224574085427011)
        ·
          refine ⟨84952092777336861128140517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56634728518224574085427011 84952092777336861128140517)
          ·
            refine ⟨15928517395750661461526347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 84952092777336861128140517 15928517395750661461526347)
            ·
              refine ⟨23892776093625992192289521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15928517395750661461526347 23892776093625992192289521)
              ·
                refine ⟨17919582070219494144217141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23892776093625992192289521 17919582070219494144217141)
                ·
                  refine ⟨1679960819083077576020357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 17919582070219494144217141 1679960819083077576020357)
                  ·
                    refine ⟨314992653578077045503817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1679960819083077576020357 314992653578077045503817)
                    ·
                      rfl

theorem cell22_920169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 2, 5, 4].length) (baseStart_920169 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_920169 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_920169 prefixEnd_920169 := by exact prefixLift 920169
  have htrace : WordTrace (prefixWord ++ tailWord_920169) baseStart_920169 baseEnd_920169 := by
    simpa [prefixWord, tailWord_920169, baseEnd_920169] using wordTrace_append hprefix tailTrace_920169
  have hstable : (prefixWord ++ tailWord_920169).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_920169).length < 2 ^ (prefixWord ++ tailWord_920169).sum := by decide
  have hdescent : baseEnd_920169 < baseStart_920169 := by decide
  rcases family_descends (prefixWord ++ tailWord_920169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_920216 : List Nat := [2, 1, 2, 4, 1, 1, 3, 2, 1, 5]
def baseStart_920216 : Nat := 118140960795 + 920216 * 2 ^ 59
def prefixEnd_920216 : Nat := 4983230072969 + 3 ^ 40 * 920216 * 2
def baseEnd_920216 : Nat := 315008742638584589578673

theorem tailTrace_920216 : CollatzResearch.WordTrace tailWord_920216 prefixEnd_920216 315008742638584589578673 := by
  unfold tailWord_920216
  simp only [CollatzResearch.WordTrace]
  refine ⟨16781517417111033612866251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22375356556148044817155001 16781517417111033612866251)
  ·
    refine ⟨25172276125666550419299377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16781517417111033612866251 25172276125666550419299377)
    ·
      refine ⟨18879207094249912814474533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25172276125666550419299377 18879207094249912814474533)
      ·
        refine ⟨3539851330171858652713975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18879207094249912814474533 3539851330171858652713975)
        ·
          refine ⟨5309776995257787979070963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3539851330171858652713975 5309776995257787979070963)
          ·
            refine ⟨7964665492886681968606445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5309776995257787979070963 7964665492886681968606445)
            ·
              refine ⟨2986749559832505738227417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7964665492886681968606445 2986749559832505738227417)
              ·
                refine ⟨2240062169874379303670563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2986749559832505738227417 2240062169874379303670563)
                ·
                  refine ⟨3360093254811568955505845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2240062169874379303670563 3360093254811568955505845)
                  ·
                    refine ⟨315008742638584589578673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3360093254811568955505845 315008742638584589578673)
                    ·
                      rfl

theorem cell22_920216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 3, 2, 1, 5].length) (baseStart_920216 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_920216 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_920216 prefixEnd_920216 := by exact prefixLift 920216
  have htrace : WordTrace (prefixWord ++ tailWord_920216) baseStart_920216 baseEnd_920216 := by
    simpa [prefixWord, tailWord_920216, baseEnd_920216] using wordTrace_append hprefix tailTrace_920216
  have hstable : (prefixWord ++ tailWord_920216).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_920216).length < 2 ^ (prefixWord ++ tailWord_920216).sum := by decide
  have hdescent : baseEnd_920216 < baseStart_920216 := by decide
  rcases family_descends (prefixWord ++ tailWord_920216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_920220 : List Nat := [2, 2, 3, 2, 2, 2, 3, 1, 1, 4]
def baseStart_920220 : Nat := 118140960795 + 920220 * 2 ^ 59
def prefixEnd_920220 : Nat := 4983230072969 + 3 ^ 40 * 920220 * 2
def baseEnd_920220 : Nat := 315010111920329912478661

theorem tailTrace_920220 : CollatzResearch.WordTrace tailWord_920220 prefixEnd_920220 315010111920329912478661 := by
  unfold tailWord_920220
  simp only [CollatzResearch.WordTrace]
  refine ⟨16781590363103787954439057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22375453817471717272585409 16781590363103787954439057)
  ·
    refine ⟨12586192772327840965829293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16781590363103787954439057 12586192772327840965829293)
    ·
      refine ⟨4719822289622940362185985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12586192772327840965829293 4719822289622940362185985)
      ·
        refine ⟨3539866717217205271639489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4719822289622940362185985 3539866717217205271639489)
        ·
          refine ⟨2654900037912903953729617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3539866717217205271639489 2654900037912903953729617)
          ·
            refine ⟨1991175028434677965297213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2654900037912903953729617 1991175028434677965297213)
            ·
              refine ⟨746690635663004236986455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1991175028434677965297213 746690635663004236986455)
              ·
                refine ⟨1120035953494506355479683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 746690635663004236986455 1120035953494506355479683)
                ·
                  refine ⟨1680053930241759533219525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1120035953494506355479683 1680053930241759533219525)
                  ·
                    refine ⟨315010111920329912478661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1680053930241759533219525 315010111920329912478661)
                    ·
                      rfl

theorem cell22_920220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 2, 3, 1, 1, 4].length) (baseStart_920220 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_920220 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_920220 prefixEnd_920220 := by exact prefixLift 920220
  have htrace : WordTrace (prefixWord ++ tailWord_920220) baseStart_920220 baseEnd_920220 := by
    simpa [prefixWord, tailWord_920220, baseEnd_920220] using wordTrace_append hprefix tailTrace_920220
  have hstable : (prefixWord ++ tailWord_920220).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_920220).length < 2 ^ (prefixWord ++ tailWord_920220).sum := by decide
  have hdescent : baseEnd_920220 < baseStart_920220 := by decide
  rcases family_descends (prefixWord ++ tailWord_920220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_920383 : List Nat := [1, 1, 2, 2, 5, 1, 1, 3, 2, 4]
def baseStart_920383 : Nat := 118140960795 + 920383 * 2 ^ 59
def prefixEnd_920383 : Nat := 4983230072969 + 3 ^ 40 * 920383 * 2
def baseEnd_920383 : Nat := 315065910151451820653161

theorem tailTrace_920383 : CollatzResearch.WordTrace tailWord_920383 prefixEnd_920383 315065910151451820653161 := by
  unfold tailWord_920383
  simp only [CollatzResearch.WordTrace]
  refine ⟨33569125824617054747061803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22379417216411369831374535 33569125824617054747061803)
  ·
    refine ⟨50353688736925582120592705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33569125824617054747061803 50353688736925582120592705)
    ·
      refine ⟨37765266552694186590444529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50353688736925582120592705 37765266552694186590444529)
      ·
        refine ⟨28323949914520639942833397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37765266552694186590444529 28323949914520639942833397)
        ·
          refine ⟨2655370304486309994640631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 28323949914520639942833397 2655370304486309994640631)
          ·
            refine ⟨3983055456729464991960947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2655370304486309994640631 3983055456729464991960947)
            ·
              refine ⟨5974583185094197487941421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3983055456729464991960947 5974583185094197487941421)
              ·
                refine ⟨2240468694410324057978033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5974583185094197487941421 2240468694410324057978033)
                ·
                  refine ⟨1680351520807743043483525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2240468694410324057978033 1680351520807743043483525)
                  ·
                    refine ⟨315065910151451820653161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1680351520807743043483525 315065910151451820653161)
                    ·
                      rfl

theorem cell22_920383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 1, 3, 2, 4].length) (baseStart_920383 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_920383 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_920383 prefixEnd_920383 := by exact prefixLift 920383
  have htrace : WordTrace (prefixWord ++ tailWord_920383) baseStart_920383 baseEnd_920383 := by
    simpa [prefixWord, tailWord_920383, baseEnd_920383] using wordTrace_append hprefix tailTrace_920383
  have hstable : (prefixWord ++ tailWord_920383).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_920383).length < 2 ^ (prefixWord ++ tailWord_920383).sum := by decide
  have hdescent : baseEnd_920383 < baseStart_920383 := by decide
  rcases family_descends (prefixWord ++ tailWord_920383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_920404 : List Nat := [2, 4, 1, 1, 4, 2, 2, 2, 4]
def baseStart_920404 : Nat := 118140960795 + 920404 * 2 ^ 59
def prefixEnd_920404 : Nat := 4983230072969 + 3 ^ 40 * 920404 * 2
def baseEnd_920404 : Nat := 105024366293538255292699

theorem tailTrace_920404 : CollatzResearch.WordTrace tailWord_920404 prefixEnd_920404 105024366293538255292699 := by
  unfold tailWord_920404
  simp only [CollatzResearch.WordTrace]
  refine ⟨16784945878770487666788133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22379927838360650222384177 16784945878770487666788133)
  ·
    refine ⟨3147177352269466437522775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16784945878770487666788133 3147177352269466437522775)
    ·
      refine ⟨4720766028404199656284163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3147177352269466437522775 4720766028404199656284163)
      ·
        refine ⟨7081149042606299484426245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4720766028404199656284163 7081149042606299484426245)
        ·
          refine ⟨1327715445488681153329921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7081149042606299484426245 1327715445488681153329921)
          ·
            refine ⟨995786584116510864997441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1327715445488681153329921 995786584116510864997441)
            ·
              refine ⟨746839938087383148748081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 995786584116510864997441 746839938087383148748081)
              ·
                refine ⟨560129953565537361561061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 746839938087383148748081 560129953565537361561061)
                ·
                  refine ⟨105024366293538255292699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 560129953565537361561061 105024366293538255292699)
                  ·
                    rfl

theorem cell22_920404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 2, 2, 2, 4].length) (baseStart_920404 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_920404 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_920404 prefixEnd_920404 := by exact prefixLift 920404
  have htrace : WordTrace (prefixWord ++ tailWord_920404) baseStart_920404 baseEnd_920404 := by
    simpa [prefixWord, tailWord_920404, baseEnd_920404] using wordTrace_append hprefix tailTrace_920404
  have hstable : (prefixWord ++ tailWord_920404).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_920404).length < 2 ^ (prefixWord ++ tailWord_920404).sum := by decide
  have hdescent : baseEnd_920404 < baseStart_920404 := by decide
  rcases family_descends (prefixWord ++ tailWord_920404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_920503 : List Nat := [1, 1, 3, 1, 3, 1, 2, 4, 1, 5]
def baseStart_920503 : Nat := 118140960795 + 920503 * 2 ^ 59
def prefixEnd_920503 : Nat := 4983230072969 + 3 ^ 40 * 920503 * 2
def baseEnd_920503 : Nat := 315106988603811507652793

theorem tailTrace_920503 : CollatzResearch.WordTrace tailWord_920503 prefixEnd_920503 315106988603811507652793 := by
  unfold tailWord_920503
  simp only [CollatzResearch.WordTrace]
  refine ⟨33573502584182315241430163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22382335056121543494286775 33573502584182315241430163)
  ·
    refine ⟨50360253876273472862145245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33573502584182315241430163 50360253876273472862145245)
    ·
      refine ⟨18885095203602552323304467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50360253876273472862145245 18885095203602552323304467)
      ·
        refine ⟨28327642805403828484956701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18885095203602552323304467 28327642805403828484956701)
        ·
          refine ⟨10622866052026435681858763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28327642805403828484956701 10622866052026435681858763)
          ·
            refine ⟨15934299078039653522788145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10622866052026435681858763 15934299078039653522788145)
            ·
              refine ⟨11950724308529740142091109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15934299078039653522788145 11950724308529740142091109)
              ·
                refine ⟨2240760807849326276642083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11950724308529740142091109 2240760807849326276642083)
                ·
                  refine ⟨3361141211773989414963125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2240760807849326276642083 3361141211773989414963125)
                  ·
                    refine ⟨315106988603811507652793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3361141211773989414963125 315106988603811507652793)
                    ·
                      rfl

theorem cell22_920503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 2, 4, 1, 5].length) (baseStart_920503 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_920503 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_920503 prefixEnd_920503 := by exact prefixLift 920503
  have htrace : WordTrace (prefixWord ++ tailWord_920503) baseStart_920503 baseEnd_920503 := by
    simpa [prefixWord, tailWord_920503, baseEnd_920503] using wordTrace_append hprefix tailTrace_920503
  have hstable : (prefixWord ++ tailWord_920503).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_920503).length < 2 ^ (prefixWord ++ tailWord_920503).sum := by decide
  have hdescent : baseEnd_920503 < baseStart_920503 := by decide
  rcases family_descends (prefixWord ++ tailWord_920503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_920537 : List Nat := [1, 2, 1, 2, 5, 2, 1, 3, 2, 3]
def baseStart_920537 : Nat := 118140960795 + 920537 * 2 ^ 59
def prefixEnd_920537 : Nat := 4983230072969 + 3 ^ 40 * 920537 * 2
def baseEnd_920537 : Nat := 315118627498646752302689

theorem tailTrace_920537 : CollatzResearch.WordTrace tailWord_920537 prefixEnd_920537 315118627498646752302689 := by
  unfold tailWord_920537
  simp only [CollatzResearch.WordTrace]
  refine ⟨33574742666059139048167865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22383161777372759365445243 33574742666059139048167865)
  ·
    refine ⟨25181056999544354286125899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33574742666059139048167865 25181056999544354286125899)
    ·
      refine ⟨37771585499316531429188849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25181056999544354286125899 37771585499316531429188849)
      ·
        refine ⟨28328689124487398571891637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37771585499316531429188849 28328689124487398571891637)
        ·
          refine ⟨2655814605420693616114841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 28328689124487398571891637 2655814605420693616114841)
          ·
            refine ⟨1991860954065520212086131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2655814605420693616114841 1991860954065520212086131)
            ·
              refine ⟨2987791431098280318129197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1991860954065520212086131 2987791431098280318129197)
              ·
                refine ⟨1120421786661855119298449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2987791431098280318129197 1120421786661855119298449)
                ·
                  refine ⟨840316339996391339473837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1120421786661855119298449 840316339996391339473837)
                  ·
                    refine ⟨315118627498646752302689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 840316339996391339473837 315118627498646752302689)
                    ·
                      rfl

theorem cell22_920537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 2, 1, 3, 2, 3].length) (baseStart_920537 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_920537 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_920537 prefixEnd_920537 := by exact prefixLift 920537
  have htrace : WordTrace (prefixWord ++ tailWord_920537) baseStart_920537 baseEnd_920537 := by
    simpa [prefixWord, tailWord_920537, baseEnd_920537] using wordTrace_append hprefix tailTrace_920537
  have hstable : (prefixWord ++ tailWord_920537).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_920537).length < 2 ^ (prefixWord ++ tailWord_920537).sum := by decide
  have hdescent : baseEnd_920537 < baseStart_920537 := by decide
  rcases family_descends (prefixWord ++ tailWord_920537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_920640 : List Nat := [2, 1, 1, 2, 2, 3, 4, 1, 6]
def baseStart_920640 : Nat := 118140960795 + 920640 * 2 ^ 59
def prefixEnd_920640 : Nat := 4983230072969 + 3 ^ 40 * 920640 * 2
def baseEnd_920640 : Nat := 105051295501196272325791

theorem tailTrace_920640 : CollatzResearch.WordTrace tailWord_920640 prefixEnd_920640 105051295501196272325791 := by
  unfold tailWord_920640
  simp only [CollatzResearch.WordTrace]
  refine ⟨16789249692342993819583687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22385666256457325092778249 16789249692342993819583687)
  ·
    refine ⟨25183874538514490729375531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16789249692342993819583687 25183874538514490729375531)
    ·
      refine ⟨37775811807771736094063297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25183874538514490729375531 37775811807771736094063297)
      ·
        refine ⟨28331858855828802070547473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37775811807771736094063297 28331858855828802070547473)
        ·
          refine ⟨21248894141871601552910605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28331858855828802070547473 21248894141871601552910605)
          ·
            refine ⟨7968335303201850582341477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21248894141871601552910605 7968335303201850582341477)
            ·
              refine ⟨1494062869350346984189027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7968335303201850582341477 1494062869350346984189027)
              ·
                refine ⟨2241094304025520476283541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1494062869350346984189027 2241094304025520476283541)
                ·
                  refine ⟨105051295501196272325791, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2241094304025520476283541 105051295501196272325791)
                  ·
                    rfl

theorem cell22_920640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 4, 1, 6].length) (baseStart_920640 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_920640 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_920640 prefixEnd_920640 := by exact prefixLift 920640
  have htrace : WordTrace (prefixWord ++ tailWord_920640) baseStart_920640 baseEnd_920640 := by
    simpa [prefixWord, tailWord_920640, baseEnd_920640] using wordTrace_append hprefix tailTrace_920640
  have hstable : (prefixWord ++ tailWord_920640).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_920640).length < 2 ^ (prefixWord ++ tailWord_920640).sum := by decide
  have hdescent : baseEnd_920640 < baseStart_920640 := by decide
  rcases family_descends (prefixWord ++ tailWord_920640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_920646 : List Nat := [6, 1, 1, 1, 1, 3, 3, 1, 5]
def baseStart_920646 : Nat := 118140960795 + 920646 * 2 ^ 59
def prefixEnd_920646 : Nat := 4983230072969 + 3 ^ 40 * 920646 * 2
def baseEnd_920646 : Nat := 105051980142068933775785

theorem tailTrace_920646 : CollatzResearch.WordTrace tailWord_920646 prefixEnd_920646 105051980142068933775785 := by
  unfold tailWord_920646
  simp only [CollatzResearch.WordTrace]
  refine ⟨1049334944458257833246431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 22385812148442833775923861 1049334944458257833246431)
  ·
    refine ⟨1574002416687386749869647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1049334944458257833246431 1574002416687386749869647)
    ·
      refine ⟨2361003625031080124804471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1574002416687386749869647 2361003625031080124804471)
      ·
        refine ⟨3541505437546620187206707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2361003625031080124804471 3541505437546620187206707)
        ·
          refine ⟨5312258156319930280810061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3541505437546620187206707 5312258156319930280810061)
          ·
            refine ⟨1992096808619973855303773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5312258156319930280810061 1992096808619973855303773)
            ·
              refine ⟨747036303232490195738915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1992096808619973855303773 747036303232490195738915)
              ·
                refine ⟨1120554454848735293608373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 747036303232490195738915 1120554454848735293608373)
                ·
                  refine ⟨105051980142068933775785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1120554454848735293608373 105051980142068933775785)
                  ·
                    rfl

theorem cell22_920646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 3, 3, 1, 5].length) (baseStart_920646 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_920646 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_920646 prefixEnd_920646 := by exact prefixLift 920646
  have htrace : WordTrace (prefixWord ++ tailWord_920646) baseStart_920646 baseEnd_920646 := by
    simpa [prefixWord, tailWord_920646, baseEnd_920646] using wordTrace_append hprefix tailTrace_920646
  have hstable : (prefixWord ++ tailWord_920646).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_920646).length < 2 ^ (prefixWord ++ tailWord_920646).sum := by decide
  have hdescent : baseEnd_920646 < baseStart_920646 := by decide
  rcases family_descends (prefixWord ++ tailWord_920646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_920655 : List Nat := [1, 1, 2, 1, 1, 2, 2, 1, 8, 3]
def baseStart_920655 : Nat := 118140960795 + 920655 * 2 ^ 59
def prefixEnd_920655 : Nat := 4983230072969 + 3 ^ 40 * 920655 * 2
def baseEnd_920655 : Nat := 315159021310133777852327

theorem tailTrace_920655 : CollatzResearch.WordTrace tailWord_920655 prefixEnd_920655 315159021310133777852327 := by
  unfold tailWord_920655
  simp only [CollatzResearch.WordTrace]
  refine ⟨33579046479631645200963419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22386030986421096800642279 33579046479631645200963419)
  ·
    refine ⟨50368569719447467801445129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33579046479631645200963419 50368569719447467801445129)
    ·
      refine ⟨37776427289585600851083847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50368569719447467801445129 37776427289585600851083847)
      ·
        refine ⟨56664640934378401276625771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37776427289585600851083847 56664640934378401276625771)
        ·
          refine ⟨84996961401567601914938657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56664640934378401276625771 84996961401567601914938657)
          ·
            refine ⟨63747721051175701436203993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84996961401567601914938657 63747721051175701436203993)
            ·
              refine ⟨47810790788381776077152995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63747721051175701436203993 47810790788381776077152995)
              ·
                refine ⟨71716186182572664115729493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47810790788381776077152995 71716186182572664115729493)
                ·
                  refine ⟨840424056827023407606205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 71716186182572664115729493 840424056827023407606205)
                  ·
                    refine ⟨315159021310133777852327, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 840424056827023407606205 315159021310133777852327)
                    ·
                      rfl

theorem cell22_920655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 1, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 1, 8, 3].length) (baseStart_920655 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_920655 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_920655 prefixEnd_920655 := by exact prefixLift 920655
  have htrace : WordTrace (prefixWord ++ tailWord_920655) baseStart_920655 baseEnd_920655 := by
    simpa [prefixWord, tailWord_920655, baseEnd_920655] using wordTrace_append hprefix tailTrace_920655
  have hstable : (prefixWord ++ tailWord_920655).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_920655).length < 2 ^ (prefixWord ++ tailWord_920655).sum := by decide
  have hdescent : baseEnd_920655 < baseStart_920655 := by decide
  rcases family_descends (prefixWord ++ tailWord_920655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_920685 : List Nat := [1, 5, 1, 1, 2, 2, 10]
def baseStart_920685 : Nat := 118140960795 + 920685 * 2 ^ 59
def prefixEnd_920685 : Nat := 4983230072969 + 3 ^ 40 * 920685 * 2
def baseEnd_920685 : Nat := 11672936700860137022305

theorem tailTrace_920685 : CollatzResearch.WordTrace tailWord_920685 prefixEnd_920685 11672936700860137022305 := by
  unfold tailWord_920685
  simp only [CollatzResearch.WordTrace]
  refine ⟨33580140669522960324555509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22386760446348640216370339 33580140669522960324555509)
  ·
    refine ⟨3148138187767777530427079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 33580140669522960324555509 3148138187767777530427079)
    ·
      refine ⟨4722207281651666295640619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3148138187767777530427079 4722207281651666295640619)
      ·
        refine ⟨7083310922477499443460929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4722207281651666295640619 7083310922477499443460929)
        ·
          refine ⟨5312483191858124582595697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7083310922477499443460929 5312483191858124582595697)
          ·
            refine ⟨3984362393893593436946773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5312483191858124582595697 3984362393893593436946773)
            ·
              refine ⟨11672936700860137022305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 3984362393893593436946773 11672936700860137022305)
              ·
                rfl

theorem cell22_920685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 10].length) (baseStart_920685 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_920685 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_920685 prefixEnd_920685 := by exact prefixLift 920685
  have htrace : WordTrace (prefixWord ++ tailWord_920685) baseStart_920685 baseEnd_920685 := by
    simpa [prefixWord, tailWord_920685, baseEnd_920685] using wordTrace_append hprefix tailTrace_920685
  have hstable : (prefixWord ++ tailWord_920685).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_920685).length < 2 ^ (prefixWord ++ tailWord_920685).sum := by decide
  have hdescent : baseEnd_920685 < baseStart_920685 := by decide
  rcases family_descends (prefixWord ++ tailWord_920685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_920751 : List Nat := [1, 1, 2, 1, 2, 3, 6, 2, 1, 3]
def baseStart_920751 : Nat := 118140960795 + 920751 * 2 ^ 59
def prefixEnd_920751 : Nat := 4983230072969 + 3 ^ 40 * 920751 * 2
def baseEnd_920751 : Nat := 315191884072021527452033

theorem tailTrace_920751 : CollatzResearch.WordTrace tailWord_920751 prefixEnd_920751 315191884072021527452033 := by
  unfold tailWord_920751
  simp only [CollatzResearch.WordTrace]
  refine ⟨33582547887283853596458107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22388365258189235730972071 33582547887283853596458107)
  ·
    refine ⟨50373821830925780394687161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33582547887283853596458107 50373821830925780394687161)
    ·
      refine ⟨37780366373194335296015371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50373821830925780394687161 37780366373194335296015371)
      ·
        refine ⟨56670549559791502944023057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37780366373194335296015371 56670549559791502944023057)
        ·
          refine ⟨42502912169843627208017293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56670549559791502944023057 42502912169843627208017293)
          ·
            refine ⟨15938592063691360203006485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42502912169843627208017293 15938592063691360203006485)
            ·
              refine ⟨747121502985532509515929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 15938592063691360203006485 747121502985532509515929)
              ·
                refine ⟨560341127239149382136947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 747121502985532509515929 560341127239149382136947)
                ·
                  refine ⟨840511690858724073205421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 560341127239149382136947 840511690858724073205421)
                  ·
                    refine ⟨315191884072021527452033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 840511690858724073205421 315191884072021527452033)
                    ·
                      rfl

theorem cell22_920751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 6, 2, 1, 3].length) (baseStart_920751 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_920751 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_920751 prefixEnd_920751 := by exact prefixLift 920751
  have htrace : WordTrace (prefixWord ++ tailWord_920751) baseStart_920751 baseEnd_920751 := by
    simpa [prefixWord, tailWord_920751, baseEnd_920751] using wordTrace_append hprefix tailTrace_920751
  have hstable : (prefixWord ++ tailWord_920751).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_920751).length < 2 ^ (prefixWord ++ tailWord_920751).sum := by decide
  have hdescent : baseEnd_920751 < baseStart_920751 := by decide
  rcases family_descends (prefixWord ++ tailWord_920751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_920927 : List Nat := [1, 1, 2, 3, 1, 2, 1, 5, 6]
def baseStart_920927 : Nat := 118140960795 + 920927 * 2 ^ 59
def prefixEnd_920927 : Nat := 4983230072969 + 3 ^ 40 * 920927 * 2
def baseEnd_920927 : Nat := 105084044156271911683831

theorem tailTrace_920927 : CollatzResearch.WordTrace tailWord_920927 prefixEnd_920927 105084044156271911683831 := by
  unfold tailWord_920927
  simp only [CollatzResearch.WordTrace]
  refine ⟨33588967134646235654865035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22392644756430823769910023 33588967134646235654865035)
  ·
    refine ⟨50383450701969353482297553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33588967134646235654865035 50383450701969353482297553)
    ·
      refine ⟨37787588026477015111723165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50383450701969353482297553 37787588026477015111723165)
      ·
        refine ⟨14170345509928880666896187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37787588026477015111723165 14170345509928880666896187)
        ·
          refine ⟨21255518264893321000344281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14170345509928880666896187 21255518264893321000344281)
          ·
            refine ⟨15941638698669990750258211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21255518264893321000344281 15941638698669990750258211)
            ·
              refine ⟨23912458048004986125387317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15941638698669990750258211 23912458048004986125387317)
              ·
                refine ⟨2241792942000467449255061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 23912458048004986125387317 2241792942000467449255061)
                ·
                  refine ⟨105084044156271911683831, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2241792942000467449255061 105084044156271911683831)
                  ·
                    rfl

theorem cell22_920927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 5, 6].length) (baseStart_920927 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_920927 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_920927 prefixEnd_920927 := by exact prefixLift 920927
  have htrace : WordTrace (prefixWord ++ tailWord_920927) baseStart_920927 baseEnd_920927 := by
    simpa [prefixWord, tailWord_920927, baseEnd_920927] using wordTrace_append hprefix tailTrace_920927
  have hstable : (prefixWord ++ tailWord_920927).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_920927).length < 2 ^ (prefixWord ++ tailWord_920927).sum := by decide
  have hdescent : baseEnd_920927 < baseStart_920927 := by decide
  rcases family_descends (prefixWord ++ tailWord_920927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_920963 : List Nat := [1, 1, 1, 3, 5, 3, 2, 1, 1, 4]
def baseStart_920963 : Nat := 118140960795 + 920963 * 2 ^ 59
def prefixEnd_920963 : Nat := 4983230072969 + 3 ^ 40 * 920963 * 2
def baseEnd_920963 : Nat := 315264456004523641151383

theorem tailTrace_920963 : CollatzResearch.WordTrace tailWord_920963 prefixEnd_920963 315264456004523641151383 := by
  unfold tailWord_920963
  simp only [CollatzResearch.WordTrace]
  refine ⟨33590280162515813803175543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22393520108343875868783695 33590280162515813803175543)
  ·
    refine ⟨50385420243773720704763315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33590280162515813803175543 50385420243773720704763315)
    ·
      refine ⟨75578130365660581057144973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50385420243773720704763315 75578130365660581057144973)
      ·
        refine ⟨28341798887122717896429365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 75578130365660581057144973 28341798887122717896429365)
        ·
          refine ⟨2657043645667754802790253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 28341798887122717896429365 2657043645667754802790253)
          ·
            refine ⟨996391367125408051046345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2657043645667754802790253 996391367125408051046345)
            ·
              refine ⟨747293525344056038284759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 996391367125408051046345 747293525344056038284759)
              ·
                refine ⟨1120940288016084057427139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 747293525344056038284759 1120940288016084057427139)
                ·
                  refine ⟨1681410432024126086140709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1120940288016084057427139 1681410432024126086140709)
                  ·
                    refine ⟨315264456004523641151383, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1681410432024126086140709 315264456004523641151383)
                    ·
                      rfl

theorem cell22_920963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 3, 2, 1, 1, 4].length) (baseStart_920963 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_920963 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_920963 prefixEnd_920963 := by exact prefixLift 920963
  have htrace : WordTrace (prefixWord ++ tailWord_920963) baseStart_920963 baseEnd_920963 := by
    simpa [prefixWord, tailWord_920963, baseEnd_920963] using wordTrace_append hprefix tailTrace_920963
  have hstable : (prefixWord ++ tailWord_920963).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_920963).length < 2 ^ (prefixWord ++ tailWord_920963).sum := by decide
  have hdescent : baseEnd_920963 < baseStart_920963 := by decide
  rcases family_descends (prefixWord ++ tailWord_920963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_920972 : List Nat := [2, 2, 1, 2, 1, 3, 11]
def baseStart_920972 : Nat := 118140960795 + 920972 * 2 ^ 59
def prefixEnd_920972 : Nat := 4983230072969 + 3 ^ 40 * 920972 * 2
def baseEnd_920972 : Nat := 11676575440312985839865

theorem tailTrace_920972 : CollatzResearch.WordTrace tailWord_920972 prefixEnd_920972 11676575440312985839865 := by
  unfold tailWord_920972
  simp only [CollatzResearch.WordTrace]
  refine ⟨16795304209741604170126585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22393738946322138893502113 16795304209741604170126585)
  ·
    refine ⟨12596478157306203127594939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16795304209741604170126585 12596478157306203127594939)
    ·
      refine ⟨18894717235959304691392409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12596478157306203127594939 18894717235959304691392409)
      ·
        refine ⟨14171037926969478518544307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18894717235959304691392409 14171037926969478518544307)
        ·
          refine ⟨21256556890454217777816461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14171037926969478518544307 21256556890454217777816461)
          ·
            refine ⟨7971208833920331666681173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21256556890454217777816461 7971208833920331666681173)
            ·
              refine ⟨11676575440312985839865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 7971208833920331666681173 11676575440312985839865)
              ·
                rfl

theorem cell22_920972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 11].length) (baseStart_920972 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_920972 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_920972 prefixEnd_920972 := by exact prefixLift 920972
  have htrace : WordTrace (prefixWord ++ tailWord_920972) baseStart_920972 baseEnd_920972 := by
    simpa [prefixWord, tailWord_920972, baseEnd_920972] using wordTrace_append hprefix tailTrace_920972
  have hstable : (prefixWord ++ tailWord_920972).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_920972).length < 2 ^ (prefixWord ++ tailWord_920972).sum := by decide
  have hdescent : baseEnd_920972 < baseStart_920972 := by decide
  rcases family_descends (prefixWord ++ tailWord_920972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_920978 : List Nat := [3, 2, 3, 3, 1, 1, 2, 1, 6]
def baseStart_920978 : Nat := 118140960795 + 920978 * 2 ^ 59
def prefixEnd_920978 : Nat := 4983230072969 + 3 ^ 40 * 920978 * 2
def baseEnd_920978 : Nat := 105089863603689534008779

theorem tailTrace_920978 : CollatzResearch.WordTrace tailWord_920978 prefixEnd_920978 105089863603689534008779 := by
  unfold tailWord_920978
  simp only [CollatzResearch.WordTrace]
  refine ⟨8397706814365367841242897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22393884838307647576647725 8397706814365367841242897)
  ·
    refine ⟨6298280110774025880932173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8397706814365367841242897 6298280110774025880932173)
    ·
      refine ⟨2361855041540259705349565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6298280110774025880932173 2361855041540259705349565)
      ·
        refine ⟨885695640577597389506087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2361855041540259705349565 885695640577597389506087)
        ·
          refine ⟨1328543460866396084259131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 885695640577597389506087 1328543460866396084259131)
          ·
            refine ⟨1992815191299594126388697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1328543460866396084259131 1992815191299594126388697)
            ·
              refine ⟨1494611393474695594791523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1992815191299594126388697 1494611393474695594791523)
              ·
                refine ⟨2241917090212043392187285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1494611393474695594791523 2241917090212043392187285)
                ·
                  refine ⟨105089863603689534008779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2241917090212043392187285 105089863603689534008779)
                  ·
                    rfl

theorem cell22_920978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 1, 2, 1, 6].length) (baseStart_920978 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_920978 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_920978 prefixEnd_920978 := by exact prefixLift 920978
  have htrace : WordTrace (prefixWord ++ tailWord_920978) baseStart_920978 baseEnd_920978 := by
    simpa [prefixWord, tailWord_920978, baseEnd_920978] using wordTrace_append hprefix tailTrace_920978
  have hstable : (prefixWord ++ tailWord_920978).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_920978).length < 2 ^ (prefixWord ++ tailWord_920978).sum := by decide
  have hdescent : baseEnd_920978 < baseStart_920978 := by decide
  rcases family_descends (prefixWord ++ tailWord_920978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_921034 : List Nat := [3, 1, 2, 1, 2, 3, 2, 1, 7]
def baseStart_921034 : Nat := 118140960795 + 921034 * 2 ^ 59
def prefixEnd_921034 : Nat := 4983230072969 + 3 ^ 40 * 921034 * 2
def baseEnd_921034 : Nat := 105096253585167707542055

theorem tailTrace_921034 : CollatzResearch.WordTrace tailWord_921034 prefixEnd_921034 105096253585167707542055 := by
  unfold tailWord_921034
  simp only [CollatzResearch.WordTrace]
  refine ⟨8398217436314648232252539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22395246496839061952673437 8398217436314648232252539)
  ·
    refine ⟨12597326154471972348378809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8398217436314648232252539 12597326154471972348378809)
    ·
      refine ⟨9447994615853979261284107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12597326154471972348378809 9447994615853979261284107)
      ·
        refine ⟨14171991923780968891926161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9447994615853979261284107 14171991923780968891926161)
        ·
          refine ⟨10628993942835726668944621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14171991923780968891926161 10628993942835726668944621)
          ·
            refine ⟨3985872728563397500854233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10628993942835726668944621 3985872728563397500854233)
            ·
              refine ⟨2989404546422548125640675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3985872728563397500854233 2989404546422548125640675)
              ·
                refine ⟨4484106819633822188461013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2989404546422548125640675 4484106819633822188461013)
                ·
                  refine ⟨105096253585167707542055, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4484106819633822188461013 105096253585167707542055)
                  ·
                    rfl

theorem cell22_921034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 2, 1, 7].length) (baseStart_921034 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_921034 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_921034 prefixEnd_921034 := by exact prefixLift 921034
  have htrace : WordTrace (prefixWord ++ tailWord_921034) baseStart_921034 baseEnd_921034 := by
    simpa [prefixWord, tailWord_921034, baseEnd_921034] using wordTrace_append hprefix tailTrace_921034
  have hstable : (prefixWord ++ tailWord_921034).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_921034).length < 2 ^ (prefixWord ++ tailWord_921034).sum := by decide
  have hdescent : baseEnd_921034 < baseStart_921034 := by decide
  rcases family_descends (prefixWord ++ tailWord_921034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_921038 : List Nat := [4, 1, 1, 1, 2, 1, 2, 6, 1, 3]
def baseStart_921038 : Nat := 118140960795 + 921038 * 2 ^ 59
def prefixEnd_921038 : Nat := 4983230072969 + 3 ^ 40 * 921038 * 2
def baseEnd_921038 : Nat := 315290130037248445526153

theorem tailTrace_921038 : CollatzResearch.WordTrace tailWord_921038 prefixEnd_921038 315290130037248445526153 := by
  unfold tailWord_921038
  simp only [CollatzResearch.WordTrace]
  refine ⟨4199126954655512701519471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22395343758162734408103845 4199126954655512701519471)
  ·
    refine ⟨6298690431983269052279207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4199126954655512701519471 6298690431983269052279207)
    ·
      refine ⟨9448035647974903578418811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6298690431983269052279207 9448035647974903578418811)
      ·
        refine ⟨14172053471962355367628217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9448035647974903578418811 14172053471962355367628217)
        ·
          refine ⟨10629040103971766525721163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14172053471962355367628217 10629040103971766525721163)
          ·
            refine ⟨15943560155957649788581745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10629040103971766525721163 15943560155957649788581745)
            ·
              refine ⟨11957670116968237341436309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15943560155957649788581745 11957670116968237341436309)
              ·
                refine ⟨560515786732886125379827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 11957670116968237341436309 560515786732886125379827)
                ·
                  refine ⟨840773680099329188069741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 560515786732886125379827 840773680099329188069741)
                  ·
                    refine ⟨315290130037248445526153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 840773680099329188069741 315290130037248445526153)
                    ·
                      rfl

theorem cell22_921038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 2, 6, 1, 3].length) (baseStart_921038 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_921038 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_921038 prefixEnd_921038 := by exact prefixLift 921038
  have htrace : WordTrace (prefixWord ++ tailWord_921038) baseStart_921038 baseEnd_921038 := by
    simpa [prefixWord, tailWord_921038, baseEnd_921038] using wordTrace_append hprefix tailTrace_921038
  have hstable : (prefixWord ++ tailWord_921038).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_921038).length < 2 ^ (prefixWord ++ tailWord_921038).sum := by decide
  have hdescent : baseEnd_921038 < baseStart_921038 := by decide
  rcases family_descends (prefixWord ++ tailWord_921038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_921089 : List Nat := [1, 2, 4, 1, 5, 1, 2, 2, 1, 3]
def baseStart_921089 : Nat := 118140960795 + 921089 * 2 ^ 59
def prefixEnd_921089 : Nat := 4983230072969 + 3 ^ 40 * 921089 * 2
def baseEnd_921089 : Nat := 315307588379501312500997

theorem tailTrace_921089 : CollatzResearch.WordTrace tailWord_921089 prefixEnd_921089 315307588379501312500997 := by
  unfold tailWord_921089
  simp only [CollatzResearch.WordTrace]
  refine ⟨33594875760059337322262321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22396583840039558214841547 33594875760059337322262321)
  ·
    refine ⟨25196156820044502991696741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33594875760059337322262321 25196156820044502991696741)
    ·
      refine ⟨4724279403758344310943139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25196156820044502991696741 4724279403758344310943139)
      ·
        refine ⟨7086419105637516466414709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4724279403758344310943139 7086419105637516466414709)
        ·
          refine ⟨664351791153517168726379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 7086419105637516466414709 664351791153517168726379)
          ·
            refine ⟨996527686730275753089569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 664351791153517168726379 996527686730275753089569)
            ·
              refine ⟨747395765047706814817177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 996527686730275753089569 747395765047706814817177)
              ·
                refine ⟨560546823785780111112883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 747395765047706814817177 560546823785780111112883)
                ·
                  refine ⟨840820235678670166669325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 560546823785780111112883 840820235678670166669325)
                  ·
                    refine ⟨315307588379501312500997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 840820235678670166669325 315307588379501312500997)
                    ·
                      rfl

theorem cell22_921089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 5, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 5, 1, 2, 2, 1, 3].length) (baseStart_921089 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_921089 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_921089 prefixEnd_921089 := by exact prefixLift 921089
  have htrace : WordTrace (prefixWord ++ tailWord_921089) baseStart_921089 baseEnd_921089 := by
    simpa [prefixWord, tailWord_921089, baseEnd_921089] using wordTrace_append hprefix tailTrace_921089
  have hstable : (prefixWord ++ tailWord_921089).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_921089).length < 2 ^ (prefixWord ++ tailWord_921089).sum := by decide
  have hdescent : baseEnd_921089 < baseStart_921089 := by decide
  rcases family_descends (prefixWord ++ tailWord_921089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_921145 : List Nat := [1, 2, 1, 5, 1, 4, 1, 2, 2, 3]
def baseStart_921145 : Nat := 118140960795 + 921145 * 2 ^ 59
def prefixEnd_921145 : Nat := 4983230072969 + 3 ^ 40 * 921145 * 2
def baseEnd_921145 : Nat := 315326758323935833100825

theorem tailTrace_921145 : CollatzResearch.WordTrace tailWord_921145 prefixEnd_921145 315326758323935833100825 := by
  unfold tailWord_921145
  simp only [CollatzResearch.WordTrace]
  refine ⟨33596918247856458886300889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22397945498570972590867259 33596918247856458886300889)
  ·
    refine ⟨25197688685892344164725667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33596918247856458886300889 25197688685892344164725667)
    ·
      refine ⟨37796533028838516247088501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25197688685892344164725667 37796533028838516247088501)
      ·
        refine ⟨3543424971453610898164547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 37796533028838516247088501 3543424971453610898164547)
        ·
          refine ⟨5315137457180416347246821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3543424971453610898164547 5315137457180416347246821)
          ·
            refine ⟨996588273221328065108779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5315137457180416347246821 996588273221328065108779)
            ·
              refine ⟨1494882409831992097663169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 996588273221328065108779 1494882409831992097663169)
              ·
                refine ⟨1121161807373994073247377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1494882409831992097663169 1121161807373994073247377)
                ·
                  refine ⟨840871355530495554935533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1121161807373994073247377 840871355530495554935533)
                  ·
                    refine ⟨315326758323935833100825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 840871355530495554935533 315326758323935833100825)
                    ·
                      rfl

theorem cell22_921145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 4, 1, 2, 2, 3].length) (baseStart_921145 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_921145 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_921145 prefixEnd_921145 := by exact prefixLift 921145
  have htrace : WordTrace (prefixWord ++ tailWord_921145) baseStart_921145 baseEnd_921145 := by
    simpa [prefixWord, tailWord_921145, baseEnd_921145] using wordTrace_append hprefix tailTrace_921145
  have hstable : (prefixWord ++ tailWord_921145).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_921145).length < 2 ^ (prefixWord ++ tailWord_921145).sum := by decide
  have hdescent : baseEnd_921145 < baseStart_921145 := by decide
  rcases family_descends (prefixWord ++ tailWord_921145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_921216 : List Nat := [2, 1, 1, 2, 1, 4, 2, 2, 3, 4]
def baseStart_921216 : Nat := 118140960795 + 921216 * 2 ^ 59
def prefixEnd_921216 : Nat := 4983230072969 + 3 ^ 40 * 921216 * 2
def baseEnd_921216 : Nat := 315351063074915314575607

theorem tailTrace_921216 : CollatzResearch.WordTrace tailWord_921216 prefixEnd_921216 315351063074915314575607 := by
  unfold tailWord_921216
  simp only [CollatzResearch.WordTrace]
  refine ⟨16799753915299619006067751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22399671887066158674757001 16799753915299619006067751)
  ·
    refine ⟨25199630872949428509101627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16799753915299619006067751 25199630872949428509101627)
    ·
      refine ⟨37799446309424142763652441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25199630872949428509101627 37799446309424142763652441)
      ·
        refine ⟨28349584732068107072739331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37799446309424142763652441 28349584732068107072739331)
        ·
          refine ⟨42524377098102160609108997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28349584732068107072739331 42524377098102160609108997)
          ·
            refine ⟨7973320705894155114207937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 42524377098102160609108997 7973320705894155114207937)
            ·
              refine ⟨5979990529420616335655953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7973320705894155114207937 5979990529420616335655953)
              ·
                refine ⟨4484992897065462251741965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5979990529420616335655953 4484992897065462251741965)
                ·
                  refine ⟨1681872336399548344403237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4484992897065462251741965 1681872336399548344403237)
                  ·
                    refine ⟨315351063074915314575607, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1681872336399548344403237 315351063074915314575607)
                    ·
                      rfl

theorem cell22_921216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 2, 2, 3, 4].length) (baseStart_921216 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_921216 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_921216 prefixEnd_921216 := by exact prefixLift 921216
  have htrace : WordTrace (prefixWord ++ tailWord_921216) baseStart_921216 baseEnd_921216 := by
    simpa [prefixWord, tailWord_921216, baseEnd_921216] using wordTrace_append hprefix tailTrace_921216
  have hstable : (prefixWord ++ tailWord_921216).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_921216).length < 2 ^ (prefixWord ++ tailWord_921216).sum := by decide
  have hdescent : baseEnd_921216 < baseStart_921216 := by decide
  rcases family_descends (prefixWord ++ tailWord_921216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_921325 : List Nat := [1, 5, 1, 2, 1, 2, 1, 3, 3, 3]
def baseStart_921325 : Nat := 118140960795 + 921325 * 2 ^ 59
def prefixEnd_921325 : Nat := 4983230072969 + 3 ^ 40 * 921325 * 2
def baseEnd_921325 : Nat := 315388376002475363600273

theorem tailTrace_921325 : CollatzResearch.WordTrace tailWord_921325 prefixEnd_921325 315388376002475363600273 := by
  unfold tailWord_921325
  simp only [CollatzResearch.WordTrace]
  refine ⟨33603483387204349627853429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22402322258136233085235619 33603483387204349627853429)
  ·
    refine ⟨3150326567550407777611259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 33603483387204349627853429 3150326567550407777611259)
    ·
      refine ⟨4725489851325611666416889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3150326567550407777611259 4725489851325611666416889)
      ·
        refine ⟨3544117388494208749812667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4725489851325611666416889 3544117388494208749812667)
        ·
          refine ⟨5316176082741313124719001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3544117388494208749812667 5316176082741313124719001)
          ·
            refine ⟨3987132062055984843539251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5316176082741313124719001 3987132062055984843539251)
            ·
              refine ⟨5980698093083977265308877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3987132062055984843539251 5980698093083977265308877)
              ·
                refine ⟨2242761784906491474490829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5980698093083977265308877 2242761784906491474490829)
                ·
                  refine ⟨841035669339934302934061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2242761784906491474490829 841035669339934302934061)
                  ·
                    refine ⟨315388376002475363600273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 841035669339934302934061 315388376002475363600273)
                    ·
                      rfl

theorem cell22_921325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 1, 3, 3, 3].length) (baseStart_921325 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_921325 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_921325 prefixEnd_921325 := by exact prefixLift 921325
  have htrace : WordTrace (prefixWord ++ tailWord_921325) baseStart_921325 baseEnd_921325 := by
    simpa [prefixWord, tailWord_921325, baseEnd_921325] using wordTrace_append hprefix tailTrace_921325
  have hstable : (prefixWord ++ tailWord_921325).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_921325).length < 2 ^ (prefixWord ++ tailWord_921325).sum := by decide
  have hdescent : baseEnd_921325 < baseStart_921325 := by decide
  rcases family_descends (prefixWord ++ tailWord_921325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_921336 : List Nat := [2, 1, 2, 1, 1, 2, 2, 3, 1, 7]
def baseStart_921336 : Nat := 118140960795 + 921336 * 2 ^ 59
def prefixEnd_921336 : Nat := 4983230072969 + 3 ^ 40 * 921336 * 2
def baseEnd_921336 : Nat := 315392141527275001575239

theorem tailTrace_921336 : CollatzResearch.WordTrace tailWord_921336 prefixEnd_921336 315392141527275001575239 := by
  unfold tailWord_921336
  simp only [CollatzResearch.WordTrace]
  refine ⟨16801942295082249253251931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22402589726776332337669241 16801942295082249253251931)
  ·
    refine ⟨25202913442623373879877897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16801942295082249253251931 25202913442623373879877897)
    ·
      refine ⟨18902185081967530409908423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25202913442623373879877897 18902185081967530409908423)
      ·
        refine ⟨28353277622951295614862635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18902185081967530409908423 28353277622951295614862635)
        ·
          refine ⟨42529916434426943422293953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28353277622951295614862635 42529916434426943422293953)
          ·
            refine ⟨31897437325820207566720465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42529916434426943422293953 31897437325820207566720465)
            ·
              refine ⟨23923077994365155675040349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31897437325820207566720465 23923077994365155675040349)
              ·
                refine ⟨8971154247886933378140131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23923077994365155675040349 8971154247886933378140131)
                ·
                  refine ⟨13456731371830400067210197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8971154247886933378140131 13456731371830400067210197)
                  ·
                    refine ⟨315392141527275001575239, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 13456731371830400067210197 315392141527275001575239)
                    ·
                      rfl

theorem cell22_921336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 3, 1, 7].length) (baseStart_921336 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_921336 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_921336 prefixEnd_921336 := by exact prefixLift 921336
  have htrace : WordTrace (prefixWord ++ tailWord_921336) baseStart_921336 baseEnd_921336 := by
    simpa [prefixWord, tailWord_921336, baseEnd_921336] using wordTrace_append hprefix tailTrace_921336
  have hstable : (prefixWord ++ tailWord_921336).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_921336).length < 2 ^ (prefixWord ++ tailWord_921336).sum := by decide
  have hdescent : baseEnd_921336 < baseStart_921336 := by decide
  rcases family_descends (prefixWord ++ tailWord_921336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_921350 : List Nat := [6, 2, 2, 1, 1, 2, 1, 3, 4]
def baseStart_921350 : Nat := 118140960795 + 921350 * 2 ^ 59
def prefixEnd_921350 : Nat := 4983230072969 + 3 ^ 40 * 921350 * 2
def baseEnd_921350 : Nat := 105132311337794543908399

theorem tailTrace_921350 : CollatzResearch.WordTrace tailWord_921350 prefixEnd_921350 105132311337794543908399 := by
  unfold tailWord_921350
  simp only [CollatzResearch.WordTrace]
  refine ⟨1050137350378555590547297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 22402930141409185931675669 1050137350378555590547297)
  ·
    refine ⟨787603012783916692910473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1050137350378555590547297 787603012783916692910473)
    ·
      refine ⟨590702259587937519682855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 787603012783916692910473 590702259587937519682855)
      ·
        refine ⟨886053389381906279524283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 590702259587937519682855 886053389381906279524283)
        ·
          refine ⟨1329080084072859419286425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 886053389381906279524283 1329080084072859419286425)
          ·
            refine ⟨996810063054644564464819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1329080084072859419286425 996810063054644564464819)
            ·
              refine ⟨1495215094581966846697229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 996810063054644564464819 1495215094581966846697229)
              ·
                refine ⟨560705660468237567511461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1495215094581966846697229 560705660468237567511461)
                ·
                  refine ⟨105132311337794543908399, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 560705660468237567511461 105132311337794543908399)
                  ·
                    rfl

theorem cell22_921350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 2, 1, 3, 4].length) (baseStart_921350 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_921350 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_921350 prefixEnd_921350 := by exact prefixLift 921350
  have htrace : WordTrace (prefixWord ++ tailWord_921350) baseStart_921350 baseEnd_921350 := by
    simpa [prefixWord, tailWord_921350, baseEnd_921350] using wordTrace_append hprefix tailTrace_921350
  have hstable : (prefixWord ++ tailWord_921350).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_921350).length < 2 ^ (prefixWord ++ tailWord_921350).sum := by decide
  have hdescent : baseEnd_921350 < baseStart_921350 := by decide
  rcases family_descends (prefixWord ++ tailWord_921350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_921402 : List Nat := [3, 1, 1, 1, 5, 3, 1, 2, 1, 4]
def baseStart_921402 : Nat := 118140960795 + 921402 * 2 ^ 59
def prefixEnd_921402 : Nat := 4983230072969 + 3 ^ 40 * 921402 * 2
def baseEnd_921402 : Nat := 315414734676072829425037

theorem tailTrace_921402 : CollatzResearch.WordTrace tailWord_921402 prefixEnd_921402 315414734676072829425037 := by
  unfold tailWord_921402
  simp only [CollatzResearch.WordTrace]
  refine ⟨8401572951981347944601615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22404194538616927852270973 8401572951981347944601615)
  ·
    refine ⟨12602359427972021916902423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8401572951981347944601615 12602359427972021916902423)
    ·
      refine ⟨18903539141958032875353635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12602359427972021916902423 18903539141958032875353635)
      ·
        refine ⟨28355308712937049313030453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18903539141958032875353635 28355308712937049313030453)
        ·
          refine ⟨2658310191837848373096605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 28355308712937049313030453 2658310191837848373096605)
          ·
            refine ⟨996866321939193139911227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2658310191837848373096605 996866321939193139911227)
            ·
              refine ⟨1495299482908789709866841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 996866321939193139911227 1495299482908789709866841)
              ·
                refine ⟨1121474612181592282400131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1495299482908789709866841 1121474612181592282400131)
                ·
                  refine ⟨1682211918272388423600197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1121474612181592282400131 1682211918272388423600197)
                  ·
                    refine ⟨315414734676072829425037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1682211918272388423600197 315414734676072829425037)
                    ·
                      rfl

theorem cell22_921402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 3, 1, 2, 1, 4].length) (baseStart_921402 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_921402 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_921402 prefixEnd_921402 := by exact prefixLift 921402
  have htrace : WordTrace (prefixWord ++ tailWord_921402) baseStart_921402 baseEnd_921402 := by
    simpa [prefixWord, tailWord_921402, baseEnd_921402] using wordTrace_append hprefix tailTrace_921402
  have hstable : (prefixWord ++ tailWord_921402).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_921402).length < 2 ^ (prefixWord ++ tailWord_921402).sum := by decide
  have hdescent : baseEnd_921402 < baseStart_921402 := by decide
  rcases family_descends (prefixWord ++ tailWord_921402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_921428 : List Nat := [2, 4, 1, 1, 3, 11]
def baseStart_921428 : Nat := 118140960795 + 921428 * 2 ^ 59
def prefixEnd_921428 : Nat := 4983230072969 + 3 ^ 40 * 921428 * 2
def baseEnd_921428 : Nat := 3894118950708857139197

theorem tailTrace_921428 : CollatzResearch.WordTrace tailWord_921428 prefixEnd_921428 3894118950708857139197 := by
  unfold tailWord_921428
  simp only [CollatzResearch.WordTrace]
  refine ⟨16803620052915599109426469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22404826737220798812568625 16803620052915599109426469)
  ·
    refine ⟨3150678759921674833017463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 16803620052915599109426469 3150678759921674833017463)
    ·
      refine ⟨4726018139882512249526195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3150678759921674833017463 4726018139882512249526195)
      ·
        refine ⟨7089027209823768374289293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4726018139882512249526195 7089027209823768374289293)
        ·
          refine ⟨2658385203683913140358485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7089027209823768374289293 2658385203683913140358485)
          ·
            refine ⟨3894118950708857139197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 2658385203683913140358485 3894118950708857139197)
            ·
              rfl

theorem cell22_921428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 11].length) (baseStart_921428 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_921428 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_921428 prefixEnd_921428 := by exact prefixLift 921428
  have htrace : WordTrace (prefixWord ++ tailWord_921428) baseStart_921428 baseEnd_921428 := by
    simpa [prefixWord, tailWord_921428, baseEnd_921428] using wordTrace_append hprefix tailTrace_921428
  have hstable : (prefixWord ++ tailWord_921428).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_921428).length < 2 ^ (prefixWord ++ tailWord_921428).sum := by decide
  have hdescent : baseEnd_921428 < baseStart_921428 := by decide
  rcases family_descends (prefixWord ++ tailWord_921428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_921458 : List Nat := [3, 2, 1, 2, 1, 1, 1, 1, 4, 6]
def baseStart_921458 : Nat := 118140960795 + 921458 * 2 ^ 59
def prefixEnd_921458 : Nat := 4983230072969 + 3 ^ 40 * 921458 * 2
def baseEnd_921458 : Nat := 315433904620507350024865

theorem tailTrace_921458 : CollatzResearch.WordTrace tailWord_921458 prefixEnd_921458 315433904620507350024865 := by
  unfold tailWord_921458
  simp only [CollatzResearch.WordTrace]
  refine ⟨8402083573930628335611257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22405556197148342228296685 8402083573930628335611257)
  ·
    refine ⟨6301562680447971251708443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8402083573930628335611257 6301562680447971251708443)
    ·
      refine ⟨9452344020671956877562665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6301562680447971251708443 9452344020671956877562665)
      ·
        refine ⟨7089258015503967658171999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9452344020671956877562665 7089258015503967658171999)
        ·
          refine ⟨10633887023255951487257999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7089258015503967658171999 10633887023255951487257999)
          ·
            refine ⟨15950830534883927230886999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10633887023255951487257999 15950830534883927230886999)
            ·
              refine ⟨23926245802325890846330499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15950830534883927230886999 23926245802325890846330499)
              ·
                refine ⟨35889368703488836269495749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23926245802325890846330499 35889368703488836269495749)
                ·
                  refine ⟨6729256631904156800530453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35889368703488836269495749 6729256631904156800530453)
                  ·
                    refine ⟨315433904620507350024865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6729256631904156800530453 315433904620507350024865)
                    ·
                      rfl

theorem cell22_921458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 1, 4, 6].length) (baseStart_921458 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_921458 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_921458 prefixEnd_921458 := by exact prefixLift 921458
  have htrace : WordTrace (prefixWord ++ tailWord_921458) baseStart_921458 baseEnd_921458 := by
    simpa [prefixWord, tailWord_921458, baseEnd_921458] using wordTrace_append hprefix tailTrace_921458
  have hstable : (prefixWord ++ tailWord_921458).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_921458).length < 2 ^ (prefixWord ++ tailWord_921458).sum := by decide
  have hdescent : baseEnd_921458 < baseStart_921458 := by decide
  rcases family_descends (prefixWord ++ tailWord_921458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_921488 : List Nat := [2, 1, 1, 1, 1, 1, 2, 6, 2, 5]
def baseStart_921488 : Nat := 118140960795 + 921488 * 2 ^ 59
def prefixEnd_921488 : Nat := 4983230072969 + 3 ^ 40 * 921488 * 2
def baseEnd_921488 : Nat := 315444174233597271774773

theorem tailTrace_921488 : CollatzResearch.WordTrace tailWord_921488 prefixEnd_921488 315444174233597271774773 := by
  unfold tailWord_921488
  simp only [CollatzResearch.WordTrace]
  refine ⟨16804714242806914233018559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22406285657075885644024745 16804714242806914233018559)
  ·
    refine ⟨25207071364210371349527839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16804714242806914233018559 25207071364210371349527839)
    ·
      refine ⟨37810607046315557024291759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25207071364210371349527839 37810607046315557024291759)
      ·
        refine ⟨56715910569473335536437639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37810607046315557024291759 56715910569473335536437639)
        ·
          refine ⟨85073865854210003304656459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56715910569473335536437639 85073865854210003304656459)
          ·
            refine ⟨127610798781315004956984689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85073865854210003304656459 127610798781315004956984689)
            ·
              refine ⟨95708099085986253717738517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 127610798781315004956984689 95708099085986253717738517)
              ·
                refine ⟨4486317144655605643018993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 95708099085986253717738517 4486317144655605643018993)
                ·
                  refine ⟨3364737858491704232264245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4486317144655605643018993 3364737858491704232264245)
                  ·
                    refine ⟨315444174233597271774773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3364737858491704232264245 315444174233597271774773)
                    ·
                      rfl

theorem cell22_921488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 6, 2, 5].length) (baseStart_921488 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_921488 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_921488 prefixEnd_921488 := by exact prefixLift 921488
  have htrace : WordTrace (prefixWord ++ tailWord_921488) baseStart_921488 baseEnd_921488 := by
    simpa [prefixWord, tailWord_921488, baseEnd_921488] using wordTrace_append hprefix tailTrace_921488
  have hstable : (prefixWord ++ tailWord_921488).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_921488).length < 2 ^ (prefixWord ++ tailWord_921488).sum := by decide
  have hdescent : baseEnd_921488 < baseStart_921488 := by decide
  rcases family_descends (prefixWord ++ tailWord_921488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_921558 : List Nat := [5, 2, 1, 1, 4, 1, 2, 1, 5]
def baseStart_921558 : Nat := 118140960795 + 921558 * 2 ^ 59
def prefixEnd_921558 : Nat := 4983230072969 + 3 ^ 40 * 921558 * 2
def baseEnd_921558 : Nat := 105156045554713474174853

theorem tailTrace_921558 : CollatzResearch.WordTrace tailWord_921558 prefixEnd_921558 105156045554713474174853 := by
  unfold tailWord_921558
  simp only [CollatzResearch.WordTrace]
  refine ⟨2100748849710014401317833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 22407987730240153614056885 2100748849710014401317833)
  ·
    refine ⟨1575561637282510800988375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2100748849710014401317833 1575561637282510800988375)
    ·
      refine ⟨2363342455923766201482563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1575561637282510800988375 2363342455923766201482563)
      ·
        refine ⟨3545013683885649302223845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2363342455923766201482563 3545013683885649302223845)
        ·
          refine ⟨664690065728559244166971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3545013683885649302223845 664690065728559244166971)
          ·
            refine ⟨997035098592838866250457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 664690065728559244166971 997035098592838866250457)
            ·
              refine ⟨747776323944629149687843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 997035098592838866250457 747776323944629149687843)
              ·
                refine ⟨1121664485916943724531765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 747776323944629149687843 1121664485916943724531765)
                ·
                  refine ⟨105156045554713474174853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1121664485916943724531765 105156045554713474174853)
                  ·
                    rfl

theorem cell22_921558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 4, 1, 2, 1, 5].length) (baseStart_921558 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_921558 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_921558 prefixEnd_921558 := by exact prefixLift 921558
  have htrace : WordTrace (prefixWord ++ tailWord_921558) baseStart_921558 baseEnd_921558 := by
    simpa [prefixWord, tailWord_921558, baseEnd_921558] using wordTrace_append hprefix tailTrace_921558
  have hstable : (prefixWord ++ tailWord_921558).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_921558).length < 2 ^ (prefixWord ++ tailWord_921558).sum := by decide
  have hdescent : baseEnd_921558 < baseStart_921558 := by decide
  rcases family_descends (prefixWord ++ tailWord_921558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_921582 : List Nat := [4, 1, 2, 1, 3, 1, 1, 3, 2, 4]
def baseStart_921582 : Nat := 118140960795 + 921582 * 2 ^ 59
def prefixEnd_921582 : Nat := 4983230072969 + 3 ^ 40 * 921582 * 2
def baseEnd_921582 : Nat := 315476352354612359924485

theorem tailTrace_921582 : CollatzResearch.WordTrace tailWord_921582 prefixEnd_921582 315476352354612359924485 := by
  unfold tailWord_921582
  simp only [CollatzResearch.WordTrace]
  refine ⟨4201607118409160314994875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22408571298182188346639333 4201607118409160314994875)
  ·
    refine ⟨6302410677613740472492313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4201607118409160314994875 6302410677613740472492313)
    ·
      refine ⟨4726808008210305354369235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6302410677613740472492313 4726808008210305354369235)
      ·
        refine ⟨7090212012315458031553853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4726808008210305354369235 7090212012315458031553853)
        ·
          refine ⟨2658829504618296761832695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7090212012315458031553853 2658829504618296761832695)
          ·
            refine ⟨3988244256927445142749043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2658829504618296761832695 3988244256927445142749043)
            ·
              refine ⟨5982366385391167714123565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3988244256927445142749043 5982366385391167714123565)
              ·
                refine ⟨2243387394521687892796337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5982366385391167714123565 2243387394521687892796337)
                ·
                  refine ⟨1682540545891265919597253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2243387394521687892796337 1682540545891265919597253)
                  ·
                    refine ⟨315476352354612359924485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1682540545891265919597253 315476352354612359924485)
                    ·
                      rfl

theorem cell22_921582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 1, 3, 2, 4].length) (baseStart_921582 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_921582 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_921582 prefixEnd_921582 := by exact prefixLift 921582
  have htrace : WordTrace (prefixWord ++ tailWord_921582) baseStart_921582 baseEnd_921582 := by
    simpa [prefixWord, tailWord_921582, baseEnd_921582] using wordTrace_append hprefix tailTrace_921582
  have hstable : (prefixWord ++ tailWord_921582).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_921582).length < 2 ^ (prefixWord ++ tailWord_921582).sum := by decide
  have hdescent : baseEnd_921582 < baseStart_921582 := by decide
  rcases family_descends (prefixWord ++ tailWord_921582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_921612 : List Nat := [2, 2, 1, 2, 3, 1, 2, 3, 3, 3]
def baseStart_921612 : Nat := 118140960795 + 921612 * 2 ^ 59
def prefixEnd_921612 : Nat := 4983230072969 + 3 ^ 40 * 921612 * 2
def baseEnd_921612 : Nat := 315486621967702281674393

theorem tailTrace_921612 : CollatzResearch.WordTrace tailWord_921612 prefixEnd_921612 315486621967702281674393 := by
  unfold tailWord_921612
  simp only [CollatzResearch.WordTrace]
  refine ⟨16806975568582298821775545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22409300758109731762367393 16806975568582298821775545)
  ·
    refine ⟨12605231676436724116331659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16806975568582298821775545 12605231676436724116331659)
    ·
      refine ⟨18907847514655086174497489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12605231676436724116331659 18907847514655086174497489)
      ·
        refine ⟨14180885635991314630873117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18907847514655086174497489 14180885635991314630873117)
        ·
          refine ⟨5317832113496742986577419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14180885635991314630873117 5317832113496742986577419)
          ·
            refine ⟨7976748170245114479866129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5317832113496742986577419 7976748170245114479866129)
            ·
              refine ⟨5982561127683835859899597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7976748170245114479866129 5982561127683835859899597)
              ·
                refine ⟨2243460422881438447462349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5982561127683835859899597 2243460422881438447462349)
                ·
                  refine ⟨841297658580539417798381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2243460422881438447462349 841297658580539417798381)
                  ·
                    refine ⟨315486621967702281674393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 841297658580539417798381 315486621967702281674393)
                    ·
                      rfl

theorem cell22_921612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 2, 3, 3, 3].length) (baseStart_921612 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_921612 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_921612 prefixEnd_921612 := by exact prefixLift 921612
  have htrace : WordTrace (prefixWord ++ tailWord_921612) baseStart_921612 baseEnd_921612 := by
    simpa [prefixWord, tailWord_921612, baseEnd_921612] using wordTrace_append hprefix tailTrace_921612
  have hstable : (prefixWord ++ tailWord_921612).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_921612).length < 2 ^ (prefixWord ++ tailWord_921612).sum := by decide
  have hdescent : baseEnd_921612 < baseStart_921612 := by decide
  rcases family_descends (prefixWord ++ tailWord_921612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_921629 : List Nat := [1, 4, 2, 2, 2, 2, 1, 2, 3, 3]
def baseStart_921629 : Nat := 118140960795 + 921629 * 2 ^ 59
def prefixEnd_921629 : Nat := 4983230072969 + 3 ^ 40 * 921629 * 2
def baseEnd_921629 : Nat := 315492441415119903999341

theorem tailTrace_921629 : CollatzResearch.WordTrace tailWord_921629 prefixEnd_921629 315492441415119903999341 := by
  unfold tailWord_921629
  simp only [CollatzResearch.WordTrace]
  refine ⟨33614571178103009546919941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22409714118735339697946627 33614571178103009546919941)
  ·
    refine ⟨6302732095894314290047489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 33614571178103009546919941 6302732095894314290047489)
    ·
      refine ⟨4727049071920735717535617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6302732095894314290047489 4727049071920735717535617)
      ·
        refine ⟨3545286803940551788151713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4727049071920735717535617 3545286803940551788151713)
        ·
          refine ⟨2658965102955413841113785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3545286803940551788151713 2658965102955413841113785)
          ·
            refine ⟨1994223827216560380835339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2658965102955413841113785 1994223827216560380835339)
            ·
              refine ⟨2991335740824840571253009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1994223827216560380835339 2991335740824840571253009)
              ·
                refine ⟨2243501805618630428439757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2991335740824840571253009 2243501805618630428439757)
                ·
                  refine ⟨841313177106986410664909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2243501805618630428439757 841313177106986410664909)
                  ·
                    refine ⟨315492441415119903999341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 841313177106986410664909 315492441415119903999341)
                    ·
                      rfl

theorem cell22_921629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 2, 1, 2, 3, 3].length) (baseStart_921629 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_921629 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_921629 prefixEnd_921629 := by exact prefixLift 921629
  have htrace : WordTrace (prefixWord ++ tailWord_921629) baseStart_921629 baseEnd_921629 := by
    simpa [prefixWord, tailWord_921629, baseEnd_921629] using wordTrace_append hprefix tailTrace_921629
  have hstable : (prefixWord ++ tailWord_921629).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_921629).length < 2 ^ (prefixWord ++ tailWord_921629).sum := by decide
  have hdescent : baseEnd_921629 < baseStart_921629 := by decide
  rcases family_descends (prefixWord ++ tailWord_921629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_921646 : List Nat := [4, 1, 3, 1, 1, 2, 1, 5, 1, 3]
def baseStart_921646 : Nat := 118140960795 + 921646 * 2 ^ 59
def prefixEnd_921646 : Nat := 4983230072969 + 3 ^ 40 * 921646 * 2
def baseEnd_921646 : Nat := 315498260862537526324289

theorem tailTrace_921646 : CollatzResearch.WordTrace tailWord_921646 prefixEnd_921646 315498260862537526324289 := by
  unfold tailWord_921646
  simp only [CollatzResearch.WordTrace]
  refine ⟨4201898902380177681286099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22410127479360947633525861 4201898902380177681286099)
  ·
    refine ⟨6302848353570266521929149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4201898902380177681286099 6302848353570266521929149)
    ·
      refine ⟨2363568132588849945723431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6302848353570266521929149 2363568132588849945723431)
      ·
        refine ⟨3545352198883274918585147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2363568132588849945723431 3545352198883274918585147)
        ·
          refine ⟨5318028298324912377877721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3545352198883274918585147 5318028298324912377877721)
          ·
            refine ⟨3988521223743684283408291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5318028298324912377877721 3988521223743684283408291)
            ·
              refine ⟨5982781835615526425112437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3988521223743684283408291 5982781835615526425112437)
              ·
                refine ⟨560885797088955602354291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5982781835615526425112437 560885797088955602354291)
                ·
                  refine ⟨841328695633433403531437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 560885797088955602354291 841328695633433403531437)
                  ·
                    refine ⟨315498260862537526324289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 841328695633433403531437 315498260862537526324289)
                    ·
                      rfl

theorem cell22_921646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 1, 5, 1, 3].length) (baseStart_921646 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_921646 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_921646 prefixEnd_921646 := by exact prefixLift 921646
  have htrace : WordTrace (prefixWord ++ tailWord_921646) baseStart_921646 baseEnd_921646 := by
    simpa [prefixWord, tailWord_921646, baseEnd_921646] using wordTrace_append hprefix tailTrace_921646
  have hstable : (prefixWord ++ tailWord_921646).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_921646).length < 2 ^ (prefixWord ++ tailWord_921646).sum := by decide
  have hdescent : baseEnd_921646 < baseStart_921646 := by decide
  rcases family_descends (prefixWord ++ tailWord_921646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_921721 : List Nat := [1, 2, 1, 3, 4, 2, 3, 2, 4]
def baseStart_921721 : Nat := 118140960795 + 921721 * 2 ^ 59
def prefixEnd_921721 : Nat := 4983230072969 + 3 ^ 40 * 921721 * 2
def baseEnd_921721 : Nat := 105174644965087443566353

theorem tailTrace_921721 : CollatzResearch.WordTrace tailWord_921721 prefixEnd_921721 105174644965087443566353 := by
  unfold tailWord_921721
  simp only [CollatzResearch.WordTrace]
  refine ⟨33617926693769709259269017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22411951129179806172846011 33617926693769709259269017)
  ·
    refine ⟨25213445020327281944451763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33617926693769709259269017 25213445020327281944451763)
    ·
      refine ⟨37820167530490922916677645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25213445020327281944451763 37820167530490922916677645)
      ·
        refine ⟨14182562823934096093754117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37820167530490922916677645 14182562823934096093754117)
        ·
          refine ⟨2659230529487643017578897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14182562823934096093754117 2659230529487643017578897)
          ·
            refine ⟨1994422897115732263184173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2659230529487643017578897 1994422897115732263184173)
            ·
              refine ⟨747908586418399598694065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1994422897115732263184173 747908586418399598694065)
              ·
                refine ⟨560931439813799699020549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 747908586418399598694065 560931439813799699020549)
                ·
                  refine ⟨105174644965087443566353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 560931439813799699020549 105174644965087443566353)
                  ·
                    rfl

theorem cell22_921721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 2, 3, 2, 4].length) (baseStart_921721 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_921721 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_921721 prefixEnd_921721 := by exact prefixLift 921721
  have htrace : WordTrace (prefixWord ++ tailWord_921721) baseStart_921721 baseEnd_921721 := by
    simpa [prefixWord, tailWord_921721, baseEnd_921721] using wordTrace_append hprefix tailTrace_921721
  have hstable : (prefixWord ++ tailWord_921721).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_921721).length < 2 ^ (prefixWord ++ tailWord_921721).sum := by decide
  have hdescent : baseEnd_921721 < baseStart_921721 := by decide
  rcases family_descends (prefixWord ++ tailWord_921721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_921732 : List Nat := [2, 3, 2, 1, 2, 1, 4, 7]
def baseStart_921732 : Nat := 118140960795 + 921732 * 2 ^ 59
def prefixEnd_921732 : Nat := 4983230072969 + 3 ^ 40 * 921732 * 2
def baseEnd_921732 : Nat := 35058633380006885408225

theorem tailTrace_921732 : CollatzResearch.WordTrace tailWord_921732 prefixEnd_921732 35058633380006885408225 := by
  unfold tailWord_921732
  simp only [CollatzResearch.WordTrace]
  refine ⟨16809163948364929068959725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22412218597819905425279633 16809163948364929068959725)
  ·
    refine ⟨6303436480636848400859897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16809163948364929068959725 6303436480636848400859897)
    ·
      refine ⟨4727577360477636300644923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6303436480636848400859897 4727577360477636300644923)
      ·
        refine ⟨7091366040716454450967385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4727577360477636300644923 7091366040716454450967385)
        ·
          refine ⟨5318524530537340838225539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7091366040716454450967385 5318524530537340838225539)
          ·
            refine ⟨7977786795806011257338309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5318524530537340838225539 7977786795806011257338309)
            ·
              refine ⟨1495835024213627110750933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7977786795806011257338309 1495835024213627110750933)
              ·
                refine ⟨35058633380006885408225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1495835024213627110750933 35058633380006885408225)
                ·
                  rfl

theorem cell22_921732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 4, 7].length) (baseStart_921732 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_921732 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_921732 prefixEnd_921732 := by exact prefixLift 921732
  have htrace : WordTrace (prefixWord ++ tailWord_921732) baseStart_921732 baseEnd_921732 := by
    simpa [prefixWord, tailWord_921732, baseEnd_921732] using wordTrace_append hprefix tailTrace_921732
  have hstable : (prefixWord ++ tailWord_921732).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_921732).length < 2 ^ (prefixWord ++ tailWord_921732).sum := by decide
  have hdescent : baseEnd_921732 < baseStart_921732 := by decide
  rcases family_descends (prefixWord ++ tailWord_921732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_921736 : List Nat := [2, 1, 3, 4, 1, 2, 1, 3, 2, 3]
def baseStart_921736 : Nat := 118140960795 + 921736 * 2 ^ 59
def prefixEnd_921736 : Nat := 4983230072969 + 3 ^ 40 * 921736 * 2
def baseEnd_921736 : Nat := 315529069701807291574013

theorem tailTrace_921736 : CollatzResearch.WordTrace tailWord_921736 prefixEnd_921736 315529069701807291574013 := by
  unfold tailWord_921736
  simp only [CollatzResearch.WordTrace]
  refine ⟨16809236894357683410532531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22412315859143577880710041 16809236894357683410532531)
  ·
    refine ⟨25213855341536525115798797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16809236894357683410532531 25213855341536525115798797)
    ·
      refine ⟨9455195753076196918424549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25213855341536525115798797 9455195753076196918424549)
      ·
        refine ⟨1772849203701786922204603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9455195753076196918424549 1772849203701786922204603)
        ·
          refine ⟨2659273805552680383306905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1772849203701786922204603 2659273805552680383306905)
          ·
            refine ⟨1994455354164510287480179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2659273805552680383306905 1994455354164510287480179)
            ·
              refine ⟨2991683031246765431220269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1994455354164510287480179 2991683031246765431220269)
              ·
                refine ⟨1121881136717537036707601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2991683031246765431220269 1121881136717537036707601)
                ·
                  refine ⟨841410852538152777530701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1121881136717537036707601 841410852538152777530701)
                  ·
                    refine ⟨315529069701807291574013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 841410852538152777530701 315529069701807291574013)
                    ·
                      rfl

theorem cell22_921736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 2, 1, 3, 2, 3].length) (baseStart_921736 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_921736 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_921736 prefixEnd_921736 := by exact prefixLift 921736
  have htrace : WordTrace (prefixWord ++ tailWord_921736) baseStart_921736 baseEnd_921736 := by
    simpa [prefixWord, tailWord_921736, baseEnd_921736] using wordTrace_append hprefix tailTrace_921736
  have hstable : (prefixWord ++ tailWord_921736).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_921736).length < 2 ^ (prefixWord ++ tailWord_921736).sum := by decide
  have hdescent : baseEnd_921736 < baseStart_921736 := by decide
  rcases family_descends (prefixWord ++ tailWord_921736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_921747 : List Nat := [1, 1, 1, 2, 1, 2, 3, 3, 5, 3]
def baseStart_921747 : Nat := 118140960795 + 921747 * 2 ^ 59
def prefixEnd_921747 : Nat := 4983230072969 + 3 ^ 40 * 921747 * 2
def baseEnd_921747 : Nat := 315532835226606929548979

theorem tailTrace_921747 : CollatzResearch.WordTrace tailWord_921747 prefixEnd_921747 315532835226606929548979 := by
  unfold tailWord_921747
  simp only [CollatzResearch.WordTrace]
  refine ⟨33618874991675515699715495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22412583327783677133143663 33618874991675515699715495)
  ·
    refine ⟨50428312487513273549573243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33618874991675515699715495 50428312487513273549573243)
    ·
      refine ⟨75642468731269910324359865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50428312487513273549573243 75642468731269910324359865)
      ·
        refine ⟨56731851548452432743269899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75642468731269910324359865 56731851548452432743269899)
        ·
          refine ⟨85097777322678649114904849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56731851548452432743269899 85097777322678649114904849)
          ·
            refine ⟨63823332992008986836178637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 85097777322678649114904849 63823332992008986836178637)
            ·
              refine ⟨23933749872003370063566989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 63823332992008986836178637 23933749872003370063566989)
              ·
                refine ⟨8975156202001263773837621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23933749872003370063566989 8975156202001263773837621)
                ·
                  refine ⟨841420893937618478797277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 8975156202001263773837621 841420893937618478797277)
                  ·
                    refine ⟨315532835226606929548979, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 841420893937618478797277 315532835226606929548979)
                    ·
                      rfl

theorem cell22_921747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 3, 5, 3].length) (baseStart_921747 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_921747 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_921747 prefixEnd_921747 := by exact prefixLift 921747
  have htrace : WordTrace (prefixWord ++ tailWord_921747) baseStart_921747 baseEnd_921747 := by
    simpa [prefixWord, tailWord_921747, baseEnd_921747] using wordTrace_append hprefix tailTrace_921747
  have hstable : (prefixWord ++ tailWord_921747).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_921747).length < 2 ^ (prefixWord ++ tailWord_921747).sum := by decide
  have hdescent : baseEnd_921747 < baseStart_921747 := by decide
  rcases family_descends (prefixWord ++ tailWord_921747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_921792 : List Nat := [2, 1, 1, 2, 5, 1, 1, 1, 1, 7]
def baseStart_921792 : Nat := 118140960795 + 921792 * 2 ^ 59
def prefixEnd_921792 : Nat := 4983230072969 + 3 ^ 40 * 921792 * 2
def baseEnd_921792 : Nat := 315548239646241812173841

theorem tailTrace_921792 : CollatzResearch.WordTrace tailWord_921792 prefixEnd_921792 315548239646241812173841 := by
  unfold tailWord_921792
  simp only [CollatzResearch.WordTrace]
  refine ⟨16810258138256244192551815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22413677517674992256735753 16810258138256244192551815)
  ·
    refine ⟨25215387207384366288827723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16810258138256244192551815 25215387207384366288827723)
    ·
      refine ⟨37823080811076549433241585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25215387207384366288827723 37823080811076549433241585)
      ·
        refine ⟨28367310608307412074931189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37823080811076549433241585 28367310608307412074931189)
        ·
          refine ⟨2659435369528819882024799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 28367310608307412074931189 2659435369528819882024799)
          ·
            refine ⟨3989153054293229823037199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2659435369528819882024799 3989153054293229823037199)
            ·
              refine ⟨5983729581439844734555799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3989153054293229823037199 5983729581439844734555799)
              ·
                refine ⟨8975594372159767101833699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5983729581439844734555799 8975594372159767101833699)
                ·
                  refine ⟨13463391558239650652750549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8975594372159767101833699 13463391558239650652750549)
                  ·
                    refine ⟨315548239646241812173841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 13463391558239650652750549 315548239646241812173841)
                    ·
                      rfl

theorem cell22_921792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 1, 1, 1, 7].length) (baseStart_921792 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_921792 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_921792 prefixEnd_921792 := by exact prefixLift 921792
  have htrace : WordTrace (prefixWord ++ tailWord_921792) baseStart_921792 baseEnd_921792 := by
    simpa [prefixWord, tailWord_921792, baseEnd_921792] using wordTrace_append hprefix tailTrace_921792
  have hstable : (prefixWord ++ tailWord_921792).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_921792).length < 2 ^ (prefixWord ++ tailWord_921792).sum := by decide
  have hdescent : baseEnd_921792 < baseStart_921792 := by decide
  rcases family_descends (prefixWord ++ tailWord_921792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_921807 : List Nat := [1, 1, 2, 1, 1, 3, 3, 3, 3, 4]
def baseStart_921807 : Nat := 118140960795 + 921807 * 2 ^ 59
def prefixEnd_921807 : Nat := 4983230072969 + 3 ^ 40 * 921807 * 2
def baseEnd_921807 : Nat := 315553374452786773048795

theorem tailTrace_921807 : CollatzResearch.WordTrace tailWord_921807 prefixEnd_921807 315553374452786773048795 := by
  unfold tailWord_921807
  simp only [CollatzResearch.WordTrace]
  refine ⟨33621063371458145946899675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22414042247638763964599783 33621063371458145946899675)
  ·
    refine ⟨50431595057187218920349513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33621063371458145946899675 50431595057187218920349513)
    ·
      refine ⟨37823696292890414190262135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50431595057187218920349513 37823696292890414190262135)
      ·
        refine ⟨56735544439335621285393203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37823696292890414190262135 56735544439335621285393203)
        ·
          refine ⟨85103316659003431928089805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56735544439335621285393203 85103316659003431928089805)
          ·
            refine ⟨31913743747126286973033677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 85103316659003431928089805 31913743747126286973033677)
            ·
              refine ⟨11967653905172357614887629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31913743747126286973033677 11967653905172357614887629)
              ·
                refine ⟨4487870214439634105582861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11967653905172357614887629 4487870214439634105582861)
                ·
                  refine ⟨1682951330414862789593573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4487870214439634105582861 1682951330414862789593573)
                  ·
                    refine ⟨315553374452786773048795, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1682951330414862789593573 315553374452786773048795)
                    ·
                      rfl

theorem cell22_921807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 3, 3, 3, 4].length) (baseStart_921807 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_921807 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_921807 prefixEnd_921807 := by exact prefixLift 921807
  have htrace : WordTrace (prefixWord ++ tailWord_921807) baseStart_921807 baseEnd_921807 := by
    simpa [prefixWord, tailWord_921807, baseEnd_921807] using wordTrace_append hprefix tailTrace_921807
  have hstable : (prefixWord ++ tailWord_921807).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_921807).length < 2 ^ (prefixWord ++ tailWord_921807).sum := by decide
  have hdescent : baseEnd_921807 < baseStart_921807 := by decide
  rcases family_descends (prefixWord ++ tailWord_921807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_921824 : List Nat := [2, 1, 1, 3, 1, 3, 3, 3, 1, 4]
def baseStart_921824 : Nat := 118140960795 + 921824 * 2 ^ 59
def prefixEnd_921824 : Nat := 4983230072969 + 3 ^ 40 * 921824 * 2
def baseEnd_921824 : Nat := 315559193900204395373743

theorem tailTrace_921824 : CollatzResearch.WordTrace tailWord_921824 prefixEnd_921824 315559193900204395373743 := by
  unfold tailWord_921824
  simp only [CollatzResearch.WordTrace]
  refine ⟨16810841706198278925134263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22414455608264371900179017 16810841706198278925134263)
  ·
    refine ⟨25216262559297418387701395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16810841706198278925134263 25216262559297418387701395)
    ·
      refine ⟨37824393838946127581552093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25216262559297418387701395 37824393838946127581552093)
      ·
        refine ⟨14184147689604797843082035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37824393838946127581552093 14184147689604797843082035)
        ·
          refine ⟨21276221534407196764623053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14184147689604797843082035 21276221534407196764623053)
          ·
            refine ⟨7978583075402698786733645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21276221534407196764623053 7978583075402698786733645)
            ·
              refine ⟨2991968653276012045025117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7978583075402698786733645 2991968653276012045025117)
              ·
                refine ⟨1121988244978504516884419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2991968653276012045025117 1121988244978504516884419)
                ·
                  refine ⟨1682982367467756775326629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1121988244978504516884419 1682982367467756775326629)
                  ·
                    refine ⟨315559193900204395373743, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1682982367467756775326629 315559193900204395373743)
                    ·
                      rfl

theorem cell22_921824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 3, 3, 1, 4].length) (baseStart_921824 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_921824 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_921824 prefixEnd_921824 := by exact prefixLift 921824
  have htrace : WordTrace (prefixWord ++ tailWord_921824) baseStart_921824 baseEnd_921824 := by
    simpa [prefixWord, tailWord_921824, baseEnd_921824] using wordTrace_append hprefix tailTrace_921824
  have hstable : (prefixWord ++ tailWord_921824).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_921824).length < 2 ^ (prefixWord ++ tailWord_921824).sum := by decide
  have hdescent : baseEnd_921824 < baseStart_921824 := by decide
  rcases family_descends (prefixWord ++ tailWord_921824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_921839 : List Nat := [1, 1, 2, 1, 6, 2, 2, 1, 6]
def baseStart_921839 : Nat := 118140960795 + 921839 * 2 ^ 59
def prefixEnd_921839 : Nat := 4983230072969 + 3 ^ 40 * 921839 * 2
def baseEnd_921839 : Nat := 105188109568916452082899

theorem tailTrace_921839 : CollatzResearch.WordTrace tailWord_921839 prefixEnd_921839 105188109568916452082899 := by
  unfold tailWord_921839
  simp only [CollatzResearch.WordTrace]
  refine ⟨33622230507342215412064571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22414820338228143608043047 33622230507342215412064571)
  ·
    refine ⟨50433345761013323118096857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33622230507342215412064571 50433345761013323118096857)
    ·
      refine ⟨37825009320759992338572643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50433345761013323118096857 37825009320759992338572643)
      ·
        refine ⟨56737513981139988507858965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37825009320759992338572643 56737513981139988507858965)
        ·
          refine ⟨2659570967865936961305889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 56737513981139988507858965 2659570967865936961305889)
          ·
            refine ⟨1994678225899452720979417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2659570967865936961305889 1994678225899452720979417)
            ·
              refine ⟨1496008669424589540734563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1994678225899452720979417 1496008669424589540734563)
              ·
                refine ⟨2244013004136884311101845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1496008669424589540734563 2244013004136884311101845)
                ·
                  refine ⟨105188109568916452082899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2244013004136884311101845 105188109568916452082899)
                  ·
                    rfl

theorem cell22_921839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 2, 2, 1, 6].length) (baseStart_921839 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_921839 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_921839 prefixEnd_921839 := by exact prefixLift 921839
  have htrace : WordTrace (prefixWord ++ tailWord_921839) baseStart_921839 baseEnd_921839 := by
    simpa [prefixWord, tailWord_921839, baseEnd_921839] using wordTrace_append hprefix tailTrace_921839
  have hstable : (prefixWord ++ tailWord_921839).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_921839).length < 2 ^ (prefixWord ++ tailWord_921839).sum := by decide
  have hdescent : baseEnd_921839 < baseStart_921839 := by decide
  rcases family_descends (prefixWord ++ tailWord_921839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_921858 : List Nat := [3, 4, 1, 1, 2, 2, 2, 2, 1, 4]
def baseStart_921858 : Nat := 118140960795 + 921858 * 2 ^ 59
def prefixEnd_921858 : Nat := 4983230072969 + 3 ^ 40 * 921858 * 2
def baseEnd_921858 : Nat := 315570832795039640023639

theorem tailTrace_921858 : CollatzResearch.WordTrace tailWord_921858 prefixEnd_921858 315570832795039640023639 := by
  unfold tailWord_921858
  simp only [CollatzResearch.WordTrace]
  refine ⟨8405730873568345414251557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22415282329515587771337485 8405730873568345414251557)
  ·
    refine ⟨1576074538794064765172167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8405730873568345414251557 1576074538794064765172167)
    ·
      refine ⟨2364111808191097147758251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1576074538794064765172167 2364111808191097147758251)
      ·
        refine ⟨3546167712286645721637377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2364111808191097147758251 3546167712286645721637377)
        ·
          refine ⟨2659625784214984291228033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3546167712286645721637377 2659625784214984291228033)
          ·
            refine ⟨1994719338161238218421025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2659625784214984291228033 1994719338161238218421025)
            ·
              refine ⟨1496039503620928663815769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1994719338161238218421025 1496039503620928663815769)
              ·
                refine ⟨1122029627715696497861827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1496039503620928663815769 1122029627715696497861827)
                ·
                  refine ⟨1683044441573544746792741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1122029627715696497861827 1683044441573544746792741)
                  ·
                    refine ⟨315570832795039640023639, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1683044441573544746792741 315570832795039640023639)
                    ·
                      rfl

theorem cell22_921858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 2, 2, 2, 1, 4].length) (baseStart_921858 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_921858 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_921858 prefixEnd_921858 := by exact prefixLift 921858
  have htrace : WordTrace (prefixWord ++ tailWord_921858) baseStart_921858 baseEnd_921858 := by
    simpa [prefixWord, tailWord_921858, baseEnd_921858] using wordTrace_append hprefix tailTrace_921858
  have hstable : (prefixWord ++ tailWord_921858).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_921858).length < 2 ^ (prefixWord ++ tailWord_921858).sum := by decide
  have hdescent : baseEnd_921858 < baseStart_921858 := by decide
  rcases family_descends (prefixWord ++ tailWord_921858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_921867 : List Nat := [1, 1, 1, 1, 5, 2, 3, 8]
def baseStart_921867 : Nat := 118140960795 + 921867 * 2 ^ 59
def prefixEnd_921867 : Nat := 4983230072969 + 3 ^ 40 * 921867 * 2
def baseEnd_921867 : Nat := 35063768186551846283179

theorem tailTrace_921867 : CollatzResearch.WordTrace tailWord_921867 prefixEnd_921867 35063768186551846283179 := by
  unfold tailWord_921867
  simp only [CollatzResearch.WordTrace]
  refine ⟨33623251751240776194083855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22415501167493850796055903 33623251751240776194083855)
  ·
    refine ⟨50434877626861164291125783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33623251751240776194083855 50434877626861164291125783)
    ·
      refine ⟨75652316440291746436688675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50434877626861164291125783 75652316440291746436688675)
      ·
        refine ⟨113478474660437619655033013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75652316440291746436688675 113478474660437619655033013)
        ·
          refine ⟨10638606999416026842659345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 113478474660437619655033013 10638606999416026842659345)
          ·
            refine ⟨7978955249562020131994509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10638606999416026842659345 7978955249562020131994509)
            ·
              refine ⟨2992108218585757549497941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7978955249562020131994509 2992108218585757549497941)
              ·
                refine ⟨35063768186551846283179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2992108218585757549497941 35063768186551846283179)
                ·
                  rfl

theorem cell22_921867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 3, 8].length) (baseStart_921867 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_921867 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_921867 prefixEnd_921867 := by exact prefixLift 921867
  have htrace : WordTrace (prefixWord ++ tailWord_921867) baseStart_921867 baseEnd_921867 := by
    simpa [prefixWord, tailWord_921867, baseEnd_921867] using wordTrace_append hprefix tailTrace_921867
  have hstable : (prefixWord ++ tailWord_921867).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_921867).length < 2 ^ (prefixWord ++ tailWord_921867).sum := by decide
  have hdescent : baseEnd_921867 < baseStart_921867 := by decide
  rcases family_descends (prefixWord ++ tailWord_921867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_921905 : List Nat := [1, 2, 2, 3, 4, 2, 2, 1, 2, 3]
def baseStart_921905 : Nat := 118140960795 + 921905 * 2 ^ 59
def prefixEnd_921905 : Nat := 4983230072969 + 3 ^ 40 * 921905 * 2
def baseEnd_921905 : Nat := 315586921855547184098495

theorem tailTrace_921905 : CollatzResearch.WordTrace tailWord_921905 prefixEnd_921905 315586921855547184098495 := by
  unfold tailWord_921905
  simp only [CollatzResearch.WordTrace]
  refine ⟨33624637725103108683967169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22416425150068739122644779 33624637725103108683967169)
  ·
    refine ⟨25218478293827331512975377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33624637725103108683967169 25218478293827331512975377)
    ·
      refine ⟨18913858720370498634731533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25218478293827331512975377 18913858720370498634731533)
      ·
        refine ⟨7092697020138936988024325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18913858720370498634731533 7092697020138936988024325)
        ·
          refine ⟨1329880691276050685254561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7092697020138936988024325 1329880691276050685254561)
          ·
            refine ⟨997410518457038013940921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1329880691276050685254561 997410518457038013940921)
            ·
              refine ⟨748057888842778510455691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 997410518457038013940921 748057888842778510455691)
              ·
                refine ⟨1122086833264167765683537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 748057888842778510455691 1122086833264167765683537)
                ·
                  refine ⟨841565124948125824262653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1122086833264167765683537 841565124948125824262653)
                  ·
                    refine ⟨315586921855547184098495, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 841565124948125824262653 315586921855547184098495)
                    ·
                      rfl

theorem cell22_921905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 2, 2, 1, 2, 3].length) (baseStart_921905 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_921905 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_921905 prefixEnd_921905 := by exact prefixLift 921905
  have htrace : WordTrace (prefixWord ++ tailWord_921905) baseStart_921905 baseEnd_921905 := by
    simpa [prefixWord, tailWord_921905, baseEnd_921905] using wordTrace_append hprefix tailTrace_921905
  have hstable : (prefixWord ++ tailWord_921905).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_921905).length < 2 ^ (prefixWord ++ tailWord_921905).sum := by decide
  have hdescent : baseEnd_921905 < baseStart_921905 := by decide
  rcases family_descends (prefixWord ++ tailWord_921905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_921993 : List Nat := [1, 2, 1, 1, 6, 1, 4, 1, 1, 4]
def baseStart_921993 : Nat := 118140960795 + 921993 * 2 ^ 59
def prefixEnd_921993 : Nat := 4983230072969 + 3 ^ 40 * 921993 * 2
def baseEnd_921993 : Nat := 315617046053944287898225

theorem tailTrace_921993 : CollatzResearch.WordTrace tailWord_921993 prefixEnd_921993 315617046053944287898225 := by
  unfold tailWord_921993
  simp only [CollatzResearch.WordTrace]
  refine ⟨33627847348784299713170633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22418564899189533142113755 33627847348784299713170633)
  ·
    refine ⟨25220885511588224784877975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33627847348784299713170633 25220885511588224784877975)
    ·
      refine ⟨37831328267382337177316963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25220885511588224784877975 37831328267382337177316963)
      ·
        refine ⟨56746992401073505765975445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37831328267382337177316963 56746992401073505765975445)
        ·
          refine ⟨2660015268800320582780099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 56746992401073505765975445 2660015268800320582780099)
          ·
            refine ⟨3990022903200480874170149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2660015268800320582780099 3990022903200480874170149)
            ·
              refine ⟨748129294350090163906903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3990022903200480874170149 748129294350090163906903)
              ·
                refine ⟨1122193941525135245860355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 748129294350090163906903 1122193941525135245860355)
                ·
                  refine ⟨1683290912287702868790533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1122193941525135245860355 1683290912287702868790533)
                  ·
                    refine ⟨315617046053944287898225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1683290912287702868790533 315617046053944287898225)
                    ·
                      rfl

theorem cell22_921993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 4, 1, 1, 4].length) (baseStart_921993 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_921993 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_921993 prefixEnd_921993 := by exact prefixLift 921993
  have htrace : WordTrace (prefixWord ++ tailWord_921993) baseStart_921993 baseEnd_921993 := by
    simpa [prefixWord, tailWord_921993, baseEnd_921993] using wordTrace_append hprefix tailTrace_921993
  have hstable : (prefixWord ++ tailWord_921993).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_921993).length < 2 ^ (prefixWord ++ tailWord_921993).sum := by decide
  have hdescent : baseEnd_921993 < baseStart_921993 := by decide
  rcases family_descends (prefixWord ++ tailWord_921993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_922008 : List Nat := [2, 1, 2, 5, 1, 1, 2, 4, 4]
def baseStart_922008 : Nat := 118140960795 + 922008 * 2 ^ 59
def prefixEnd_922008 : Nat := 4983230072969 + 3 ^ 40 * 922008 * 2
def baseEnd_922008 : Nat := 105207393620163082924393

theorem tailTrace_922008 : CollatzResearch.WordTrace tailWord_922008 prefixEnd_922008 105207393620163082924393 := by
  unfold tailWord_922008
  simp only [CollatzResearch.WordTrace]
  refine ⟨16814197221864978637483339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22418929629153304849977785 16814197221864978637483339)
  ·
    refine ⟨25221295832797467956225009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16814197221864978637483339 25221295832797467956225009)
    ·
      refine ⟨18915971874598100967168757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25221295832797467956225009 18915971874598100967168757)
      ·
        refine ⟨1773372363243571965672071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 18915971874598100967168757 1773372363243571965672071)
        ·
          refine ⟨2660058544865357948508107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1773372363243571965672071 2660058544865357948508107)
          ·
            refine ⟨3990087817298036922762161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2660058544865357948508107 3990087817298036922762161)
            ·
              refine ⟨2992565862973527692071621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3990087817298036922762161 2992565862973527692071621)
              ·
                refine ⟨561106099307536442263429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2992565862973527692071621 561106099307536442263429)
                ·
                  refine ⟨105207393620163082924393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 561106099307536442263429 105207393620163082924393)
                  ·
                    rfl

theorem cell22_922008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 2, 4, 4].length) (baseStart_922008 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_922008 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_922008 prefixEnd_922008 := by exact prefixLift 922008
  have htrace : WordTrace (prefixWord ++ tailWord_922008) baseStart_922008 baseEnd_922008 := by
    simpa [prefixWord, tailWord_922008, baseEnd_922008] using wordTrace_append hprefix tailTrace_922008
  have hstable : (prefixWord ++ tailWord_922008).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_922008).length < 2 ^ (prefixWord ++ tailWord_922008).sum := by decide
  have hdescent : baseEnd_922008 < baseStart_922008 := by decide
  rcases family_descends (prefixWord ++ tailWord_922008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_922023 : List Nat := [1, 1, 6, 1, 1, 4, 1, 1, 1, 5]
def baseStart_922023 : Nat := 118140960795 + 922023 * 2 ^ 59
def prefixEnd_922023 : Nat := 4983230072969 + 3 ^ 40 * 922023 * 2
def baseEnd_922023 : Nat := 315627315667034209648133

theorem tailTrace_922023 : CollatzResearch.WordTrace tailWord_922023 prefixEnd_922023 315627315667034209648133 := by
  unfold tailWord_922023
  simp only [CollatzResearch.WordTrace]
  refine ⟨33628941538675614836762723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22419294359117076557841815 33628941538675614836762723)
  ·
    refine ⟨50443412308013422255144085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33628941538675614836762723 50443412308013422255144085)
    ·
      refine ⟨2364534951938129168209879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 50443412308013422255144085 2364534951938129168209879)
      ·
        refine ⟨3546802427907193752314819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2364534951938129168209879 3546802427907193752314819)
        ·
          refine ⟨5320203641860790628472229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3546802427907193752314819 5320203641860790628472229)
          ·
            refine ⟨997538182848898242838543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5320203641860790628472229 997538182848898242838543)
            ·
              refine ⟨1496307274273347364257815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 997538182848898242838543 1496307274273347364257815)
              ·
                refine ⟨2244460911410021046386723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1496307274273347364257815 2244460911410021046386723)
                ·
                  refine ⟨3366691367115031569580085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2244460911410021046386723 3366691367115031569580085)
                  ·
                    refine ⟨315627315667034209648133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3366691367115031569580085 315627315667034209648133)
                    ·
                      rfl

theorem cell22_922023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 4, 1, 1, 1, 5].length) (baseStart_922023 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_922023 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_922023 prefixEnd_922023 := by exact prefixLift 922023
  have htrace : WordTrace (prefixWord ++ tailWord_922023) baseStart_922023 baseEnd_922023 := by
    simpa [prefixWord, tailWord_922023, baseEnd_922023] using wordTrace_append hprefix tailTrace_922023
  have hstable : (prefixWord ++ tailWord_922023).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_922023).length < 2 ^ (prefixWord ++ tailWord_922023).sum := by decide
  have hdescent : baseEnd_922023 < baseStart_922023 := by decide
  rcases family_descends (prefixWord ++ tailWord_922023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_922034 : List Nat := [3, 2, 1, 1, 1, 1, 3, 1, 2, 7]
def baseStart_922034 : Nat := 118140960795 + 922034 * 2 ^ 59
def prefixEnd_922034 : Nat := 4983230072969 + 3 ^ 40 * 922034 * 2
def baseEnd_922034 : Nat := 315631081191833847623099

theorem tailTrace_922034 : CollatzResearch.WordTrace tailWord_922034 prefixEnd_922034 315631081191833847623099 := by
  unfold tailWord_922034
  simp only [CollatzResearch.WordTrace]
  refine ⟨8407335685408940928853289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22419561827757175810275437 8407335685408940928853289)
  ·
    refine ⟨6305501764056705696639967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8407335685408940928853289 6305501764056705696639967)
    ·
      refine ⟨9458252646085058544959951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6305501764056705696639967 9458252646085058544959951)
      ·
        refine ⟨14187378969127587817439927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9458252646085058544959951 14187378969127587817439927)
        ·
          refine ⟨21281068453691381726159891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14187378969127587817439927 21281068453691381726159891)
          ·
            refine ⟨31921602680537072589239837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21281068453691381726159891 31921602680537072589239837)
            ·
              refine ⟨11970601005201402220964939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31921602680537072589239837 11970601005201402220964939)
              ·
                refine ⟨17955901507802103331447409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11970601005201402220964939 17955901507802103331447409)
                ·
                  refine ⟨13466926130851577498585557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17955901507802103331447409 13466926130851577498585557)
                  ·
                    refine ⟨315631081191833847623099, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 13466926130851577498585557 315631081191833847623099)
                    ·
                      rfl

theorem cell22_922034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 3, 1, 2, 7].length) (baseStart_922034 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_922034 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_922034 prefixEnd_922034 := by exact prefixLift 922034
  have htrace : WordTrace (prefixWord ++ tailWord_922034) baseStart_922034 baseEnd_922034 := by
    simpa [prefixWord, tailWord_922034, baseEnd_922034] using wordTrace_append hprefix tailTrace_922034
  have hstable : (prefixWord ++ tailWord_922034).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_922034).length < 2 ^ (prefixWord ++ tailWord_922034).sum := by decide
  have hdescent : baseEnd_922034 < baseStart_922034 := by decide
  rcases family_descends (prefixWord ++ tailWord_922034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_922081 : List Nat := [1, 2, 3, 1, 2, 2, 3, 3, 5]
def baseStart_922081 : Nat := 118140960795 + 922081 * 2 ^ 59
def prefixEnd_922081 : Nat := 4983230072969 + 3 ^ 40 * 922081 * 2
def baseEnd_922081 : Nat := 105215723417447130565985

theorem tailTrace_922081 : CollatzResearch.WordTrace tailWord_922081 prefixEnd_922081 105215723417447130565985 := by
  unfold tailWord_922081
  simp only [CollatzResearch.WordTrace]
  refine ⟨33631056972465490742374097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22420704648310327161582731 33631056972465490742374097)
  ·
    refine ⟨25223292729349118056780573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33631056972465490742374097 25223292729349118056780573)
    ·
      refine ⟨9458734773505919271292715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25223292729349118056780573 9458734773505919271292715)
      ·
        refine ⟨14188102160258878906939073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9458734773505919271292715 14188102160258878906939073)
        ·
          refine ⟨10641076620194159180204305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14188102160258878906939073 10641076620194159180204305)
          ·
            refine ⟨7980807465145619385153229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10641076620194159180204305 7980807465145619385153229)
            ·
              refine ⟨2992802799429607269432461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7980807465145619385153229 2992802799429607269432461)
              ·
                refine ⟨1122301049786102726037173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2992802799429607269432461 1122301049786102726037173)
                ·
                  refine ⟨105215723417447130565985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1122301049786102726037173 105215723417447130565985)
                  ·
                    rfl

theorem cell22_922081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 3, 3, 5].length) (baseStart_922081 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_922081 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_922081 prefixEnd_922081 := by exact prefixLift 922081
  have htrace : WordTrace (prefixWord ++ tailWord_922081) baseStart_922081 baseEnd_922081 := by
    simpa [prefixWord, tailWord_922081, baseEnd_922081] using wordTrace_append hprefix tailTrace_922081
  have hstable : (prefixWord ++ tailWord_922081).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_922081).length < 2 ^ (prefixWord ++ tailWord_922081).sum := by decide
  have hdescent : baseEnd_922081 < baseStart_922081 := by decide
  rcases family_descends (prefixWord ++ tailWord_922081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_922119 : List Nat := [1, 1, 4, 3, 3, 2, 2, 2, 1, 3]
def baseStart_922119 : Nat := 118140960795 + 922119 * 2 ^ 59
def prefixEnd_922119 : Nat := 4983230072969 + 3 ^ 40 * 922119 * 2
def baseEnd_922119 : Nat := 315660178428921959247839

theorem tailTrace_922119 : CollatzResearch.WordTrace tailWord_922119 prefixEnd_922119 315660178428921959247839 := by
  unfold tailWord_922119
  simp only [CollatzResearch.WordTrace]
  refine ⟨33632442946327823232257411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22421628630885215488171607 33632442946327823232257411)
  ·
    refine ⟨50448664419491734848386117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33632442946327823232257411 50448664419491734848386117)
    ·
      refine ⟨9459124578654700284072397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 50448664419491734848386117 9459124578654700284072397)
      ·
        refine ⟨3547171716995512606527149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9459124578654700284072397 3547171716995512606527149)
        ·
          refine ⟨1330189393873317227447681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3547171716995512606527149 1330189393873317227447681)
          ·
            refine ⟨997642045404987920585761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1330189393873317227447681 997642045404987920585761)
            ·
              refine ⟨748231534053740940439321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 997642045404987920585761 748231534053740940439321)
              ·
                refine ⟨561173650540305705329491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 748231534053740940439321 561173650540305705329491)
                ·
                  refine ⟨841760475810458557994237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 561173650540305705329491 841760475810458557994237)
                  ·
                    refine ⟨315660178428921959247839, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 841760475810458557994237 315660178428921959247839)
                    ·
                      rfl

theorem cell22_922119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 2, 2, 2, 1, 3].length) (baseStart_922119 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_922119 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_922119 prefixEnd_922119 := by exact prefixLift 922119
  have htrace : WordTrace (prefixWord ++ tailWord_922119) baseStart_922119 baseEnd_922119 := by
    simpa [prefixWord, tailWord_922119, baseEnd_922119] using wordTrace_append hprefix tailTrace_922119
  have hstable : (prefixWord ++ tailWord_922119).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_922119).length < 2 ^ (prefixWord ++ tailWord_922119).sum := by decide
  have hdescent : baseEnd_922119 < baseStart_922119 := by decide
  rcases family_descends (prefixWord ++ tailWord_922119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_922231 : List Nat := [1, 1, 3, 1, 1, 3, 2, 1, 4, 5]
def baseStart_922231 : Nat := 118140960795 + 922231 * 2 ^ 59
def prefixEnd_922231 : Nat := 4983230072969 + 3 ^ 40 * 922231 * 2
def baseEnd_922231 : Nat := 315698518317791000447495

theorem tailTrace_922231 : CollatzResearch.WordTrace tailWord_922231 prefixEnd_922231 315698518317791000447495 := by
  unfold tailWord_922231
  simp only [CollatzResearch.WordTrace]
  refine ⟨33636527921922066360334547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22424351947948044240223031 33636527921922066360334547)
  ·
    refine ⟨50454791882883099540501821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33636527921922066360334547 50454791882883099540501821)
    ·
      refine ⟨18920546956081162327688183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50454791882883099540501821 18920546956081162327688183)
      ·
        refine ⟨28380820434121743491532275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18920546956081162327688183 28380820434121743491532275)
        ·
          refine ⟨42571230651182615237298413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28380820434121743491532275 42571230651182615237298413)
          ·
            refine ⟨15964211494193480713986905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42571230651182615237298413 15964211494193480713986905)
            ·
              refine ⟨11973158620645110535490179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15964211494193480713986905 11973158620645110535490179)
              ·
                refine ⟨17959737930967665803235269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11973158620645110535490179 17959737930967665803235269)
                ·
                  refine ⟨3367450862056437338106613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17959737930967665803235269 3367450862056437338106613)
                  ·
                    refine ⟨315698518317791000447495, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3367450862056437338106613 315698518317791000447495)
                    ·
                      rfl

theorem cell22_922231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 2, 1, 4, 5].length) (baseStart_922231 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_922231 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_922231 prefixEnd_922231 := by exact prefixLift 922231
  have htrace : WordTrace (prefixWord ++ tailWord_922231) baseStart_922231 baseEnd_922231 := by
    simpa [prefixWord, tailWord_922231, baseEnd_922231] using wordTrace_append hprefix tailTrace_922231
  have hstable : (prefixWord ++ tailWord_922231).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_922231).length < 2 ^ (prefixWord ++ tailWord_922231).sum := by decide
  have hdescent : baseEnd_922231 < baseStart_922231 := by decide
  rcases family_descends (prefixWord ++ tailWord_922231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_922237 : List Nat := [1, 4, 1, 1, 5, 2, 1, 1, 3, 3]
def baseStart_922237 : Nat := 118140960795 + 922237 * 2 ^ 59
def prefixEnd_922237 : Nat := 4983230072969 + 3 ^ 40 * 922237 * 2
def baseEnd_922237 : Nat := 315700572240408984797477

theorem tailTrace_922237 : CollatzResearch.WordTrace tailWord_922237 prefixEnd_922237 315700572240408984797477 := by
  unfold tailWord_922237
  simp only [CollatzResearch.WordTrace]
  refine ⟨33636746759900329385052965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22424497839933552923368643 33636746759900329385052965)
  ·
    refine ⟨6306890017481311759697431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 33636746759900329385052965 6306890017481311759697431)
    ·
      refine ⟨9460335026221967639546147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6306890017481311759697431 9460335026221967639546147)
      ·
        refine ⟨14190502539332951459319221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9460335026221967639546147 14190502539332951459319221)
        ·
          refine ⟨1330359613062464199311177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 14190502539332951459319221 1330359613062464199311177)
          ·
            refine ⟨997769709796848149483383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1330359613062464199311177 997769709796848149483383)
            ·
              refine ⟨1496654564695272224225075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 997769709796848149483383 1496654564695272224225075)
              ·
                refine ⟨2244981847042908336337613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1496654564695272224225075 2244981847042908336337613)
                ·
                  refine ⟨841868192641090626126605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2244981847042908336337613 841868192641090626126605)
                  ·
                    refine ⟨315700572240408984797477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 841868192641090626126605 315700572240408984797477)
                    ·
                      rfl

theorem cell22_922237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 2, 1, 1, 3, 3].length) (baseStart_922237 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_922237 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_922237 prefixEnd_922237 := by exact prefixLift 922237
  have htrace : WordTrace (prefixWord ++ tailWord_922237) baseStart_922237 baseEnd_922237 := by
    simpa [prefixWord, tailWord_922237, baseEnd_922237] using wordTrace_append hprefix tailTrace_922237
  have hstable : (prefixWord ++ tailWord_922237).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_922237).length < 2 ^ (prefixWord ++ tailWord_922237).sum := by decide
  have hdescent : baseEnd_922237 < baseStart_922237 := by decide
  rcases family_descends (prefixWord ++ tailWord_922237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_922250 : List Nat := [3, 1, 2, 3, 3, 1, 1, 3, 5]
def baseStart_922250 : Nat := 118140960795 + 922250 * 2 ^ 59
def prefixEnd_922250 : Nat := 4983230072969 + 3 ^ 40 * 922250 * 2
def baseEnd_922250 : Nat := 105235007468693761407479

theorem tailTrace_922250 : CollatzResearch.WordTrace tailWord_922250 prefixEnd_922250 105235007468693761407479 := by
  unfold tailWord_922250
  simp only [CollatzResearch.WordTrace]
  refine ⟨8409305227213308151319051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22424813939235488403517469 8409305227213308151319051)
  ·
    refine ⟨12613957840819962226978577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8409305227213308151319051 12613957840819962226978577)
    ·
      refine ⟨9460468380614971670233933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12613957840819962226978577 9460468380614971670233933)
      ·
        refine ⟨3547675642730614376337725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9460468380614971670233933 3547675642730614376337725)
        ·
          refine ⟨1330378366023980391126647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3547675642730614376337725 1330378366023980391126647)
          ·
            refine ⟨1995567549035970586689971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1330378366023980391126647 1995567549035970586689971)
            ·
              refine ⟨2993351323553955880034957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1995567549035970586689971 2993351323553955880034957)
              ·
                refine ⟨1122506746332733455013109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2993351323553955880034957 1122506746332733455013109)
                ·
                  refine ⟨105235007468693761407479, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1122506746332733455013109 105235007468693761407479)
                  ·
                    rfl

theorem cell22_922250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 1, 1, 3, 5].length) (baseStart_922250 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_922250 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_922250 prefixEnd_922250 := by exact prefixLift 922250
  have htrace : WordTrace (prefixWord ++ tailWord_922250) baseStart_922250 baseEnd_922250 := by
    simpa [prefixWord, tailWord_922250, baseEnd_922250] using wordTrace_append hprefix tailTrace_922250
  have hstable : (prefixWord ++ tailWord_922250).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_922250).length < 2 ^ (prefixWord ++ tailWord_922250).sum := by decide
  have hdescent : baseEnd_922250 < baseStart_922250 := by decide
  rcases family_descends (prefixWord ++ tailWord_922250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_922263 : List Nat := [1, 1, 3, 3, 2, 1, 3, 1, 3, 4]
def baseStart_922263 : Nat := 118140960795 + 922263 * 2 ^ 59
def prefixEnd_922263 : Nat := 4983230072969 + 3 ^ 40 * 922263 * 2
def baseEnd_922263 : Nat := 315709472571753583647397

theorem tailTrace_922263 : CollatzResearch.WordTrace tailWord_922263 prefixEnd_922263 315709472571753583647397 := by
  unfold tailWord_922263
  simp only [CollatzResearch.WordTrace]
  refine ⟨33637695057806135825499443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22425130038537423883666295 33637695057806135825499443)
  ·
    refine ⟨50456542586709203738249165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33637695057806135825499443 50456542586709203738249165)
    ·
      refine ⟨18921203470015951401843437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50456542586709203738249165 18921203470015951401843437)
      ·
        refine ⟨7095451301255981775691289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18921203470015951401843437 7095451301255981775691289)
        ·
          refine ⟨5321588475941986331768467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7095451301255981775691289 5321588475941986331768467)
          ·
            refine ⟨7982382713912979497652701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5321588475941986331768467 7982382713912979497652701)
            ·
              refine ⟨2993393517717367311619763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7982382713912979497652701 2993393517717367311619763)
              ·
                refine ⟨4490090276576050967429645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2993393517717367311619763 4490090276576050967429645)
                ·
                  refine ⟨1683783853716019112786117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4490090276576050967429645 1683783853716019112786117)
                  ·
                    refine ⟨315709472571753583647397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1683783853716019112786117 315709472571753583647397)
                    ·
                      rfl

theorem cell22_922263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 3, 1, 3, 4].length) (baseStart_922263 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_922263 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_922263 prefixEnd_922263 := by exact prefixLift 922263
  have htrace : WordTrace (prefixWord ++ tailWord_922263) baseStart_922263 baseEnd_922263 := by
    simpa [prefixWord, tailWord_922263, baseEnd_922263] using wordTrace_append hprefix tailTrace_922263
  have hstable : (prefixWord ++ tailWord_922263).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_922263).length < 2 ^ (prefixWord ++ tailWord_922263).sum := by decide
  have hdescent : baseEnd_922263 < baseStart_922263 := by decide
  rcases family_descends (prefixWord ++ tailWord_922263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_922344 : List Nat := [2, 1, 4, 1, 4, 2, 1, 2, 2, 3]
def baseStart_922344 : Nat := 118140960795 + 922344 * 2 ^ 59
def prefixEnd_922344 : Nat := 4983230072969 + 3 ^ 40 * 922344 * 2
def baseEnd_922344 : Nat := 315737200527096372372149

theorem tailTrace_922344 : CollatzResearch.WordTrace tailWord_922344 prefixEnd_922344 315737200527096372372149 := by
  unfold tailWord_922344
  simp only [CollatzResearch.WordTrace]
  refine ⟨16820324685256343329599043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22427099580341791106132057 16820324685256343329599043)
  ·
    refine ⟨25230487027884514994398565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16820324685256343329599043 25230487027884514994398565)
    ·
      refine ⟨4730716317728346561449731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25230487027884514994398565 4730716317728346561449731)
      ·
        refine ⟨7096074476592519842174597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4730716317728346561449731 7096074476592519842174597)
        ·
          refine ⟨1330513964361097470407737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7096074476592519842174597 1330513964361097470407737)
          ·
            refine ⟨997885473270823102805803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1330513964361097470407737 997885473270823102805803)
            ·
              refine ⟨1496828209906234654208705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 997885473270823102805803 1496828209906234654208705)
              ·
                refine ⟨1122621157429675990656529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1496828209906234654208705 1122621157429675990656529)
                ·
                  refine ⟨841965868072256992992397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1122621157429675990656529 841965868072256992992397)
                  ·
                    refine ⟨315737200527096372372149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 841965868072256992992397 315737200527096372372149)
                    ·
                      rfl

theorem cell22_922344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 2, 1, 2, 2, 3].length) (baseStart_922344 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_922344 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_922344 prefixEnd_922344 := by exact prefixLift 922344
  have htrace : WordTrace (prefixWord ++ tailWord_922344) baseStart_922344 baseEnd_922344 := by
    simpa [prefixWord, tailWord_922344, baseEnd_922344] using wordTrace_append hprefix tailTrace_922344
  have hstable : (prefixWord ++ tailWord_922344).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_922344).length < 2 ^ (prefixWord ++ tailWord_922344).sum := by decide
  have hdescent : baseEnd_922344 < baseStart_922344 := by decide
  rcases family_descends (prefixWord ++ tailWord_922344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_922449 : List Nat := [1, 2, 2, 1, 6, 1, 3, 1, 1, 4]
def baseStart_922449 : Nat := 118140960795 + 922449 * 2 ^ 59
def prefixEnd_922449 : Nat := 4983230072969 + 3 ^ 40 * 922449 * 2
def baseEnd_922449 : Nat := 315773144172911098496827

theorem tailTrace_922449 : CollatzResearch.WordTrace tailWord_922449 prefixEnd_922449 315773144172911098496827 := by
  unfold tailWord_922449
  simp only [CollatzResearch.WordTrace]
  refine ⟨33644479035132289591770401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22429652690088193061180267 33644479035132289591770401)
  ·
    refine ⟨25233359276349217193827801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33644479035132289591770401 25233359276349217193827801)
    ·
      refine ⟨18925019457261912895370851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25233359276349217193827801 18925019457261912895370851)
      ·
        refine ⟨28387529185892869343056277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18925019457261912895370851 28387529185892869343056277)
        ·
          refine ⟨1330665430588728250455763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 28387529185892869343056277 1330665430588728250455763)
          ·
            refine ⟨1995998145883092375683645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1330665430588728250455763 1995998145883092375683645)
            ·
              refine ⟨748499304706159640881367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1995998145883092375683645 748499304706159640881367)
              ·
                refine ⟨1122748957059239461322051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 748499304706159640881367 1122748957059239461322051)
                ·
                  refine ⟨1684123435588859191983077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1122748957059239461322051 1684123435588859191983077)
                  ·
                    refine ⟨315773144172911098496827, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1684123435588859191983077 315773144172911098496827)
                    ·
                      rfl

theorem cell22_922449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 1, 3, 1, 1, 4].length) (baseStart_922449 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_922449 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_922449 prefixEnd_922449 := by exact prefixLift 922449
  have htrace : WordTrace (prefixWord ++ tailWord_922449) baseStart_922449 baseEnd_922449 := by
    simpa [prefixWord, tailWord_922449, baseEnd_922449] using wordTrace_append hprefix tailTrace_922449
  have hstable : (prefixWord ++ tailWord_922449).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_922449).length < 2 ^ (prefixWord ++ tailWord_922449).sum := by decide
  have hdescent : baseEnd_922449 < baseStart_922449 := by decide
  rcases family_descends (prefixWord ++ tailWord_922449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_922458 : List Nat := [3, 1, 1, 2, 1, 14]
def baseStart_922458 : Nat := 118140960795 + 922458 * 2 ^ 59
def prefixEnd_922458 : Nat := 4983230072969 + 3 ^ 40 * 922458 * 2
def baseEnd_922458 : Nat := 3898471914281951543479

theorem tailTrace_922458 : CollatzResearch.WordTrace tailWord_922458 prefixEnd_922458 3898471914281951543479 := by
  unfold tailWord_922458
  simp only [CollatzResearch.WordTrace]
  refine ⟨8411201823024921032212007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22429871528066456085898685 8411201823024921032212007)
  ·
    refine ⟨12616802734537381548318011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8411201823024921032212007 12616802734537381548318011)
    ·
      refine ⟨18925204101806072322477017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12616802734537381548318011 18925204101806072322477017)
      ·
        refine ⟨14193903076354554241857763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18925204101806072322477017 14193903076354554241857763)
        ·
          refine ⟨21290854614531831362786645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14193903076354554241857763 21290854614531831362786645)
          ·
            refine ⟨3898471914281951543479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 14 21290854614531831362786645 3898471914281951543479)
            ·
              rfl

theorem cell22_922458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 14].length) (baseStart_922458 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_922458 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_922458 prefixEnd_922458 := by exact prefixLift 922458
  have htrace : WordTrace (prefixWord ++ tailWord_922458) baseStart_922458 baseEnd_922458 := by
    simpa [prefixWord, tailWord_922458, baseEnd_922458] using wordTrace_append hprefix tailTrace_922458
  have hstable : (prefixWord ++ tailWord_922458).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_922458).length < 2 ^ (prefixWord ++ tailWord_922458).sum := by decide
  have hdescent : baseEnd_922458 < baseStart_922458 := by decide
  rcases family_descends (prefixWord ++ tailWord_922458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_922473 : List Nat := [1, 2, 1, 1, 1, 3, 1, 1, 4, 7]
def baseStart_922473 : Nat := 118140960795 + 922473 * 2 ^ 59
def prefixEnd_922473 : Nat := 4983230072969 + 3 ^ 40 * 922473 * 2
def baseEnd_922473 : Nat := 315781359863383035896753

theorem tailTrace_922473 : CollatzResearch.WordTrace tailWord_922473 prefixEnd_922473 315781359863383035896753 := by
  unfold tailWord_922473
  simp only [CollatzResearch.WordTrace]
  refine ⟨33645354387045341690644073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22430236258030227793762715 33645354387045341690644073)
  ·
    refine ⟨25234015790284006267983055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33645354387045341690644073 25234015790284006267983055)
    ·
      refine ⟨37851023685426009401974583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25234015790284006267983055 37851023685426009401974583)
      ·
        refine ⟨56776535528139014102961875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37851023685426009401974583 56776535528139014102961875)
        ·
          refine ⟨85164803292208521154442813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56776535528139014102961875 85164803292208521154442813)
          ·
            refine ⟨31936801234578195432916055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 85164803292208521154442813 31936801234578195432916055)
            ·
              refine ⟨47905201851867293149374083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31936801234578195432916055 47905201851867293149374083)
              ·
                refine ⟨71857802777800939724061125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47905201851867293149374083 71857802777800939724061125)
                ·
                  refine ⟨13473338020837676198261461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 71857802777800939724061125 13473338020837676198261461)
                  ·
                    refine ⟨315781359863383035896753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 13473338020837676198261461 315781359863383035896753)
                    ·
                      rfl

theorem cell22_922473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 1, 4, 7].length) (baseStart_922473 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_922473 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_922473 prefixEnd_922473 := by exact prefixLift 922473
  have htrace : WordTrace (prefixWord ++ tailWord_922473) baseStart_922473 baseEnd_922473 := by
    simpa [prefixWord, tailWord_922473, baseEnd_922473] using wordTrace_append hprefix tailTrace_922473
  have hstable : (prefixWord ++ tailWord_922473).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_922473).length < 2 ^ (prefixWord ++ tailWord_922473).sum := by decide
  have hdescent : baseEnd_922473 < baseStart_922473 := by decide
  rcases family_descends (prefixWord ++ tailWord_922473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_922494 : List Nat := [4, 2, 3, 1, 2, 1, 1, 1, 1, 6]
def baseStart_922494 : Nat := 118140960795 + 922494 * 2 ^ 59
def prefixEnd_922494 : Nat := 4983230072969 + 3 ^ 40 * 922494 * 2
def baseEnd_922494 : Nat := 315788548592545981121689

theorem tailTrace_922494 : CollatzResearch.WordTrace tailWord_922494 prefixEnd_922494 315788548592545981121689 := by
  unfold tailWord_922494
  simp only [CollatzResearch.WordTrace]
  refine ⟨4205765039996157784644817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22430746879979508184772357 4205765039996157784644817)
  ·
    refine ⟨3154323779997118338483613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4205765039996157784644817 3154323779997118338483613)
    ·
      refine ⟨1182871417498919376931355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3154323779997118338483613 1182871417498919376931355)
      ·
        refine ⟨1774307126248379065397033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1182871417498919376931355 1774307126248379065397033)
        ·
          refine ⟨1330730344686284299047775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1774307126248379065397033 1330730344686284299047775)
          ·
            refine ⟨1996095517029426448571663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1330730344686284299047775 1996095517029426448571663)
            ·
              refine ⟨2994143275544139672857495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1996095517029426448571663 2994143275544139672857495)
              ·
                refine ⟨4491214913316209509286243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2994143275544139672857495 4491214913316209509286243)
                ·
                  refine ⟨6736822369974314263929365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4491214913316209509286243 6736822369974314263929365)
                  ·
                    refine ⟨315788548592545981121689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6736822369974314263929365 315788548592545981121689)
                    ·
                      rfl

theorem cell22_922494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 1, 1, 1, 1, 6].length) (baseStart_922494 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_922494 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_922494 prefixEnd_922494 := by exact prefixLift 922494
  have htrace : WordTrace (prefixWord ++ tailWord_922494) baseStart_922494 baseEnd_922494 := by
    simpa [prefixWord, tailWord_922494, baseEnd_922494] using wordTrace_append hprefix tailTrace_922494
  have hstable : (prefixWord ++ tailWord_922494).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_922494).length < 2 ^ (prefixWord ++ tailWord_922494).sum := by decide
  have hdescent : baseEnd_922494 < baseStart_922494 := by decide
  rcases family_descends (prefixWord ++ tailWord_922494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_922498 : List Nat := [3, 4, 2, 2, 1, 1, 2, 3, 4]
def baseStart_922498 : Nat := 118140960795 + 922498 * 2 ^ 59
def prefixEnd_922498 : Nat := 4983230072969 + 3 ^ 40 * 922498 * 2
def baseEnd_922498 : Nat := 105263305958097101340559

theorem tailTrace_922498 : CollatzResearch.WordTrace tailWord_922498 prefixEnd_922498 105263305958097101340559 := by
  unfold tailWord_922498
  simp only [CollatzResearch.WordTrace]
  refine ⟨8411566552988692740076037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22430844141303180640202765 8411566552988692740076037)
  ·
    refine ⟨1577168728685379888764257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8411566552988692740076037 1577168728685379888764257)
    ·
      refine ⟨1182876546514034916573193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1577168728685379888764257 1182876546514034916573193)
      ·
        refine ⟨887157409885526187429895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1182876546514034916573193 887157409885526187429895)
        ·
          refine ⟨1330736114828289281144843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 887157409885526187429895 1330736114828289281144843)
          ·
            refine ⟨1996104172242433921717265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1330736114828289281144843 1996104172242433921717265)
            ·
              refine ⟨1497078129181825441287949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1996104172242433921717265 1497078129181825441287949)
              ·
                refine ⟨561404298443184540482981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1497078129181825441287949 561404298443184540482981)
                ·
                  refine ⟨105263305958097101340559, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 561404298443184540482981 105263305958097101340559)
                  ·
                    rfl

theorem cell22_922498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 1, 2, 3, 4].length) (baseStart_922498 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_922498 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_922498 prefixEnd_922498 := by exact prefixLift 922498
  have htrace : WordTrace (prefixWord ++ tailWord_922498) baseStart_922498 baseEnd_922498 := by
    simpa [prefixWord, tailWord_922498, baseEnd_922498] using wordTrace_append hprefix tailTrace_922498
  have hstable : (prefixWord ++ tailWord_922498).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_922498).length < 2 ^ (prefixWord ++ tailWord_922498).sum := by decide
  have hdescent : baseEnd_922498 < baseStart_922498 := by decide
  rcases family_descends (prefixWord ++ tailWord_922498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_922537 : List Nat := [1, 2, 1, 1, 1, 1, 9, 1, 5]
def baseStart_922537 : Nat := 118140960795 + 922537 * 2 ^ 59
def prefixEnd_922537 : Nat := 4983230072969 + 3 ^ 40 * 922537 * 2
def baseEnd_922537 : Nat := 105267756123769400765519

theorem tailTrace_922537 : CollatzResearch.WordTrace tailWord_922537 prefixEnd_922537 105267756123769400765519 := by
  unfold tailWord_922537
  simp only [CollatzResearch.WordTrace]
  refine ⟨33647688658813480620973865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22431792439208987080649243 33647688658813480620973865)
  ·
    refine ⟨25235766494110110465730399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33647688658813480620973865 25235766494110110465730399)
    ·
      refine ⟨37853649741165165698595599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25235766494110110465730399 37853649741165165698595599)
      ·
        refine ⟨56780474611747748547893399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37853649741165165698595599 56780474611747748547893399)
        ·
          refine ⟨85170711917621622821840099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56780474611747748547893399 85170711917621622821840099)
          ·
            refine ⟨127756067876432434232760149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85170711917621622821840099 127756067876432434232760149)
            ·
              refine ⟨748570710213471294332579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 127756067876432434232760149 748570710213471294332579)
              ·
                refine ⟨1122856065320206941498869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 748570710213471294332579 1122856065320206941498869)
                ·
                  refine ⟨105267756123769400765519, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1122856065320206941498869 105267756123769400765519)
                  ·
                    rfl

theorem cell22_922537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 9, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 9, 1, 5].length) (baseStart_922537 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_922537 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_922537 prefixEnd_922537 := by exact prefixLift 922537
  have htrace : WordTrace (prefixWord ++ tailWord_922537) baseStart_922537 baseEnd_922537 := by
    simpa [prefixWord, tailWord_922537, baseEnd_922537] using wordTrace_append hprefix tailTrace_922537
  have hstable : (prefixWord ++ tailWord_922537).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_922537).length < 2 ^ (prefixWord ++ tailWord_922537).sum := by decide
  have hdescent : baseEnd_922537 < baseStart_922537 := by decide
  rcases family_descends (prefixWord ++ tailWord_922537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_922567 : List Nat := [1, 1, 4, 1, 1, 2, 4, 3, 1, 4]
def baseStart_922567 : Nat := 118140960795 + 922567 * 2 ^ 59
def prefixEnd_922567 : Nat := 4983230072969 + 3 ^ 40 * 922567 * 2
def baseEnd_922567 : Nat := 315813537984398124046465

theorem tailTrace_922567 : CollatzResearch.WordTrace tailWord_922567 prefixEnd_922567 315813537984398124046465 := by
  unfold tailWord_922567
  simp only [CollatzResearch.WordTrace]
  refine ⟨33648782848704795744565955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22432521899136530496377303 33648782848704795744565955)
  ·
    refine ⟨50473174273057193616848933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33648782848704795744565955 50473174273057193616848933)
    ·
      refine ⟨9463720176198223803159175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 50473174273057193616848933 9463720176198223803159175)
      ·
        refine ⟨14195580264297335704738763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9463720176198223803159175 14195580264297335704738763)
        ·
          refine ⟨21293370396446003557108145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14195580264297335704738763 21293370396446003557108145)
          ·
            refine ⟨15970027797334502667831109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21293370396446003557108145 15970027797334502667831109)
            ·
              refine ⟨2994380212000219250218333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15970027797334502667831109 2994380212000219250218333)
              ·
                refine ⟨1122892579500082218831875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2994380212000219250218333 1122892579500082218831875)
                ·
                  refine ⟨1684338869250123328247813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1122892579500082218831875 1684338869250123328247813)
                  ·
                    refine ⟨315813537984398124046465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1684338869250123328247813 315813537984398124046465)
                    ·
                      rfl

theorem cell22_922567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 4, 3, 1, 4].length) (baseStart_922567 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_922567 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_922567 prefixEnd_922567 := by exact prefixLift 922567
  have htrace : WordTrace (prefixWord ++ tailWord_922567) baseStart_922567 baseEnd_922567 := by
    simpa [prefixWord, tailWord_922567, baseEnd_922567] using wordTrace_append hprefix tailTrace_922567
  have hstable : (prefixWord ++ tailWord_922567).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_922567).length < 2 ^ (prefixWord ++ tailWord_922567).sum := by decide
  have hdescent : baseEnd_922567 < baseStart_922567 := by decide
  rcases family_descends (prefixWord ++ tailWord_922567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_922614 : List Nat := [5, 1, 1, 1, 3, 2, 1, 2, 1, 5]
def baseStart_922614 : Nat := 118140960795 + 922614 * 2 ^ 59
def prefixEnd_922614 : Nat := 4983230072969 + 3 ^ 40 * 922614 * 2
def baseEnd_922614 : Nat := 315829627044905668121321

theorem tailTrace_922614 : CollatzResearch.WordTrace tailWord_922614 prefixEnd_922614 315829627044905668121321 := by
  unfold tailWord_922614
  simp only [CollatzResearch.WordTrace]
  refine ⟨2103156067470907673220431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 22433664719689681847684597 2103156067470907673220431)
  ·
    refine ⟨3154734101206361509830647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2103156067470907673220431 3154734101206361509830647)
    ·
      refine ⟨4732101151809542264745971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3154734101206361509830647 4732101151809542264745971)
      ·
        refine ⟨7098151727714313397118957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4732101151809542264745971 7098151727714313397118957)
        ·
          refine ⟨2661806897892867523919609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7098151727714313397118957 2661806897892867523919609)
          ·
            refine ⟨1996355173419650642939707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2661806897892867523919609 1996355173419650642939707)
            ·
              refine ⟨2994532760129475964409561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1996355173419650642939707 2994532760129475964409561)
              ·
                refine ⟨2245899570097106973307171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2994532760129475964409561 2245899570097106973307171)
                ·
                  refine ⟨3368849355145660459960757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2245899570097106973307171 3368849355145660459960757)
                  ·
                    refine ⟨315829627044905668121321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3368849355145660459960757 315829627044905668121321)
                    ·
                      rfl

theorem cell22_922614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 2, 1, 2, 1, 5].length) (baseStart_922614 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_922614 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_922614 prefixEnd_922614 := by exact prefixLift 922614
  have htrace : WordTrace (prefixWord ++ tailWord_922614) baseStart_922614 baseEnd_922614 := by
    simpa [prefixWord, tailWord_922614, baseEnd_922614] using wordTrace_append hprefix tailTrace_922614
  have hstable : (prefixWord ++ tailWord_922614).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_922614).length < 2 ^ (prefixWord ++ tailWord_922614).sum := by decide
  have hdescent : baseEnd_922614 < baseStart_922614 := by decide
  rcases family_descends (prefixWord ++ tailWord_922614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_922659 : List Nat := [1, 1, 1, 4, 3, 3, 1, 2, 3, 3]
def baseStart_922659 : Nat := 118140960795 + 922659 * 2 ^ 59
def prefixEnd_922659 : Nat := 4983230072969 + 3 ^ 40 * 922659 * 2
def baseEnd_922659 : Nat := 315845031464540550746183

theorem tailTrace_922659 : CollatzResearch.WordTrace tailWord_922659 prefixEnd_922659 315845031464540550746183 := by
  unfold tailWord_922659
  simp only [CollatzResearch.WordTrace]
  refine ⟨33652138364371495456915031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22434758909580996971276687 33652138364371495456915031)
  ·
    refine ⟨50478207546557243185372547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33652138364371495456915031 50478207546557243185372547)
    ·
      refine ⟨75717311319835864778058821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50478207546557243185372547 75717311319835864778058821)
      ·
        refine ⟨14196995872469224645886029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 75717311319835864778058821 14196995872469224645886029)
        ·
          refine ⟨5323873452175959242207261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14196995872469224645886029 5323873452175959242207261)
          ·
            refine ⟨1996452544565984715827723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5323873452175959242207261 1996452544565984715827723)
            ·
              refine ⟨2994678816848977073741585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1996452544565984715827723 2994678816848977073741585)
              ·
                refine ⟨2246009112636732805306189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2994678816848977073741585 2246009112636732805306189)
                ·
                  refine ⟨842253417238774801989821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2246009112636732805306189 842253417238774801989821)
                  ·
                    refine ⟨315845031464540550746183, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 842253417238774801989821 315845031464540550746183)
                    ·
                      rfl

theorem cell22_922659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 3, 1, 2, 3, 3].length) (baseStart_922659 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_922659 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_922659 prefixEnd_922659 := by exact prefixLift 922659
  have htrace : WordTrace (prefixWord ++ tailWord_922659) baseStart_922659 baseEnd_922659 := by
    simpa [prefixWord, tailWord_922659, baseEnd_922659] using wordTrace_append hprefix tailTrace_922659
  have hstable : (prefixWord ++ tailWord_922659).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_922659).length < 2 ^ (prefixWord ++ tailWord_922659).sum := by decide
  have hdescent : baseEnd_922659 < baseStart_922659 := by decide
  rcases family_descends (prefixWord ++ tailWord_922659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_922689 : List Nat := [1, 2, 5, 1, 3, 1, 1, 1, 7]
def baseStart_922689 : Nat := 118140960795 + 922689 * 2 ^ 59
def prefixEnd_922689 : Nat := 4983230072969 + 3 ^ 40 * 922689 * 2
def baseEnd_922689 : Nat := 105285100359210157498697

theorem tailTrace_922689 : CollatzResearch.WordTrace tailWord_922689 prefixEnd_922689 105285100359210157498697 := by
  unfold tailWord_922689
  simp only [CollatzResearch.WordTrace]
  refine ⟨33653232554262810580507121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22435488369508540387004747 33653232554262810580507121)
  ·
    refine ⟨25239924415697107935380341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33653232554262810580507121 25239924415697107935380341)
    ·
      refine ⟨2366242913971603868941907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 25239924415697107935380341 2366242913971603868941907)
      ·
        refine ⟨3549364370957405803412861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2366242913971603868941907 3549364370957405803412861)
        ·
          refine ⟨1331011639109027176279823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3549364370957405803412861 1331011639109027176279823)
          ·
            refine ⟨1996517458663540764419735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1331011639109027176279823 1996517458663540764419735)
            ·
              refine ⟨2994776187995311146629603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1996517458663540764419735 2994776187995311146629603)
              ·
                refine ⟨4492164281992966719944405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2994776187995311146629603 4492164281992966719944405)
                ·
                  refine ⟨105285100359210157498697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4492164281992966719944405 105285100359210157498697)
                  ·
                    rfl

theorem cell22_922689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 1, 1, 1, 7].length) (baseStart_922689 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_922689 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_922689 prefixEnd_922689 := by exact prefixLift 922689
  have htrace : WordTrace (prefixWord ++ tailWord_922689) baseStart_922689 baseEnd_922689 := by
    simpa [prefixWord, tailWord_922689, baseEnd_922689] using wordTrace_append hprefix tailTrace_922689
  have hstable : (prefixWord ++ tailWord_922689).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_922689).length < 2 ^ (prefixWord ++ tailWord_922689).sum := by decide
  have hdescent : baseEnd_922689 < baseStart_922689 := by decide
  rcases family_descends (prefixWord ++ tailWord_922689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_922706 : List Nat := [3, 2, 2, 1, 3, 2, 3, 1, 5]
def baseStart_922706 : Nat := 118140960795 + 922706 * 2 ^ 59
def prefixEnd_922706 : Nat := 4983230072969 + 3 ^ 40 * 922706 * 2
def baseEnd_922706 : Nat := 105287040175016031607013

theorem tailTrace_922706 : CollatzResearch.WordTrace tailWord_922706 prefixEnd_922706 105287040175016031607013 := by
  unfold tailWord_922706
  simp only [CollatzResearch.WordTrace]
  refine ⟨8413463148800305620968993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22435901730134148322583981 8413463148800305620968993)
  ·
    refine ⟨6310097361600229215726745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8413463148800305620968993 6310097361600229215726745)
    ·
      refine ⟨4732573021200171911795059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6310097361600229215726745 4732573021200171911795059)
      ·
        refine ⟨7098859531800257867692589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4732573021200171911795059 7098859531800257867692589)
        ·
          refine ⟨2662072324425096700384721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7098859531800257867692589 2662072324425096700384721)
          ·
            refine ⟨1996554243318822525288541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2662072324425096700384721 1996554243318822525288541)
            ·
              refine ⟨748707841244558446983203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1996554243318822525288541 748707841244558446983203)
              ·
                refine ⟨1123061761866837670474805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 748707841244558446983203 1123061761866837670474805)
                ·
                  refine ⟨105287040175016031607013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1123061761866837670474805 105287040175016031607013)
                  ·
                    rfl

theorem cell22_922706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 2, 3, 1, 5].length) (baseStart_922706 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_922706 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_922706 prefixEnd_922706 := by exact prefixLift 922706
  have htrace : WordTrace (prefixWord ++ tailWord_922706) baseStart_922706 baseEnd_922706 := by
    simpa [prefixWord, tailWord_922706, baseEnd_922706] using wordTrace_append hprefix tailTrace_922706
  have hstable : (prefixWord ++ tailWord_922706).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_922706).length < 2 ^ (prefixWord ++ tailWord_922706).sum := by decide
  have hdescent : baseEnd_922706 < baseStart_922706 := by decide
  rcases family_descends (prefixWord ++ tailWord_922706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_922719 : List Nat := [1, 1, 2, 3, 1, 1, 6, 2, 1, 4]
def baseStart_922719 : Nat := 118140960795 + 922719 * 2 ^ 59
def prefixEnd_922719 : Nat := 4983230072969 + 3 ^ 40 * 922719 * 2
def baseEnd_922719 : Nat := 315865570690720394245999

theorem tailTrace_922719 : CollatzResearch.WordTrace tailWord_922719 prefixEnd_922719 315865570690720394245999 := by
  unfold tailWord_922719
  simp only [CollatzResearch.WordTrace]
  refine ⟨33654326744154125704099211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22436217829436083802732807 33654326744154125704099211)
  ·
    refine ⟨50481490116231188556148817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33654326744154125704099211 50481490116231188556148817)
    ·
      refine ⟨37861117587173391417111613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50481490116231188556148817 37861117587173391417111613)
      ·
        refine ⟨14197919095190021781416855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37861117587173391417111613 14197919095190021781416855)
        ·
          refine ⟨21296878642785032672125283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14197919095190021781416855 21296878642785032672125283)
          ·
            refine ⟨31945317964177549008187925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21296878642785032672125283 31945317964177549008187925)
            ·
              refine ⟨1497436779570822609758809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 31945317964177549008187925 1497436779570822609758809)
              ·
                refine ⟨1123077584678116957319107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1497436779570822609758809 1123077584678116957319107)
                ·
                  refine ⟨1684616377017175435978661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1123077584678116957319107 1684616377017175435978661)
                  ·
                    refine ⟨315865570690720394245999, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1684616377017175435978661 315865570690720394245999)
                    ·
                      rfl

theorem cell22_922719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 6, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 6, 2, 1, 4].length) (baseStart_922719 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_922719 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_922719 prefixEnd_922719 := by exact prefixLift 922719
  have htrace : WordTrace (prefixWord ++ tailWord_922719) baseStart_922719 baseEnd_922719 := by
    simpa [prefixWord, tailWord_922719, baseEnd_922719] using wordTrace_append hprefix tailTrace_922719
  have hstable : (prefixWord ++ tailWord_922719).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_922719).length < 2 ^ (prefixWord ++ tailWord_922719).sum := by decide
  have hdescent : baseEnd_922719 < baseStart_922719 := by decide
  rcases family_descends (prefixWord ++ tailWord_922719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_922732 : List Nat := [2, 2, 1, 1, 3, 2, 2, 1, 3, 5]
def baseStart_922732 : Nat := 118140960795 + 922732 * 2 ^ 59
def prefixEnd_922732 : Nat := 4983230072969 + 3 ^ 40 * 922732 * 2
def baseEnd_922732 : Nat := 315870020856392693670959

theorem tailTrace_922732 : CollatzResearch.WordTrace tailWord_922732 prefixEnd_922732 315870020856392693670959 := by
  unfold tailWord_922732
  simp only [CollatzResearch.WordTrace]
  refine ⟨16827400446553514462161225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22436533928738019282881633 16827400446553514462161225)
  ·
    refine ⟨12620550334915135846620919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16827400446553514462161225 12620550334915135846620919)
    ·
      refine ⟨18930825502372703769931379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12620550334915135846620919 18930825502372703769931379)
      ·
        refine ⟨28396238253559055654897069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18930825502372703769931379 28396238253559055654897069)
        ·
          refine ⟨10648589345084645870586401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28396238253559055654897069 10648589345084645870586401)
          ·
            refine ⟨7986442008813484402939801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10648589345084645870586401 7986442008813484402939801)
            ·
              refine ⟨5989831506610113302204851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7986442008813484402939801 5989831506610113302204851)
              ·
                refine ⟨8984747259915169953307277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5989831506610113302204851 8984747259915169953307277)
                ·
                  refine ⟨3369280222468188732490229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8984747259915169953307277 3369280222468188732490229)
                  ·
                    refine ⟨315870020856392693670959, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3369280222468188732490229 315870020856392693670959)
                    ·
                      rfl

theorem cell22_922732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 5].length) (baseStart_922732 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_922732 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_922732 prefixEnd_922732 := by exact prefixLift 922732
  have htrace : WordTrace (prefixWord ++ tailWord_922732) baseStart_922732 baseEnd_922732 := by
    simpa [prefixWord, tailWord_922732, baseEnd_922732] using wordTrace_append hprefix tailTrace_922732
  have hstable : (prefixWord ++ tailWord_922732).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_922732).length < 2 ^ (prefixWord ++ tailWord_922732).sum := by decide
  have hdescent : baseEnd_922732 < baseStart_922732 := by decide
  rcases family_descends (prefixWord ++ tailWord_922732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_922749 : List Nat := [1, 4, 1, 1, 3, 1, 1, 3, 4, 3]
def baseStart_922749 : Nat := 118140960795 + 922749 * 2 ^ 59
def prefixEnd_922749 : Nat := 4983230072969 + 3 ^ 40 * 922749 * 2
def baseEnd_922749 : Nat := 315875840303810315995907

theorem tailTrace_922749 : CollatzResearch.WordTrace tailWord_922749 prefixEnd_922749 315875840303810315995907 := by
  unfold tailWord_922749
  simp only [CollatzResearch.WordTrace]
  refine ⟨33655420934045440827691301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22436947289363627218460867 33655420934045440827691301)
  ·
    refine ⟨6310391425133520155192119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 33655420934045440827691301 6310391425133520155192119)
    ·
      refine ⟨9465587137700280232788179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6310391425133520155192119 9465587137700280232788179)
      ·
        refine ⟨14198380706550420349182269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9465587137700280232788179 14198380706550420349182269)
        ·
          refine ⟨5324392764956407630943351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14198380706550420349182269 5324392764956407630943351)
          ·
            refine ⟨7986589147434611446415027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5324392764956407630943351 7986589147434611446415027)
            ·
              refine ⟨11979883721151917169622541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7986589147434611446415027 11979883721151917169622541)
              ·
                refine ⟨4492456395431968938608453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11979883721151917169622541 4492456395431968938608453)
                ·
                  refine ⟨842335574143494175989085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4492456395431968938608453 842335574143494175989085)
                  ·
                    refine ⟨315875840303810315995907, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 842335574143494175989085 315875840303810315995907)
                    ·
                      rfl

theorem cell22_922749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 1, 3, 4, 3].length) (baseStart_922749 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_922749 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_922749 prefixEnd_922749 := by exact prefixLift 922749
  have htrace : WordTrace (prefixWord ++ tailWord_922749) baseStart_922749 baseEnd_922749 := by
    simpa [prefixWord, tailWord_922749, baseEnd_922749] using wordTrace_append hprefix tailTrace_922749
  have hstable : (prefixWord ++ tailWord_922749).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_922749).length < 2 ^ (prefixWord ++ tailWord_922749).sum := by decide
  have hdescent : baseEnd_922749 < baseStart_922749 := by decide
  rcases family_descends (prefixWord ++ tailWord_922749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_922824 : List Nat := [2, 1, 3, 1, 2, 1, 4, 3, 5]
def baseStart_922824 : Nat := 118140960795 + 922824 * 2 ^ 59
def prefixEnd_922824 : Nat := 4983230072969 + 3 ^ 40 * 922824 * 2
def baseEnd_922824 : Nat := 105300504778845040123559

theorem tailTrace_922824 : CollatzResearch.WordTrace tailWord_922824 prefixEnd_922824 105300504778845040123559 := by
  unfold tailWord_922824
  simp only [CollatzResearch.WordTrace]
  refine ⟨16829078204386864318335763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22438770939182485757781017 16829078204386864318335763)
  ·
    refine ⟨25243617306580296477503645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16829078204386864318335763 25243617306580296477503645)
    ·
      refine ⟨9466356489967611179063867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25243617306580296477503645 9466356489967611179063867)
      ·
        refine ⟨14199534734951416768595801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9466356489967611179063867 14199534734951416768595801)
        ·
          refine ⟨10649651051213562576446851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14199534734951416768595801 10649651051213562576446851)
          ·
            refine ⟨15974476576820343864670277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10649651051213562576446851 15974476576820343864670277)
            ·
              refine ⟨2995214358153814474625677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15974476576820343864670277 2995214358153814474625677)
              ·
                refine ⟨1123205384307680427984629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2995214358153814474625677 1123205384307680427984629)
                ·
                  refine ⟨105300504778845040123559, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1123205384307680427984629 105300504778845040123559)
                  ·
                    rfl

theorem cell22_922824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 4, 3, 5].length) (baseStart_922824 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_922824 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_922824 prefixEnd_922824 := by exact prefixLift 922824
  have htrace : WordTrace (prefixWord ++ tailWord_922824) baseStart_922824 baseEnd_922824 := by
    simpa [prefixWord, tailWord_922824, baseEnd_922824] using wordTrace_append hprefix tailTrace_922824
  have hstable : (prefixWord ++ tailWord_922824).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_922824).length < 2 ^ (prefixWord ++ tailWord_922824).sum := by decide
  have hdescent : baseEnd_922824 < baseStart_922824 := by decide
  rcases family_descends (prefixWord ++ tailWord_922824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_922888 : List Nat := [2, 1, 3, 2, 4, 1, 2, 2, 1, 4]
def baseStart_922888 : Nat := 118140960795 + 922888 * 2 ^ 59
def prefixEnd_922888 : Nat := 4983230072969 + 3 ^ 40 * 922888 * 2
def baseEnd_922888 : Nat := 315923422844460286770481

theorem tailTrace_922888 : CollatzResearch.WordTrace tailWord_922888 prefixEnd_922888 315923422844460286770481 := by
  unfold tailWord_922888
  simp only [CollatzResearch.WordTrace]
  refine ⟨16830245340270933783500659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22440327120361245044667545 16830245340270933783500659)
  ·
    refine ⟨25245368010406400675250989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16830245340270933783500659 25245368010406400675250989)
    ·
      refine ⟨9467013003902400253219121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25245368010406400675250989 9467013003902400253219121)
      ·
        refine ⟨7100259752926800189914341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9467013003902400253219121 7100259752926800189914341)
        ·
          refine ⟨1331298703673775035608939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7100259752926800189914341 1331298703673775035608939)
          ·
            refine ⟨1996948055510662553413409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1331298703673775035608939 1996948055510662553413409)
            ·
              refine ⟨1497711041632996915060057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1996948055510662553413409 1497711041632996915060057)
              ·
                refine ⟨1123283281224747686295043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1497711041632996915060057 1123283281224747686295043)
                ·
                  refine ⟨1684924921837121529442565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1123283281224747686295043 1684924921837121529442565)
                  ·
                    refine ⟨315923422844460286770481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1684924921837121529442565 315923422844460286770481)
                    ·
                      rfl

theorem cell22_922888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 1, 2, 2, 1, 4].length) (baseStart_922888 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_922888 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_922888 prefixEnd_922888 := by exact prefixLift 922888
  have htrace : WordTrace (prefixWord ++ tailWord_922888) baseStart_922888 baseEnd_922888 := by
    simpa [prefixWord, tailWord_922888, baseEnd_922888] using wordTrace_append hprefix tailTrace_922888
  have hstable : (prefixWord ++ tailWord_922888).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_922888).length < 2 ^ (prefixWord ++ tailWord_922888).sum := by decide
  have hdescent : baseEnd_922888 < baseStart_922888 := by decide
  rcases family_descends (prefixWord ++ tailWord_922888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_922916 : List Nat := [2, 3, 1, 3, 1, 1, 3, 2, 2, 4]
def baseStart_922916 : Nat := 118140960795 + 922916 * 2 ^ 59
def prefixEnd_922916 : Nat := 4983230072969 + 3 ^ 40 * 922916 * 2
def baseEnd_922916 : Nat := 315933007816677547070395

theorem tailTrace_922916 : CollatzResearch.WordTrace tailWord_922916 prefixEnd_922916 315933007816677547070395 := by
  unfold tailWord_922916
  simp only [CollatzResearch.WordTrace]
  refine ⟨16830755962220214174510301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22441007949626952232680401 16830755962220214174510301)
  ·
    refine ⟨6311533485832580315441363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16830755962220214174510301 6311533485832580315441363)
    ·
      refine ⟨9467300228748870473162045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6311533485832580315441363 9467300228748870473162045)
      ·
        refine ⟨3550237585780826427435767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9467300228748870473162045 3550237585780826427435767)
        ·
          refine ⟨5325356378671239641153651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3550237585780826427435767 5325356378671239641153651)
          ·
            refine ⟨7988034568006859461730477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5325356378671239641153651 7988034568006859461730477)
            ·
              refine ⟨2995512963002572298148929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7988034568006859461730477 2995512963002572298148929)
              ·
                refine ⟨2246634722251929223611697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2995512963002572298148929 2246634722251929223611697)
                ·
                  refine ⟨1684976041688946917708773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2246634722251929223611697 1684976041688946917708773)
                  ·
                    refine ⟨315933007816677547070395, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1684976041688946917708773 315933007816677547070395)
                    ·
                      rfl

theorem cell22_922916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 3, 2, 2, 4].length) (baseStart_922916 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_922916 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_922916 prefixEnd_922916 := by exact prefixLift 922916
  have htrace : WordTrace (prefixWord ++ tailWord_922916) baseStart_922916 baseEnd_922916 := by
    simpa [prefixWord, tailWord_922916, baseEnd_922916] using wordTrace_append hprefix tailTrace_922916
  have hstable : (prefixWord ++ tailWord_922916).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_922916).length < 2 ^ (prefixWord ++ tailWord_922916).sum := by decide
  have hdescent : baseEnd_922916 < baseStart_922916 := by decide
  rcases family_descends (prefixWord ++ tailWord_922916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_922920 : List Nat := [2, 1, 5, 1, 2, 2, 3, 2, 4]
def baseStart_922920 : Nat := 118140960795 + 922920 * 2 ^ 59
def prefixEnd_922920 : Nat := 4983230072969 + 3 ^ 40 * 922920 * 2
def baseEnd_922920 : Nat := 105311459032807623323461

theorem tailTrace_922920 : CollatzResearch.WordTrace tailWord_922920 prefixEnd_922920 105311459032807623323461 := by
  unfold tailWord_922920
  simp only [CollatzResearch.WordTrace]
  refine ⟨16830828908212968516083107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22441105210950624688110809 16830828908212968516083107)
  ·
    refine ⟨25246243362319452774124661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16830828908212968516083107 25246243362319452774124661)
    ·
      refine ⟨2366835315217448697574187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 25246243362319452774124661 2366835315217448697574187)
      ·
        refine ⟨3550252972826173046361281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2366835315217448697574187 3550252972826173046361281)
        ·
          refine ⟨2662689729619629784770961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3550252972826173046361281 2662689729619629784770961)
          ·
            refine ⟨1997017297214722338578221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2662689729619629784770961 1997017297214722338578221)
            ·
              refine ⟨748881486455520876966833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1997017297214722338578221 748881486455520876966833)
              ·
                refine ⟨561661114841640657725125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 748881486455520876966833 561661114841640657725125)
                ·
                  refine ⟨105311459032807623323461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 561661114841640657725125 105311459032807623323461)
                  ·
                    rfl

theorem cell22_922920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 2, 3, 2, 4].length) (baseStart_922920 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_922920 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_922920 prefixEnd_922920 := by exact prefixLift 922920
  have htrace : WordTrace (prefixWord ++ tailWord_922920) baseStart_922920 baseEnd_922920 := by
    simpa [prefixWord, tailWord_922920, baseEnd_922920] using wordTrace_append hprefix tailTrace_922920
  have hstable : (prefixWord ++ tailWord_922920).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_922920).length < 2 ^ (prefixWord ++ tailWord_922920).sum := by decide
  have hdescent : baseEnd_922920 < baseStart_922920 := by decide
  rcases family_descends (prefixWord ++ tailWord_922920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_922963 : List Nat := [1, 1, 1, 2, 1, 1, 6, 5, 1, 3]
def baseStart_922963 : Nat := 118140960795 + 922963 * 2 ^ 59
def prefixEnd_922963 : Nat := 4983230072969 + 3 ^ 40 * 922963 * 2
def baseEnd_922963 : Nat := 315949096877185091145251

theorem tailTrace_922963 : CollatzResearch.WordTrace tailWord_922963 prefixEnd_922963 315949096877185091145251 := by
  unfold tailWord_922963
  simp only [CollatzResearch.WordTrace]
  refine ⟨33663226155270155375981543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22442150770180103583987695 33663226155270155375981543)
  ·
    refine ⟨50494839232905233063972315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33663226155270155375981543 50494839232905233063972315)
    ·
      refine ⟨75742258849357849595958473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50494839232905233063972315 75742258849357849595958473)
      ·
        refine ⟨56806694137018387196968855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75742258849357849595958473 56806694137018387196968855)
        ·
          refine ⟨85210041205527580795453283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56806694137018387196968855 85210041205527580795453283)
          ·
            refine ⟨127815061808291371193179925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 85210041205527580795453283 127815061808291371193179925)
            ·
              refine ⟨5991331022263658024680309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 127815061808291371193179925 5991331022263658024680309)
              ·
                refine ⟨561687283337217939813779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5991331022263658024680309 561687283337217939813779)
                ·
                  refine ⟨842530925005826909720669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 561687283337217939813779 842530925005826909720669)
                  ·
                    refine ⟨315949096877185091145251, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 842530925005826909720669 315949096877185091145251)
                    ·
                      rfl

theorem cell22_922963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 6, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 6, 5, 1, 3].length) (baseStart_922963 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_922963 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_922963 prefixEnd_922963 := by exact prefixLift 922963
  have htrace : WordTrace (prefixWord ++ tailWord_922963) baseStart_922963 baseEnd_922963 := by
    simpa [prefixWord, tailWord_922963, baseEnd_922963] using wordTrace_append hprefix tailTrace_922963
  have hstable : (prefixWord ++ tailWord_922963).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_922963).length < 2 ^ (prefixWord ++ tailWord_922963).sum := by decide
  have hdescent : baseEnd_922963 < baseStart_922963 := by decide
  rcases family_descends (prefixWord ++ tailWord_922963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_922976 : List Nat := [2, 1, 1, 3, 4, 1, 1, 4, 5]
def baseStart_922976 : Nat := 118140960795 + 922976 * 2 ^ 59
def prefixEnd_922976 : Nat := 4983230072969 + 3 ^ 40 * 922976 * 2
def baseEnd_922976 : Nat := 105317849014285796856737

theorem tailTrace_922976 : CollatzResearch.WordTrace tailWord_922976 prefixEnd_922976 105317849014285796856737 := by
  unfold tailWord_922976
  simp only [CollatzResearch.WordTrace]
  refine ⟨16831850152111529298102391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22442466869482039064136521 16831850152111529298102391)
  ·
    refine ⟨25247775228167293947153587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16831850152111529298102391 25247775228167293947153587)
    ·
      refine ⟨37871662842250940920730381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25247775228167293947153587 37871662842250940920730381)
      ·
        refine ⟨14201873565844102845273893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37871662842250940920730381 14201873565844102845273893)
        ·
          refine ⟨2662851293595769283488855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14201873565844102845273893 2662851293595769283488855)
          ·
            refine ⟨3994276940393653925233283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2662851293595769283488855 3994276940393653925233283)
            ·
              refine ⟨5991415410590480887849925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3994276940393653925233283 5991415410590480887849925)
              ·
                refine ⟨1123390389485715166471861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5991415410590480887849925 1123390389485715166471861)
                ·
                  refine ⟨105317849014285796856737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1123390389485715166471861 105317849014285796856737)
                  ·
                    rfl

theorem cell22_922976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 1, 4, 5].length) (baseStart_922976 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_922976 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_922976 prefixEnd_922976 := by exact prefixLift 922976
  have htrace : WordTrace (prefixWord ++ tailWord_922976) baseStart_922976 baseEnd_922976 := by
    simpa [prefixWord, tailWord_922976, baseEnd_922976] using wordTrace_append hprefix tailTrace_922976
  have hstable : (prefixWord ++ tailWord_922976).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_922976).length < 2 ^ (prefixWord ++ tailWord_922976).sum := by decide
  have hdescent : baseEnd_922976 < baseStart_922976 := by decide
  rcases family_descends (prefixWord ++ tailWord_922976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_922980 : List Nat := [2, 3, 1, 1, 3, 3, 1, 4, 1, 3]
def baseStart_922980 : Nat := 118140960795 + 922980 * 2 ^ 59
def prefixEnd_922980 : Nat := 4983230072969 + 3 ^ 40 * 922980 * 2
def baseEnd_922980 : Nat := 315954916324602713470199

theorem tailTrace_922980 : CollatzResearch.WordTrace tailWord_922980 prefixEnd_922980 315954916324602713470199 := by
  unfold tailWord_922980
  simp only [CollatzResearch.WordTrace]
  refine ⟨16831923098104283639675197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22442564130805711519566929 16831923098104283639675197)
  ·
    refine ⟨6311971161789106364878199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16831923098104283639675197 6311971161789106364878199)
    ·
      refine ⟨9467956742683659547317299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6311971161789106364878199 9467956742683659547317299)
      ·
        refine ⟨14201935114025489320975949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9467956742683659547317299 14201935114025489320975949)
        ·
          refine ⟨5325725667759558495365981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14201935114025489320975949 5325725667759558495365981)
          ·
            refine ⟨1997147125409834435762243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5325725667759558495365981 1997147125409834435762243)
            ·
              refine ⟨2995720688114751653643365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1997147125409834435762243 2995720688114751653643365)
              ·
                refine ⟨561697629021515935058131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2995720688114751653643365 561697629021515935058131)
                ·
                  refine ⟨842546443532273902587197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 561697629021515935058131 842546443532273902587197)
                  ·
                    refine ⟨315954916324602713470199, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 842546443532273902587197 315954916324602713470199)
                    ·
                      rfl

theorem cell22_922980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 3, 1, 4, 1, 3].length) (baseStart_922980 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_922980 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_922980 prefixEnd_922980 := by exact prefixLift 922980
  have htrace : WordTrace (prefixWord ++ tailWord_922980) baseStart_922980 baseEnd_922980 := by
    simpa [prefixWord, tailWord_922980, baseEnd_922980] using wordTrace_append hprefix tailTrace_922980
  have hstable : (prefixWord ++ tailWord_922980).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_922980).length < 2 ^ (prefixWord ++ tailWord_922980).sum := by decide
  have hdescent : baseEnd_922980 < baseStart_922980 := by decide
  rcases family_descends (prefixWord ++ tailWord_922980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_923166 : List Nat := [4, 3, 3, 1, 1, 1, 1, 2, 3, 3]
def baseStart_923166 : Nat := 118140960795 + 923166 * 2 ^ 59
def prefixEnd_923166 : Nat := 4983230072969 + 3 ^ 40 * 923166 * 2
def baseEnd_923166 : Nat := 316018587925760228319629

theorem tailTrace_923166 : CollatzResearch.WordTrace tailWord_923166 prefixEnd_923166 316018587925760228319629 := by
  unfold tailWord_923166
  simp only [CollatzResearch.WordTrace]
  refine ⟨4208828771691840130702669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22447086782356480697080901 4208828771691840130702669)
  ·
    refine ⟨1578310789384440049013501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4208828771691840130702669 1578310789384440049013501)
    ·
      refine ⟨591866546019165018380063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1578310789384440049013501 591866546019165018380063)
      ·
        refine ⟨887799819028747527570095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 591866546019165018380063 887799819028747527570095)
        ·
          refine ⟨1331699728543121291355143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 887799819028747527570095 1331699728543121291355143)
          ·
            refine ⟨1997549592814681937032715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1331699728543121291355143 1997549592814681937032715)
            ·
              refine ⟨2996324389222022905549073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1997549592814681937032715 2996324389222022905549073)
              ·
                refine ⟨2247243291916517179161805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2996324389222022905549073 2247243291916517179161805)
                ·
                  refine ⟨842716234468693942185677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2247243291916517179161805 842716234468693942185677)
                  ·
                    refine ⟨316018587925760228319629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 842716234468693942185677 316018587925760228319629)
                    ·
                      rfl

theorem cell22_923166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 1, 1, 2, 3, 3].length) (baseStart_923166 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_923166 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_923166 prefixEnd_923166 := by exact prefixLift 923166
  have htrace : WordTrace (prefixWord ++ tailWord_923166) baseStart_923166 baseEnd_923166 := by
    simpa [prefixWord, tailWord_923166, baseEnd_923166] using wordTrace_append hprefix tailTrace_923166
  have hstable : (prefixWord ++ tailWord_923166).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_923166).length < 2 ^ (prefixWord ++ tailWord_923166).sum := by decide
  have hdescent : baseEnd_923166 < baseStart_923166 := by decide
  rcases family_descends (prefixWord ++ tailWord_923166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_923192 : List Nat := [2, 1, 2, 1, 4, 4, 2, 1, 1, 4]
def baseStart_923192 : Nat := 118140960795 + 923192 * 2 ^ 59
def prefixEnd_923192 : Nat := 4983230072969 + 3 ^ 40 * 923192 * 2
def baseEnd_923192 : Nat := 316027488257104827169549

theorem tailTrace_923192 : CollatzResearch.WordTrace tailWord_923192 prefixEnd_923192 316027488257104827169549 := by
  unfold tailWord_923192
  simp only [CollatzResearch.WordTrace]
  refine ⟨16835789235720263743033915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22447718980960351657378553 16835789235720263743033915)
  ·
    refine ⟨25253683853580395614550873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16835789235720263743033915 25253683853580395614550873)
    ·
      refine ⟨18940262890185296710913155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25253683853580395614550873 18940262890185296710913155)
      ·
        refine ⟨28410394335277945066369733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18940262890185296710913155 28410394335277945066369733)
        ·
          refine ⟨5326948937864614699944325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28410394335277945066369733 5326948937864614699944325)
          ·
            refine ⟨998802925849615256239561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5326948937864614699944325 998802925849615256239561)
            ·
              refine ⟨749102194387211442179671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 998802925849615256239561 749102194387211442179671)
              ·
                refine ⟨1123653291580817163269507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 749102194387211442179671 1123653291580817163269507)
                ·
                  refine ⟨1685479937371225744904261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1123653291580817163269507 1685479937371225744904261)
                  ·
                    refine ⟨316027488257104827169549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1685479937371225744904261 316027488257104827169549)
                    ·
                      rfl

theorem cell22_923192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 4, 2, 1, 1, 4].length) (baseStart_923192 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_923192 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_923192 prefixEnd_923192 := by exact prefixLift 923192
  have htrace : WordTrace (prefixWord ++ tailWord_923192) baseStart_923192 baseEnd_923192 := by
    simpa [prefixWord, tailWord_923192, baseEnd_923192] using wordTrace_append hprefix tailTrace_923192
  have hstable : (prefixWord ++ tailWord_923192).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_923192).length < 2 ^ (prefixWord ++ tailWord_923192).sum := by decide
  have hdescent : baseEnd_923192 < baseStart_923192 := by decide
  rcases family_descends (prefixWord ++ tailWord_923192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_923235 : List Nat := [1, 1, 1, 5, 1, 5, 2, 6]
def baseStart_923235 : Nat := 118140960795 + 923235 * 2 ^ 59
def prefixEnd_923235 : Nat := 4983230072969 + 3 ^ 40 * 923235 * 2
def baseEnd_923235 : Nat := 35115800892874116482713

theorem tailTrace_923235 : CollatzResearch.WordTrace tailWord_923235 prefixEnd_923235 35115800892874116482713 := by
  unfold tailWord_923235
  simp only [CollatzResearch.WordTrace]
  refine ⟨33673146810284745829883159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22448764540189830553255439 33673146810284745829883159)
  ·
    refine ⟨50509720215427118744824739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33673146810284745829883159 50509720215427118744824739)
    ·
      refine ⟨75764580323140678117237109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50509720215427118744824739 75764580323140678117237109)
      ·
        refine ⟨7102929405294438573490979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 75764580323140678117237109 7102929405294438573490979)
        ·
          refine ⟨10654394107941657860236469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7102929405294438573490979 10654394107941657860236469)
          ·
            refine ⟨998849447619530424397169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 10654394107941657860236469 998849447619530424397169)
            ·
              refine ⟨749137085714647818297877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 998849447619530424397169 749137085714647818297877)
              ·
                refine ⟨35115800892874116482713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 749137085714647818297877 35115800892874116482713)
                ·
                  rfl

theorem cell22_923235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 5, 2, 6].length) (baseStart_923235 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_923235 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_923235 prefixEnd_923235 := by exact prefixLift 923235
  have htrace : WordTrace (prefixWord ++ tailWord_923235) baseStart_923235 baseEnd_923235 := by
    simpa [prefixWord, tailWord_923235, baseEnd_923235] using wordTrace_append hprefix tailTrace_923235
  have hstable : (prefixWord ++ tailWord_923235).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_923235).length < 2 ^ (prefixWord ++ tailWord_923235).sum := by decide
  have hdescent : baseEnd_923235 < baseStart_923235 := by decide
  rcases family_descends (prefixWord ++ tailWord_923235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_923318 : List Nat := [5, 1, 3, 1, 1, 1, 4, 2, 1, 3]
def baseStart_923318 : Nat := 118140960795 + 923318 * 2 ^ 59
def prefixEnd_923318 : Nat := 4983230072969 + 3 ^ 40 * 923318 * 2
def baseEnd_923318 : Nat := 316070620632082498519163

theorem tailTrace_923318 : CollatzResearch.WordTrace tailWord_923318 prefixEnd_923318 316070620632082498519163 := by
  unfold tailWord_923318
  simp only [CollatzResearch.WordTrace]
  refine ⟨2104760879311503187822163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 22450782712656034003436405 2104760879311503187822163)
  ·
    refine ⟨3157141318967254781733245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2104760879311503187822163 3157141318967254781733245)
    ·
      refine ⟨1183927994612720543149967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3157141318967254781733245 1183927994612720543149967)
      ·
        refine ⟨1775891991919080814724951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1183927994612720543149967 1775891991919080814724951)
        ·
          refine ⟨2663837987878621222087427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1775891991919080814724951 2663837987878621222087427)
          ·
            refine ⟨3995756981817931833131141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2663837987878621222087427 3995756981817931833131141)
            ·
              refine ⟨749204434090862218712089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3995756981817931833131141 749204434090862218712089)
              ·
                refine ⟨561903325568146664034067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 749204434090862218712089 561903325568146664034067)
                ·
                  refine ⟨842854988352219996051101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 561903325568146664034067 842854988352219996051101)
                  ·
                    refine ⟨316070620632082498519163, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 842854988352219996051101 316070620632082498519163)
                    ·
                      rfl

theorem cell22_923318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 4, 2, 1, 3].length) (baseStart_923318 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_923318 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_923318 prefixEnd_923318 := by exact prefixLift 923318
  have htrace : WordTrace (prefixWord ++ tailWord_923318) baseStart_923318 baseEnd_923318 := by
    simpa [prefixWord, tailWord_923318, baseEnd_923318] using wordTrace_append hprefix tailTrace_923318
  have hstable : (prefixWord ++ tailWord_923318).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_923318).length < 2 ^ (prefixWord ++ tailWord_923318).sum := by decide
  have hdescent : baseEnd_923318 < baseStart_923318 := by decide
  rcases family_descends (prefixWord ++ tailWord_923318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_923361 : List Nat := [1, 2, 3, 1, 6, 1, 2, 1, 1, 4]
def baseStart_923361 : Nat := 118140960795 + 923361 * 2 ^ 59
def prefixEnd_923361 : Nat := 4983230072969 + 3 ^ 40 * 923361 * 2
def baseEnd_923361 : Nat := 316085340410844719694031

theorem tailTrace_923361 : CollatzResearch.WordTrace tailWord_923361 prefixEnd_923361 316085340410844719694031 := by
  unfold tailWord_923361
  simp only [CollatzResearch.WordTrace]
  refine ⟨33677742407828269348969937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22451828271885512899313291 33677742407828269348969937)
  ·
    refine ⟨25258306805871202011727453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33677742407828269348969937 25258306805871202011727453)
    ·
      refine ⟨9471865052201700754397795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25258306805871202011727453 9471865052201700754397795)
      ·
        refine ⟨14207797578302551131596693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9471865052201700754397795 14207797578302551131596693)
        ·
          refine ⟨665990511482932084293595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 14207797578302551131596693 665990511482932084293595)
          ·
            refine ⟨998985767224398126440393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 665990511482932084293595 998985767224398126440393)
            ·
              refine ⟨749239325418298594830295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 998985767224398126440393 749239325418298594830295)
              ·
                refine ⟨1123858988127447892245443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 749239325418298594830295 1123858988127447892245443)
                ·
                  refine ⟨1685788482191171838368165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1123858988127447892245443 1685788482191171838368165)
                  ·
                    refine ⟨316085340410844719694031, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1685788482191171838368165 316085340410844719694031)
                    ·
                      rfl

theorem cell22_923361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 6, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 6, 1, 2, 1, 1, 4].length) (baseStart_923361 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_923361 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_923361 prefixEnd_923361 := by exact prefixLift 923361
  have htrace : WordTrace (prefixWord ++ tailWord_923361) baseStart_923361 baseEnd_923361 := by
    simpa [prefixWord, tailWord_923361, baseEnd_923361] using wordTrace_append hprefix tailTrace_923361
  have hstable : (prefixWord ++ tailWord_923361).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_923361).length < 2 ^ (prefixWord ++ tailWord_923361).sum := by decide
  have hdescent : baseEnd_923361 < baseStart_923361 := by decide
  rcases family_descends (prefixWord ++ tailWord_923361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_923383 : List Nat := [1, 1, 3, 1, 1, 1, 4, 1, 1, 8]
def baseStart_923383 : Nat := 118140960795 + 923383 * 2 ^ 59
def prefixEnd_923383 : Nat := 4983230072969 + 3 ^ 40 * 923383 * 2
def baseEnd_923383 : Nat := 316092871460443995643963

theorem tailTrace_923383 : CollatzResearch.WordTrace tailWord_923383 prefixEnd_923383 316092871460443995643963 := by
  unfold tailWord_923383
  simp only [CollatzResearch.WordTrace]
  refine ⟨33678544813748567106270803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22452363209165711404180535 33678544813748567106270803)
  ·
    refine ⟨50517817220622850659406205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33678544813748567106270803 50517817220622850659406205)
    ·
      refine ⟨18944181457733568997277327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50517817220622850659406205 18944181457733568997277327)
      ·
        refine ⟨28416272186600353495915991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18944181457733568997277327 28416272186600353495915991)
        ·
          refine ⟨42624408279900530243873987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28416272186600353495915991 42624408279900530243873987)
          ·
            refine ⟨63936612419850795365810981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42624408279900530243873987 63936612419850795365810981)
            ·
              refine ⟨11988114828722024131089559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 63936612419850795365810981 11988114828722024131089559)
              ·
                refine ⟨17982172243083036196634339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11988114828722024131089559 17982172243083036196634339)
                ·
                  refine ⟨26973258364624554294951509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17982172243083036196634339 26973258364624554294951509)
                  ·
                    refine ⟨316092871460443995643963, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 26973258364624554294951509 316092871460443995643963)
                    ·
                      rfl

theorem cell22_923383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 4, 1, 1, 8].length) (baseStart_923383 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_923383 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_923383 prefixEnd_923383 := by exact prefixLift 923383
  have htrace : WordTrace (prefixWord ++ tailWord_923383) baseStart_923383 baseEnd_923383 := by
    simpa [prefixWord, tailWord_923383, baseEnd_923383] using wordTrace_append hprefix tailTrace_923383
  have hstable : (prefixWord ++ tailWord_923383).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_923383).length < 2 ^ (prefixWord ++ tailWord_923383).sum := by decide
  have hdescent : baseEnd_923383 < baseStart_923383 := by decide
  rcases family_descends (prefixWord ++ tailWord_923383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_923402 : List Nat := [3, 1, 2, 2, 1, 3, 2, 2, 3, 3]
def baseStart_923402 : Nat := 118140960795 + 923402 * 2 ^ 59
def prefixEnd_923402 : Nat := 4983230072969 + 3 ^ 40 * 923402 * 2
def baseEnd_923402 : Nat := 316099375548734279418905

theorem tailTrace_923402 : CollatzResearch.WordTrace tailWord_923402 prefixEnd_923402 316099375548734279418905 := by
  unfold tailWord_923402
  simp only [CollatzResearch.WordTrace]
  refine ⟨8419809450169933337803115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22452825200453155567474973 8419809450169933337803115)
  ·
    refine ⟨12629714175254900006704673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8419809450169933337803115 12629714175254900006704673)
    ·
      refine ⟨9472285631441175005028505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12629714175254900006704673 9472285631441175005028505)
      ·
        refine ⟨7104214223580881253771379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9472285631441175005028505 7104214223580881253771379)
        ·
          refine ⟨10656321335371321880657069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7104214223580881253771379 10656321335371321880657069)
          ·
            refine ⟨3996120500764245705246401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10656321335371321880657069 3996120500764245705246401)
            ·
              refine ⟨2997090375573184278934801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3996120500764245705246401 2997090375573184278934801)
              ·
                refine ⟨2247817781679888209201101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2997090375573184278934801 2247817781679888209201101)
                ·
                  refine ⟨842931668129958078450413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2247817781679888209201101 842931668129958078450413)
                  ·
                    refine ⟨316099375548734279418905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 842931668129958078450413 316099375548734279418905)
                    ·
                      rfl

theorem cell22_923402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 2, 2, 3, 3].length) (baseStart_923402 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_923402 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_923402 prefixEnd_923402 := by exact prefixLift 923402
  have htrace : WordTrace (prefixWord ++ tailWord_923402) baseStart_923402 baseEnd_923402 := by
    simpa [prefixWord, tailWord_923402, baseEnd_923402] using wordTrace_append hprefix tailTrace_923402
  have hstable : (prefixWord ++ tailWord_923402).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_923402).length < 2 ^ (prefixWord ++ tailWord_923402).sum := by decide
  have hdescent : baseEnd_923402 < baseStart_923402 := by decide
  rcases family_descends (prefixWord ++ tailWord_923402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_923415 : List Nat := [1, 1, 3, 4, 2, 1, 1, 2, 7]
def baseStart_923415 : Nat := 118140960795 + 923415 * 2 ^ 59
def prefixEnd_923415 : Nat := 4983230072969 + 3 ^ 40 * 923415 * 2
def baseEnd_923415 : Nat := 105367941904802192947955

theorem tailTrace_923415 : CollatzResearch.WordTrace tailWord_923415 prefixEnd_923415 105367941904802192947955 := by
  unfold tailWord_923415
  simp only [CollatzResearch.WordTrace]
  refine ⟨33679711949632636571435699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22453141299755091047623799 33679711949632636571435699)
  ·
    refine ⟨50519567924448954857153549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33679711949632636571435699 50519567924448954857153549)
    ·
      refine ⟨18944837971668358071432581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50519567924448954857153549 18944837971668358071432581)
      ·
        refine ⟨3552157119687817138393609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18944837971668358071432581 3552157119687817138393609)
        ·
          refine ⟨2664117839765862853795207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3552157119687817138393609 2664117839765862853795207)
          ·
            refine ⟨3996176759648794280692811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2664117839765862853795207 3996176759648794280692811)
            ·
              refine ⟨5994265139473191421039217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3996176759648794280692811 5994265139473191421039217)
              ·
                refine ⟨4495698854604893565779413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5994265139473191421039217 4495698854604893565779413)
                ·
                  refine ⟨105367941904802192947955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4495698854604893565779413 105367941904802192947955)
                  ·
                    rfl

theorem cell22_923415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 1, 2, 7].length) (baseStart_923415 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_923415 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_923415 prefixEnd_923415 := by exact prefixLift 923415
  have htrace : WordTrace (prefixWord ++ tailWord_923415) baseStart_923415 baseEnd_923415 := by
    simpa [prefixWord, tailWord_923415, baseEnd_923415] using wordTrace_append hprefix tailTrace_923415
  have hstable : (prefixWord ++ tailWord_923415).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_923415).length < 2 ^ (prefixWord ++ tailWord_923415).sum := by decide
  have hdescent : baseEnd_923415 < baseStart_923415 := by decide
  rcases family_descends (prefixWord ++ tailWord_923415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_923436 : List Nat := [2, 2, 1, 1, 1, 6, 3, 2, 1, 3]
def baseStart_923436 : Nat := 118140960795 + 923436 * 2 ^ 59
def prefixEnd_923436 : Nat := 4983230072969 + 3 ^ 40 * 923436 * 2
def baseEnd_923436 : Nat := 316111014443569524068801

theorem tailTrace_923436 : CollatzResearch.WordTrace tailWord_923436 prefixEnd_923436 316111014443569524068801 := by
  unfold tailWord_923436
  simp only [CollatzResearch.WordTrace]
  refine ⟨16840238941278278578975081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22453651921704371438633441 16840238941278278578975081)
  ·
    refine ⟨12630179205958708934231311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16840238941278278578975081 12630179205958708934231311)
    ·
      refine ⟨18945268808938063401346967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12630179205958708934231311 18945268808938063401346967)
      ·
        refine ⟨28417903213407095102020451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18945268808938063401346967 28417903213407095102020451)
        ·
          refine ⟨42626854820110642653030677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28417903213407095102020451 42626854820110642653030677)
          ·
            refine ⟨1998133819692686374360813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 42626854820110642653030677 1998133819692686374360813)
            ·
              refine ⟨749300182384757390385305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1998133819692686374360813 749300182384757390385305)
              ·
                refine ⟨561975136788568042788979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 749300182384757390385305 561975136788568042788979)
                ·
                  refine ⟨842962705182852064183469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 561975136788568042788979 842962705182852064183469)
                  ·
                    refine ⟨316111014443569524068801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 842962705182852064183469 316111014443569524068801)
                    ·
                      rfl

theorem cell22_923436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 6, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 6, 3, 2, 1, 3].length) (baseStart_923436 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_923436 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_923436 prefixEnd_923436 := by exact prefixLift 923436
  have htrace : WordTrace (prefixWord ++ tailWord_923436) baseStart_923436 baseEnd_923436 := by
    simpa [prefixWord, tailWord_923436, baseEnd_923436] using wordTrace_append hprefix tailTrace_923436
  have hstable : (prefixWord ++ tailWord_923436).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_923436).length < 2 ^ (prefixWord ++ tailWord_923436).sum := by decide
  have hdescent : baseEnd_923436 < baseStart_923436 := by decide
  rcases family_descends (prefixWord ++ tailWord_923436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_923449 : List Nat := [1, 2, 1, 7, 1, 1, 1, 3, 5]
def baseStart_923449 : Nat := 118140960795 + 923449 * 2 ^ 59
def prefixEnd_923449 : Nat := 4983230072969 + 3 ^ 40 * 923449 * 2
def baseEnd_923449 : Nat := 105371821536413941164587

theorem tailTrace_923449 : CollatzResearch.WordTrace tailWord_923449 prefixEnd_923449 105371821536413941164587 := by
  unfold tailWord_923449
  simp only [CollatzResearch.WordTrace]
  refine ⟨33680952031509460378173401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22453968021006306918782267 33680952031509460378173401)
  ·
    refine ⟨25260714023632095283630051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33680952031509460378173401 25260714023632095283630051)
    ·
      refine ⟨37891071035448142925445077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25260714023632095283630051 37891071035448142925445077)
      ·
        refine ⟨888071977393315849815119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 37891071035448142925445077 888071977393315849815119)
        ·
          refine ⟨1332107966089973774722679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 888071977393315849815119 1332107966089973774722679)
          ·
            refine ⟨1998161949134960662084019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1332107966089973774722679 1998161949134960662084019)
            ·
              refine ⟨2997242923702440993126029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1998161949134960662084019 2997242923702440993126029)
              ·
                refine ⟨1123966096388415372422261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2997242923702440993126029 1123966096388415372422261)
                ·
                  refine ⟨105371821536413941164587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1123966096388415372422261 105371821536413941164587)
                  ·
                    rfl

theorem cell22_923449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 1, 1, 3, 5].length) (baseStart_923449 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_923449 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_923449 prefixEnd_923449 := by exact prefixLift 923449
  have htrace : WordTrace (prefixWord ++ tailWord_923449) baseStart_923449 baseEnd_923449 := by
    simpa [prefixWord, tailWord_923449, baseEnd_923449] using wordTrace_append hprefix tailTrace_923449
  have hstable : (prefixWord ++ tailWord_923449).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_923449).length < 2 ^ (prefixWord ++ tailWord_923449).sum := by decide
  have hdescent : baseEnd_923449 < baseStart_923449 := by decide
  rcases family_descends (prefixWord ++ tailWord_923449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_923509 : List Nat := [1, 3, 4, 1, 1, 1, 1, 5, 2, 3]
def baseStart_923509 : Nat := 118140960795 + 923509 * 2 ^ 59
def prefixEnd_923509 : Nat := 4983230072969 + 3 ^ 40 * 923509 * 2
def baseEnd_923509 : Nat := 316136003835421666993577

theorem tailTrace_923509 : CollatzResearch.WordTrace tailWord_923509 prefixEnd_923509 316136003835421666993577 := by
  unfold tailWord_923509
  simp only [CollatzResearch.WordTrace]
  refine ⟨33683140411292090625357581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22455426940861393750238387 33683140411292090625357581)
  ·
    refine ⟨12631177654234533984509093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33683140411292090625357581 12631177654234533984509093)
    ·
      refine ⟨2368345810168975122095455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12631177654234533984509093 2368345810168975122095455)
      ·
        refine ⟨3552518715253462683143183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2368345810168975122095455 3552518715253462683143183)
        ·
          refine ⟨5328778072880194024714775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3552518715253462683143183 5328778072880194024714775)
          ·
            refine ⟨7993167109320291037072163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5328778072880194024714775 7993167109320291037072163)
            ·
              refine ⟨11989750663980436555608245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7993167109320291037072163 11989750663980436555608245)
              ·
                refine ⟨1124039124748165927088273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11989750663980436555608245 1124039124748165927088273)
                ·
                  refine ⟨843029343561124445316205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1124039124748165927088273 843029343561124445316205)
                  ·
                    refine ⟨316136003835421666993577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 843029343561124445316205 316136003835421666993577)
                    ·
                      rfl

theorem cell22_923509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 1, 5, 2, 3].length) (baseStart_923509 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_923509 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_923509 prefixEnd_923509 := by exact prefixLift 923509
  have htrace : WordTrace (prefixWord ++ tailWord_923509) baseStart_923509 baseEnd_923509 := by
    simpa [prefixWord, tailWord_923509, baseEnd_923509] using wordTrace_append hprefix tailTrace_923509
  have hstable : (prefixWord ++ tailWord_923509).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_923509).length < 2 ^ (prefixWord ++ tailWord_923509).sum := by decide
  have hdescent : baseEnd_923509 < baseStart_923509 := by decide
  rcases family_descends (prefixWord ++ tailWord_923509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_923560 : List Nat := [2, 1, 6, 2, 1, 1, 3, 1, 2, 3]
def baseStart_923560 : Nat := 118140960795 + 923560 * 2 ^ 59
def prefixEnd_923560 : Nat := 4983230072969 + 3 ^ 40 * 923560 * 2
def baseEnd_923560 : Nat := 316153462177674533968421

theorem tailTrace_923560 : CollatzResearch.WordTrace tailWord_923560 prefixEnd_923560 316153462177674533968421 := by
  unfold tailWord_923560
  simp only [CollatzResearch.WordTrace]
  refine ⟨16842500267053663167732067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22456667022738217556976089 16842500267053663167732067)
  ·
    refine ⟨25263750400580494751598101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16842500267053663167732067 25263750400580494751598101)
    ·
      refine ⟨1184238300027210691481161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 25263750400580494751598101 1184238300027210691481161)
      ·
        refine ⟨888178725020408018610871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1184238300027210691481161 888178725020408018610871)
        ·
          refine ⟨1332268087530612027916307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 888178725020408018610871 1332268087530612027916307)
          ·
            refine ⟨1998402131295918041874461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1332268087530612027916307 1998402131295918041874461)
            ·
              refine ⟨749400799235969265702923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1998402131295918041874461 749400799235969265702923)
              ·
                refine ⟨1124101198853953898554385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 749400799235969265702923 1124101198853953898554385)
                ·
                  refine ⟨843075899140465423915789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1124101198853953898554385 843075899140465423915789)
                  ·
                    refine ⟨316153462177674533968421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 843075899140465423915789 316153462177674533968421)
                    ·
                      rfl

theorem cell22_923560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 1, 3, 1, 2, 3].length) (baseStart_923560 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_923560 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_923560 prefixEnd_923560 := by exact prefixLift 923560
  have htrace : WordTrace (prefixWord ++ tailWord_923560) baseStart_923560 baseEnd_923560 := by
    simpa [prefixWord, tailWord_923560, baseEnd_923560] using wordTrace_append hprefix tailTrace_923560
  have hstable : (prefixWord ++ tailWord_923560).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_923560).length < 2 ^ (prefixWord ++ tailWord_923560).sum := by decide
  have hdescent : baseEnd_923560 < baseStart_923560 := by decide
  rcases family_descends (prefixWord ++ tailWord_923560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_923674 : List Nat := [3, 1, 1, 3, 1, 5, 1, 7]
def baseStart_923674 : Nat := 118140960795 + 923674 * 2 ^ 59
def prefixEnd_923674 : Nat := 4983230072969 + 3 ^ 40 * 923674 * 2
def baseEnd_923674 : Nat := 35132498523046248513119

theorem tailTrace_923674 : CollatzResearch.WordTrace tailWord_923674 prefixEnd_923674 35132498523046248513119 := by
  unfold tailWord_923674
  simp only [CollatzResearch.WordTrace]
  refine ⟨8422289613923580951278519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22459438970462882536742717 8422289613923580951278519)
  ·
    refine ⟨12633434420885371426917779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8422289613923580951278519 12633434420885371426917779)
    ·
      refine ⟨18950151631328057140376669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12633434420885371426917779 18950151631328057140376669)
      ·
        refine ⟨7106306861748021427641251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18950151631328057140376669 7106306861748021427641251)
        ·
          refine ⟨10659460292622032141461877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7106306861748021427641251 10659460292622032141461877)
          ·
            refine ⟨999324402433315513262051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 10659460292622032141461877 999324402433315513262051)
            ·
              refine ⟨1498986603649973269893077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 999324402433315513262051 1498986603649973269893077)
              ·
                refine ⟨35132498523046248513119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1498986603649973269893077 35132498523046248513119)
                ·
                  rfl

theorem cell22_923674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 5, 1, 7].length) (baseStart_923674 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_923674 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_923674 prefixEnd_923674 := by exact prefixLift 923674
  have htrace : WordTrace (prefixWord ++ tailWord_923674) baseStart_923674 baseEnd_923674 := by
    simpa [prefixWord, tailWord_923674, baseEnd_923674] using wordTrace_append hprefix tailTrace_923674
  have hstable : (prefixWord ++ tailWord_923674).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_923674).length < 2 ^ (prefixWord ++ tailWord_923674).sum := by decide
  have hdescent : baseEnd_923674 < baseStart_923674 := by decide
  rcases family_descends (prefixWord ++ tailWord_923674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_923736 : List Nat := [2, 1, 2, 2, 1, 5, 3, 1, 5]
def baseStart_923736 : Nat := 118140960795 + 923736 * 2 ^ 59
def prefixEnd_923736 : Nat := 4983230072969 + 3 ^ 40 * 923736 * 2
def baseEnd_923736 : Nat := 105404570191489580522627

theorem tailTrace_923736 : CollatzResearch.WordTrace tailWord_923736 prefixEnd_923736 105404570191489580522627 := by
  unfold tailWord_923736
  simp only [CollatzResearch.WordTrace]
  refine ⟨16845709890734854196935531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22460946520979805595914041 16845709890734854196935531)
  ·
    refine ⟨25268564836102281295403297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16845709890734854196935531 25268564836102281295403297)
    ·
      refine ⟨18951423627076710971552473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25268564836102281295403297 18951423627076710971552473)
      ·
        refine ⟨14213567720307533228664355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18951423627076710971552473 14213567720307533228664355)
        ·
          refine ⟨21320351580461299842996533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14213567720307533228664355 21320351580461299842996533)
          ·
            refine ⟨1998782960668246860280925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 21320351580461299842996533 1998782960668246860280925)
            ·
              refine ⟨749543610250592572605347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1998782960668246860280925 749543610250592572605347)
              ·
                refine ⟨1124315415375888858908021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 749543610250592572605347 1124315415375888858908021)
                ·
                  refine ⟨105404570191489580522627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1124315415375888858908021 105404570191489580522627)
                  ·
                    rfl

theorem cell22_923736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 5, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 5, 3, 1, 5].length) (baseStart_923736 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_923736 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_923736 prefixEnd_923736 := by exact prefixLift 923736
  have htrace : WordTrace (prefixWord ++ tailWord_923736) baseStart_923736 baseEnd_923736 := by
    simpa [prefixWord, tailWord_923736, baseEnd_923736] using wordTrace_append hprefix tailTrace_923736
  have hstable : (prefixWord ++ tailWord_923736).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_923736).length < 2 ^ (prefixWord ++ tailWord_923736).sum := by decide
  have hdescent : baseEnd_923736 < baseStart_923736 := by decide
  rcases family_descends (prefixWord ++ tailWord_923736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_923742 : List Nat := [4, 4, 1, 1, 3, 1, 2, 6]
def baseStart_923742 : Nat := 118140960795 + 923742 * 2 ^ 59
def prefixEnd_923742 : Nat := 4983230072969 + 3 ^ 40 * 923742 * 2
def baseEnd_923742 : Nat := 35135084944120747324207

theorem tailTrace_923742 : CollatzResearch.WordTrace tailWord_923742 prefixEnd_923742 35135084944120747324207 := by
  unfold tailWord_923742
  simp only [CollatzResearch.WordTrace]
  refine ⟨4211454827430996427323685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22461092412965314279059653 4211454827430996427323685)
  ·
    refine ⟨789647780143311830123191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4211454827430996427323685 789647780143311830123191)
    ·
      refine ⟨1184471670214967745184787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 789647780143311830123191 1184471670214967745184787)
      ·
        refine ⟨1776707505322451617777181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1184471670214967745184787 1776707505322451617777181)
        ·
          refine ⟨666265314495919356666443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1776707505322451617777181 666265314495919356666443)
          ·
            refine ⟨999397971743879034999665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 666265314495919356666443 999397971743879034999665)
            ·
              refine ⟨749548478807909276249749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 999397971743879034999665 749548478807909276249749)
              ·
                refine ⟨35135084944120747324207, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 749548478807909276249749 35135084944120747324207)
                ·
                  rfl

theorem cell22_923742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 3, 1, 2, 6].length) (baseStart_923742 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_923742 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_923742 prefixEnd_923742 := by exact prefixLift 923742
  have htrace : WordTrace (prefixWord ++ tailWord_923742) baseStart_923742 baseEnd_923742 := by
    simpa [prefixWord, tailWord_923742, baseEnd_923742] using wordTrace_append hprefix tailTrace_923742
  have hstable : (prefixWord ++ tailWord_923742).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_923742).length < 2 ^ (prefixWord ++ tailWord_923742).sum := by decide
  have hdescent : baseEnd_923742 < baseStart_923742 := by decide
  rcases family_descends (prefixWord ++ tailWord_923742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_923781 : List Nat := [1, 3, 1, 1, 5, 3, 1, 1, 6]
def baseStart_923781 : Nat := 118140960795 + 923781 * 2 ^ 59
def prefixEnd_923781 : Nat := 4983230072969 + 3 ^ 40 * 923781 * 2
def baseEnd_923781 : Nat := 105409704998034541397581

theorem tailTrace_923781 : CollatzResearch.WordTrace tailWord_923781 prefixEnd_923781 105409704998034541397581 := by
  unfold tailWord_923781
  simp only [CollatzResearch.WordTrace]
  refine ⟨33693061066306681079259197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22462040710871120719506131 33693061066306681079259197)
  ·
    refine ⟨12634897899865005404722199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33693061066306681079259197 12634897899865005404722199)
    ·
      refine ⟨18952346849797508107083299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12634897899865005404722199 18952346849797508107083299)
      ·
        refine ⟨28428520274696262160624949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18952346849797508107083299 28428520274696262160624949)
        ·
          refine ⟨2665173775752774577558589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 28428520274696262160624949 2665173775752774577558589)
          ·
            refine ⟨999440165907290466584471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2665173775752774577558589 999440165907290466584471)
            ·
              refine ⟨1499160248860935699876707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 999440165907290466584471 1499160248860935699876707)
              ·
                refine ⟨2248740373291403549815061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1499160248860935699876707 2248740373291403549815061)
                ·
                  refine ⟨105409704998034541397581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2248740373291403549815061 105409704998034541397581)
                  ·
                    rfl

theorem cell22_923781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 3, 1, 1, 6].length) (baseStart_923781 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_923781 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_923781 prefixEnd_923781 := by exact prefixLift 923781
  have htrace : WordTrace (prefixWord ++ tailWord_923781) baseStart_923781 baseEnd_923781 := by
    simpa [prefixWord, tailWord_923781, baseEnd_923781] using wordTrace_append hprefix tailTrace_923781
  have hstable : (prefixWord ++ tailWord_923781).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_923781).length < 2 ^ (prefixWord ++ tailWord_923781).sum := by decide
  have hdescent : baseEnd_923781 < baseStart_923781 := by decide
  rcases family_descends (prefixWord ++ tailWord_923781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_923800 : List Nat := [2, 1, 2, 4, 4, 1, 1, 2, 1, 4]
def baseStart_923800 : Nat := 118140960795 + 923800 * 2 ^ 59
def prefixEnd_923800 : Nat := 4983230072969 + 3 ^ 40 * 923800 * 2
def baseEnd_923800 : Nat := 316235619082393907967685

theorem tailTrace_923800 : CollatzResearch.WordTrace tailWord_923800 prefixEnd_923800 316235619082393907967685 := by
  unfold tailWord_923800
  simp only [CollatzResearch.WordTrace]
  refine ⟨16846877026618923662100427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22462502702158564882800569 16846877026618923662100427)
  ·
    refine ⟨25270315539928385493150641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16846877026618923662100427 25270315539928385493150641)
    ·
      refine ⟨18952736654946289119862981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25270315539928385493150641 18952736654946289119862981)
      ·
        refine ⟨3553638122802429209974309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18952736654946289119862981 3553638122802429209974309)
        ·
          refine ⟨666307148025455476870183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3553638122802429209974309 666307148025455476870183)
          ·
            refine ⟨999460722038183215305275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 666307148025455476870183 999460722038183215305275)
            ·
              refine ⟨1499191083057274822957913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 999460722038183215305275 1499191083057274822957913)
              ·
                refine ⟨1124393312292956117218435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1499191083057274822957913 1124393312292956117218435)
                ·
                  refine ⟨1686589968439434175827653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1124393312292956117218435 1686589968439434175827653)
                  ·
                    refine ⟨316235619082393907967685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1686589968439434175827653 316235619082393907967685)
                    ·
                      rfl

theorem cell22_923800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 4, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 4, 1, 1, 2, 1, 4].length) (baseStart_923800 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_923800 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_923800 prefixEnd_923800 := by exact prefixLift 923800
  have htrace : WordTrace (prefixWord ++ tailWord_923800) baseStart_923800 baseEnd_923800 := by
    simpa [prefixWord, tailWord_923800, baseEnd_923800] using wordTrace_append hprefix tailTrace_923800
  have hstable : (prefixWord ++ tailWord_923800).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_923800).length < 2 ^ (prefixWord ++ tailWord_923800).sum := by decide
  have hdescent : baseEnd_923800 < baseStart_923800 := by decide
  rcases family_descends (prefixWord ++ tailWord_923800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_923809 : List Nat := [1, 2, 3, 3, 1, 2, 2, 8]
def baseStart_923809 : Nat := 118140960795 + 923809 * 2 ^ 59
def prefixEnd_923809 : Nat := 4983230072969 + 3 ^ 40 * 923809 * 2
def baseEnd_923809 : Nat := 35137633329591209388073

theorem tailTrace_923809 : CollatzResearch.WordTrace tailWord_923809 prefixEnd_923809 35137633329591209388073 := by
  unfold tailWord_923809
  simp only [CollatzResearch.WordTrace]
  refine ⟨33694082310205241861278481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22462721540136827907518987 33694082310205241861278481)
  ·
    refine ⟨25270561732653931395958861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33694082310205241861278481 25270561732653931395958861)
    ·
      refine ⟨9476460649745224273484573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25270561732653931395958861 9476460649745224273484573)
      ·
        refine ⟨3553672743654459102556715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9476460649745224273484573 3553672743654459102556715)
        ·
          refine ⟨5330509115481688653835073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3553672743654459102556715 5330509115481688653835073)
          ·
            refine ⟨3997881836611266490376305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5330509115481688653835073 3997881836611266490376305)
            ·
              refine ⟨2998411377458449867782229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3997881836611266490376305 2998411377458449867782229)
              ·
                refine ⟨35137633329591209388073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2998411377458449867782229 35137633329591209388073)
                ·
                  rfl

theorem cell22_923809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 2, 8].length) (baseStart_923809 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_923809 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_923809 prefixEnd_923809 := by exact prefixLift 923809
  have htrace : WordTrace (prefixWord ++ tailWord_923809) baseStart_923809 baseEnd_923809 := by
    simpa [prefixWord, tailWord_923809, baseEnd_923809] using wordTrace_append hprefix tailTrace_923809
  have hstable : (prefixWord ++ tailWord_923809).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_923809).length < 2 ^ (prefixWord ++ tailWord_923809).sum := by decide
  have hdescent : baseEnd_923809 < baseStart_923809 := by decide
  rcases family_descends (prefixWord ++ tailWord_923809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_923858 : List Nat := [3, 2, 2, 2, 1, 3, 1, 2, 3, 3]
def baseStart_923858 : Nat := 118140960795 + 923858 * 2 ^ 59
def prefixEnd_923858 : Nat := 4983230072969 + 3 ^ 40 * 923858 * 2
def baseEnd_923858 : Nat := 316255473667701090017507

theorem tailTrace_923858 : CollatzResearch.WordTrace tailWord_923858 prefixEnd_923858 316255473667701090017507 := by
  unfold tailWord_923858
  simp only [CollatzResearch.WordTrace]
  refine ⟨8423967371756930807453057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22463912991351815486541485 8423967371756930807453057)
  ·
    refine ⟨6317975528817698105589793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8423967371756930807453057 6317975528817698105589793)
    ·
      refine ⟨4738481646613273579192345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6317975528817698105589793 4738481646613273579192345)
      ·
        refine ⟨3553861234959955184394259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4738481646613273579192345 3553861234959955184394259)
        ·
          refine ⟨5330791852439932776591389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3553861234959955184394259 5330791852439932776591389)
          ·
            refine ⟨1999046944664974791221771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5330791852439932776591389 1999046944664974791221771)
            ·
              refine ⟨2998570416997462186832657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1999046944664974791221771 2998570416997462186832657)
              ·
                refine ⟨2248927812748096640124493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2998570416997462186832657 2248927812748096640124493)
                ·
                  refine ⟨843347929780536240046685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2248927812748096640124493 843347929780536240046685)
                  ·
                    refine ⟨316255473667701090017507, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 843347929780536240046685 316255473667701090017507)
                    ·
                      rfl

theorem cell22_923858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 3, 1, 2, 3, 3].length) (baseStart_923858 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_923858 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_923858 prefixEnd_923858 := by exact prefixLift 923858
  have htrace : WordTrace (prefixWord ++ tailWord_923858) baseStart_923858 baseEnd_923858 := by
    simpa [prefixWord, tailWord_923858, baseEnd_923858] using wordTrace_append hprefix tailTrace_923858
  have hstable : (prefixWord ++ tailWord_923858).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_923858).length < 2 ^ (prefixWord ++ tailWord_923858).sum := by decide
  have hdescent : baseEnd_923858 < baseStart_923858 := by decide
  rcases family_descends (prefixWord ++ tailWord_923858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_923918 : List Nat := [4, 1, 1, 2, 1, 2, 4, 2, 1, 4]
def baseStart_923918 : Nat := 118140960795 + 923918 * 2 ^ 59
def prefixEnd_923918 : Nat := 4983230072969 + 3 ^ 40 * 923918 * 2
def baseEnd_923918 : Nat := 316276012893880933517323

theorem tailTrace_923918 : CollatzResearch.WordTrace tailWord_923918 prefixEnd_923918 316276012893880933517323 := by
  unfold tailWord_923918
  simp only [CollatzResearch.WordTrace]
  refine ⟨4212257233351294184624551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22465371911206902317997605 4212257233351294184624551)
  ·
    refine ⟨6318385850026941276936827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4212257233351294184624551 6318385850026941276936827)
    ·
      refine ⟨9477578775040411915405241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6318385850026941276936827 9477578775040411915405241)
      ·
        refine ⟨7108184081280308936553931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9477578775040411915405241 7108184081280308936553931)
        ·
          refine ⟨10662276121920463404830897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7108184081280308936553931 10662276121920463404830897)
          ·
            refine ⟨7996707091440347553623173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10662276121920463404830897 7996707091440347553623173)
            ·
              refine ⟨1499382579645065166304345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7996707091440347553623173 1499382579645065166304345)
              ·
                refine ⟨1124536934733798874728259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1499382579645065166304345 1124536934733798874728259)
                ·
                  refine ⟨1686805402100698312092389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1124536934733798874728259 1686805402100698312092389)
                  ·
                    refine ⟨316276012893880933517323, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1686805402100698312092389 316276012893880933517323)
                    ·
                      rfl

theorem cell22_923918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 4, 2, 1, 4].length) (baseStart_923918 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_923918 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_923918 prefixEnd_923918 := by exact prefixLift 923918
  have htrace : WordTrace (prefixWord ++ tailWord_923918) baseStart_923918 baseEnd_923918 := by
    simpa [prefixWord, tailWord_923918, baseEnd_923918] using wordTrace_append hprefix tailTrace_923918
  have hstable : (prefixWord ++ tailWord_923918).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_923918).length < 2 ^ (prefixWord ++ tailWord_923918).sum := by decide
  have hdescent : baseEnd_923918 < baseStart_923918 := by decide
  rcases family_descends (prefixWord ++ tailWord_923918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_923931 : List Nat := [1, 1, 1, 1, 1, 1, 7, 2, 4, 3]
def baseStart_923931 : Nat := 118140960795 + 923931 * 2 ^ 59
def prefixEnd_923931 : Nat := 4983230072969 + 3 ^ 40 * 923931 * 2
def baseEnd_923931 : Nat := 316280463059553232942283

theorem tailTrace_923931 : CollatzResearch.WordTrace tailWord_923931 prefixEnd_923931 316280463059553232942283 := by
  unfold tailWord_923931
  simp only [CollatzResearch.WordTrace]
  refine ⟨33698532015763256697219647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22465688010508837798146431 33698532015763256697219647)
  ·
    refine ⟨50547798023644885045829471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33698532015763256697219647 50547798023644885045829471)
    ·
      refine ⟨75821697035467327568744207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50547798023644885045829471 75821697035467327568744207)
      ·
        refine ⟨113732545553200991353116311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75821697035467327568744207 113732545553200991353116311)
        ·
          refine ⟨170598818329801487029674467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113732545553200991353116311 170598818329801487029674467)
          ·
            refine ⟨255898227494702230544511701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 170598818329801487029674467 255898227494702230544511701)
            ·
              refine ⟨5997614706907083528386993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 255898227494702230544511701 5997614706907083528386993)
              ·
                refine ⟨4498211030180312646290245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5997614706907083528386993 4498211030180312646290245)
                ·
                  refine ⟨843414568158808621179421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4498211030180312646290245 843414568158808621179421)
                  ·
                    refine ⟨316280463059553232942283, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 843414568158808621179421 316280463059553232942283)
                    ·
                      rfl

theorem cell22_923931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 7, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 7, 2, 4, 3].length) (baseStart_923931 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_923931 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_923931 prefixEnd_923931 := by exact prefixLift 923931
  have htrace : WordTrace (prefixWord ++ tailWord_923931) baseStart_923931 baseEnd_923931 := by
    simpa [prefixWord, tailWord_923931, baseEnd_923931] using wordTrace_append hprefix tailTrace_923931
  have hstable : (prefixWord ++ tailWord_923931).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_923931).length < 2 ^ (prefixWord ++ tailWord_923931).sum := by decide
  have hdescent : baseEnd_923931 < baseStart_923931 := by decide
  rcases family_descends (prefixWord ++ tailWord_923931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_923961 : List Nat := [1, 2, 1, 6, 1, 1, 1, 9]
def baseStart_923961 : Nat := 118140960795 + 923961 * 2 ^ 59
def prefixEnd_923961 : Nat := 4983230072969 + 3 ^ 40 * 923961 * 2
def baseEnd_923961 : Nat := 35143414741404794965799

theorem tailTrace_923961 : CollatzResearch.WordTrace tailWord_923961 prefixEnd_923961 35143414741404794965799 := by
  unfold tailWord_923961
  simp only [CollatzResearch.WordTrace]
  refine ⟨33699626205654571820811737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22466417470436381213874491 33699626205654571820811737)
  ·
    refine ⟨25274719654240928865608803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33699626205654571820811737 25274719654240928865608803)
    ·
      refine ⟨37912079481361393298413205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25274719654240928865608803 37912079481361393298413205)
      ·
        refine ⟨1777128725688815310863119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 37912079481361393298413205 1777128725688815310863119)
        ·
          refine ⟨2665693088533222966294679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1777128725688815310863119 2665693088533222966294679)
          ·
            refine ⟨3998539632799834449442019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2665693088533222966294679 3998539632799834449442019)
            ·
              refine ⟨5997809449199751674163029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3998539632799834449442019 5997809449199751674163029)
              ·
                refine ⟨35143414741404794965799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 5997809449199751674163029 35143414741404794965799)
                ·
                  rfl

theorem cell22_923961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 1, 9].length) (baseStart_923961 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_923961 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_923961 prefixEnd_923961 := by exact prefixLift 923961
  have htrace : WordTrace (prefixWord ++ tailWord_923961) baseStart_923961 baseEnd_923961 := by
    simpa [prefixWord, tailWord_923961, baseEnd_923961] using wordTrace_append hprefix tailTrace_923961
  have hstable : (prefixWord ++ tailWord_923961).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_923961).length < 2 ^ (prefixWord ++ tailWord_923961).sum := by decide
  have hdescent : baseEnd_923961 < baseStart_923961 := by decide
  rcases family_descends (prefixWord ++ tailWord_923961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_924237 : List Nat := [1, 6, 1, 1, 2, 2, 2, 1, 6]
def baseStart_924237 : Nat := 118140960795 + 924237 * 2 ^ 59
def prefixEnd_924237 : Nat := 4983230072969 + 3 ^ 40 * 924237 * 2
def baseEnd_924237 : Nat := 105461737704356811597115

theorem tailTrace_924237 : CollatzResearch.WordTrace tailWord_924237 prefixEnd_924237 105461737704356811597115 := by
  unfold tailWord_924237
  simp only [CollatzResearch.WordTrace]
  refine ⟨33709692752654670957858965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22473128501769780638572643 33709692752654670957858965)
  ·
    refine ⟨1580141847780687701149639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 33709692752654670957858965 1580141847780687701149639)
    ·
      refine ⟨2370212771671031551724459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1580141847780687701149639 2370212771671031551724459)
      ·
        refine ⟨3555319157506547327586689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2370212771671031551724459 3555319157506547327586689)
        ·
          refine ⟨2666489368129910495690017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3555319157506547327586689 2666489368129910495690017)
          ·
            refine ⟨1999867026097432871767513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2666489368129910495690017 1999867026097432871767513)
            ·
              refine ⟨1499900269573074653825635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1999867026097432871767513 1499900269573074653825635)
              ·
                refine ⟨2249850404359611980738453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1499900269573074653825635 2249850404359611980738453)
                ·
                  refine ⟨105461737704356811597115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2249850404359611980738453 105461737704356811597115)
                  ·
                    rfl

theorem cell22_924237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 2, 2, 1, 6].length) (baseStart_924237 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_924237 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_924237 prefixEnd_924237 := by exact prefixLift 924237
  have htrace : WordTrace (prefixWord ++ tailWord_924237) baseStart_924237 baseEnd_924237 := by
    simpa [prefixWord, tailWord_924237, baseEnd_924237] using wordTrace_append hprefix tailTrace_924237
  have hstable : (prefixWord ++ tailWord_924237).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_924237).length < 2 ^ (prefixWord ++ tailWord_924237).sum := by decide
  have hdescent : baseEnd_924237 < baseStart_924237 := by decide
  rcases family_descends (prefixWord ++ tailWord_924237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_924263 : List Nat := [1, 1, 5, 1, 1, 1, 1, 1, 1, 9]
def baseStart_924263 : Nat := 118140960795 + 924263 * 2 ^ 59
def prefixEnd_924263 : Nat := 4983230072969 + 3 ^ 40 * 924263 * 2
def baseEnd_924263 : Nat := 316394113444415033641265

theorem tailTrace_924263 : CollatzResearch.WordTrace tailWord_924263 prefixEnd_924263 316394113444415033641265 := by
  unfold tailWord_924263
  simp only [CollatzResearch.WordTrace]
  refine ⟨33710641050560477398305443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22473760700373651598870295 33710641050560477398305443)
  ·
    refine ⟨50565961575840716097458165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33710641050560477398305443 50565961575840716097458165)
    ·
      refine ⟨4740558897735067134136703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 50565961575840716097458165 4740558897735067134136703)
      ·
        refine ⟨7110838346602600701205055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4740558897735067134136703 7110838346602600701205055)
        ·
          refine ⟨10666257519903901051807583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7110838346602600701205055 10666257519903901051807583)
          ·
            refine ⟨15999386279855851577711375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10666257519903901051807583 15999386279855851577711375)
            ·
              refine ⟨23999079419783777366567063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15999386279855851577711375 23999079419783777366567063)
              ·
                refine ⟨35998619129675666049850595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23999079419783777366567063 35998619129675666049850595)
                ·
                  refine ⟨53997928694513499074775893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35998619129675666049850595 53997928694513499074775893)
                  ·
                    refine ⟨316394113444415033641265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 53997928694513499074775893 316394113444415033641265)
                    ·
                      rfl

theorem cell22_924263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 1, 1, 9].length) (baseStart_924263 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_924263 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_924263 prefixEnd_924263 := by exact prefixLift 924263
  have htrace : WordTrace (prefixWord ++ tailWord_924263) baseStart_924263 baseEnd_924263 := by
    simpa [prefixWord, tailWord_924263, baseEnd_924263] using wordTrace_append hprefix tailTrace_924263
  have hstable : (prefixWord ++ tailWord_924263).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_924263).length < 2 ^ (prefixWord ++ tailWord_924263).sum := by decide
  have hdescent : baseEnd_924263 < baseStart_924263 := by decide
  rcases family_descends (prefixWord ++ tailWord_924263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_924387 : List Nat := [1, 1, 1, 7, 1, 1, 2, 2, 1, 5]
def baseStart_924387 : Nat := 118140960795 + 924387 * 2 ^ 59
def prefixEnd_924387 : Nat := 4983230072969 + 3 ^ 40 * 924387 * 2
def baseEnd_924387 : Nat := 316436561178520043540885

theorem tailTrace_924387 : CollatzResearch.WordTrace tailWord_924387 prefixEnd_924387 316436561178520043540885 := by
  unfold tailWord_924387
  simp only [CollatzResearch.WordTrace]
  refine ⟨33715163702111246575819415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22476775801407497717212943 33715163702111246575819415)
  ·
    refine ⟨50572745553166869863729123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33715163702111246575819415 50572745553166869863729123)
    ·
      refine ⟨75859118329750304795593685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50572745553166869863729123 75859118329750304795593685)
      ·
        refine ⟨1777948085853522768646727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 75859118329750304795593685 1777948085853522768646727)
        ·
          refine ⟨2666922128780284152970091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1777948085853522768646727 2666922128780284152970091)
          ·
            refine ⟨4000383193170426229455137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2666922128780284152970091 4000383193170426229455137)
            ·
              refine ⟨3000287394877819672091353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4000383193170426229455137 3000287394877819672091353)
              ·
                refine ⟨2250215546158364754068515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3000287394877819672091353 2250215546158364754068515)
                ·
                  refine ⟨3375323319237547131102773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2250215546158364754068515 3375323319237547131102773)
                  ·
                    refine ⟨316436561178520043540885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3375323319237547131102773 316436561178520043540885)
                    ·
                      rfl

theorem cell22_924387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 2, 2, 1, 5].length) (baseStart_924387 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_924387 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_924387 prefixEnd_924387 := by exact prefixLift 924387
  have htrace : WordTrace (prefixWord ++ tailWord_924387) baseStart_924387 baseEnd_924387 := by
    simpa [prefixWord, tailWord_924387, baseEnd_924387] using wordTrace_append hprefix tailTrace_924387
  have hstable : (prefixWord ++ tailWord_924387).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_924387).length < 2 ^ (prefixWord ++ tailWord_924387).sum := by decide
  have hdescent : baseEnd_924387 < baseStart_924387 := by decide
  rcases family_descends (prefixWord ++ tailWord_924387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_924389 : List Nat := [1, 3, 1, 4, 1, 3, 2, 3, 4]
def baseStart_924389 : Nat := 118140960795 + 924389 * 2 ^ 59
def prefixEnd_924389 : Nat := 4983230072969 + 3 ^ 40 * 924389 * 2
def baseEnd_924389 : Nat := 105479081939797568330293

theorem tailTrace_924389 : CollatzResearch.WordTrace tailWord_924389 prefixEnd_924389 105479081939797568330293 := by
  unfold tailWord_924389
  simp only [CollatzResearch.WordTrace]
  refine ⟨33715236648104000917392221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22476824432069333944928147 33715236648104000917392221)
  ·
    refine ⟨12643213743039000344022083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33715236648104000917392221 12643213743039000344022083)
    ·
      refine ⟨18964820614558500516033125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12643213743039000344022083 18964820614558500516033125)
      ·
        refine ⟨3555903865229718846756211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18964820614558500516033125 3555903865229718846756211)
        ·
          refine ⟨5333855797844578270134317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3555903865229718846756211 5333855797844578270134317)
          ·
            refine ⟨2000195924191716851300369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5333855797844578270134317 2000195924191716851300369)
            ·
              refine ⟨1500146943143787638475277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2000195924191716851300369 1500146943143787638475277)
              ·
                refine ⟨562555103678920364428229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1500146943143787638475277 562555103678920364428229)
                ·
                  refine ⟨105479081939797568330293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 562555103678920364428229 105479081939797568330293)
                  ·
                    rfl

theorem cell22_924389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 3, 2, 3, 4].length) (baseStart_924389 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_924389 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_924389 prefixEnd_924389 := by exact prefixLift 924389
  have htrace : WordTrace (prefixWord ++ tailWord_924389) baseStart_924389 baseEnd_924389 := by
    simpa [prefixWord, tailWord_924389, baseEnd_924389] using wordTrace_append hprefix tailTrace_924389
  have hstable : (prefixWord ++ tailWord_924389).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_924389).length < 2 ^ (prefixWord ++ tailWord_924389).sum := by decide
  have hdescent : baseEnd_924389 < baseStart_924389 := by decide
  rcases family_descends (prefixWord ++ tailWord_924389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_924434 : List Nat := [3, 2, 4, 1, 2, 1, 1, 8]
def baseStart_924434 : Nat := 118140960795 + 924434 * 2 ^ 59
def prefixEnd_924434 : Nat := 4983230072969 + 3 ^ 40 * 924434 * 2
def baseEnd_924434 : Nat := 35161405582114176401749

theorem tailTrace_924434 : CollatzResearch.WordTrace tailWord_924434 prefixEnd_924434 35161405582114176401749 := by
  unfold tailWord_924434
  simp only [CollatzResearch.WordTrace]
  refine ⟨8429219483235243400695089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22477918621960649068520237 8429219483235243400695089)
  ·
    refine ⟨6321914612426432550521317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8429219483235243400695089 6321914612426432550521317)
    ·
      refine ⟨1185358989829956103222747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6321914612426432550521317 1185358989829956103222747)
      ·
        refine ⟨1778038484744934154834121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1185358989829956103222747 1778038484744934154834121)
        ·
          refine ⟨1333528863558700616125591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1778038484744934154834121 1333528863558700616125591)
          ·
            refine ⟨2000293295338050924188387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1333528863558700616125591 2000293295338050924188387)
            ·
              refine ⟨3000439943007076386282581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2000293295338050924188387 3000439943007076386282581)
              ·
                refine ⟨35161405582114176401749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3000439943007076386282581 35161405582114176401749)
                ·
                  rfl

theorem cell22_924434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 1, 1, 8].length) (baseStart_924434 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_924434 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_924434 prefixEnd_924434 := by exact prefixLift 924434
  have htrace : WordTrace (prefixWord ++ tailWord_924434) baseStart_924434 baseEnd_924434 := by
    simpa [prefixWord, tailWord_924434, baseEnd_924434] using wordTrace_append hprefix tailTrace_924434
  have hstable : (prefixWord ++ tailWord_924434).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_924434).length < 2 ^ (prefixWord ++ tailWord_924434).sum := by decide
  have hdescent : baseEnd_924434 < baseStart_924434 := by decide
  rcases family_descends (prefixWord ++ tailWord_924434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_924479 : List Nat := [1, 1, 2, 2, 5, 1, 4, 1, 5]
def baseStart_924479 : Nat := 118140960795 + 924479 * 2 ^ 59
def prefixEnd_924479 : Nat := 4983230072969 + 3 ^ 40 * 924479 * 2
def baseEnd_924479 : Nat := 105489351552887490080201

theorem tailTrace_924479 : CollatzResearch.WordTrace tailWord_924479 prefixEnd_924479 105489351552887490080201 := by
  unfold tailWord_924479
  simp only [CollatzResearch.WordTrace]
  refine ⟨33718519217777946288168491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22479012811851964192112327 33718519217777946288168491)
  ·
    refine ⟨50577778826666919432252737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33718519217777946288168491 50577778826666919432252737)
    ·
      refine ⟨37933334120000189574189553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50577778826666919432252737 37933334120000189574189553)
      ·
        refine ⟨28450000590000142180642165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37933334120000189574189553 28450000590000142180642165)
        ·
          refine ⟨2667187555312513329435203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 28450000590000142180642165 2667187555312513329435203)
          ·
            refine ⟨4000781332968769994152805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2667187555312513329435203 4000781332968769994152805)
            ·
              refine ⟨750146499931644373903651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4000781332968769994152805 750146499931644373903651)
              ·
                refine ⟨1125219749897466560855477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 750146499931644373903651 1125219749897466560855477)
                ·
                  refine ⟨105489351552887490080201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1125219749897466560855477 105489351552887490080201)
                  ·
                    rfl

theorem cell22_924479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 4, 1, 5].length) (baseStart_924479 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_924479 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_924479 prefixEnd_924479 := by exact prefixLift 924479
  have htrace : WordTrace (prefixWord ++ tailWord_924479) baseStart_924479 baseEnd_924479 := by
    simpa [prefixWord, tailWord_924479, baseEnd_924479] using wordTrace_append hprefix tailTrace_924479
  have hstable : (prefixWord ++ tailWord_924479).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_924479).length < 2 ^ (prefixWord ++ tailWord_924479).sum := by decide
  have hdescent : baseEnd_924479 < baseStart_924479 := by decide
  rcases family_descends (prefixWord ++ tailWord_924479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_924524 : List Nat := [2, 2, 1, 1, 4, 1, 3, 4, 4]
def baseStart_924524 : Nat := 118140960795 + 924524 * 2 ^ 59
def prefixEnd_924524 : Nat := 4983230072969 + 3 ^ 40 * 924524 * 2
def baseEnd_924524 : Nat := 105494486359432450955155

theorem tailTrace_924524 : CollatzResearch.WordTrace tailWord_924524 prefixEnd_924524 105494486359432450955155 := by
  unfold tailWord_924524
  simp only [CollatzResearch.WordTrace]
  refine ⟨16860080251307459486778313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22480107001743279315704417 16860080251307459486778313)
  ·
    refine ⟨12645060188480594615083735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16860080251307459486778313 12645060188480594615083735)
    ·
      refine ⟨18967590282720891922625603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12645060188480594615083735 18967590282720891922625603)
      ·
        refine ⟨28451385424081337883938405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18967590282720891922625603 28451385424081337883938405)
        ·
          refine ⟨5334634767015250853238451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28451385424081337883938405 5334634767015250853238451)
          ·
            refine ⟨8001952150522876279857677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5334634767015250853238451 8001952150522876279857677)
            ·
              refine ⟨3000732056446078604946629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8001952150522876279857677 3000732056446078604946629)
              ·
                refine ⟨562637260583639738427493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3000732056446078604946629 562637260583639738427493)
                ·
                  refine ⟨105494486359432450955155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 562637260583639738427493 105494486359432450955155)
                  ·
                    rfl

theorem cell22_924524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 3, 4, 4].length) (baseStart_924524 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_924524 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_924524 prefixEnd_924524 := by exact prefixLift 924524
  have htrace : WordTrace (prefixWord ++ tailWord_924524) baseStart_924524 baseEnd_924524 := by
    simpa [prefixWord, tailWord_924524, baseEnd_924524] using wordTrace_append hprefix tailTrace_924524
  have hstable : (prefixWord ++ tailWord_924524).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_924524).length < 2 ^ (prefixWord ++ tailWord_924524).sum := by decide
  have hdescent : baseEnd_924524 < baseStart_924524 := by decide
  rcases family_descends (prefixWord ++ tailWord_924524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_924539 : List Nat := [1, 1, 1, 1, 1, 5, 4, 3, 2, 3]
def baseStart_924539 : Nat := 118140960795 + 924539 * 2 ^ 59
def prefixEnd_924539 : Nat := 4983230072969 + 3 ^ 40 * 924539 * 2
def baseEnd_924539 : Nat := 316488593884842313740419

theorem tailTrace_924539 : CollatzResearch.WordTrace tailWord_924539 prefixEnd_924539 316488593884842313740419 := by
  unfold tailWord_924539
  simp only [CollatzResearch.WordTrace]
  refine ⟨33720707597560576535352671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22480471731707051023568447 33720707597560576535352671)
  ·
    refine ⟨50581061396340864803029007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33720707597560576535352671 50581061396340864803029007)
    ·
      refine ⟨75871592094511297204543511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50581061396340864803029007 75871592094511297204543511)
      ·
        refine ⟨113807388141766945806815267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75871592094511297204543511 113807388141766945806815267)
        ·
          refine ⟨170711082212650418710222901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 113807388141766945806815267 170711082212650418710222901)
          ·
            refine ⟨16004163957435976754083397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 170711082212650418710222901 16004163957435976754083397)
            ·
              refine ⟨3000780742019245641390637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16004163957435976754083397 3000780742019245641390637)
              ·
                refine ⟨1125292778257217115521489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3000780742019245641390637 1125292778257217115521489)
                ·
                  refine ⟨843969583692912836641117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1125292778257217115521489 843969583692912836641117)
                  ·
                    refine ⟨316488593884842313740419, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 843969583692912836641117 316488593884842313740419)
                    ·
                      rfl

theorem cell22_924539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 4, 3, 2, 3].length) (baseStart_924539 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_924539 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_924539 prefixEnd_924539 := by exact prefixLift 924539
  have htrace : WordTrace (prefixWord ++ tailWord_924539) baseStart_924539 baseEnd_924539 := by
    simpa [prefixWord, tailWord_924539, baseEnd_924539] using wordTrace_append hprefix tailTrace_924539
  have hstable : (prefixWord ++ tailWord_924539).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_924539).length < 2 ^ (prefixWord ++ tailWord_924539).sum := by decide
  have hdescent : baseEnd_924539 < baseStart_924539 := by decide
  rcases family_descends (prefixWord ++ tailWord_924539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_924554 : List Nat := [3, 1, 2, 4, 1, 2, 1, 1, 1, 6]
def baseStart_924554 : Nat := 118140960795 + 924554 * 2 ^ 59
def prefixEnd_924554 : Nat := 4983230072969 + 3 ^ 40 * 924554 * 2
def baseEnd_924554 : Nat := 316493728691387274615373

theorem tailTrace_924554 : CollatzResearch.WordTrace tailWord_924554 prefixEnd_924554 316493728691387274615373 := by
  unfold tailWord_924554
  simp only [CollatzResearch.WordTrace]
  refine ⟨8430313673126558524287179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22480836461670822731432477 8430313673126558524287179)
  ·
    refine ⟨12645470509689837786430769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8430313673126558524287179 12645470509689837786430769)
    ·
      refine ⟨9484102882267378339823077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12645470509689837786430769 9484102882267378339823077)
      ·
        refine ⟨1778269290425133438716827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9484102882267378339823077 1778269290425133438716827)
        ·
          refine ⟨2667403935637700158075241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1778269290425133438716827 2667403935637700158075241)
          ·
            refine ⟨2000552951728275118556431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2667403935637700158075241 2000552951728275118556431)
            ·
              refine ⟨3000829427592412677834647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2000552951728275118556431 3000829427592412677834647)
              ·
                refine ⟨4501244141388619016751971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3000829427592412677834647 4501244141388619016751971)
                ·
                  refine ⟨6751866212082928525127957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4501244141388619016751971 6751866212082928525127957)
                  ·
                    refine ⟨316493728691387274615373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6751866212082928525127957 316493728691387274615373)
                    ·
                      rfl

theorem cell22_924554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 2, 1, 1, 1, 6].length) (baseStart_924554 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_924554 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_924554 prefixEnd_924554 := by exact prefixLift 924554
  have htrace : WordTrace (prefixWord ++ tailWord_924554) baseStart_924554 baseEnd_924554 := by
    simpa [prefixWord, tailWord_924554, baseEnd_924554] using wordTrace_append hprefix tailTrace_924554
  have hstable : (prefixWord ++ tailWord_924554).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_924554).length < 2 ^ (prefixWord ++ tailWord_924554).sum := by decide
  have hdescent : baseEnd_924554 < baseStart_924554 := by decide
  rcases family_descends (prefixWord ++ tailWord_924554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_924672 : List Nat := [2, 1, 1, 2, 1, 1, 1, 2, 5, 6]
def baseStart_924672 : Nat := 118140960795 + 924672 * 2 ^ 59
def prefixEnd_924672 : Nat := 4983230072969 + 3 ^ 40 * 924672 * 2
def baseEnd_924672 : Nat := 316534122502874300165011

theorem tailTrace_924672 : CollatzResearch.WordTrace tailWord_924672 prefixEnd_924672 316534122502874300165011 := by
  unfold tailWord_924672
  simp only [CollatzResearch.WordTrace]
  refine ⟨16862779253039370124972135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22483705670719160166629513 16862779253039370124972135)
  ·
    refine ⟨25294168879559055187458203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16862779253039370124972135 25294168879559055187458203)
    ·
      refine ⟨37941253319338582781187305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25294168879559055187458203 37941253319338582781187305)
      ·
        refine ⟨28455939989503937085890479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37941253319338582781187305 28455939989503937085890479)
        ·
          refine ⟨42683909984255905628835719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28455939989503937085890479 42683909984255905628835719)
          ·
            refine ⟨64025864976383858443253579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42683909984255905628835719 64025864976383858443253579)
            ·
              refine ⟨96038797464575787664880369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64025864976383858443253579 96038797464575787664880369)
              ·
                refine ⟨72029098098431840748660277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 96038797464575787664880369 72029098098431840748660277)
                ·
                  refine ⟨6752727946727985070186901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 72029098098431840748660277 6752727946727985070186901)
                  ·
                    refine ⟨316534122502874300165011, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6752727946727985070186901 316534122502874300165011)
                    ·
                      rfl

theorem cell22_924672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 2, 5, 6].length) (baseStart_924672 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_924672 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_924672 prefixEnd_924672 := by exact prefixLift 924672
  have htrace : WordTrace (prefixWord ++ tailWord_924672) baseStart_924672 baseEnd_924672 := by
    simpa [prefixWord, tailWord_924672, baseEnd_924672] using wordTrace_append hprefix tailTrace_924672
  have hstable : (prefixWord ++ tailWord_924672).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_924672).length < 2 ^ (prefixWord ++ tailWord_924672).sum := by decide
  have hdescent : baseEnd_924672 < baseStart_924672 := by decide
  rcases family_descends (prefixWord ++ tailWord_924672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_924693 : List Nat := [1, 3, 2, 1, 4, 1, 4, 2, 4]
def baseStart_924693 : Nat := 118140960795 + 924693 * 2 ^ 59
def prefixEnd_924693 : Nat := 4983230072969 + 3 ^ 40 * 924693 * 2
def baseEnd_924693 : Nat := 105513770410679081796649

theorem tailTrace_924693 : CollatzResearch.WordTrace tailWord_924693 prefixEnd_924693 105513770410679081796649 := by
  unfold tailWord_924693
  simp only [CollatzResearch.WordTrace]
  refine ⟨33726324439002660836458733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22484216292668440557639155 33726324439002660836458733)
  ·
    refine ⟨12647371664625997813672025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33726324439002660836458733 12647371664625997813672025)
    ·
      refine ⟨9485528748469498360254019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12647371664625997813672025 9485528748469498360254019)
      ·
        refine ⟨14228293122704247540381029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9485528748469498360254019 14228293122704247540381029)
        ·
          refine ⟨2667804960507046413821443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14228293122704247540381029 2667804960507046413821443)
          ·
            refine ⟨4001707440760569620732165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2667804960507046413821443 4001707440760569620732165)
            ·
              refine ⟨750320145142606803887281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4001707440760569620732165 750320145142606803887281)
              ·
                refine ⟨562740108856955102915461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 750320145142606803887281 562740108856955102915461)
                ·
                  refine ⟨105513770410679081796649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 562740108856955102915461 105513770410679081796649)
                  ·
                    rfl

theorem cell22_924693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 4, 2, 4].length) (baseStart_924693 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_924693 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_924693 prefixEnd_924693 := by exact prefixLift 924693
  have htrace : WordTrace (prefixWord ++ tailWord_924693) baseStart_924693 baseEnd_924693 := by
    simpa [prefixWord, tailWord_924693, baseEnd_924693] using wordTrace_append hprefix tailTrace_924693
  have hstable : (prefixWord ++ tailWord_924693).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_924693).length < 2 ^ (prefixWord ++ tailWord_924693).sum := by decide
  have hdescent : baseEnd_924693 < baseStart_924693 := by decide
  rcases family_descends (prefixWord ++ tailWord_924693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_924708 : List Nat := [2, 3, 1, 4, 1, 1, 2, 3, 2, 3]
def baseStart_924708 : Nat := 118140960795 + 924708 * 2 ^ 59
def prefixEnd_924708 : Nat := 4983230072969 + 3 ^ 40 * 924708 * 2
def baseEnd_924708 : Nat := 316546446038582206264901

theorem tailTrace_924708 : CollatzResearch.WordTrace tailWord_924708 prefixEnd_924708 316546446038582206264901 := by
  unfold tailWord_924708
  simp only [CollatzResearch.WordTrace]
  refine ⟨16863435766974159199127389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22484581022632212265503185 16863435766974159199127389)
  ·
    refine ⟨6323788412615309699672771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16863435766974159199127389 6323788412615309699672771)
    ·
      refine ⟨9485682618922964549509157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6323788412615309699672771 9485682618922964549509157)
      ·
        refine ⟨1778565491048055853032967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9485682618922964549509157 1778565491048055853032967)
        ·
          refine ⟨2667848236572083779549451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1778565491048055853032967 2667848236572083779549451)
          ·
            refine ⟨4001772354858125669324177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2667848236572083779549451 4001772354858125669324177)
            ·
              refine ⟨3001329266143594251993133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4001772354858125669324177 3001329266143594251993133)
              ·
                refine ⟨1125498474803847844497425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3001329266143594251993133 1125498474803847844497425)
                ·
                  refine ⟨844123856102885883373069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1125498474803847844497425 844123856102885883373069)
                  ·
                    refine ⟨316546446038582206264901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 844123856102885883373069 316546446038582206264901)
                    ·
                      rfl

theorem cell22_924708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 2, 3, 2, 3].length) (baseStart_924708 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_924708 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_924708 prefixEnd_924708 := by exact prefixLift 924708
  have htrace : WordTrace (prefixWord ++ tailWord_924708) baseStart_924708 baseEnd_924708 := by
    simpa [prefixWord, tailWord_924708, baseEnd_924708] using wordTrace_append hprefix tailTrace_924708
  have hstable : (prefixWord ++ tailWord_924708).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_924708).length < 2 ^ (prefixWord ++ tailWord_924708).sum := by decide
  have hdescent : baseEnd_924708 < baseStart_924708 := by decide
  rcases family_descends (prefixWord ++ tailWord_924708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_924742 : List Nat := [6, 1, 1, 1, 1, 4, 1, 2, 2, 3]
def baseStart_924742 : Nat := 118140960795 + 924742 * 2 ^ 59
def prefixEnd_924742 : Nat := 4983230072969 + 3 ^ 40 * 924742 * 2
def baseEnd_924742 : Nat := 316558084933417450914797

theorem tailTrace_924742 : CollatzResearch.WordTrace tailWord_924742 prefixEnd_924742 316558084933417450914797 := by
  unfold tailWord_924742
  simp only [CollatzResearch.WordTrace]
  refine ⟨1054003487994535693906015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 22485407743883428136661653 1054003487994535693906015)
  ·
    refine ⟨1581005231991803540859023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1054003487994535693906015 1581005231991803540859023)
    ·
      refine ⟨2371507847987705311288535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1581005231991803540859023 2371507847987705311288535)
      ·
        refine ⟨3557261771981557966932803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2371507847987705311288535 3557261771981557966932803)
        ·
          refine ⟨5335892657972336950399205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3557261771981557966932803 5335892657972336950399205)
          ·
            refine ⟨1000479873369813178199851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5335892657972336950399205 1000479873369813178199851)
            ·
              refine ⟨1500719810054719767299777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1000479873369813178199851 1500719810054719767299777)
              ·
                refine ⟨1125539857541039825474833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1500719810054719767299777 1125539857541039825474833)
                ·
                  refine ⟨844154893155779869106125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1125539857541039825474833 844154893155779869106125)
                  ·
                    refine ⟨316558084933417450914797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 844154893155779869106125 316558084933417450914797)
                    ·
                      rfl

theorem cell22_924742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 4, 1, 2, 2, 3].length) (baseStart_924742 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_924742 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_924742 prefixEnd_924742 := by exact prefixLift 924742
  have htrace : WordTrace (prefixWord ++ tailWord_924742) baseStart_924742 baseEnd_924742 := by
    simpa [prefixWord, tailWord_924742, baseEnd_924742] using wordTrace_append hprefix tailTrace_924742
  have hstable : (prefixWord ++ tailWord_924742).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_924742).length < 2 ^ (prefixWord ++ tailWord_924742).sum := by decide
  have hdescent : baseEnd_924742 < baseStart_924742 := by decide
  rcases family_descends (prefixWord ++ tailWord_924742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_924753 : List Nat := [1, 2, 2, 1, 3, 1, 4, 4, 1, 3]
def baseStart_924753 : Nat := 118140960795 + 924753 * 2 ^ 59
def prefixEnd_924753 : Nat := 4983230072969 + 3 ^ 40 * 924753 * 2
def baseEnd_924753 : Nat := 316561850458217088889763

theorem tailTrace_924753 : CollatzResearch.WordTrace tailWord_924753 prefixEnd_924753 316561850458217088889763 := by
  unfold tailWord_924753
  simp only [CollatzResearch.WordTrace]
  refine ⟨33728512818785291083642913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22485675212523527389095275 33728512818785291083642913)
  ·
    refine ⟨25296384614088968312732185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33728512818785291083642913 25296384614088968312732185)
    ·
      refine ⟨18972288460566726234549139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25296384614088968312732185 18972288460566726234549139)
      ·
        refine ⟨28458432690850089351823709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18972288460566726234549139 28458432690850089351823709)
        ·
          refine ⟨10671912259068783506933891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28458432690850089351823709 10671912259068783506933891)
          ·
            refine ⟨16007868388603175260400837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10671912259068783506933891 16007868388603175260400837)
            ·
              refine ⟨3001475322863095361325157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16007868388603175260400837 3001475322863095361325157)
              ·
                refine ⟨562776623036830380248467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3001475322863095361325157 562776623036830380248467)
                ·
                  refine ⟨844164934555245570372701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 562776623036830380248467 844164934555245570372701)
                  ·
                    refine ⟨316561850458217088889763, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 844164934555245570372701 316561850458217088889763)
                    ·
                      rfl

theorem cell22_924753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 4, 4, 1, 3].length) (baseStart_924753 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_924753 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_924753 prefixEnd_924753 := by exact prefixLift 924753
  have htrace : WordTrace (prefixWord ++ tailWord_924753) baseStart_924753 baseEnd_924753 := by
    simpa [prefixWord, tailWord_924753, baseEnd_924753] using wordTrace_append hprefix tailTrace_924753
  have hstable : (prefixWord ++ tailWord_924753).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_924753).length < 2 ^ (prefixWord ++ tailWord_924753).sum := by decide
  have hdescent : baseEnd_924753 < baseStart_924753 := by decide
  rcases family_descends (prefixWord ++ tailWord_924753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_924796 : List Nat := [2, 2, 2, 1, 1, 3, 1, 5, 1, 4]
def baseStart_924796 : Nat := 118140960795 + 924796 * 2 ^ 59
def prefixEnd_924796 : Nat := 4983230072969 + 3 ^ 40 * 924796 * 2
def baseEnd_924796 : Nat := 316576570236979310064631

theorem tailTrace_924796 : CollatzResearch.WordTrace tailWord_924796 prefixEnd_924796 316576570236979310064631 := by
  unfold tailWord_924796
  simp only [CollatzResearch.WordTrace]
  refine ⟨16865040578814754713729121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22486720771753006284972161 16865040578814754713729121)
  ·
    refine ⟨12648780434111066035296841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16865040578814754713729121 12648780434111066035296841)
    ·
      refine ⟨9486585325583299526472631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12648780434111066035296841 9486585325583299526472631)
      ·
        refine ⟨14229877988374949289708947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9486585325583299526472631 14229877988374949289708947)
        ·
          refine ⟨21344816982562423934563421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14229877988374949289708947 21344816982562423934563421)
          ·
            refine ⟨8004306368460908975461283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21344816982562423934563421 8004306368460908975461283)
            ·
              refine ⟨12006459552691363463191925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8004306368460908975461283 12006459552691363463191925)
              ·
                refine ⟨1125605583064815324674243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12006459552691363463191925 1125605583064815324674243)
                ·
                  refine ⟨1688408374597222987011365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1125605583064815324674243 1688408374597222987011365)
                  ·
                    refine ⟨316576570236979310064631, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1688408374597222987011365 316576570236979310064631)
                    ·
                      rfl

theorem cell22_924796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 1, 5, 1, 4].length) (baseStart_924796 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_924796 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_924796 prefixEnd_924796 := by exact prefixLift 924796
  have htrace : WordTrace (prefixWord ++ tailWord_924796) baseStart_924796 baseEnd_924796 := by
    simpa [prefixWord, tailWord_924796, baseEnd_924796] using wordTrace_append hprefix tailTrace_924796
  have hstable : (prefixWord ++ tailWord_924796).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_924796).length < 2 ^ (prefixWord ++ tailWord_924796).sum := by decide
  have hdescent : baseEnd_924796 < baseStart_924796 := by decide
  rcases family_descends (prefixWord ++ tailWord_924796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_924811 : List Nat := [1, 1, 1, 1, 4, 1, 1, 8, 4]
def baseStart_924811 : Nat := 118140960795 + 924811 * 2 ^ 59
def prefixEnd_924811 : Nat := 4983230072969 + 3 ^ 40 * 924811 * 2
def baseEnd_924811 : Nat := 105527235014508090313195

theorem tailTrace_924811 : CollatzResearch.WordTrace tailWord_924811 prefixEnd_924811 105527235014508090313195 := by
  unfold tailWord_924811
  simp only [CollatzResearch.WordTrace]
  refine ⟨33730628252575166989254287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22487085501716777992836191 33730628252575166989254287)
  ·
    refine ⟨50595942378862750483881431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33730628252575166989254287 50595942378862750483881431)
    ·
      refine ⟨75893913568294125725822147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50595942378862750483881431 75893913568294125725822147)
      ·
        refine ⟨113840870352441188588733221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75893913568294125725822147 113840870352441188588733221)
        ·
          refine ⟨21345163191082722860387479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 113840870352441188588733221 21345163191082722860387479)
          ·
            refine ⟨32017744786624084290581219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21345163191082722860387479 32017744786624084290581219)
            ·
              refine ⟨48026617179936126435871829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32017744786624084290581219 48026617179936126435871829)
              ·
                refine ⟨562811920077376481670373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 48026617179936126435871829 562811920077376481670373)
                ·
                  refine ⟨105527235014508090313195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 562811920077376481670373 105527235014508090313195)
                  ·
                    rfl

theorem cell22_924811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 8, 4].length) (baseStart_924811 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_924811 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_924811 prefixEnd_924811 := by exact prefixLift 924811
  have htrace : WordTrace (prefixWord ++ tailWord_924811) baseStart_924811 baseEnd_924811 := by
    simpa [prefixWord, tailWord_924811, baseEnd_924811] using wordTrace_append hprefix tailTrace_924811
  have hstable : (prefixWord ++ tailWord_924811).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_924811).length < 2 ^ (prefixWord ++ tailWord_924811).sum := by decide
  have hdescent : baseEnd_924811 < baseStart_924811 := by decide
  rcases family_descends (prefixWord ++ tailWord_924811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_924830 : List Nat := [4, 3, 1, 1, 2, 1, 3, 2, 1, 4]
def baseStart_924830 : Nat := 118140960795 + 924830 * 2 ^ 59
def prefixEnd_924830 : Nat := 4983230072969 + 3 ^ 40 * 924830 * 2
def baseEnd_924830 : Nat := 316588209131814554714527

theorem tailTrace_924830 : CollatzResearch.WordTrace tailWord_924830 prefixEnd_924830 316588209131814554714527 := by
  unfold tailWord_924830
  simp only [CollatzResearch.WordTrace]
  refine ⟨4216415154938291654274493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22487547493004222156130629 4216415154938291654274493)
  ·
    refine ⟨1581155683101859370352935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4216415154938291654274493 1581155683101859370352935)
    ·
      refine ⟨2371733524652789055529403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1581155683101859370352935 2371733524652789055529403)
      ·
        refine ⟨3557600286979183583294105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2371733524652789055529403 3557600286979183583294105)
        ·
          refine ⟨2668200215234387687470579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3557600286979183583294105 2668200215234387687470579)
          ·
            refine ⟨4002300322851581531205869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2668200215234387687470579 4002300322851581531205869)
            ·
              refine ⟨1500862621069343074202201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4002300322851581531205869 1500862621069343074202201)
              ·
                refine ⟨1125646965802007305651651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1500862621069343074202201 1125646965802007305651651)
                ·
                  refine ⟨1688470448703010958477477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1125646965802007305651651 1688470448703010958477477)
                  ·
                    refine ⟨316588209131814554714527, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1688470448703010958477477 316588209131814554714527)
                    ·
                      rfl

theorem cell22_924830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 3, 2, 1, 4].length) (baseStart_924830 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_924830 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_924830 prefixEnd_924830 := by exact prefixLift 924830
  have htrace : WordTrace (prefixWord ++ tailWord_924830) baseStart_924830 baseEnd_924830 := by
    simpa [prefixWord, tailWord_924830, baseEnd_924830] using wordTrace_append hprefix tailTrace_924830
  have hstable : (prefixWord ++ tailWord_924830).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_924830).length < 2 ^ (prefixWord ++ tailWord_924830).sum := by decide
  have hdescent : baseEnd_924830 < baseStart_924830 := by decide
  rcases family_descends (prefixWord ++ tailWord_924830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_924860 : List Nat := [2, 2, 2, 3, 2, 2, 2, 2, 2, 3]
def baseStart_924860 : Nat := 118140960795 + 924860 * 2 ^ 59
def prefixEnd_924860 : Nat := 4983230072969 + 3 ^ 40 * 924860 * 2
def baseEnd_924860 : Nat := 316598478744904476464435

theorem tailTrace_924860 : CollatzResearch.WordTrace tailWord_924860 prefixEnd_924860 316598478744904476464435 := by
  unfold tailWord_924860
  simp only [CollatzResearch.WordTrace]
  refine ⟨16866207714698824178894017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22488276952931765571858689 16866207714698824178894017)
  ·
    refine ⟨12649655786024118134170513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16866207714698824178894017 12649655786024118134170513)
    ·
      refine ⟨9487241839518088600627885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12649655786024118134170513 9487241839518088600627885)
      ·
        refine ⟨3557715689819283225235457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9487241839518088600627885 3557715689819283225235457)
        ·
          refine ⟨2668286767364462418926593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3557715689819283225235457 2668286767364462418926593)
          ·
            refine ⟨2001215075523346814194945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2668286767364462418926593 2001215075523346814194945)
            ·
              refine ⟨1500911306642510110646209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2001215075523346814194945 1500911306642510110646209)
              ·
                refine ⟨1125683479981882582984657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1500911306642510110646209 1125683479981882582984657)
                ·
                  refine ⟨844262609986411937238493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1125683479981882582984657 844262609986411937238493)
                  ·
                    refine ⟨316598478744904476464435, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 844262609986411937238493 316598478744904476464435)
                    ·
                      rfl

theorem cell22_924860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 2, 2, 2, 2, 3].length) (baseStart_924860 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_924860 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_924860 prefixEnd_924860 := by exact prefixLift 924860
  have htrace : WordTrace (prefixWord ++ tailWord_924860) baseStart_924860 baseEnd_924860 := by
    simpa [prefixWord, tailWord_924860, baseEnd_924860] using wordTrace_append hprefix tailTrace_924860
  have hstable : (prefixWord ++ tailWord_924860).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_924860).length < 2 ^ (prefixWord ++ tailWord_924860).sum := by decide
  have hdescent : baseEnd_924860 < baseStart_924860 := by decide
  rcases family_descends (prefixWord ++ tailWord_924860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_924862 : List Nat := [4, 2, 1, 1, 3, 3, 2, 2, 4]
def baseStart_924862 : Nat := 118140960795 + 924862 * 2 ^ 59
def prefixEnd_924862 : Nat := 4983230072969 + 3 ^ 40 * 924862 * 2
def baseEnd_924862 : Nat := 105533054461925712638143

theorem tailTrace_924862 : CollatzResearch.WordTrace tailWord_924862 prefixEnd_924862 105533054461925712638143 := by
  unfold tailWord_924862
  simp only [CollatzResearch.WordTrace]
  refine ⟨4216561046923800337420105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 22488325583593601799573893 4216561046923800337420105)
  ·
    refine ⟨3162420785192850253065079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4216561046923800337420105 3162420785192850253065079)
    ·
      refine ⟨4743631177789275379597619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3162420785192850253065079 4743631177789275379597619)
      ·
        refine ⟨7115446766683913069396429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4743631177789275379597619 7115446766683913069396429)
        ·
          refine ⟨2668292537506467401023661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7115446766683913069396429 2668292537506467401023661)
          ·
            refine ⟨1000609701564925275383873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2668292537506467401023661 1000609701564925275383873)
            ·
              refine ⟨750457276173693956537905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1000609701564925275383873 750457276173693956537905)
              ·
                refine ⟨562842957130270467403429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 750457276173693956537905 562842957130270467403429)
                ·
                  refine ⟨105533054461925712638143, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 562842957130270467403429 105533054461925712638143)
                  ·
                    rfl

theorem cell22_924862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 3, 2, 2, 4].length) (baseStart_924862 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_924862 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_924862 prefixEnd_924862 := by exact prefixLift 924862
  have htrace : WordTrace (prefixWord ++ tailWord_924862) baseStart_924862 baseEnd_924862 := by
    simpa [prefixWord, tailWord_924862, baseEnd_924862] using wordTrace_append hprefix tailTrace_924862
  have hstable : (prefixWord ++ tailWord_924862).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_924862).length < 2 ^ (prefixWord ++ tailWord_924862).sum := by decide
  have hdescent : baseEnd_924862 < baseStart_924862 := by decide
  rcases family_descends (prefixWord ++ tailWord_924862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_924871 : List Nat := [1, 1, 4, 1, 1, 1, 1, 2, 7, 3]
def baseStart_924871 : Nat := 118140960795 + 924871 * 2 ^ 59
def prefixEnd_924871 : Nat := 4983230072969 + 3 ^ 40 * 924871 * 2
def baseEnd_924871 : Nat := 316602244269704114439401

theorem tailTrace_924871 : CollatzResearch.WordTrace tailWord_924871 prefixEnd_924871 316602244269704114439401 := by
  unfold tailWord_924871
  simp only [CollatzResearch.WordTrace]
  refine ⟨33732816632357797236438467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22488544421571864824292311 33732816632357797236438467)
  ·
    refine ⟨50599224948536695854657701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33732816632357797236438467 50599224948536695854657701)
    ·
      refine ⟨9487354677850630472748319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 50599224948536695854657701 9487354677850630472748319)
      ·
        refine ⟨14231032016775945709122479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9487354677850630472748319 14231032016775945709122479)
        ·
          refine ⟨21346548025163918563683719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14231032016775945709122479 21346548025163918563683719)
          ·
            refine ⟨32019822037745877845525579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21346548025163918563683719 32019822037745877845525579)
            ·
              refine ⟨48029733056618816768288369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32019822037745877845525579 48029733056618816768288369)
              ·
                refine ⟨36022299792464112576216277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48029733056618816768288369 36022299792464112576216277)
                ·
                  refine ⟨844272651385877638505069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 36022299792464112576216277 844272651385877638505069)
                  ·
                    refine ⟨316602244269704114439401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 844272651385877638505069 316602244269704114439401)
                    ·
                      rfl

theorem cell22_924871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 2, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 2, 7, 3].length) (baseStart_924871 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_924871 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_924871 prefixEnd_924871 := by exact prefixLift 924871
  have htrace : WordTrace (prefixWord ++ tailWord_924871) baseStart_924871 baseEnd_924871 := by
    simpa [prefixWord, tailWord_924871, baseEnd_924871] using wordTrace_append hprefix tailTrace_924871
  have hstable : (prefixWord ++ tailWord_924871).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_924871).length < 2 ^ (prefixWord ++ tailWord_924871).sum := by decide
  have hdescent : baseEnd_924871 < baseStart_924871 := by decide
  rcases family_descends (prefixWord ++ tailWord_924871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_924877 : List Nat := [1, 6, 2, 2, 1, 1, 2, 1, 1, 5]
def baseStart_924877 : Nat := 118140960795 + 924877 * 2 ^ 59
def prefixEnd_924877 : Nat := 4983230072969 + 3 ^ 40 * 924877 * 2
def baseEnd_924877 : Nat := 316604298192322098789383

theorem tailTrace_924877 : CollatzResearch.WordTrace tailWord_924877 prefixEnd_924877 316604298192322098789383 := by
  unfold tailWord_924877
  simp only [CollatzResearch.WordTrace]
  refine ⟨33733035470336060261156885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22488690313557373507437923 33733035470336060261156885)
  ·
    refine ⟨1581236037672002824741729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 33733035470336060261156885 1581236037672002824741729)
    ·
      refine ⟨1185927028254002118556297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1581236037672002824741729 1185927028254002118556297)
      ·
        refine ⟨889445271190501588917223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1185927028254002118556297 889445271190501588917223)
        ·
          refine ⟨1334167906785752383375835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 889445271190501588917223 1334167906785752383375835)
          ·
            refine ⟨2001251860178628575063753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1334167906785752383375835 2001251860178628575063753)
            ·
              refine ⟨1500938895133971431297815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2001251860178628575063753 1500938895133971431297815)
              ·
                refine ⟨2251408342700957146946723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1500938895133971431297815 2251408342700957146946723)
                ·
                  refine ⟨3377112514051435720420085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2251408342700957146946723 3377112514051435720420085)
                  ·
                    refine ⟨316604298192322098789383, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3377112514051435720420085 316604298192322098789383)
                    ·
                      rfl

theorem cell22_924877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 1, 2, 1, 1, 5].length) (baseStart_924877 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_924877 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_924877 prefixEnd_924877 := by exact prefixLift 924877
  have htrace : WordTrace (prefixWord ++ tailWord_924877) baseStart_924877 baseEnd_924877 := by
    simpa [prefixWord, tailWord_924877, baseEnd_924877] using wordTrace_append hprefix tailTrace_924877
  have hstable : (prefixWord ++ tailWord_924877).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_924877).length < 2 ^ (prefixWord ++ tailWord_924877).sum := by decide
  have hdescent : baseEnd_924877 < baseStart_924877 := by decide
  rcases family_descends (prefixWord ++ tailWord_924877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_924961 : List Nat := [1, 2, 3, 2, 1, 1, 1, 3, 3, 5]
def baseStart_924961 : Nat := 118140960795 + 924961 * 2 ^ 59
def prefixEnd_924961 : Nat := 4983230072969 + 3 ^ 40 * 924961 * 2
def baseEnd_924961 : Nat := 316633053108973879689125

theorem tailTrace_924961 : CollatzResearch.WordTrace tailWord_924961 prefixEnd_924961 316633053108973879689125 := by
  unfold tailWord_924961
  simp only [CollatzResearch.WordTrace]
  refine ⟨33736099202031742607214737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22490732801354495071476491 33736099202031742607214737)
  ·
    refine ⟨25302074401523806955411053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33736099202031742607214737 25302074401523806955411053)
    ·
      refine ⟨9488277900571427608279145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25302074401523806955411053 9488277900571427608279145)
      ·
        refine ⟨7116208425428570706209359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9488277900571427608279145 7116208425428570706209359)
        ·
          refine ⟨10674312638142856059314039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7116208425428570706209359 10674312638142856059314039)
          ·
            refine ⟨16011468957214284088971059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10674312638142856059314039 16011468957214284088971059)
            ·
              refine ⟨24017203435821426133456589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16011468957214284088971059 24017203435821426133456589)
              ·
                refine ⟨9006451288433034800046221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24017203435821426133456589 9006451288433034800046221)
                ·
                  refine ⟨3377419233162388050017333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9006451288433034800046221 3377419233162388050017333)
                  ·
                    refine ⟨316633053108973879689125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3377419233162388050017333 316633053108973879689125)
                    ·
                      rfl

theorem cell22_924961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 3, 3, 5].length) (baseStart_924961 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_924961 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_924961 prefixEnd_924961 := by exact prefixLift 924961
  have htrace : WordTrace (prefixWord ++ tailWord_924961) baseStart_924961 baseEnd_924961 := by
    simpa [prefixWord, tailWord_924961, baseEnd_924961] using wordTrace_append hprefix tailTrace_924961
  have hstable : (prefixWord ++ tailWord_924961).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_924961).length < 2 ^ (prefixWord ++ tailWord_924961).sum := by decide
  have hdescent : baseEnd_924961 < baseStart_924961 := by decide
  rcases family_descends (prefixWord ++ tailWord_924961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_924991 : List Nat := [1, 1, 2, 2, 4, 2, 1, 9]
def baseStart_924991 : Nat := 118140960795 + 924991 * 2 ^ 59
def prefixEnd_924991 : Nat := 4983230072969 + 3 ^ 40 * 924991 * 2
def baseEnd_924991 : Nat := 35182591413562644604337

theorem tailTrace_924991 : CollatzResearch.WordTrace tailWord_924991 prefixEnd_924991 35182591413562644604337 := by
  unfold tailWord_924991
  simp only [CollatzResearch.WordTrace]
  refine ⟨33737193391923057730806827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22491462261282038487204551 33737193391923057730806827)
  ·
    refine ⟨50605790087884586596210241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33737193391923057730806827 50605790087884586596210241)
    ·
      refine ⟨37954342565913439947157681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50605790087884586596210241 37954342565913439947157681)
      ·
        refine ⟨28465756924435079960368261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37954342565913439947157681 28465756924435079960368261)
        ·
          refine ⟨5337329423331577492569049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28465756924435079960368261 5337329423331577492569049)
          ·
            refine ⟨4002997067498683119426787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5337329423331577492569049 4002997067498683119426787)
            ·
              refine ⟨6004495601248024679140181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4002997067498683119426787 6004495601248024679140181)
              ·
                refine ⟨35182591413562644604337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 6004495601248024679140181 35182591413562644604337)
                ·
                  rfl

theorem cell22_924991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 1, 9].length) (baseStart_924991 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_924991 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_924991 prefixEnd_924991 := by exact prefixLift 924991
  have htrace : WordTrace (prefixWord ++ tailWord_924991) baseStart_924991 baseEnd_924991 := by
    simpa [prefixWord, tailWord_924991, baseEnd_924991] using wordTrace_append hprefix tailTrace_924991
  have hstable : (prefixWord ++ tailWord_924991).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_924991).length < 2 ^ (prefixWord ++ tailWord_924991).sum := by decide
  have hdescent : baseEnd_924991 < baseStart_924991 := by decide
  rcases family_descends (prefixWord ++ tailWord_924991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_925053 : List Nat := [1, 4, 1, 1, 2, 2, 1, 5, 5]
def baseStart_925053 : Nat := 118140960795 + 925053 * 2 ^ 59
def prefixEnd_925053 : Nat := 4983230072969 + 3 ^ 40 * 925053 * 2
def baseEnd_925053 : Nat := 105554848863038768796281

theorem tailTrace_925053 : CollatzResearch.WordTrace tailWord_925053 prefixEnd_925053 105554848863038768796281 := by
  unfold tailWord_925053
  simp only [CollatzResearch.WordTrace]
  refine ⟨33739454717698442319563813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22492969811798961546375875 33739454717698442319563813)
  ·
    refine ⟨6326147759568457934918215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 33739454717698442319563813 6326147759568457934918215)
    ·
      refine ⟨9489221639352686902377323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6326147759568457934918215 9489221639352686902377323)
      ·
        refine ⟨14233832459029030353565985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9489221639352686902377323 14233832459029030353565985)
        ·
          refine ⟨10675374344271772765174489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14233832459029030353565985 10675374344271772765174489)
          ·
            refine ⟨8006530758203829573880867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10675374344271772765174489 8006530758203829573880867)
            ·
              refine ⟨12009796137305744360821301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8006530758203829573880867 12009796137305744360821301)
              ·
                refine ⟨1125918387872413533826997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12009796137305744360821301 1125918387872413533826997)
                ·
                  refine ⟨105554848863038768796281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1125918387872413533826997 105554848863038768796281)
                  ·
                    rfl

theorem cell22_925053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 1, 5, 5].length) (baseStart_925053 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_925053 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_925053 prefixEnd_925053 := by exact prefixLift 925053
  have htrace : WordTrace (prefixWord ++ tailWord_925053) baseStart_925053 baseEnd_925053 := by
    simpa [prefixWord, tailWord_925053, baseEnd_925053] using wordTrace_append hprefix tailTrace_925053
  have hstable : (prefixWord ++ tailWord_925053).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_925053).length < 2 ^ (prefixWord ++ tailWord_925053).sum := by decide
  have hdescent : baseEnd_925053 < baseStart_925053 := by decide
  rcases family_descends (prefixWord ++ tailWord_925053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_925057 : List Nat := [1, 2, 4, 3, 2, 1, 1, 2, 3, 3]
def baseStart_925057 : Nat := 118140960795 + 925057 * 2 ^ 59
def prefixEnd_925057 : Nat := 4983230072969 + 3 ^ 40 * 925057 * 2
def baseEnd_925057 : Nat := 316665915870861629288831

theorem tailTrace_925057 : CollatzResearch.WordTrace tailWord_925057 prefixEnd_925057 316665915870861629288831 := by
  unfold tailWord_925057
  simp only [CollatzResearch.WordTrace]
  refine ⟨33739600609683951002709425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22493067073122634001806283 33739600609683951002709425)
  ·
    refine ⟨25304700457262963252032069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33739600609683951002709425 25304700457262963252032069)
    ·
      refine ⟨4744631335736805609756013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25304700457262963252032069 4744631335736805609756013)
      ·
        refine ⟨1779236750901302103658505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4744631335736805609756013 1779236750901302103658505)
        ·
          refine ⟨1334427563175976577743879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1779236750901302103658505 1334427563175976577743879)
          ·
            refine ⟨2001641344763964866615819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1334427563175976577743879 2001641344763964866615819)
            ·
              refine ⟨3002462017145947299923729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2001641344763964866615819 3002462017145947299923729)
              ·
                refine ⟨2251846512859460474942797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3002462017145947299923729 2251846512859460474942797)
                ·
                  refine ⟨844442442322297678103549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2251846512859460474942797 844442442322297678103549)
                  ·
                    refine ⟨316665915870861629288831, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 844442442322297678103549 316665915870861629288831)
                    ·
                      rfl

theorem cell22_925057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 1, 1, 2, 3, 3].length) (baseStart_925057 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_925057 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_925057 prefixEnd_925057 := by exact prefixLift 925057
  have htrace : WordTrace (prefixWord ++ tailWord_925057) baseStart_925057 baseEnd_925057 := by
    simpa [prefixWord, tailWord_925057, baseEnd_925057] using wordTrace_append hprefix tailTrace_925057
  have hstable : (prefixWord ++ tailWord_925057).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_925057).length < 2 ^ (prefixWord ++ tailWord_925057).sum := by decide
  have hdescent : baseEnd_925057 < baseStart_925057 := by decide
  rcases family_descends (prefixWord ++ tailWord_925057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_925128 : List Nat := [2, 1, 3, 1, 3, 1, 1, 3, 1, 6]
def baseStart_925128 : Nat := 118140960795 + 925128 * 2 ^ 59
def prefixEnd_925128 : Nat := 4983230072969 + 3 ^ 40 * 925128 * 2
def baseEnd_925128 : Nat := 316690220621841110763613

theorem tailTrace_925128 : CollatzResearch.WordTrace tailWord_925128 prefixEnd_925128 316690220621841110763613 := by
  unfold tailWord_925128
  simp only [CollatzResearch.WordTrace]
  refine ⟨16871095096213365064272019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22494793461617820085696025 16871095096213365064272019)
  ·
    refine ⟨25306642644320047596408029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16871095096213365064272019 25306642644320047596408029)
    ·
      refine ⟨9489990991620017848653011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25306642644320047596408029 9489990991620017848653011)
      ·
        refine ⟨14234986487430026772979517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9489990991620017848653011 14234986487430026772979517)
        ·
          refine ⟨5338119932786260039867319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14234986487430026772979517 5338119932786260039867319)
          ·
            refine ⟨8007179899179390059800979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5338119932786260039867319 8007179899179390059800979)
            ·
              refine ⟨12010769848769085089701469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8007179899179390059800979 12010769848769085089701469)
              ·
                refine ⟨4504038693288406908638051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12010769848769085089701469 4504038693288406908638051)
                ·
                  refine ⟨6756058039932610362957077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4504038693288406908638051 6756058039932610362957077)
                  ·
                    refine ⟨316690220621841110763613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6756058039932610362957077 316690220621841110763613)
                    ·
                      rfl

theorem cell22_925128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 1, 3, 1, 6].length) (baseStart_925128 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_925128 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_925128 prefixEnd_925128 := by exact prefixLift 925128
  have htrace : WordTrace (prefixWord ++ tailWord_925128) baseStart_925128 baseEnd_925128 := by
    simpa [prefixWord, tailWord_925128, baseEnd_925128] using wordTrace_append hprefix tailTrace_925128
  have hstable : (prefixWord ++ tailWord_925128).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_925128).length < 2 ^ (prefixWord ++ tailWord_925128).sum := by decide
  have hdescent : baseEnd_925128 < baseStart_925128 := by decide
  rcases family_descends (prefixWord ++ tailWord_925128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_925130 : List Nat := [3, 1, 2, 1, 2, 3, 1, 2, 4, 3]
def baseStart_925130 : Nat := 118140960795 + 925130 * 2 ^ 59
def prefixEnd_925130 : Nat := 4983230072969 + 3 ^ 40 * 925130 * 2
def baseEnd_925130 : Nat := 316690905262713772213607

theorem tailTrace_925130 : CollatzResearch.WordTrace tailWord_925130 prefixEnd_925130 316690905262713772213607 := by
  unfold tailWord_925130
  simp only [CollatzResearch.WordTrace]
  refine ⟨8435565784604871117529211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 22494842092279656313411229 8435565784604871117529211)
  ·
    refine ⟨12653348676907306676293817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8435565784604871117529211 12653348676907306676293817)
    ·
      refine ⟨9490011507680480007220363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12653348676907306676293817 9490011507680480007220363)
      ·
        refine ⟨14235017261520720010830545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9490011507680480007220363 14235017261520720010830545)
        ·
          refine ⟨10676262946140540008122909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14235017261520720010830545 10676262946140540008122909)
          ·
            refine ⟨4003598604802702503046091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10676262946140540008122909 4003598604802702503046091)
            ·
              refine ⟨6005397907204053754569137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4003598604802702503046091 6005397907204053754569137)
              ·
                refine ⟨4504048430403040315926853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6005397907204053754569137 4504048430403040315926853)
                ·
                  refine ⟨844509080700570059236285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4504048430403040315926853 844509080700570059236285)
                  ·
                    refine ⟨316690905262713772213607, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 844509080700570059236285 316690905262713772213607)
                    ·
                      rfl

theorem cell22_925130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 1, 2, 4, 3].length) (baseStart_925130 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_925130 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_925130 prefixEnd_925130 := by exact prefixLift 925130
  have htrace : WordTrace (prefixWord ++ tailWord_925130) baseStart_925130 baseEnd_925130 := by
    simpa [prefixWord, tailWord_925130, baseEnd_925130] using wordTrace_append hprefix tailTrace_925130
  have hstable : (prefixWord ++ tailWord_925130).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_925130).length < 2 ^ (prefixWord ++ tailWord_925130).sum := by decide
  have hdescent : baseEnd_925130 < baseStart_925130 := by decide
  rcases family_descends (prefixWord ++ tailWord_925130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_925132 : List Nat := [2, 2, 1, 4, 2, 1, 3, 3, 4]
def baseStart_925132 : Nat := 118140960795 + 925132 * 2 ^ 59
def prefixEnd_925132 : Nat := 4983230072969 + 3 ^ 40 * 925132 * 2
def baseEnd_925132 : Nat := 105563863301195477887867

theorem tailTrace_925132 : CollatzResearch.WordTrace tailWord_925132 prefixEnd_925132 105563863301195477887867 := by
  unfold tailWord_925132
  simp only [CollatzResearch.WordTrace]
  refine ⟨16871168042206119405844825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 22494890722941492541126433 16871168042206119405844825)
  ·
    refine ⟨12653376031654589554383619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16871168042206119405844825 12653376031654589554383619)
    ·
      refine ⟨18980064047481884331575429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12653376031654589554383619 18980064047481884331575429)
      ·
        refine ⟨3558762008902853312170393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18980064047481884331575429 3558762008902853312170393)
        ·
          refine ⟨2669071506677139984127795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3558762008902853312170393 2669071506677139984127795)
          ·
            refine ⟨4003607260015709976191693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2669071506677139984127795 4003607260015709976191693)
            ·
              refine ⟨1501352722505891241071885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4003607260015709976191693 1501352722505891241071885)
              ·
                refine ⟨563007270939709215401957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1501352722505891241071885 563007270939709215401957)
                ·
                  refine ⟨105563863301195477887867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 563007270939709215401957 105563863301195477887867)
                  ·
                    rfl

theorem cell22_925132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 3, 3, 4].length) (baseStart_925132 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_925132 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_925132 prefixEnd_925132 := by exact prefixLift 925132
  have htrace : WordTrace (prefixWord ++ tailWord_925132) baseStart_925132 baseEnd_925132 := by
    simpa [prefixWord, tailWord_925132, baseEnd_925132] using wordTrace_append hprefix tailTrace_925132
  have hstable : (prefixWord ++ tailWord_925132).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_925132).length < 2 ^ (prefixWord ++ tailWord_925132).sum := by decide
  have hdescent : baseEnd_925132 < baseStart_925132 := by decide
  rcases family_descends (prefixWord ++ tailWord_925132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_925145 : List Nat := [1, 2, 1, 2, 4, 3, 1, 2, 2, 4]
def baseStart_925145 : Nat := 118140960795 + 925145 * 2 ^ 59
def prefixEnd_925145 : Nat := 4983230072969 + 3 ^ 40 * 925145 * 2
def baseEnd_925145 : Nat := 316696040069258733088561

theorem tailTrace_925145 : CollatzResearch.WordTrace tailWord_925145 prefixEnd_925145 316696040069258733088561 := by
  unfold tailWord_925145
  simp only [CollatzResearch.WordTrace]
  refine ⟨33742810233365142031912889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 22495206822243428021275259 33742810233365142031912889)
  ·
    refine ⟨25307107675023856523934667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33742810233365142031912889 25307107675023856523934667)
    ·
      refine ⟨37960661512535784785902001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25307107675023856523934667 37960661512535784785902001)
      ·
        refine ⟨28470496134401838589426501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37960661512535784785902001 28470496134401838589426501)
        ·
          refine ⟨5338218025200344735517469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28470496134401838589426501 5338218025200344735517469)
          ·
            refine ⟨2001831759450129275819051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5338218025200344735517469 2001831759450129275819051)
            ·
              refine ⟨3002747639175193913728577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2001831759450129275819051 3002747639175193913728577)
              ·
                refine ⟨2252060729381395435296433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3002747639175193913728577 2252060729381395435296433)
                ·
                  refine ⟨1689045547036046576472325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2252060729381395435296433 1689045547036046576472325)
                  ·
                    refine ⟨316696040069258733088561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1689045547036046576472325 316696040069258733088561)
                    ·
                      rfl

theorem cell22_925145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 3, 1, 2, 2, 4].length) (baseStart_925145 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_925145 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_925145 prefixEnd_925145 := by exact prefixLift 925145
  have htrace : WordTrace (prefixWord ++ tailWord_925145) baseStart_925145 baseEnd_925145 := by
    simpa [prefixWord, tailWord_925145, baseEnd_925145] using wordTrace_append hprefix tailTrace_925145
  have hstable : (prefixWord ++ tailWord_925145).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_925145).length < 2 ^ (prefixWord ++ tailWord_925145).sum := by decide
  have hdescent : baseEnd_925145 < baseStart_925145 := by decide
  rcases family_descends (prefixWord ++ tailWord_925145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
